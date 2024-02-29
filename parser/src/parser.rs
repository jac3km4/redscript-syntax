use crate::lexer::Token;
use chumsky::{input::SpannedInput, prelude::*};

mod expr;
mod item;
mod stmt;

pub use expr::expr;
pub use item::{item, item_decl};
use redscript_ast::{
    Block, Expr, FileId, Module, Path, Span, Spanned, SpannedBlock, SpannedModule, SpannedStmt,
    Stmt, Type,
};
pub use stmt::stmt;

use self::{item::item_decl_rec, stmt::stmt_rec};

pub type ParserInput<'tok, 'src> = SpannedInput<Token<'src>, Span, &'tok [(Token<'src>, Span)]>;

pub type ParserExtra<'tok, 'src> = extra::Full<Rich<'tok, Token<'src>, Span>, (), FileId>;

pub trait Parse<'tok, 'src: 'tok, A>:
    Parser<'tok, ParserInput<'tok, 'src>, A, ParserExtra<'tok, 'src>> + Clone
{
}

impl<'tok, 'src: 'tok, A, P> Parse<'tok, 'src, A> for P where
    P: Parser<'tok, ParserInput<'tok, 'src>, A, ParserExtra<'tok, 'src>> + Clone
{
}

pub fn module<'tok, 'src: 'tok>() -> impl Parse<'tok, 'src, SpannedModule<'src>> {
    let mut item_decl = Recursive::declare();
    item_decl.define(item_decl_rec(item_decl.clone()));

    just(Token::Ident("module"))
        .ignore_then(
            ident()
                .separated_by(just(Token::Period))
                .at_least(1)
                .collect::<Vec<_>>(),
        )
        .or_not()
        .then(
            item_decl
                .map_with(|i, e| (i, e.span()))
                .repeated()
                .collect::<Vec<_>>(),
        )
        .map(|(path, items)| Module::new(path.map(Path::new), items))
}

#[inline]
fn block<'tok, 'src: 'tok>() -> impl Parse<'tok, 'src, SpannedBlock<'src>> {
    let mut stmt = Recursive::declare();
    stmt.define(stmt_rec(stmt.clone()));
    block_rec(stmt)
}

fn block_rec<'tok, 'src: 'tok>(
    stmt: impl Parse<'tok, 'src, SpannedStmt<'src>>,
) -> impl Parse<'tok, 'src, SpannedBlock<'src>> {
    stmt.map_with(|stmt, e| (stmt, e.span()))
        .repeated()
        .collect::<Vec<_>>()
        .delimited_by(just(Token::LBrace), just(Token::RBrace))
        .map(Block::new)
        .recover_with(via_parser(nested_delimiters(
            Token::LBrace,
            Token::RBrace,
            [
                (Token::LParen, Token::RParen),
                (Token::LBracket, Token::RBracket),
            ],
            |span| Block::single((Stmt::Expr((Expr::Error, span).into()), span)),
        )))
        .labelled("block")
}

fn ident<'tok, 'src: 'tok>() -> impl Parse<'tok, 'src, &'src str> {
    select! {
        Token::Ident(ident) => ident,
    }
    .labelled("identifier")
}

#[inline]
fn type_with_span<'tok, 'src: 'tok>() -> impl Parse<'tok, 'src, Spanned<Type<'src>>> {
    type_().map_with(|ty, e| (ty, e.span()))
}

#[inline(never)]
fn type_<'tok, 'src: 'tok>() -> impl Parse<'tok, 'src, Type<'src>> {
    recursive(|this| {
        let array_size = select! {  Token::Int(i) => i };
        choice((
            this.clone()
                .then(just(Token::Semicolon).ignore_then(array_size).or_not())
                .delimited_by(just(Token::LBracket), just(Token::RBracket))
                .map(|(ex, size)| match size {
                    Some(size) => Type::StaticArray(Box::new(ex), size as _),
                    None => Type::Array(Box::new(ex)),
                }),
            ident()
                .then(
                    this.separated_by(just(Token::Comma))
                        .collect::<Vec<_>>()
                        .delimited_by(just(Token::LAngle), just(Token::RAngle))
                        .or_not(),
                )
                .map(|(name, args)| Type::Named {
                    name,
                    args: args.unwrap_or_default().into(),
                }),
        ))
        .labelled("type")
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse_module;

    use pretty_assertions::assert_eq;
    use redscript_ast::{
        Aggregate, Constant, Function, Import, Item, ItemDecl, ItemQualifiers, Visibility,
    };

    #[test]
    fn mod_with_imports() {
        let code = r#"
        module Dummy
        import Std.*
        import Something.{Test1, Test2}
        import Exact.Path
        "#;

        let res = parse_module(code, FileId::from_u32(0))
            .0
            .unwrap()
            .unwrapped();
        assert_eq!(
            res,
            Module::new(
                Some(Path::new(["Dummy".into()])),
                [
                    ItemDecl::new(
                        [],
                        None,
                        ItemQualifiers::empty(),
                        Item::Import(Import::All(Path::new(["Std"])))
                    ),
                    ItemDecl::new(
                        [],
                        None,
                        ItemQualifiers::empty(),
                        Item::Import(Import::Select(
                            Path::new(["Something".into()]),
                            ["Test1", "Test2"].into()
                        ))
                    ),
                    ItemDecl::new(
                        [],
                        None,
                        ItemQualifiers::empty(),
                        Item::Import(Import::Exact(Path::new(["Exact", "Path"])))
                    ),
                ]
            )
        );
    }

    #[test]
    fn items() {
        let code = r#"
        public static func Dummy()

        native struct Test {}

        func Inline() -> Int32 = 1
        "#;

        let res = parse_module(code, FileId::from_u32(0))
            .0
            .unwrap()
            .unwrapped();
        assert_eq!(
            res,
            Module::new(
                None,
                [
                    ItemDecl::new(
                        [],
                        Some(Visibility::Public),
                        ItemQualifiers::STATIC,
                        Item::Function(Function::new("Dummy", [], None, None))
                    ),
                    ItemDecl::new(
                        [],
                        None,
                        ItemQualifiers::NATIVE,
                        Item::Struct(Aggregate::new("Test", None, []))
                    ),
                    ItemDecl::new(
                        [],
                        None,
                        ItemQualifiers::empty(),
                        Item::Function(Function::new(
                            "Inline",
                            [],
                            Some(Type::plain("Int32")),
                            Some(
                                Block::single(Stmt::Return(Some(
                                    Expr::Constant(Constant::I32(1)).into()
                                )))
                                .into()
                            )
                        ))
                    ),
                ]
            )
        );
    }
}
