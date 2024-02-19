use std::ops::BitOr;

use crate::{
    lexer::Token, Span, SpannedAnnotation, SpannedEnum, SpannedExpr, SpannedField, SpannedFunction,
    SpannedItem, SpannedItemDecl,
};
use chumsky::{container::Container, prelude::*};
use redscript_ast::{
    Aggregate, Annotation, Block, Enum, EnumVariant, Field, Function, Import, Item, ItemDecl,
    ItemQualifiers, Param, ParamQualifiers, Path, Stmt, Visibility,
};

use super::{block, expr::expr_with_span, ident, type_with_span, ParseError, ParserInput};

#[inline]
pub fn item_decl<'tok, 'src: 'tok>(
) -> impl Parser<'tok, ParserInput<'tok, 'src>, SpannedItemDecl<'src>, ParseError<'tok, 'src>> + Clone
{
    recursive(item_decl_rec)
}

pub fn item_decl_rec<'tok, 'src: 'tok>(
    item_decl: impl Parser<'tok, ParserInput<'tok, 'src>, SpannedItemDecl<'src>, ParseError<'tok, 'src>>
        + Clone,
) -> impl Parser<'tok, ParserInput<'tok, 'src>, SpannedItemDecl<'src>, ParseError<'tok, 'src>> + Clone
{
    annotation()
        .map_with(|a, e| (a, e.span()))
        .repeated()
        .collect::<Vec<_>>()
        .then(visibility().or_not())
        .then(item_qualifier().repeated().collect::<BitCollection<_>>())
        .then(item_rec(item_decl))
        .map(|(((annotations, visibility), qualifiers), item)| {
            ItemDecl::new(annotations, visibility, qualifiers.value, item)
        })
        .labelled("declaration")
}

#[inline]
#[allow(unused)]
pub fn item<'tok, 'src: 'tok>(
) -> impl Parser<'tok, ParserInput<'tok, 'src>, SpannedItem<'src>, ParseError<'tok, 'src>> + Clone {
    item_rec(item_decl())
}

fn item_rec<'tok, 'src: 'tok>(
    item_decl: impl Parser<'tok, ParserInput<'tok, 'src>, SpannedItemDecl<'src>, ParseError<'tok, 'src>>
        + Clone,
) -> impl Parser<'tok, ParserInput<'tok, 'src>, SpannedItem<'src>, ParseError<'tok, 'src>> + Clone {
    choice((
        import().map(Item::Import),
        aggregate(item_decl),
        enum_().map(Item::Enum),
        function().map(Item::Function),
        field().map(Item::Let),
    ))
    .labelled("item")
}

fn function<'tok, 'src: 'tok>(
) -> impl Parser<'tok, ParserInput<'tok, 'src>, SpannedFunction<'src>, ParseError<'tok, 'src>> + Clone
{
    let param_qualifiers = select! {
        Token::Ident("opt") => ParamQualifiers::OPTIONAL,
        Token::Ident("out") => ParamQualifiers::OUT,
        Token::Ident("const") => ParamQualifiers::CONST,
    }
    .labelled("parameter qualifiers");

    let ty = type_with_span();

    let params = param_qualifiers
        .repeated()
        .collect::<BitCollection<_>>()
        .then(ident())
        .then(just(Token::Colon).ignore_then(ty.clone()))
        .map_with(|((qualifiers, name), typ), e| {
            (Param::new(name, typ, qualifiers.value), e.span())
        })
        .repeated()
        .collect::<Vec<_>>()
        .delimited_by(just(Token::LParen), just(Token::RParen));

    let inline_body = just(Token::Assign)
        .ignore_then(item_expr())
        .map(|(ex, span)| Block::single((Stmt::Return(Some((ex, span).into())), span)));

    just(Token::Ident("func"))
        .ignore_then(ident())
        .then(params)
        .then(just(Token::Arrow).ignore_then(ty).or_not())
        .then(block().or(inline_body).or_not())
        .then_ignore(just(Token::Semicolon).or_not())
        .map(|(((name, params), ret_ty), body)| Function::new(name, params, ret_ty, body))
}

fn field<'tok, 'src: 'tok>(
) -> impl Parser<'tok, ParserInput<'tok, 'src>, SpannedField<'src>, ParseError<'tok, 'src>> + Clone
{
    just(Token::Ident("let"))
        .ignore_then(ident())
        .then(just(Token::Colon).ignore_then(type_with_span()))
        .then(just(Token::Assign).ignore_then(item_expr()).or_not())
        .then_ignore(just(Token::Semicolon))
        .map(|((name, ty), default)| Field::new(name, ty, default))
}

fn enum_<'tok, 'src: 'tok>(
) -> impl Parser<'tok, ParserInput<'tok, 'src>, SpannedEnum<'src>, ParseError<'tok, 'src>> + Clone {
    let int = select! { Token::Int(i) => i };

    let variants = ident()
        .then(just(Token::Assign).ignore_then(int).or_not())
        .map_with(|(name, value), e| (EnumVariant::new(name, value), e.span()))
        .separated_by(just(Token::Comma))
        .allow_trailing()
        .collect::<Vec<_>>()
        .delimited_by(just(Token::LBrace), just(Token::RBrace));

    just(Token::Ident("enum"))
        .ignore_then(ident())
        .then(variants)
        .then_ignore(just(Token::Semicolon).or_not())
        .map(|(name, variants)| Enum::new(name, variants))
}

fn aggregate<'tok, 'src: 'tok>(
    item_decl: impl Parser<'tok, ParserInput<'tok, 'src>, SpannedItemDecl<'src>, ParseError<'tok, 'src>>
        + Clone,
) -> impl Parser<'tok, ParserInput<'tok, 'src>, SpannedItem<'src>, ParseError<'tok, 'src>> + Clone {
    let is_struct = select! {
        Token::Ident("class") => false,
        Token::Ident("struct") => true,
    };

    let items = item_decl
        .map_with(|i, e| (i, e.span()))
        .repeated()
        .collect::<Vec<_>>()
        .delimited_by(just(Token::LBrace), just(Token::RBrace));

    is_struct
        .then(ident())
        .then(just(Token::Ident("extends")).ignore_then(ident()).or_not())
        .then(items)
        .then_ignore(just(Token::Semicolon).or_not())
        .map(|(((is_struct, name), extends), items)| {
            let aggregate = Aggregate::new(name, extends, items);
            if is_struct {
                Item::Struct(aggregate)
            } else {
                Item::Class(aggregate)
            }
        })
}

fn import<'tok, 'src: 'tok>(
) -> impl Parser<'tok, ParserInput<'tok, 'src>, Import<'src>, ParseError<'tok, 'src>> + Clone {
    let ident = ident();
    let import_selector = ident
        .clone()
        .separated_by(just(Token::Comma))
        .allow_trailing()
        .collect::<Vec<_>>()
        .delimited_by(just(Token::LBrace), just(Token::RBrace))
        .map(Some)
        .or(just(Token::Star).to(None));

    just(Token::Ident("import"))
        .ignore_then(
            ident
                .clone()
                .separated_by(just(Token::Period))
                .at_least(1)
                .collect::<Vec<_>>()
                .map(Path::new)
                .then(just(Token::Period).ignore_then(import_selector).or_not()),
        )
        .then_ignore(just(Token::Semicolon).or_not())
        .map(|(path, last)| match last {
            Some(Some(idents)) => Import::Select(path, idents.into()),
            Some(None) => Import::All(path),
            None => Import::Exact(path),
        })
}

fn visibility<'tok, 'src: 'tok>(
) -> impl Parser<'tok, ParserInput<'tok, 'src>, Visibility, ParseError<'tok, 'src>> + Clone {
    select! {
        Token::Ident("public") => Visibility::Public,
        Token::Ident("private") => Visibility::Private,
        Token::Ident("protected") => Visibility::Protected,
    }
    .labelled("item visibility")
}

fn annotation<'tok, 'src: 'tok>(
) -> impl Parser<'tok, ParserInput<'tok, 'src>, SpannedAnnotation<'src>, ParseError<'tok, 'src>> + Clone
{
    just(Token::At)
        .ignore_then(ident())
        .then(
            item_expr()
                .separated_by(just(Token::Comma))
                .allow_trailing()
                .collect::<Vec<_>>()
                .delimited_by(just(Token::LParen), just(Token::RParen)),
        )
        .map(|(name, args)| Annotation::new(name, args))
}

fn item_qualifier<'tok, 'src: 'tok>(
) -> impl Parser<'tok, ParserInput<'tok, 'src>, ItemQualifiers, ParseError<'tok, 'src>> + Clone {
    select! {
        Token::Ident("abstract") => ItemQualifiers::ABSTRACT,
        Token::Ident("cb") => ItemQualifiers::CALLBACK,
        Token::Ident("const") => ItemQualifiers::CONST,
        Token::Ident("exec") => ItemQualifiers::EXEC,
        Token::Ident("final") => ItemQualifiers::FINAL,
        Token::Ident("importonly") => ItemQualifiers::IMPORT_ONLY,
        Token::Ident("native") => ItemQualifiers::NATIVE,
        Token::Ident("persistent") => ItemQualifiers::PERSISTENT,
        Token::Ident("quest") => ItemQualifiers::QUEST,
        Token::Ident("static") => ItemQualifiers::STATIC

    }
    .labelled("item qualifier")
}

#[inline(never)]
fn item_expr<'tok, 'src: 'tok>(
) -> impl Parser<'tok, ParserInput<'tok, 'src>, (SpannedExpr<'src>, Span), ParseError<'tok, 'src>> + Clone
{
    expr_with_span()
}

#[derive(Debug, Default, Clone, Copy)]
struct BitCollection<A> {
    value: A,
}

impl<A: Default + Copy + BitOr<Output = A>> Container<A> for BitCollection<A> {
    #[inline]
    fn push(&mut self, item: A) {
        self.value = self.value | item;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{parse_item, parse_item_decl};

    use pretty_assertions::assert_eq;
    use redscript_ast::{Constant, Expr, Type};

    #[test]
    fn class() {
        let code = r#"
        class Test {
            public final func Method(opt arg: Int32) -> Int32 {
                return arg;
            }
        }
        "#;

        assert_eq!(
            parse_item(code).0.unwrap().unwrapped(),
            Item::Class(Aggregate::new(
                "Test",
                None,
                [ItemDecl::new(
                    [],
                    Some(Visibility::Public),
                    ItemQualifiers::FINAL,
                    Item::Function(
                        Function::new(
                            "Method",
                            [Param::new(
                                "arg",
                                Type::Named("Int32"),
                                ParamQualifiers::OPTIONAL
                            )],
                            Some(Type::Named("Int32")),
                            Some(Block::single(Stmt::Return(Some(Expr::Ident("arg").into()))))
                        )
                        .into()
                    )
                    .into()
                )]
            ))
        );
    }

    #[test]
    fn enum_() {
        let code = r#"
        enum Test {
            A = 1,
            B = 2,
            C,
        }
        "#;

        assert_eq!(
            parse_item(code).0.unwrap().unwrapped(),
            Item::Enum(Enum::new(
                "Test",
                [
                    EnumVariant::new("A", Some(1)),
                    EnumVariant::new("B", Some(2)),
                    EnumVariant::new("C", None),
                ]
            ))
        );
    }

    #[test]
    fn struct_() {
        let code = r#"
        struct Test {
            let a: Int32;
            let b: Int32 = 3;
        }
        "#;

        assert_eq!(
            parse_item(code).0.unwrap().unwrapped(),
            Item::Struct(Aggregate::new(
                "Test",
                None,
                [
                    ItemDecl::new(
                        [],
                        None,
                        ItemQualifiers::empty(),
                        Item::Let(Field::new("a", Type::Named("Int32"), None)).into()
                    ),
                    ItemDecl::new(
                        [],
                        None,
                        ItemQualifiers::empty(),
                        Item::Let(Field::new(
                            "b",
                            Type::Named("Int32"),
                            Some(Expr::Constant(Constant::I32(3)))
                        ))
                        .into()
                    ),
                ]
            ))
        );
    }

    #[test]
    fn func() {
        let code = r#"
        func Test(arg: Int32) -> Int32 {
            return arg;
        }
        "#;

        assert_eq!(
            parse_item(code).0.unwrap().unwrapped(),
            Item::Function(
                Function::new(
                    "Test",
                    [Param::new(
                        "arg",
                        Type::Named("Int32"),
                        ParamQualifiers::empty()
                    )],
                    Some(Type::Named("Int32")),
                    Some(Block::single(Stmt::Return(Some(Expr::Ident("arg").into()))))
                )
                .into()
            )
        );
    }

    #[test]
    fn annotations() {
        let code = r#"
        @if(true)
        @replaceGlobal()
        func Test()
        "#;

        assert_eq!(
            parse_item_decl(code).0.unwrap().unwrapped(),
            ItemDecl::new(
                [
                    Annotation::new("if", [Expr::Constant(Constant::Bool(true)).into()]),
                    Annotation::new("replaceGlobal", [])
                ],
                None,
                ItemQualifiers::empty(),
                Item::Function(Function::new("Test", [], None, None).into()).into()
            )
        );
    }
}
