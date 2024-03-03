use std::ops::BitOr;

use crate::lexer::Token;
use chumsky::{container::Container, prelude::*};
use redscript_ast::{
    Aggregate, Annotation, Enum, EnumVariant, Field, Function, FunctionBody, Import, Item,
    ItemDecl, ItemQualifiers, Param, ParamQualifiers, Path, Span, SpannedAnnotation, SpannedEnum,
    SpannedExpr, SpannedField, SpannedFunction, SpannedItem, SpannedItemDecl, Visibility,
};

use super::{block, expr::expr_with_span, ident, type_with_span, Parse};

#[inline]
pub fn item_decl<'tok, 'src: 'tok>() -> impl Parse<'tok, 'src, SpannedItemDecl<'src>> {
    recursive(item_decl_rec)
}

pub fn item_decl_rec<'tok, 'src: 'tok>(
    item_decl: impl Parse<'tok, 'src, SpannedItemDecl<'src>>,
) -> impl Parse<'tok, 'src, SpannedItemDecl<'src>> {
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
pub fn item<'tok, 'src: 'tok>() -> impl Parse<'tok, 'src, SpannedItem<'src>> {
    item_rec(item_decl())
}

fn item_rec<'tok, 'src: 'tok>(
    item_decl: impl Parse<'tok, 'src, SpannedItemDecl<'src>>,
) -> impl Parse<'tok, 'src, SpannedItem<'src>> {
    choice((
        import().map(Item::Import),
        aggregate(item_decl),
        enum_().map(Item::Enum),
        function().map(Item::Function),
        field().map(Item::Let),
    ))
    .labelled("item")
}

fn function<'tok, 'src: 'tok>() -> impl Parse<'tok, 'src, SpannedFunction<'src>> {
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
        .separated_by(just(Token::Comma))
        .allow_trailing()
        .collect::<Vec<_>>()
        .delimited_by(just(Token::LParen), just(Token::RParen));

    let function_body = choice((
        block().map(FunctionBody::Block),
        just(Token::Assign)
            .ignore_then(item_expr())
            .map(|e| FunctionBody::Inline(e.into())),
    ));

    just(Token::Ident("func"))
        .ignore_then(ident())
        .then(params)
        .then(just(Token::Arrow).ignore_then(ty).or_not())
        .then(function_body.or_not())
        .then_ignore(just(Token::Semicolon).or_not())
        .map(|(((name, params), ret_ty), body)| {
            Function::new(name, params, ret_ty.map(Box::new), body)
        })
}

fn field<'tok, 'src: 'tok>() -> impl Parse<'tok, 'src, SpannedField<'src>> {
    just(Token::Ident("let"))
        .ignore_then(ident())
        .then(just(Token::Colon).ignore_then(type_with_span()))
        .then(just(Token::Assign).ignore_then(item_expr()).or_not())
        .then_ignore(just(Token::Semicolon))
        .map(|((name, ty), default)| Field::new(name, ty.into(), default.map(Box::new)))
}

fn enum_<'tok, 'src: 'tok>() -> impl Parse<'tok, 'src, SpannedEnum<'src>> {
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
    item_decl: impl Parse<'tok, 'src, SpannedItemDecl<'src>>,
) -> impl Parse<'tok, 'src, SpannedItem<'src>> {
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
        .then(
            just(Token::Ident("extends"))
                .ignore_then(type_with_span())
                .or_not(),
        )
        .then(items)
        .then_ignore(just(Token::Semicolon).or_not())
        .map(|(((is_struct, name), extends), items)| {
            let aggregate = Aggregate::new(name, extends.map(Box::new), items);
            if is_struct {
                Item::Struct(aggregate)
            } else {
                Item::Class(aggregate)
            }
        })
}

fn import<'tok, 'src: 'tok>() -> impl Parse<'tok, 'src, Import<'src>> {
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

fn visibility<'tok, 'src: 'tok>() -> impl Parse<'tok, 'src, Visibility> {
    select! {
        Token::Ident("public") => Visibility::Public,
        Token::Ident("private") => Visibility::Private,
        Token::Ident("protected") => Visibility::Protected,
    }
    .labelled("item visibility")
}

fn annotation<'tok, 'src: 'tok>() -> impl Parse<'tok, 'src, SpannedAnnotation<'src>> {
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

fn item_qualifier<'tok, 'src: 'tok>() -> impl Parse<'tok, 'src, ItemQualifiers> {
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
fn item_expr<'tok, 'src: 'tok>() -> impl Parse<'tok, 'src, (SpannedExpr<'src>, Span)> {
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
    use redscript_ast::{Block, Constant, Expr, FileId, FunctionBody, Stmt, Type};

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
            parse_item(code, FileId::from_u32(0)).0.unwrap().unwrapped(),
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
                                Type::plain("Int32"),
                                ParamQualifiers::OPTIONAL
                            )],
                            Some(Type::plain("Int32").into()),
                            Some(FunctionBody::Block(Block::single(Stmt::Return(Some(
                                Expr::Ident("arg").into()
                            )))))
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
            parse_item(code, FileId::from_u32(0)).0.unwrap().unwrapped(),
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
            parse_item(code, FileId::from_u32(0)).0.unwrap().unwrapped(),
            Item::Struct(Aggregate::new(
                "Test",
                None,
                [
                    ItemDecl::new(
                        [],
                        None,
                        ItemQualifiers::empty(),
                        Item::Let(Field::new("a", Type::plain("Int32").into(), None)).into()
                    ),
                    ItemDecl::new(
                        [],
                        None,
                        ItemQualifiers::empty(),
                        Item::Let(Field::new(
                            "b",
                            Type::plain("Int32").into(),
                            Some(Expr::Constant(Constant::I32(3)).into())
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
        func Test(arg1: Int32, arg2: Int64) -> Int32 {
            return arg1;
        }
        "#;

        assert_eq!(
            parse_item(code, FileId::from_u32(0)).0.unwrap().unwrapped(),
            Item::Function(
                Function::new(
                    "Test",
                    [
                        Param::new("arg1", Type::plain("Int32"), ParamQualifiers::empty()),
                        Param::new("arg2", Type::plain("Int64"), ParamQualifiers::empty()),
                    ],
                    Some(Type::plain("Int32").into()),
                    Some(FunctionBody::Block(Block::single(Stmt::Return(Some(
                        Expr::Ident("arg1").into()
                    )))))
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
            parse_item_decl(code, FileId::from_u32(0))
                .0
                .unwrap()
                .unwrapped(),
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
