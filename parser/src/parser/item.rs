use std::ops::BitOr;

use crate::lexer::Token;
use chumsky::{container::Container, prelude::*};
use redscript_ast::{
    Aggregate, Annotation, Enum, EnumVariant, Field, Function, FunctionBody, Import, Item,
    ItemDecl, ItemQualifiers, Param, ParamQualifiers, Path, SourceAnnotation, SourceBlock,
    SourceEnum, SourceExpr, SourceField, SourceFunction, SourceItem, SourceItemDecl, Span,
    Visibility,
};

use super::{ident, ident_with_span, type_params, type_with_span, Parse};

pub fn item_decl_rec<'tok, 'src: 'tok>(
    item_decl: impl Parse<'tok, 'src, SourceItemDecl<'src>>,
    block: impl Parse<'tok, 'src, SourceBlock<'src>>,
    expr: impl Parse<'tok, 'src, (SourceExpr<'src>, Span)>,
) -> impl Parse<'tok, 'src, SourceItemDecl<'src>> {
    annotation(expr.clone())
        .map_with(|a, e| (a, e.span()))
        .repeated()
        .collect::<Vec<_>>()
        .then(visibility().or_not())
        .then(item_qualifier().repeated().collect::<BitCollection<_>>())
        .then(item_rec(item_decl, block, expr))
        .map(|(((annotations, visibility), qualifiers), item)| {
            ItemDecl::new(annotations, visibility, qualifiers.value, item)
        })
        .labelled("declaration")
}

pub fn item_rec<'tok, 'src: 'tok>(
    item_decl: impl Parse<'tok, 'src, SourceItemDecl<'src>>,
    block: impl Parse<'tok, 'src, SourceBlock<'src>>,
    expr: impl Parse<'tok, 'src, (SourceExpr<'src>, Span)>,
) -> impl Parse<'tok, 'src, SourceItem<'src>> {
    choice((
        import().map(Item::Import),
        aggregate(item_decl),
        enum_().map(Item::Enum),
        function(block, expr.clone()).map(Item::Function),
        field(expr).map(Item::Let),
    ))
    .labelled("item")
}

fn function<'tok, 'src: 'tok>(
    block: impl Parse<'tok, 'src, SourceBlock<'src>>,
    expr: impl Parse<'tok, 'src, (SourceExpr<'src>, Span)>,
) -> impl Parse<'tok, 'src, SourceFunction<'src>> {
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
            (Param::new(name, Some(typ), qualifiers.value), e.span())
        })
        .separated_by(just(Token::Comma))
        .allow_trailing()
        .collect::<Vec<_>>()
        .delimited_by(just(Token::LParen), just(Token::RParen));

    let function_body = choice((
        block.map(FunctionBody::Block),
        just(Token::Assign)
            .ignore_then(expr)
            .map(|e| FunctionBody::Inline(e.into())),
    ));

    just(Token::Ident("func"))
        .ignore_then(ident_with_span())
        .then(type_params().or_not())
        .then(params)
        .then(just(Token::Arrow).ignore_then(ty).or_not())
        .then(function_body.or_not())
        .then_ignore(just(Token::Semicolon).or_not())
        .map(|((((name, type_params), params), ret_ty), body)| {
            Function::new(
                name,
                type_params.unwrap_or_default(),
                params,
                ret_ty.map(Box::new),
                body,
            )
        })
}

fn field<'tok, 'src: 'tok>(
    expr: impl Parse<'tok, 'src, (SourceExpr<'src>, Span)>,
) -> impl Parse<'tok, 'src, SourceField<'src>> {
    just(Token::Ident("let"))
        .ignore_then(ident_with_span())
        .then(just(Token::Colon).ignore_then(type_with_span()))
        .then(just(Token::Assign).ignore_then(expr).or_not())
        .then_ignore(just(Token::Semicolon))
        .map(|((name, ty), default)| Field::new(name, ty.into(), default.map(Box::new)))
}

fn enum_<'tok, 'src: 'tok>() -> impl Parse<'tok, 'src, SourceEnum<'src>> {
    let int = select! { Token::Int(i) => i };

    let variants = ident()
        .then(just(Token::Assign).ignore_then(int).or_not())
        .map_with(|(name, value), e| (EnumVariant::new(name, value), e.span()))
        .separated_by(just(Token::Comma))
        .allow_trailing()
        .collect::<Vec<_>>()
        .delimited_by(just(Token::LBrace), just(Token::RBrace));

    just(Token::Ident("enum"))
        .ignore_then(ident_with_span())
        .then(variants)
        .then_ignore(just(Token::Semicolon).or_not())
        .map(|(name, variants)| Enum::new(name, variants))
}

fn aggregate<'tok, 'src: 'tok>(
    item_decl: impl Parse<'tok, 'src, SourceItemDecl<'src>>,
) -> impl Parse<'tok, 'src, SourceItem<'src>> {
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
        .then(ident_with_span())
        .then(type_params().or_not())
        .then(
            just(Token::Ident("extends"))
                .ignore_then(type_with_span())
                .or_not(),
        )
        .then(items)
        .then_ignore(just(Token::Semicolon).or_not())
        .map(|((((is_struct, name), type_params), extends), items)| {
            let aggregate = Aggregate::new(
                name,
                type_params.unwrap_or_default(),
                extends.map(Box::new),
                items,
            );
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

fn annotation<'tok, 'src: 'tok>(
    expr: impl Parse<'tok, 'src, (SourceExpr<'src>, Span)>,
) -> impl Parse<'tok, 'src, SourceAnnotation<'src>> {
    just(Token::At)
        .ignore_then(ident())
        .then(
            expr.separated_by(just(Token::Comma))
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
    use redscript_ast::{
        Block, Constant, Expr, FileId, FunctionBody, Stmt, Type, TypeParam, Variance,
    };

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
                [],
                None,
                [ItemDecl::new(
                    [],
                    Some(Visibility::Public),
                    ItemQualifiers::FINAL,
                    Item::Function(Function::new(
                        "Method",
                        [],
                        [Param::new(
                            "arg",
                            Some(Type::plain("Int32")),
                            ParamQualifiers::OPTIONAL
                        )],
                        Some(Type::plain("Int32").into()),
                        Some(FunctionBody::Block(Block::single(Stmt::Return(Some(
                            Expr::Ident("arg").into()
                        )))))
                    ))
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
                [],
                None,
                [
                    ItemDecl::new(
                        [],
                        None,
                        ItemQualifiers::empty(),
                        Item::Let(Field::new("a", Type::plain("Int32").into(), None))
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
            Item::Function(Function::new(
                "Test",
                [],
                [
                    Param::new("arg1", Some(Type::plain("Int32")), ParamQualifiers::empty()),
                    Param::new("arg2", Some(Type::plain("Int64")), ParamQualifiers::empty()),
                ],
                Some(Type::plain("Int32").into()),
                Some(FunctionBody::Block(Block::single(Stmt::Return(Some(
                    Expr::Ident("arg1").into()
                )))))
            ))
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
                    Annotation::new("if", [Expr::Constant(Constant::Bool(true))]),
                    Annotation::new("replaceGlobal", [])
                ],
                None,
                ItemQualifiers::empty(),
                Item::Function(Function::new("Test", [], [], None, None))
            )
        );
    }

    #[test]
    fn class_with_type_params() {
        let code = r#"
        class Test<-A, +B extends C> {
            public final func Method<D extends E>(opt arg: Int32) -> Int32 {
                return arg;
            }
        }
        "#;

        assert_eq!(
            parse_item(code, FileId::from_u32(0)).0.unwrap().unwrapped(),
            Item::Class(Aggregate::new(
                "Test",
                [
                    TypeParam::new(Variance::Contravariant, "A", None),
                    TypeParam::new(Variance::Covariant, "B", Some(Type::plain("C").into()))
                ],
                None,
                [ItemDecl::new(
                    [],
                    Some(Visibility::Public),
                    ItemQualifiers::FINAL,
                    Item::Function(Function::new(
                        "Method",
                        [TypeParam::new(
                            Variance::Invariant,
                            "D",
                            Some(Type::plain("E").into())
                        )],
                        [Param::new(
                            "arg",
                            Some(Type::plain("Int32")),
                            ParamQualifiers::OPTIONAL
                        )],
                        Some(Type::plain("Int32").into()),
                        Some(FunctionBody::Block(Block::single(Stmt::Return(Some(
                            Expr::Ident("arg").into()
                        )))))
                    ))
                )]
            ))
        );
    }
}
