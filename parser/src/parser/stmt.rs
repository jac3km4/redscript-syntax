use std::iter;

use crate::lexer::Token;
use chumsky::prelude::*;
use redscript_ast::{Case, ConditionalBlock, SourceBlock, SourceExpr, SourceStmt, Span, Stmt};

use super::{ident_with_span, type_with_span, Parse};

pub fn stmt_rec<'tok, 'src: 'tok>(
    expr: impl Parse<'tok, 'src, (SourceExpr<'src>, Span)>,
    stmt: impl Parse<'tok, 'src, SourceStmt<'src>>,
    block: impl Parse<'tok, 'src, SourceBlock<'src>>,
) -> impl Parse<'tok, 'src, SourceStmt<'src>> {
    let typ = type_with_span();

    let semicolon = just(Token::Semicolon).or_not().validate(|semi, ctx, errs| {
        if semi.is_none() {
            errs.emit(Rich::custom(ctx.span(), "expected ';'"));
        }
    });

    let let_ = just(Token::Ident("let"))
        .ignore_then(ident_with_span())
        .then(just(Token::Colon).ignore_then(typ).or_not())
        .then(just(Token::Assign).ignore_then(expr.clone()).or_not())
        .then_ignore(semicolon.clone())
        .map(|((name, typ), value)| {
            let value = value.map(Box::new);
            let typ = typ.map(Box::new);
            Stmt::Let { name, typ, value }
        });

    let case_body = stmt
        .map_with(|stmt, e| (stmt, e.span()))
        .repeated()
        .collect::<Vec<_>>();
    let cases = just(Token::Case)
        .ignore_then(expr.clone())
        .then_ignore(just(Token::Colon))
        .then(case_body.clone())
        .map(|(cond, body)| Case::new(cond, body))
        .repeated()
        .collect::<Vec<_>>()
        .then(
            just(Token::Default)
                .ignore_then(just(Token::Colon).ignore_then(case_body))
                .or_not(),
        )
        .delimited_by(just(Token::LBrace), just(Token::RBrace));

    let switch = just(Token::Ident("switch"))
        .ignore_then(expr.clone())
        .then(cases)
        .then_ignore(just(Token::Semicolon).or_not())
        .map(|(expr, (cases, default))| Stmt::Switch {
            expr: expr.into(),
            cases: cases.into(),
            default: default.map(Into::into),
        });

    let if_ = just(Token::Ident("if"))
        .ignore_then(expr.clone().then(block.clone()))
        .map(|(cond, body)| ConditionalBlock::new(cond, body));
    let else_if = just(Token::Ident("else")).ignore_then(if_.clone());
    let else_ = just(Token::Ident("else")).ignore_then(block.clone());
    let if_stmt = if_
        .then(else_if.repeated().collect::<Vec<_>>())
        .then(else_.or_not())
        .then_ignore(just(Token::Semicolon).or_not())
        .map(|((if_, else_ifs), else_)| Stmt::If {
            blocks: iter::once(if_).chain(else_ifs).collect(),
            else_,
        });

    let while_stmt = just(Token::Ident("while"))
        .ignore_then(expr.clone().then(block.clone()))
        .then_ignore(just(Token::Semicolon).or_not())
        .map(|(cond, body)| Stmt::While(ConditionalBlock::new(cond, body).into()));

    let for_stmt = just(Token::Ident("for"))
        .ignore_then(ident_with_span())
        .then_ignore(just(Token::Ident("in")))
        .then(expr.clone())
        .then(block)
        .then_ignore(just(Token::Semicolon).or_not())
        .map(|((name, iter), body)| {
            let iter = Box::new(iter);
            Stmt::ForIn { name, iter, body }
        });

    let return_stmt = just(Token::Ident("return"))
        .ignore_then(expr.clone().or_not())
        .then_ignore(semicolon.clone())
        .map(|e| Stmt::Return(e.map(Box::new)));

    let break_stmt = just(Token::Ident("break"))
        .ignore_then(semicolon.clone())
        .map(|_| Stmt::Break);

    let continue_stmt = just(Token::Ident("continue"))
        .ignore_then(semicolon.clone())
        .map(|_| Stmt::Continue);

    let expr_stmt = expr.then_ignore(semicolon).map(|e| Stmt::Expr(e.into()));

    choice((
        let_,
        switch,
        if_stmt,
        while_stmt,
        for_stmt,
        return_stmt,
        break_stmt,
        continue_stmt,
        expr_stmt,
    ))
    .labelled("statement")
    .as_context()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{parse_stmt, Error, Span};

    use pretty_assertions::assert_eq;
    use redscript_ast::{BinOp, Block, Constant, Expr, FileId, Type};

    #[test]
    fn if_else_chain() {
        let code = r#"
        if true {
            return 1;
        } else if false {
            return 2;
        } else {
            return 3;
        }
        "#;

        assert_eq!(
            parse_stmt(code, FileId::from_u32(0)).0.unwrap().unwrapped(),
            Stmt::If {
                blocks: [
                    ConditionalBlock::new(
                        Expr::Constant(Constant::Bool(true)),
                        Block::single(Stmt::Return(Some(Expr::Constant(Constant::I32(1)).into())))
                    ),
                    ConditionalBlock::new(
                        Expr::Constant(Constant::Bool(false)),
                        Block::single(Stmt::Return(Some(Expr::Constant(Constant::I32(2)).into())))
                    ),
                ]
                .into(),
                else_: Some(Block::single(Stmt::Return(Some(
                    Expr::Constant(Constant::I32(3)).into()
                )))),
            }
        );
    }

    #[test]
    fn switch() {
        let code = r#"
        switch a {
            case 0:
                break;
            case 1:
                return 0;
            default:
                return 1;
        }
        "#;

        assert_eq!(
            parse_stmt(code, FileId::from_u32(0)).0.unwrap().unwrapped(),
            Stmt::Switch {
                expr: Expr::Ident("a").into(),
                cases: [
                    Case::new(Expr::Constant(Constant::I32(0)), [Stmt::Break]),
                    Case::new(
                        Expr::Constant(Constant::I32(1)),
                        [(Stmt::Return(Some(Expr::Constant(Constant::I32(0)).into())))]
                    ),
                ]
                .into(),
                default: Some([Stmt::Return(Some(Expr::Constant(Constant::I32(1)).into()))].into()),
            }
        );
    }

    #[test]
    fn while_() {
        let code = r#"
        while i > 0 {
            i = i - 1;
        }
        "#;

        assert_eq!(
            parse_stmt(code, FileId::from_u32(0)).0.unwrap().unwrapped(),
            Stmt::While(
                ConditionalBlock::new(
                    Expr::BinOp {
                        op: BinOp::Gt,
                        lhs: Box::new(Expr::Ident("i")),
                        rhs: Box::new(Expr::Constant(Constant::I32(0))),
                    },
                    Block::single(Stmt::Expr(
                        Expr::Assign {
                            lhs: Box::new(Expr::Ident("i")),
                            rhs: Box::new(Expr::BinOp {
                                op: BinOp::Sub,
                                lhs: Box::new(Expr::Ident("i")),
                                rhs: Box::new(Expr::Constant(Constant::I32(1))),
                            }),
                        }
                        .into()
                    ))
                )
                .into()
            )
        );
    }

    #[test]
    fn for_in() {
        let code = r#"
        for i in range {
            print(i);
        }
        "#;

        assert_eq!(
            parse_stmt(code, FileId::from_u32(0)).0.unwrap().unwrapped(),
            Stmt::ForIn {
                name: "i",
                iter: Expr::Ident("range").into(),
                body: Block::single(Stmt::Expr(
                    Expr::Call {
                        expr: Expr::Ident("print").into(),
                        type_args: [].into(),
                        args: [Expr::Ident("i")].into(),
                    }
                    .into()
                )),
            }
        );
    }

    #[test]
    fn stmt_with_comments() {
        let code = r#"
        // a line comment
        /* block comment */
        /* /* */ */
        let a: Int32 = 1;
        "#;
        let res = parse_stmt(code, FileId::from_u32(0)).0.unwrap().unwrapped();

        assert_eq!(
            res,
            Stmt::Let {
                name: "a",
                typ: Some(Type::plain("Int32").into()),
                value: Some(Expr::Constant(Constant::I32(1)).into()),
            }
        );
    }

    #[test]
    fn missing_semicolon() {
        let code = "a";
        let file = FileId::from_u32(0);
        let (stmt, errors) = parse_stmt(code, file);

        assert_eq!(
            errors,
            vec![Error::Parse(
                "expected ';' in statement at 0-1".into(),
                Span::from((file, 0..1))
            )]
        );
        assert_eq!(
            stmt.expect("should parse").unwrapped(),
            Stmt::Expr(Expr::Ident("a").into())
        );
    }

    #[test]
    fn trailing_comma() {
        let code = "a.";
        let file = FileId::from_u32(0);
        let (stmt, errors) = parse_stmt(code, file);

        assert_eq!(
            errors,
            vec![
                Error::Parse(
                    "unexpected '.' in statement at 0-2".into(),
                    Span::from((file, 0..2))
                ),
                Error::Parse(
                    "expected ';' in statement at 0-2".into(),
                    Span::from((file, 0..2))
                )
            ]
        );
        assert_eq!(
            stmt.expect("should parse").unwrapped(),
            Stmt::Expr(Expr::Ident("a").into())
        );
    }
}
