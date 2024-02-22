use crate::{lexer::Token, SpannedStmt};
use chumsky::prelude::*;
use redscript_ast::{Block, Case, Stmt};

use super::{block_rec, expr::expr_with_span, ident, type_with_span, ParseError, ParserInput};

#[inline]
pub fn stmt<'tok, 'src: 'tok>(
) -> impl Parser<'tok, ParserInput<'tok, 'src>, SpannedStmt<'src>, ParseError<'tok, 'src>> + Clone {
    recursive(stmt_rec)
}

pub fn stmt_rec<'tok, 'src: 'tok>(
    stmt: impl Parser<'tok, ParserInput<'tok, 'src>, SpannedStmt<'src>, ParseError<'tok, 'src>> + Clone,
) -> impl Parser<'tok, ParserInput<'tok, 'src>, SpannedStmt<'src>, ParseError<'tok, 'src>> + Clone {
    let ident = ident();
    let ty = type_with_span();
    let expr = expr_with_span();
    let block = block_rec(stmt.clone());

    let let_ = just(Token::Ident("let"))
        .ignore_then(ident.clone())
        .then(just(Token::Colon).ignore_then(ty).or_not())
        .then(just(Token::Assign).ignore_then(expr.clone().or_not()))
        .then_ignore(just(Token::Semicolon))
        .map(|((name, ty), value)| {
            let value = value.map(Box::new);
            Stmt::Let { name, ty, value }
        });

    let case_body = stmt
        .map_with(|stmt, e| (stmt, e.span()))
        .repeated()
        .collect::<Vec<_>>();
    let cases = just(Token::Ident("case"))
        .ignore_then(expr.clone())
        .then_ignore(just(Token::Colon))
        .then(case_body.clone())
        .map(|(cond, body)| Case::new(cond, body))
        .repeated()
        .collect::<Vec<_>>()
        .then(
            just(Token::Ident("default"))
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

    let if_ = just(Token::Ident("if")).ignore_then(expr.clone().then(block.clone()));
    let else_chain = just(Token::Ident("else"))
        .ignore_then(if_.clone())
        .repeated()
        .foldr_with(
            just(Token::Ident("else"))
                .ignore_then(block.clone())
                .or_not(),
            |(cond, then), else_, e| {
                let cond = Box::new(cond);
                Some(Block::single((Stmt::If { cond, then, else_ }, e.span())))
            },
        );

    let if_stmt = if_
        .then(else_chain)
        .then_ignore(just(Token::Semicolon).or_not())
        .map(|((cond, then), else_)| {
            let cond = Box::new(cond);
            Stmt::If { cond, then, else_ }
        });

    let while_stmt = just(Token::Ident("while"))
        .ignore_then(expr.clone().then(block.clone()))
        .then_ignore(just(Token::Semicolon).or_not())
        .map(|(cond, body)| {
            let cond = Box::new(cond);
            Stmt::While { cond, body }
        });

    let for_stmt = just(Token::Ident("for"))
        .ignore_then(ident)
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
        .then_ignore(just(Token::Semicolon))
        .map(|e| Stmt::Return(e.map(Box::new)));

    let break_stmt = just(Token::Ident("break"))
        .ignore_then(just(Token::Semicolon))
        .map(|_| Stmt::Break);

    let expr_stmt = expr
        .then_ignore(just(Token::Semicolon))
        .map(|e| Stmt::Expr(e.into()));

    choice((
        let_,
        switch,
        if_stmt,
        while_stmt,
        for_stmt,
        return_stmt,
        break_stmt,
        expr_stmt,
    ))
    .labelled("statement")
    .as_context()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse_stmt;

    use pretty_assertions::assert_eq;
    use redscript_ast::{BinOp, Constant, Expr, Type};

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
            parse_stmt(code).0.unwrap().unwrapped(),
            Stmt::If {
                cond: Expr::Constant(Constant::Bool(true)).into(),
                then: Block::single(Stmt::Return(Some(Expr::Constant(Constant::I32(1)).into()))),
                else_: Some(Block::single(Stmt::If {
                    cond: Expr::Constant(Constant::Bool(false)).into(),
                    then: Block::single(Stmt::Return(Some(
                        Expr::Constant(Constant::I32(2)).into()
                    ))),
                    else_: Some(Block::single(Stmt::Return(Some(
                        Expr::Constant(Constant::I32(3)).into()
                    )))),
                })),
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
            parse_stmt(code).0.unwrap().unwrapped(),
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
            parse_stmt(code).0.unwrap().unwrapped(),
            Stmt::While {
                cond: Expr::BinOp {
                    op: BinOp::Gt,
                    lhs: Box::new(Expr::Ident("i")),
                    rhs: Box::new(Expr::Constant(Constant::I32(0))),
                }
                .into(),
                body: Block::single(Stmt::Expr(
                    Expr::Assign {
                        lhs: Box::new(Expr::Ident("i")),
                        rhs: Box::new(Expr::BinOp {
                            op: BinOp::Sub,
                            lhs: Box::new(Expr::Ident("i")),
                            rhs: Box::new(Expr::Constant(Constant::I32(1))),
                        }),
                    }
                    .into()
                )),
            }
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
            parse_stmt(code).0.unwrap().unwrapped(),
            Stmt::ForIn {
                name: "i",
                iter: Expr::Ident("range").into(),
                body: Block::single(Stmt::Expr(
                    Expr::Call {
                        expr: Expr::Ident("print").into(),
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
        let res = parse_stmt(code).0.unwrap().unwrapped();

        assert_eq!(
            res,
            Stmt::Let {
                name: "a",
                ty: Some(Type::plain("Int32")),
                value: Some(Expr::Constant(Constant::I32(1)).into()),
            }
        )
    }
}
