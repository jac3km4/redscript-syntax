mod lexer;
mod parser;

use std::fmt;

use chumsky::prelude::*;
use lexer::Token;
use parser::{ParseError, ParserInput};
use redscript_ast::{
    Aggregate, Annotation, AstKind, Block, Case, Enum, Expr, Field, Function, Item, ItemDecl,
    Module, Param, Stmt,
};

pub type Span = SimpleSpan;
pub type Spanned<A> = (A, Span);

pub type SpannedAggregate<'src> = Aggregate<'src, WithSpan>;
pub type SpannedAnnotation<'src> = Annotation<'src, WithSpan>;
pub type SpannedBlock<'src> = Block<'src, WithSpan>;
pub type SpannedCase<'src> = Case<'src, WithSpan>;
pub type SpannedEnum<'src> = Enum<'src, WithSpan>;
pub type SpannedExpr<'src> = Expr<'src, WithSpan>;
pub type SpannedField<'src> = Field<'src, WithSpan>;
pub type SpannedFunction<'src> = Function<'src, WithSpan>;
pub type SpannedItem<'src> = Item<'src, WithSpan>;
pub type SpannedItemDecl<'src> = ItemDecl<'src, WithSpan>;
pub type SpannedModule<'src> = Module<'src, WithSpan>;
pub type SpannedParam<'src> = Param<'src, WithSpan>;
pub type SpannedStmt<'src> = Stmt<'src, WithSpan>;

pub type Result<A> = (Option<A>, Vec<Error>);

// this can't be written as a generic function due to a GAT bug
macro_rules! parse {
    ($src:expr, $parser:expr) => {{
        let (toks, mut errs) = lex($src);
        let Some(toks) = toks else {
            return (None, errs);
        };
        let (res, perrs) = parse($parser, &toks);
        errs.extend(perrs);
        (res, errs)
    }};
}

pub fn parse_module(src: &str) -> Result<SpannedModule<'_>> {
    parse!(src, parser::module())
}

pub fn parse_item_decl(src: &str) -> Result<SpannedItemDecl<'_>> {
    parse!(src, parser::item_decl())
}

#[allow(unused)]
fn parse_item(src: &str) -> Result<SpannedItem<'_>> {
    parse!(src, parser::item())
}

pub fn parse_stmt(src: &str) -> Result<SpannedStmt<'_>> {
    parse!(src, parser::stmt())
}

pub fn parse_expr(src: &str) -> Result<SpannedExpr<'_>> {
    parse!(src, parser::expr())
}

fn lex(src: &str) -> Result<Vec<Spanned<Token<'_>>>> {
    let (output, errors) = lexer::lex().parse(src).into_output_errors();
    let errors = errors
        .into_iter()
        .map(|err| Error::Lex(err.to_string(), *err.span()))
        .collect();
    (output, errors)
}

fn parse<'tok, 'src: 'tok, A>(
    parser: impl Parser<'tok, ParserInput<'tok, 'src>, A, ParseError<'tok, 'src>>,
    tokens: &'tok [(Token<'src>, Span)],
) -> Result<A> {
    let (output, errors) = parser.parse(parser_input(tokens)).into_output_errors();
    let errors = errors
        .into_iter()
        .map(|err| Error::Parse(err.to_string(), *err.span()))
        .collect();
    (output, errors)
}

fn parser_input<'tok, 'src>(tokens: &'tok [(Token<'src>, Span)]) -> ParserInput<'tok, 'src> {
    let max = tokens.last().map(|(_, span)| span.end()).unwrap_or(0);
    tokens.spanned((max..max).into())
}

pub struct WithSpan;

impl AstKind for WithSpan {
    type Inner<A> = Spanned<A>
    where
        A: fmt::Debug + PartialEq;
}

#[derive(Debug, PartialEq, Eq)]
pub enum Error {
    Parse(String, Span),
    Lex(String, Span),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::Parse(msg, span) => write!(f, "parse error at {}: {}", span, msg),
            Error::Lex(msg, span) => write!(f, "lex error at {}: {}", span, msg),
        }
    }
}

impl std::error::Error for Error {}
