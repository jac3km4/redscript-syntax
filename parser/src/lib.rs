mod lexer;
pub mod parser;

use std::fmt;

use chumsky::prelude::*;
pub use lexer::Token;
use parser::{Parse, ParserInput};
use redscript_ast::{
    FileId, SourceExpr, SourceItem, SourceItemDecl, SourceMap, SourceModule, SourceStmt, Span,
    Spanned,
};

pub type ParseResult<A> = (Option<A>, Vec<Error>);

// this can't be written as a generic function due to a GAT bug
macro_rules! parse {
    ($src:expr, $parser:expr, $ctx:expr) => {{
        let (toks, mut errs) = lex($src, $ctx);
        let Some(toks) = toks else {
            return (None, errs);
        };
        let (res, perrs) = parse($parser, &toks, $ctx);
        errs.extend(perrs);
        (res, errs)
    }};
}

pub fn parse_module(src: &str, file: FileId) -> ParseResult<SourceModule<'_>> {
    parse!(src, parser::module(), file)
}

pub fn parse_item_decl(src: &str, file: FileId) -> ParseResult<SourceItemDecl<'_>> {
    parse!(src, parser::item_decl(), file)
}

pub fn parse_item(src: &str, file: FileId) -> ParseResult<SourceItem<'_>> {
    parse!(src, parser::item(), file)
}

pub fn parse_stmt(src: &str, file: FileId) -> ParseResult<SourceStmt<'_>> {
    parse!(src, parser::stmt(), file)
}

pub fn parse_expr(src: &str, file: FileId) -> ParseResult<SourceExpr<'_>> {
    parse!(src, parser::expr(), file)
}

pub fn lex(src: &str, f: FileId) -> ParseResult<Vec<Spanned<Token<'_, Span>>>> {
    lex_internal(src, f, false)
}

pub fn lex_with_lf_and_comments(
    src: &str,
    f: FileId,
) -> ParseResult<Vec<Spanned<Token<'_, Span>>>> {
    lex_internal(src, f, true)
}

fn lex_internal(
    src: &str,
    file_id: FileId,
    keep_lf_and_comments: bool,
) -> ParseResult<Vec<Spanned<Token<'_, Span>>>> {
    let (output, errors) = lexer::lex(keep_lf_and_comments)
        .parse(src)
        .into_output_errors();
    let errors = errors
        .into_iter()
        .map(|err| {
            let span = Span::from((file_id, *err.span()));
            Error::Lex(FormattedError(err).to_string(), span)
        })
        .collect();
    let Some(tokens) = output else {
        return (None, errors);
    };

    let output = tokens
        .into_iter()
        .map(|(tok, span)| {
            let tok = tok.map_span(|s| Span::from((file_id, s)));
            (tok, Span::from((file_id, span)))
        })
        .collect();
    (Some(output), errors)
}

pub fn parse<'tok, 'src: 'tok, A>(
    parser: impl Parse<'tok, 'src, A>,
    tokens: &'tok [(Token<'src>, Span)],
    file: FileId,
) -> ParseResult<A> {
    let parser: &dyn Parser<'tok, _, A, extra::Err<_>> = &parser.with_ctx(file);
    let (output, errors) = parser
        .parse(parser_input(tokens, file))
        .into_output_errors();
    let errors = errors.into_iter().map(Error::new_parse).collect();
    (output, errors)
}

fn parser_input<'tok, 'src>(
    tokens: &'tok [(Token<'src>, Span)],
    file: FileId,
) -> ParserInput<'tok, 'src> {
    let max = tokens.last().map(|(_, span)| span.end()).unwrap_or(0);
    tokens.spanned(Span {
        start: max,
        end: max,
        file,
    })
}

#[derive(Debug, PartialEq, Eq)]
pub enum Error {
    Parse(String, Span),
    Lex(String, Span),
}

impl Error {
    fn new_parse<T>(error: chumsky::error::Rich<'_, T, Span>) -> Self
    where
        T: fmt::Display,
    {
        let span = *error.span();
        Error::Parse(format!("{}", FormattedError(error)), span)
    }

    pub fn pretty<'a>(&'a self, map: &'a SourceMap) -> impl fmt::Display + 'a {
        ErrorDisplay { map, err: self }
    }

    pub fn span(&self) -> Span {
        match self {
            Error::Parse(_, span) | Error::Lex(_, span) => *span,
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::Parse(msg, _) | Error::Lex(msg, _) => write!(f, "{msg}"),
        }
    }
}

impl std::error::Error for Error {}

struct FormattedError<'a, T, S>(chumsky::error::Rich<'a, T, S>);

impl<T: fmt::Display, S> fmt::Display for FormattedError<'_, T, S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0.reason())?;
        self.0
            .contexts()
            .try_for_each(|(label, _)| write!(f, " in {label}"))
    }
}

#[derive(Debug)]
struct ErrorDisplay<'a> {
    map: &'a SourceMap,
    err: &'a Error,
}

impl fmt::Display for ErrorDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let span = match self.err {
            Error::Parse(_, span) | Error::Lex(_, span) => span,
        };
        if let Some(file) = self.map.get(span.file) {
            let start = file.lookup(span.start);
            writeln!(f, "{}:{}:", file.path().display(), start)?;

            if let Some(line) = file.line(start.line) {
                let end = file.lookup(span.end);
                let underline_len = if start.line == end.line {
                    (end.col - start.col).max(1)
                } else {
                    3
                };
                writeln!(f, "{}", line)?;
                writeln!(f, "{0:1$}{:^<underline_len$}", "", start.col)?;
            }
        }
        write!(f, "{}", self.err)
    }
}
