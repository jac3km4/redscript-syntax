use std::{borrow::Cow, fmt, mem};

use crate::Span;
use chumsky::{container::Container, input::InputRef, prelude::*};

pub fn lex<'src>(
) -> impl Parser<'src, &'src str, Vec<(Token<'src>, Span)>, extra::Err<Rich<'src, char, Span>>> {
    recursive(|this| {
        let kw = choice([
            just("true").to(Token::True),
            just("false").to(Token::False),
            just("null").to(Token::Null),
            just("this").to(Token::This),
            just("super").to(Token::Super),
            just("case").to(Token::Case),
            just("default").to(Token::Default),
        ]);

        let num = text::int(10)
            .then(just('.').then(text::digits(10).or_not()).or_not())
            .to_slice()
            .then(choice([just("ul"), just("u"), just("l"), just("d")]).or_not())
            .try_map(|(s, suffix): (&str, _), span| match suffix {
                Some("ul") => Ok(Token::Ulong(s.parse().map_err(|e| Rich::custom(span, e))?)),
                Some("u") => Ok(Token::Uint(s.parse().map_err(|e| Rich::custom(span, e))?)),
                Some("l") => Ok(Token::Long(s.parse().map_err(|e| Rich::custom(span, e))?)),
                Some("d") => Ok(Token::Double(s.parse().map_err(|e| Rich::custom(span, e))?)),
                _ if s.contains('.') => {
                    Ok(Token::Float(s.parse().map_err(|e| Rich::custom(span, e))?))
                }
                _ => Ok(Token::Int(s.parse().map_err(|e| Rich::custom(span, e))?)),
            });

        let unicode_escape = any()
            .filter(char::is_ascii_hexdigit)
            .repeated()
            .at_least(1)
            .at_most(6)
            .to_slice()
            .delimited_by(just('{'), just('}'))
            .try_map(|str, span| {
                let n = u32::from_str_radix(str, 16).map_err(|err| Rich::custom(span, err))?;
                let c = std::char::from_u32(n)
                    .ok_or_else(|| Rich::custom(span, "invalid unicode escape"))?;
                Ok(Cow::Owned(c.into()))
            });

        let str_part = choice((
            none_of("\"\\")
                .repeated()
                .at_least(1)
                .to_slice()
                .map(Cow::Borrowed),
            just('\\').ignore_then(choice((
                just('n').to("\n".into()),
                just('r').to("\r".into()),
                just('t').to("\t".into()),
                just('\'').to("'".into()),
                just('"').to("\"".into()),
                just('\\').to("\\".into()),
                just('u').ignore_then(unicode_escape),
            ))),
        ));

        let str = one_of("nrt")
            .or_not()
            .then(
                str_part
                    .clone()
                    .repeated()
                    .collect::<StrParts<'_>>()
                    .delimited_by(just('"'), just('"')),
            )
            .map(|(prefix, parts)| match prefix {
                Some('n') => Token::CName(parts.str),
                Some('r') => Token::ResRef(parts.str),
                Some('t') => Token::TdbId(parts.str),
                _ => Token::Str(parts.str),
            });

        let balanced_parens = recursive(|p| {
            just('(')
                .ignore_then(p.or(any().and_is(just(')').not()).ignored()).repeated())
                .then_ignore(just(')'))
        })
        .to_slice();

        let interp_str = just('s')
            .ignore_then(
                choice((
                    str_part
                        .repeated()
                        .at_least(1)
                        .collect::<StrParts<'_>>()
                        .map(|ps| Token::StrFrag(ps.str)),
                    just("\\")
                        .ignore_then(
                            this.repeated()
                                .collect::<Vec<_>>()
                                .nested_in(balanced_parens),
                        )
                        .map(|tok| Token::Group(tok.into())),
                ))
                .map_with(|tok, e| (tok, e.span()))
                .repeated()
                .collect::<Vec<_>>()
                .delimited_by(just('"'), just('"')),
            )
            .map(|ps| Token::InterpStr(ps.into()));

        let ident = text::ascii::ident().map(Token::Ident);

        let line_comment = just("//")
            .ignored()
            .then_ignore(any().and_is(just('\n').not()).repeated())
            .padded();

        let block_comment = recursive(|comment| {
            just("/*")
                .ignored()
                .then_ignore(
                    comment
                        .or(any().and_is(just("*/").not()).ignored())
                        .repeated(),
                )
                .then_ignore(just("*/"))
                .padded()
        });

        let comment = line_comment.or(block_comment);

        choice((symbol(), kw, num, str, interp_str, ident))
            .padded_by(comment.repeated())
            .padded()
            .recover_with(skip_then_retry_until(any().ignored(), end()))
            .map_with(|tok, e| (tok, e.span()))
    })
    .repeated()
    .collect()
}

fn symbol<'src>(
) -> impl Parser<'src, &'src str, Token<'src>, extra::Err<Rich<'src, char, Span>>> + Clone {
    custom(|inp| {
        let before = inp.save();
        let pos = inp.offset();
        let skipped = |inp: &mut InputRef<'src, '_, _, _>, tok| {
            inp.skip();
            tok
        };
        let res = match inp.next() {
            Some('+') if inp.peek() == Some('=') => skipped(inp, Token::AssignAdd),
            Some('+') => Token::Plus,
            Some('-') if inp.peek() == Some('=') => skipped(inp, Token::AssignSub),
            Some('-') if inp.peek() == Some('>') => skipped(inp, Token::Arrow),
            Some('-') => Token::Minus,
            Some('*') if inp.peek() == Some('=') => skipped(inp, Token::AssignMul),
            Some('*') => Token::Star,
            Some('/') if inp.peek() == Some('=') => skipped(inp, Token::AssignDiv),
            Some('/') => Token::Slash,
            Some('%') => Token::Percent,
            Some('<') if inp.peek() == Some('=') => skipped(inp, Token::Le),
            Some('<') => Token::LAngle,
            Some('>') if inp.peek() == Some('=') => skipped(inp, Token::Ge),
            Some('>') => Token::RAngle,
            Some('!') if inp.peek() == Some('=') => skipped(inp, Token::Ne),
            Some('!') => Token::Not,
            Some('~') => Token::BitNot,
            Some('.') => Token::Period,
            Some(',') => Token::Comma,
            Some('(') => Token::LParen,
            Some(')') => Token::RParen,
            Some('{') => Token::LBrace,
            Some('}') => Token::RBrace,
            Some('[') => Token::LBracket,
            Some(']') => Token::RBracket,
            Some('&') if inp.peek() == Some('&') => skipped(inp, Token::And),
            Some('&') if inp.peek() == Some('=') => skipped(inp, Token::AssignBitAnd),
            Some('&') => Token::BitAnd,
            Some('|') if inp.peek() == Some('|') => skipped(inp, Token::Or),
            Some('|') if inp.peek() == Some('=') => skipped(inp, Token::AssignBitOr),
            Some('|') => Token::BitOr,
            Some('^') => Token::BitXor,
            Some(':') => Token::Colon,
            Some(';') => Token::Semicolon,
            Some('=') if inp.peek() == Some('=') => skipped(inp, Token::Eq),
            Some('=') => Token::Assign,
            Some('?') => Token::Question,
            Some('@') => Token::At,
            _ => {
                inp.rewind(before);
                return Err(Rich::custom(inp.span(pos..pos), "invalid symbol"));
            }
        };
        Ok(res)
    })
}

#[derive(Debug, Clone, PartialEq)]
pub enum Token<'src> {
    Group(Box<[(Self, Span)]>),
    Ident(&'src str),
    Int(i32),
    Uint(u32),
    Ulong(u64),
    Long(i64),
    Float(f32),
    Double(f64),
    Str(Cow<'src, str>),
    CName(Cow<'src, str>),
    ResRef(Cow<'src, str>),
    TdbId(Cow<'src, str>),
    StrFrag(Cow<'src, str>),
    InterpStr(Box<[(Self, Span)]>),

    AssignAdd,
    AssignSub,
    AssignMul,
    AssignDiv,
    AssignBitOr,
    AssignBitAnd,

    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    Eq,
    Ne,
    Le,
    Ge,
    And,
    Or,
    BitAnd,
    BitOr,
    BitXor,
    Not,
    BitNot,

    Period,
    Comma,
    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket,
    RBracket,
    LAngle,
    RAngle,
    Arrow,
    Colon,
    Semicolon,
    Assign,
    Question,
    At,

    True,
    False,
    Null,
    This,
    Super,
    Case,
    Default,
}

impl fmt::Display for Token<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Token::Ident(s) => write!(f, "{}", s),
            Token::Int(n) => write!(f, "{}", n),
            Token::Uint(n) => write!(f, "{}u", n),
            Token::Ulong(n) => write!(f, "{}ul", n),
            Token::Long(n) => write!(f, "{}l", n),
            Token::Float(n) => write!(f, "{}", n),
            Token::Double(n) => write!(f, "{}d", n),
            Token::Str(s) => write!(f, "\"{}\"", s),
            Token::CName(s) => write!(f, "n\"{}\"", s),
            Token::ResRef(s) => write!(f, "r\"{}\"", s),
            Token::TdbId(s) => write!(f, "t\"{}\"", s),
            Token::InterpStr(s) => {
                write!(f, "s\"")?;
                for (tok, _) in s.iter() {
                    write!(f, "{}", tok)?;
                }
                write!(f, "\"")
            }
            Token::Group(s) => {
                for (tok, _) in s.iter() {
                    write!(f, "\\({})", tok)?;
                }
                Ok(())
            }
            Token::StrFrag(s) => write!(f, "{}", s),
            Token::AssignAdd => write!(f, "+="),
            Token::AssignSub => write!(f, "-="),
            Token::AssignMul => write!(f, "*="),
            Token::AssignDiv => write!(f, "/="),
            Token::AssignBitOr => write!(f, "|="),
            Token::AssignBitAnd => write!(f, "&="),
            Token::Plus => write!(f, "+"),
            Token::Minus => write!(f, "-"),
            Token::Star => write!(f, "*"),
            Token::Slash => write!(f, "/"),
            Token::Percent => write!(f, "%"),
            Token::Eq => write!(f, "=="),
            Token::Ne => write!(f, "!="),
            Token::Le => write!(f, "<="),
            Token::Ge => write!(f, ">="),
            Token::And => write!(f, "&&"),
            Token::Or => write!(f, "||"),
            Token::BitAnd => write!(f, "&"),
            Token::BitOr => write!(f, "|"),
            Token::BitXor => write!(f, "^"),
            Token::Not => write!(f, "!"),
            Token::BitNot => write!(f, "~"),
            Token::Period => write!(f, "."),
            Token::Comma => write!(f, ","),
            Token::LParen => write!(f, "("),
            Token::RParen => write!(f, ")"),
            Token::LBrace => write!(f, "{{"),
            Token::RBrace => write!(f, "}}"),
            Token::LBracket => write!(f, "["),
            Token::RBracket => write!(f, "]"),
            Token::LAngle => write!(f, "<"),
            Token::RAngle => write!(f, ">"),
            Token::Arrow => write!(f, "->"),
            Token::Colon => write!(f, ":"),
            Token::Semicolon => write!(f, ";"),
            Token::Assign => write!(f, "="),
            Token::Question => write!(f, "?"),
            Token::At => write!(f, "@"),
            Token::True => write!(f, "true"),
            Token::False => write!(f, "false"),
            Token::Null => write!(f, "null"),
            Token::This => write!(f, "this"),
            Token::Super => write!(f, "super"),
            Token::Case => write!(f, "case"),
            Token::Default => write!(f, "default"),
        }
    }
}

#[derive(Debug, Default)]
struct StrParts<'src> {
    str: Cow<'src, str>,
}

impl<'src> Container<Cow<'src, str>> for StrParts<'src> {
    #[inline]
    fn push(&mut self, c: Cow<'src, str>) {
        if self.str.is_empty() {
            self.str = c;
        } else {
            self.str = Cow::Owned(mem::take(&mut self.str).into_owned() + &c);
        }
    }
}
