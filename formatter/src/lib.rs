use std::fmt;

use pretty_dtoa::{dtoa, ftoa, FmtFloatConfig};
use redscript_ast::{
    Aggregate, Annotation, BinOp, Block, Constant, Enum, EnumVariant, Expr, Field, Function,
    Import, Item, ItemDecl, ItemQualifiers, Module, Param, ParamQualifiers, Path, Stmt, StrPart,
    Type, UnOp, Visibility, Wrap, Wrapper,
};

#[derive(Debug, Clone, Copy)]
pub struct FormatSettings {
    pub indent: u16,
    pub max_sig_digits: Option<u8>,
}

#[derive(Debug, Clone, Copy)]
pub struct FormatCtx<'s> {
    settings: &'s FormatSettings,
    depth: u16,
}

impl FormatCtx<'_> {
    fn ws(&self) -> Indent {
        Indent(self.depth * self.settings.indent)
    }

    fn bump(&self, n: u16) -> Self {
        Self {
            settings: self.settings,
            depth: self.depth + n,
        }
    }
}

pub trait Formattable: Sized {
    fn format(&self, f: &mut fmt::Formatter<'_>, ctx: FormatCtx<'_>) -> fmt::Result;

    fn display(&self, settings: &FormatSettings) -> impl fmt::Display {
        DisplayProxy(self, FormatCtx { settings, depth: 0 })
    }
}

impl<W: Wrap> Formattable for Item<'_, W> {
    fn format(&self, f: &mut fmt::Formatter<'_>, ctx: FormatCtx<'_>) -> fmt::Result {
        match self {
            Item::Import(import) => write!(f, "{}", import.as_fmt(ctx)),
            Item::Class(class) => write!(f, "class {}", class.as_fmt(ctx)),
            Item::Struct(struct_) => write!(f, "struct {}", struct_.as_fmt(ctx)),
            Item::Function(func) => write!(f, "{}", func.as_fmt(ctx)),
            Item::Let(field) => write!(f, "{}", field.as_fmt(ctx)),
            Item::Enum(enum_) => write!(f, "{}", enum_.as_fmt(ctx)),
        }
    }
}

impl<W: Wrap> Formattable for Module<'_, W> {
    fn format(&self, f: &mut fmt::Formatter<'_>, ctx: FormatCtx<'_>) -> fmt::Result {
        if let Some(path) = &self.path {
            writeln!(f, "module {}", path.as_fmt(ctx))?;
        }
        for item in &self.items[..] {
            writeln!(f, "{}", item.as_val().as_fmt(ctx))?;
        }
        Ok(())
    }
}

impl<W: Wrap> Formattable for ItemDecl<'_, W> {
    fn format(&self, f: &mut fmt::Formatter<'_>, ctx: FormatCtx<'_>) -> fmt::Result {
        for ann in &self.annotations[..] {
            writeln!(f, "{}{}", ctx.ws(), ann.as_val().as_fmt(ctx))?;
        }
        write!(f, "{}", ctx.ws())?;
        if let Some(visibility) = &self.visibility {
            write!(f, "{} ", visibility.as_fmt(ctx))?;
        }
        writeln!(
            f,
            "{}{}",
            self.qualifiers.as_fmt(ctx),
            self.item.as_fmt(ctx)
        )
    }
}

impl Formattable for Import<'_> {
    fn format(&self, f: &mut fmt::Formatter<'_>, ctx: FormatCtx<'_>) -> fmt::Result {
        match self {
            Import::Exact(path) => write!(f, "import {}", path.as_fmt(ctx)),
            Import::Select(path, items) => write!(
                f,
                "import {}.{{{}}}",
                path.as_fmt(ctx),
                SepBy(items.iter().map(Wrapper::as_val), ", ", ctx)
            ),
            Import::All(path) => write!(f, "import {}.*", path.as_fmt(ctx)),
        }
    }
}

impl<W: Wrap> Formattable for Aggregate<'_, W> {
    fn format(&self, f: &mut fmt::Formatter<'_>, ctx: FormatCtx<'_>) -> fmt::Result {
        writeln!(f, "{} {{", self.name)?;
        for item in &self.items[..] {
            writeln!(f, "{}", item.as_val().as_fmt(ctx.bump(1)))?;
        }
        write!(f, "{}}}", ctx.ws())
    }
}

impl<W: Wrap> Formattable for Field<'_, W> {
    fn format(&self, f: &mut fmt::Formatter<'_>, ctx: FormatCtx<'_>) -> fmt::Result {
        write!(f, "let {}: {}", self.name, self.ty.as_val().as_fmt(ctx))?;
        if let Some(value) = &self.default {
            write!(f, " = {}", value.as_val().as_fmt(ctx))?;
        }
        write!(f, ";")
    }
}

impl<W: Wrap> Formattable for Function<'_, W> {
    fn format(&self, f: &mut fmt::Formatter<'_>, ctx: FormatCtx<'_>) -> fmt::Result {
        write!(
            f,
            "func {}({}) ",
            self.name,
            SepBy(self.params.iter().map(Wrapper::as_val), ", ", ctx)
        )?;
        if let Some(ty) = &self.return_ty {
            write!(f, "-> {} ", ty.as_val().as_fmt(ctx))?;
        }
        if let Some(body) = &self.body {
            write!(f, "{}", body.as_fmt(ctx))
        } else {
            write!(f, ";")
        }
    }
}

impl<W: Wrap> Formattable for Enum<'_, W> {
    fn format(&self, f: &mut fmt::Formatter<'_>, ctx: FormatCtx<'_>) -> fmt::Result {
        writeln!(f, "enum {} {{", self.name)?;
        for variant in &self.variants[..] {
            let ctx = ctx.bump(1);
            writeln!(f, "{}{},", ctx.ws(), variant.as_val().as_fmt(ctx))?;
        }
        writeln!(f, "}}")
    }
}

impl Formattable for EnumVariant<'_> {
    fn format(&self, f: &mut fmt::Formatter<'_>, _ctx: FormatCtx<'_>) -> fmt::Result {
        write!(f, "{}", self.name)?;
        if let Some(value) = &self.value {
            write!(f, " = {value}")?;
        }
        Ok(())
    }
}

impl<W: Wrap> Formattable for Block<'_, W> {
    fn format(&self, f: &mut fmt::Formatter<'_>, ctx: FormatCtx<'_>) -> fmt::Result {
        writeln!(f, "{{")?;
        for stmt in &self.stmts[..] {
            writeln!(f, "{}", stmt.as_val().as_fmt(ctx.bump(1)))?;
        }
        write!(f, "{}}}", ctx.ws())
    }
}

impl<W: Wrap> Formattable for Stmt<'_, W> {
    fn format(&self, f: &mut fmt::Formatter<'_>, ctx: FormatCtx<'_>) -> fmt::Result {
        match self {
            Stmt::Let { name, ty, value } => {
                write!(f, "{}let {name}", ctx.ws())?;
                if let Some(ty) = ty {
                    write!(f, ": {}", ty.as_val().as_fmt(ctx))?;
                }
                if let Some(value) = value {
                    write!(f, " = {}", (**value).as_val().as_fmt(ctx.bump(1)))?;
                }
                write!(f, ";")
            }
            Stmt::Switch {
                expr,
                cases,
                default,
            } => {
                writeln!(f, "{}switch {} {{", ctx.ws(), (**expr).as_val().as_fmt(ctx))?;
                for case in &cases[..] {
                    let ctx = ctx.bump(1);
                    writeln!(f, "{}case {}:", ctx.ws(), case.label.as_val().as_fmt(ctx))?;
                    for stmt in &case.body[..] {
                        writeln!(f, "{}", stmt.as_val().as_fmt(ctx.bump(1)))?;
                    }
                }
                if let Some(default) = default {
                    let ctx = ctx.bump(1);
                    writeln!(f, "{}default:", ctx.ws())?;
                    for stmt in &default[..] {
                        writeln!(f, "{}", stmt.as_val().as_fmt(ctx.bump(1)))?;
                    }
                }
                writeln!(f, "{}}}", ctx.ws())
            }
            Stmt::If { blocks, else_ } => {
                write!(f, "{}", ctx.ws())?;
                let mut it = blocks.iter();
                if let Some(block) = it.next() {
                    write!(
                        f,
                        "if {} {}",
                        block.cond.as_val().as_fmt(ctx),
                        block.body.as_fmt(ctx)
                    )?;
                }
                for block in it {
                    write!(
                        f,
                        " else if {} {}",
                        block.cond.as_val().as_fmt(ctx),
                        block.body.as_fmt(ctx)
                    )?;
                }
                if let Some(else_) = else_ {
                    write!(f, " else {}", else_.as_fmt(ctx))?;
                }
                Ok(())
            }
            Stmt::While(block) => {
                write!(f, "{}while {} ", ctx.ws(), block.cond.as_val().as_fmt(ctx))?;
                writeln!(f, "{}", block.body.as_fmt(ctx))
            }
            Stmt::ForIn { name, iter, body } => {
                write!(
                    f,
                    "{}for {} in {} ",
                    ctx.ws(),
                    name,
                    (**iter).as_val().as_fmt(ctx)
                )?;
                writeln!(f, "{}", body.as_fmt(ctx))
            }
            Stmt::Return(Some(expr)) => {
                write!(f, "{}return {};", ctx.ws(), (**expr).as_val().as_fmt(ctx))
            }
            Stmt::Return(None) => {
                write!(f, "{}return;", ctx.ws())
            }
            Stmt::Break => {
                write!(f, "{}break;", ctx.ws())
            }
            Stmt::Expr(expr) => write!(f, "{}{};", ctx.ws(), (**expr).as_val().as_fmt(ctx)),
        }
    }
}

impl<W: Wrap> Formattable for Expr<'_, W> {
    fn format(&self, f: &mut fmt::Formatter<'_>, ctx: FormatCtx<'_>) -> fmt::Result {
        match self {
            Expr::Ident(name) => write!(f, "{name}"),
            Expr::Constant(value) => match (value, ctx.settings.max_sig_digits) {
                (Constant::String(s), _) => write!(f, "\"{}\"", str::escape_default(s)),
                (Constant::CName(s), _) => write!(f, "n\"{}\"", str::escape_default(s)),
                (Constant::Resource(s), _) => write!(f, "r\"{}\"", str::escape_default(s)),
                (Constant::TweakDbId(s), _) => write!(f, "t\"{}\"", str::escape_default(s)),
                (&Constant::F32(v), Some(max_sig_digits)) => {
                    let conf = FmtFloatConfig::default()
                        .max_significant_digits(max_sig_digits)
                        .round();
                    write!(f, "{}", ftoa(v, conf))
                }
                (Constant::F32(v), _) => {
                    write!(f, "{v}")
                }
                (&Constant::F64(v), Some(max_sig_digits)) => {
                    let conf = FmtFloatConfig::default()
                        .max_significant_digits(max_sig_digits)
                        .round();
                    write!(f, "{}d", dtoa(v, conf))
                }
                (Constant::F64(v), _) => {
                    write!(f, "{v}d")
                }
                (Constant::I32(v), _) => write!(f, "{v}"),
                (Constant::I64(v), _) => write!(f, "{v}l"),
                (Constant::U32(v), _) => write!(f, "{v}u"),
                (Constant::U64(v), _) => write!(f, "{v}ul"),
                (Constant::Bool(v), _) => write!(f, "{v}"),
            },
            Expr::ArrayLit(elems) => {
                write!(
                    f,
                    "[{}]",
                    SepBy(elems.iter().map(Wrapper::as_val), ", ", ctx)
                )
            }
            Expr::InterpolatedString(parts) => {
                write!(f, "s\"")?;
                for part in &parts[..] {
                    match part {
                        StrPart::Expr(expr) => write!(f, "\\({})", expr.as_val().as_fmt(ctx))?,
                        StrPart::Str(s) => write!(f, "{}", str::escape_default(s))?,
                    }
                }
                write!(f, "\"")?;
                Ok(())
            }
            Expr::Assign { lhs, rhs } => {
                write!(
                    f,
                    "{} = {}",
                    (**lhs).as_val().as_fmt(ctx),
                    (**rhs).as_val().as_fmt(ctx)
                )
            }
            Expr::BinOp { lhs, op, rhs } => {
                write!(
                    f,
                    "{} {} {}",
                    (**lhs).as_val().as_fmt(ctx),
                    op.as_fmt(ctx),
                    (**rhs).as_val().as_fmt(ctx)
                )
            }
            Expr::UnOp { op, expr } => {
                write!(f, "{}{}", op.as_fmt(ctx), (**expr).as_val().as_fmt(ctx))
            }
            Expr::Call { expr, args } => {
                write!(
                    f,
                    "{}({})",
                    (**expr).as_val().as_fmt(ctx),
                    SepBy(args.iter().map(Wrapper::as_val), ", ", ctx)
                )
            }
            Expr::Member { expr, member } => {
                write!(f, "{}.{member}", (**expr).as_val().as_fmt(ctx))
            }
            Expr::Index { expr, index } => {
                write!(
                    f,
                    "{}[{}]",
                    (**expr).as_val().as_fmt(ctx),
                    (**index).as_val().as_fmt(ctx)
                )
            }
            Expr::DynCast { expr, ty } => {
                write!(
                    f,
                    "{} as {}",
                    (**expr).as_val().as_fmt(ctx),
                    ty.as_val().as_fmt(ctx)
                )
            }
            Expr::New { ty, args } => {
                write!(
                    f,
                    "new {}({})",
                    ty.as_val().as_fmt(ctx),
                    SepBy(args.iter().map(Wrapper::as_val), ", ", ctx)
                )
            }
            Expr::Conditional { cond, then, else_ } => {
                write!(
                    f,
                    "{} ? {} : {}",
                    (**cond).as_val().as_fmt(ctx),
                    (**then).as_val().as_fmt(ctx),
                    (**else_).as_val().as_fmt(ctx)
                )
            }
            Expr::This => write!(f, "this"),
            Expr::Super => write!(f, "super"),
            Expr::Null => write!(f, "null"),
            Expr::Error => Ok(()),
        }
    }
}

impl<W: Wrap> Formattable for Param<'_, W> {
    fn format(&self, f: &mut fmt::Formatter<'_>, ctx: FormatCtx<'_>) -> fmt::Result {
        if self.qualifiers.contains(ParamQualifiers::OUT) {
            write!(f, "out ")?;
        };
        if self.qualifiers.contains(ParamQualifiers::OPTIONAL) {
            write!(f, "opt ")?;
        };
        if self.qualifiers.contains(ParamQualifiers::CONST) {
            write!(f, "const ")?;
        };
        write!(f, "{}: {}", self.name, self.ty.as_val().as_fmt(ctx))
    }
}

impl Formattable for Type<'_> {
    fn format(&self, f: &mut fmt::Formatter<'_>, ctx: FormatCtx<'_>) -> fmt::Result {
        match self {
            Type::Named { name, args } if args.is_empty() => write!(f, "{name}"),
            Type::Named { name, args } => write!(
                f,
                "{}<{}>",
                name,
                SepBy(args.iter().map(Wrapper::as_val), ", ", ctx)
            ),
            Type::Array(el) => write!(f, "[{}]", el.as_val().as_fmt(ctx)),
            Type::StaticArray(el, size) => write!(f, "[{}; {}]", el.as_val().as_fmt(ctx), size),
        }
    }
}

impl<W: Wrap> Formattable for Annotation<'_, W> {
    fn format(&self, f: &mut fmt::Formatter<'_>, ctx: FormatCtx<'_>) -> fmt::Result {
        write!(
            f,
            "@{}({})",
            self.name,
            SepBy(self.args.iter().map(Wrapper::as_val), ", ", ctx)
        )
    }
}

impl Formattable for Path<'_> {
    fn format(&self, f: &mut fmt::Formatter<'_>, ctx: FormatCtx<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            SepBy(self.segments.iter().map(Wrapper::as_val), ".", ctx)
        )
    }
}

impl Formattable for BinOp {
    fn format(&self, f: &mut fmt::Formatter<'_>, _ctx: FormatCtx<'_>) -> fmt::Result {
        match self {
            Self::AssignAdd => write!(f, "+="),
            Self::AssignSub => write!(f, "-="),
            Self::AssignMul => write!(f, "*="),
            Self::AssignDiv => write!(f, "/="),
            Self::AssignBitOr => write!(f, "|="),
            Self::AssignBitAnd => write!(f, "&="),
            Self::Or => write!(f, "||"),
            Self::And => write!(f, "&&"),
            Self::BitOr => write!(f, "|"),
            Self::BitXor => write!(f, "^"),
            Self::BitAnd => write!(f, "&"),
            Self::Eq => write!(f, "=="),
            Self::Ne => write!(f, "!="),
            Self::Lt => write!(f, "<"),
            Self::Le => write!(f, "<="),
            Self::Gt => write!(f, ">"),
            Self::Ge => write!(f, ">="),
            Self::Add => write!(f, "+"),
            Self::Sub => write!(f, "-"),
            Self::Mul => write!(f, "*"),
            Self::Div => write!(f, "/"),
            Self::Mod => write!(f, "%"),
        }
    }
}

impl Formattable for UnOp {
    fn format(&self, f: &mut fmt::Formatter<'_>, _ctx: FormatCtx<'_>) -> fmt::Result {
        match self {
            Self::BitNot => write!(f, "~"),
            Self::Not => write!(f, "!"),
            Self::Neg => write!(f, "-"),
        }
    }
}

impl Formattable for ItemQualifiers {
    fn format(&self, f: &mut fmt::Formatter<'_>, _ctx: FormatCtx<'_>) -> fmt::Result {
        if self.contains(ItemQualifiers::ABSTRACT) {
            write!(f, "abstract ")?;
        }
        if self.contains(ItemQualifiers::CALLBACK) {
            write!(f, "cb ")?;
        }
        if self.contains(ItemQualifiers::CONST) {
            write!(f, "const ")?;
        }
        if self.contains(ItemQualifiers::EXEC) {
            write!(f, "exec ")?;
        }
        if self.contains(ItemQualifiers::FINAL) {
            write!(f, "final ")?;
        }
        if self.contains(ItemQualifiers::IMPORT_ONLY) {
            write!(f, "importonly ")?;
        }
        if self.contains(ItemQualifiers::NATIVE) {
            write!(f, "native ")?;
        }
        if self.contains(ItemQualifiers::PERSISTENT) {
            write!(f, "persistent ")?;
        }
        if self.contains(ItemQualifiers::QUEST) {
            write!(f, "quest ")?;
        }
        if self.contains(ItemQualifiers::STATIC) {
            write!(f, "static ")?;
        }
        Ok(())
    }
}

impl Formattable for Visibility {
    fn format(&self, f: &mut fmt::Formatter<'_>, _ctx: FormatCtx<'_>) -> fmt::Result {
        match self {
            Self::Public => write!(f, "public"),
            Self::Protected => write!(f, "protected"),
            Self::Private => write!(f, "private"),
        }
    }
}

struct DisplayProxy<'s, A>(A, FormatCtx<'s>);

impl<A: Formattable> fmt::Display for DisplayProxy<'_, &A> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.format(f, self.1)
    }
}

struct Indent(u16);

impl fmt::Display for Indent {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:w$}", "", w = usize::from(self.0))
    }
}

struct SepBy<'s, I>(I, &'static str, FormatCtx<'s>);

impl<I: Iterator + Clone> fmt::Display for SepBy<'_, I>
where
    I::Item: Formattable,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, item) in self.0.clone().enumerate() {
            if i > 0 {
                write!(f, "{}", self.1)?;
            }
            write!(f, "{}", item.as_fmt(self.2))?;
        }
        Ok(())
    }
}

trait SyntaxOps {
    fn as_fmt(&self, ctx: FormatCtx<'_>) -> impl fmt::Display;
}

impl<A> SyntaxOps for A
where
    A: Formattable,
{
    #[inline]
    fn as_fmt(&self, ctx: FormatCtx<'_>) -> impl fmt::Display {
        DisplayProxy(self, ctx)
    }
}

impl Formattable for &str {
    fn format(&self, f: &mut fmt::Formatter<'_>, _ctx: FormatCtx<'_>) -> fmt::Result {
        write!(f, "{}", self)
    }
}

impl<A: Formattable> Formattable for &A {
    fn format(&self, f: &mut fmt::Formatter<'_>, ctx: FormatCtx<'_>) -> fmt::Result {
        (*self).format(f, ctx)
    }
}
