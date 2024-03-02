use std::{fmt, mem};

use pretty_dtoa::{dtoa, ftoa, FmtFloatConfig};
use redscript_ast::{
    Aggregate, Annotation, Assoc, AstKind, BinOp, Block, Constant, Enum, EnumVariant, Expr, Field,
    Function, FunctionBody, Import, Item, ItemDecl, ItemQualifiers, Module, Param, ParamQualifiers,
    Path, Stmt, StrPart, Type, UnOp, Visibility, Wrapper,
};

#[derive(Debug, Clone, Copy)]
pub struct FormatSettings {
    pub indent: u16,
    pub max_length: u16,
    pub max_chain: u8,
    pub trunc_sig_digits: Option<u8>,
}

impl Default for FormatSettings {
    fn default() -> Self {
        Self {
            indent: 2,
            max_length: 80,
            max_chain: 2,
            trunc_sig_digits: None,
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct FormatCtx<'s> {
    settings: &'s FormatSettings,
    depth: u16,
    parent: Option<ParentOp>,
}

impl FormatCtx<'_> {
    fn ws(&self) -> Indent {
        Indent(self.depth * self.settings.indent)
    }

    fn bump(&self, n: u16) -> Self {
        Self {
            settings: self.settings,
            depth: self.depth + n,
            parent: self.parent,
        }
    }

    fn decrement(&self) -> Self {
        Self {
            settings: self.settings,
            depth: self.depth - 1,
            parent: self.parent,
        }
    }

    fn current_indent(&self) -> u16 {
        self.depth * self.settings.indent
    }

    fn with_parent_op(&self, parent: ParentOp) -> Self {
        Self {
            parent: Some(parent),
            ..*self
        }
    }

    fn without_parent_op(&self) -> Self {
        Self {
            parent: None,
            ..*self
        }
    }
}

pub trait Formattable: Sized {
    fn format(&self, f: &mut fmt::Formatter<'_>, ctx: FormatCtx<'_>) -> fmt::Result;

    fn display(&self, settings: &FormatSettings) -> impl fmt::Display {
        DisplayProxy(
            self,
            FormatCtx {
                settings,
                depth: 0,
                parent: None,
            },
        )
    }
}

impl<K: AstKind> Formattable for Item<'_, K> {
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

impl<K: AstKind> Formattable for Module<'_, K> {
    fn format(&self, f: &mut fmt::Formatter<'_>, ctx: FormatCtx<'_>) -> fmt::Result {
        if let Some(path) = &self.path {
            writeln!(f, "module {}", path.as_fmt(ctx))?;
        }
        writeln!(f)?;
        format_items(self.items.iter().map(Wrapper::as_val), f, ctx)
    }
}

impl<K: AstKind> Formattable for ItemDecl<'_, K> {
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

impl<K: AstKind> Formattable for Aggregate<'_, K> {
    fn format(&self, f: &mut fmt::Formatter<'_>, ctx: FormatCtx<'_>) -> fmt::Result {
        writeln!(f, "{} {{", self.name)?;
        format_items(self.items.iter().map(Wrapper::as_val), f, ctx.bump(1))?;
        write!(f, "{}}}", ctx.ws())
    }
}

impl<K: AstKind> Formattable for Field<'_, K> {
    fn format(&self, f: &mut fmt::Formatter<'_>, ctx: FormatCtx<'_>) -> fmt::Result {
        write!(f, "let {}: {}", self.name, self.ty.as_val().as_fmt(ctx))?;
        if let Some(value) = &self.default {
            write!(f, " = {}", value.as_val().as_fmt(ctx))?;
        }
        write!(f, ";")
    }
}

impl<K: AstKind> Formattable for Function<'_, K> {
    fn format(&self, f: &mut fmt::Formatter<'_>, ctx: FormatCtx<'_>) -> fmt::Result {
        write!(
            f,
            "func {}({}) ",
            self.name,
            SepByMultiline(self.params.iter().map(Wrapper::as_val), ", ", ctx)
        )?;
        if let Some(ty) = &self.return_ty {
            write!(f, "-> {} ", ty.as_val().as_fmt(ctx))?;
        }
        match &self.body {
            Some(FunctionBody::Block(block)) => write!(f, "{}", block.as_fmt(ctx)),
            Some(FunctionBody::Inline(expr)) => write!(f, "= {};", (**expr).as_val().as_fmt(ctx)),
            None => write!(f, ";"),
        }
    }
}

impl<K: AstKind> Formattable for Enum<'_, K> {
    fn format(&self, f: &mut fmt::Formatter<'_>, ctx: FormatCtx<'_>) -> fmt::Result {
        writeln!(f, "enum {} {{", self.name)?;
        for variant in &self.variants[..] {
            let ctx = ctx.bump(1);
            writeln!(f, "{}{},", ctx.ws(), variant.as_val().as_fmt(ctx))?;
        }
        write!(f, "}}")
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

impl<K: AstKind> Formattable for Block<'_, K> {
    fn format(&self, f: &mut fmt::Formatter<'_>, ctx: FormatCtx<'_>) -> fmt::Result {
        writeln!(f, "{{")?;
        format_stmts(self.stmts.iter().map(Wrapper::as_val), f, ctx.bump(1))?;
        write!(f, "{}}}", ctx.ws())
    }
}

impl<K: AstKind> Formattable for Stmt<'_, K> {
    fn format(&self, f: &mut fmt::Formatter<'_>, ctx: FormatCtx<'_>) -> fmt::Result {
        match self {
            Stmt::Let { name, ty, value } => {
                write!(f, "{}let {name}", ctx.ws())?;
                if let Some(ty) = ty {
                    write!(f, ": {}", ty.as_val().as_fmt(ctx))?;
                }
                if let Some(value) = value {
                    write!(f, " = {}", (**value).as_val().as_fmt(ctx))?;
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
                write!(f, "{}}}", ctx.ws())
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
                write!(f, "{}", block.body.as_fmt(ctx))
            }
            Stmt::ForIn { name, iter, body } => {
                write!(
                    f,
                    "{}for {} in {} ",
                    ctx.ws(),
                    name,
                    (**iter).as_val().as_fmt(ctx)
                )?;
                write!(f, "{}", body.as_fmt(ctx))
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

impl<K: AstKind> Formattable for Expr<'_, K> {
    fn format(&self, f: &mut fmt::Formatter<'_>, ctx: FormatCtx<'_>) -> fmt::Result {
        match self {
            Expr::Ident(name) => write!(f, "{name}"),
            Expr::Constant(value) => match (value, ctx.settings.trunc_sig_digits) {
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
                (&Constant::F32(v), _) => {
                    write!(f, "{}", ftoa(v, FmtFloatConfig::default()))
                }
                (&Constant::F64(v), Some(max_sig_digits)) => {
                    let conf = FmtFloatConfig::default()
                        .max_significant_digits(max_sig_digits)
                        .round();
                    write!(f, "{}d", dtoa(v, conf))
                }
                (&Constant::F64(v), _) => {
                    write!(f, "{}", dtoa(v, FmtFloatConfig::default()))
                }
                (Constant::I32(v), _) => write!(f, "{v}"),
                (Constant::I64(v), _) => write!(f, "{v}l"),
                (Constant::U32(v), _) => write!(f, "{v}u"),
                (Constant::U64(v), _) => write!(f, "{v}ul"),
                (Constant::Bool(v), _) => write!(f, "{v}"),
            },
            Expr::ArrayLit(elems) => {
                let ctx = ctx.without_parent_op();
                write!(
                    f,
                    "[{}]",
                    SepByMultiline(elems.iter().map(Wrapper::as_val), ", ", ctx)
                )
            }
            Expr::InterpolatedString(parts) => {
                let ctx = ctx.without_parent_op();
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
                let ctx = ctx.without_parent_op();
                write!(
                    f,
                    "{} = {}",
                    (**lhs).as_val().as_fmt(ctx),
                    (**rhs).as_val().as_fmt(ctx)
                )
            }
            Expr::BinOp { lhs, op, rhs } => {
                let can_assoc = match ctx.parent {
                    Some(ParentOp::TopPrec | ParentOp::Unary) => false,
                    Some(ParentOp::BinaryLhs(parent)) | Some(ParentOp::BinaryRhs(parent))
                        if parent.precedence() < op.precedence() =>
                    {
                        true
                    }
                    Some(ParentOp::BinaryLhs(parent)) => {
                        parent.precedence() == op.precedence() && parent.assoc() == Assoc::Left
                    }
                    Some(ParentOp::BinaryRhs(parent)) => {
                        parent.precedence() == op.precedence() && parent.assoc() == Assoc::Right
                    }
                    None => true,
                };
                let lhs = (**lhs)
                    .as_val()
                    .as_fmt(ctx.with_parent_op(ParentOp::BinaryLhs(*op)));
                let rhs = (**rhs)
                    .as_val()
                    .as_fmt(ctx.with_parent_op(ParentOp::BinaryRhs(*op)));
                if can_assoc {
                    write!(f, "{} {} {}", lhs, op.as_fmt(ctx), rhs)
                } else {
                    write!(f, "({} {} {})", lhs, op.as_fmt(ctx), rhs)
                }
            }
            Expr::UnOp { op, expr } => {
                let can_assoc = !matches!(ctx.parent, Some(ParentOp::TopPrec));
                let ctx = ctx.with_parent_op(ParentOp::Unary);
                let expr = (**expr).as_val().as_fmt(ctx);
                if can_assoc {
                    write!(f, "{}{}", op.as_fmt(ctx), expr)
                } else {
                    write!(f, "({}{})", op.as_fmt(ctx), expr)
                }
            }
            Expr::Call { expr, args } => {
                write!(
                    f,
                    "{}({})",
                    (**expr)
                        .as_val()
                        .as_fmt(ctx.with_parent_op(ParentOp::TopPrec)),
                    SepByMultiline(
                        args.iter().map(Wrapper::as_val),
                        ", ",
                        ctx.without_parent_op()
                    )
                )
            }
            Expr::Member { .. } => {
                let ctx = ctx.without_parent_op();
                format_member(self, f, ctx)
            }
            Expr::Index { expr, index } => {
                write!(
                    f,
                    "{}[{}]",
                    (**expr)
                        .as_val()
                        .as_fmt(ctx.with_parent_op(ParentOp::TopPrec)),
                    (**index).as_val().as_fmt(ctx.without_parent_op())
                )
            }
            Expr::DynCast { expr, ty } => {
                let ctx = ctx.with_parent_op(ParentOp::TopPrec);
                write!(
                    f,
                    "{} as {}",
                    (**expr).as_val().as_fmt(ctx),
                    ty.as_val().as_fmt(ctx)
                )
            }
            Expr::New { ty, args } => {
                let ctx = ctx.without_parent_op();
                write!(
                    f,
                    "new {}({})",
                    ty.as_val().as_fmt(ctx),
                    SepByMultiline(args.iter().map(Wrapper::as_val), ", ", ctx)
                )
            }
            Expr::Conditional { cond, then, else_ } => {
                let ctx = ctx.without_parent_op();
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

impl<K: AstKind> Formattable for Param<'_, K> {
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

impl<K: AstKind> Formattable for Annotation<'_, K> {
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

struct SepByMultiline<'s, I>(I, &'static str, FormatCtx<'s>);

impl<I: Iterator + Clone> fmt::Display for SepByMultiline<'_, I>
where
    I::Item: Formattable,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self(iter, sep, ctx) = self;
        let vec: Vec<_> = iter
            .clone()
            .into_iter()
            .map(|elem| elem.as_fmt(ctx.bump(1)).to_string())
            .collect();
        if ctx.current_indent() + vec.iter().map(|s| s.len() as u16).sum::<u16>()
            > ctx.settings.max_length
        {
            let sep = sep.trim_end();
            let ctx = ctx.bump(1);
            for (i, elem) in vec.iter().enumerate() {
                if i > 0 {
                    write!(f, "{sep}")?;
                }
                writeln!(f)?;
                write!(f, "{}{}", ctx.ws(), elem)?;
            }
            writeln!(f)?;
            write!(f, "{}", ctx.decrement().ws())
        } else {
            write!(f, "{}", SepBy(vec.iter().map(String::as_str), ", ", *ctx))
        }
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

enum Chain<'ast, 'src, K: AstKind> {
    Member(&'src str),
    Call(&'src str, &'ast [K::Inner<Expr<'src, K>>]),
    Index(&'ast Expr<'src, K>),
}

fn format_member<K: AstKind>(
    expr: &Expr<'_, K>,
    f: &mut fmt::Formatter<'_>,
    ctx: FormatCtx<'_>,
) -> fmt::Result {
    let mut cur = expr;
    let mut chain = vec![];
    loop {
        match cur {
            Expr::Member { expr, member } => {
                cur = (**expr).as_val();
                chain.push(Chain::Member(member));
            }
            Expr::Index { expr, index } => {
                cur = (**expr).as_val();
                chain.push(Chain::Index((**index).as_val()));
            }
            Expr::Call { expr, args } => {
                if let Expr::Member { expr, member } = (**expr).as_val() {
                    cur = (**expr).as_val();
                    chain.push(Chain::Call(member, &args[..]));
                } else {
                    break;
                }
            }
            _ => break,
        };
    }

    let break_line = chain
        .iter()
        .filter(|i| matches!(i, Chain::Member(..) | Chain::Call(..)))
        .count()
        > usize::from(ctx.settings.max_chain);

    write!(f, "{}", cur.as_fmt(ctx.with_parent_op(ParentOp::TopPrec)))?;
    let ctx = ctx.bump(1);
    for i in chain.into_iter().rev() {
        match i {
            Chain::Member(member) => {
                if break_line {
                    writeln!(f)?;
                    write!(f, "{}", ctx.ws())?
                }
                write!(f, ".{}", member)?
            }
            Chain::Call(member, args) => {
                if break_line {
                    writeln!(f)?;
                    write!(f, "{}", ctx.ws())?
                }
                write!(
                    f,
                    ".{}({})",
                    member,
                    SepBy(args.iter().map(Wrapper::as_val), ", ", ctx)
                )?
            }
            Chain::Index(index) => write!(f, "[{}]", index.as_fmt(ctx))?,
        }
    }
    Ok(())
}

fn format_items<'a, 'c: 'a, K: AstKind + 'a>(
    items: impl IntoIterator<Item = &'a ItemDecl<'c, K>>,
    f: &mut fmt::Formatter<'_>,
    ctx: FormatCtx<'_>,
) -> fmt::Result {
    let mut it = items.into_iter();
    let Some(first) = it.next() else {
        return Ok(());
    };
    let mut discriminant = mem::discriminant(&first.item);
    write!(f, "{}", first.as_fmt(ctx))?;

    for decl in it {
        let decl = decl.as_val();
        if !matches!(decl.item, Item::Import(_) | Item::Let(_))
            || discriminant != mem::discriminant(&decl.item)
        {
            writeln!(f)?;
        }
        discriminant = mem::discriminant(&decl.item);
        write!(f, "{}", decl.as_fmt(ctx))?;
    }

    Ok(())
}

fn format_stmts<'a, 'c: 'a, K: AstKind + 'a>(
    stmts: impl IntoIterator<Item = &'a Stmt<'c, K>>,
    f: &mut fmt::Formatter<'_>,
    ctx: FormatCtx<'_>,
) -> fmt::Result {
    let mut it = stmts.into_iter();
    let Some(first) = it.next() else {
        return Ok(());
    };
    writeln!(f, "{}", first.as_fmt(ctx))?;

    for stmt in it {
        if matches!(
            stmt,
            Stmt::Switch { .. } | Stmt::While { .. } | Stmt::ForIn { .. } | Stmt::Return(_)
        ) {
            writeln!(f)?;
        }
        writeln!(f, "{}", stmt.as_fmt(ctx))?;
    }

    Ok(())
}

#[derive(Debug, Clone, Copy)]
enum ParentOp {
    Unary,
    BinaryLhs(BinOp),
    BinaryRhs(BinOp),
    TopPrec,
}
