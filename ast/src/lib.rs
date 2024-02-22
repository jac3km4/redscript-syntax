use std::{borrow::Cow, fmt};

use bitflags::bitflags;
use derive_where::derive_where;

type AnnotationT<'src, A> = <A as Wrap>::Inner<Annotation<'src, A>>;
type ExprT<'src, A> = <A as Wrap>::Inner<Expr<'src, A>>;
type ItemDeclT<'src, A> = <A as Wrap>::Inner<ItemDecl<'src, A>>;
type ParamT<'src, A> = <A as Wrap>::Inner<Param<'src, A>>;
type StmtT<'src, A> = <A as Wrap>::Inner<Stmt<'src, A>>;
type TypeT<'src, A> = <A as Wrap>::Inner<Type<'src>>;

#[derive_where(Debug, PartialEq)]
pub struct Module<'src, W: Wrap = Identity> {
    pub path: Option<Path<'src>>,
    pub items: Box<[ItemDeclT<'src, W>]>,
}

impl<'src, W: Wrap> Module<'src, W> {
    pub fn new(path: Option<Path<'src>>, items: impl Into<Box<[ItemDeclT<'src, W>]>>) -> Self {
        Self {
            path,
            items: items.into(),
        }
    }

    pub fn unwrapped(self) -> Module<'src> {
        Module {
            path: self.path,
            items: self
                .items
                .into_vec()
                .into_iter()
                .map(|i| i.into_val().unwrapped())
                .collect(),
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum Import<'src> {
    Exact(Path<'src>),
    Select(Path<'src>, Box<[&'src str]>),
    All(Path<'src>),
}

#[derive_where(Debug, PartialEq)]
pub struct ItemDecl<'src, W: Wrap = Identity> {
    pub annotations: Box<[AnnotationT<'src, W>]>,
    pub visibility: Option<Visibility>,
    pub qualifiers: ItemQualifiers,
    pub item: Item<'src, W>,
}

impl<'src, W: Wrap> ItemDecl<'src, W> {
    pub fn new(
        annotations: impl Into<Box<[AnnotationT<'src, W>]>>,
        visibility: Option<Visibility>,
        qualifiers: ItemQualifiers,
        item: Item<'src, W>,
    ) -> Self {
        Self {
            annotations: annotations.into(),
            visibility,
            qualifiers,
            item,
        }
    }

    pub fn unwrapped(self) -> ItemDecl<'src> {
        ItemDecl {
            annotations: self
                .annotations
                .into_vec()
                .into_iter()
                .map(|a| a.into_val().unwrapped())
                .collect(),
            visibility: self.visibility,
            qualifiers: self.qualifiers,
            item: self.item.into_val().unwrapped(),
        }
    }
}

#[derive_where(Debug, PartialEq)]
pub enum Item<'src, W: Wrap = Identity> {
    Import(Import<'src>),
    Class(Aggregate<'src, W>),
    Struct(Aggregate<'src, W>),
    Function(Function<'src, W>),
    Let(Field<'src, W>),
    Enum(Enum<'src, W>),
}

impl<'src, W: Wrap> Item<'src, W> {
    pub fn unwrapped(self) -> Item<'src> {
        match self {
            Item::Import(i) => Item::Import(i),
            Item::Class(c) => Item::Class(c.unwrapped()),
            Item::Struct(s) => Item::Struct(s.unwrapped()),
            Item::Function(f) => Item::Function(f.unwrapped()),
            Item::Let(l) => Item::Let(l.unwrapped()),
            Item::Enum(e) => Item::Enum(e.unwrapped()),
        }
    }
}

#[derive_where(Debug, PartialEq)]
pub struct Aggregate<'src, W: Wrap = Identity> {
    pub name: &'src str,
    pub extends: Option<&'src str>,
    pub items: Box<[ItemDeclT<'src, W>]>,
}

impl<'src, W: Wrap> Aggregate<'src, W> {
    pub fn new(
        name: &'src str,
        extends: Option<&'src str>,
        items: impl Into<Box<[ItemDeclT<'src, W>]>>,
    ) -> Self {
        Self {
            name,
            extends,
            items: items.into(),
        }
    }

    pub fn unwrapped(self) -> Aggregate<'src> {
        Aggregate {
            name: self.name,
            extends: self.extends,
            items: self
                .items
                .into_vec()
                .into_iter()
                .map(|m| m.into_val().unwrapped())
                .collect(),
        }
    }
}

#[derive_where(Debug, PartialEq)]
pub struct Field<'src, W: Wrap = Identity> {
    pub name: &'src str,
    pub ty: TypeT<'src, W>,
    pub default: Option<ExprT<'src, W>>,
}

impl<'src, W: Wrap> Field<'src, W> {
    pub fn new(name: &'src str, ty: TypeT<'src, W>, default: Option<ExprT<'src, W>>) -> Self {
        Self { name, ty, default }
    }

    pub fn unwrapped(self) -> Field<'src> {
        Field {
            name: self.name,
            ty: self.ty.into_val(),
            default: self.default.map(|d| d.into_val().unwrapped()),
        }
    }
}

#[derive_where(Debug, PartialEq)]
pub struct Function<'src, W: Wrap = Identity> {
    pub name: &'src str,
    pub params: Box<[ParamT<'src, W>]>,
    pub return_ty: Option<TypeT<'src, W>>,
    pub body: Option<Block<'src, W>>,
}

impl<'src, W: Wrap> Function<'src, W> {
    pub fn new(
        name: &'src str,
        params: impl Into<Box<[ParamT<'src, W>]>>,
        return_ty: Option<TypeT<'src, W>>,
        body: Option<Block<'src, W>>,
    ) -> Self {
        Self {
            name,
            params: params.into(),
            return_ty,
            body,
        }
    }

    pub fn unwrapped(self) -> Function<'src> {
        Function {
            name: self.name,
            params: self
                .params
                .into_vec()
                .into_iter()
                .map(|p| p.into_val().unwrapped())
                .collect(),
            return_ty: self.return_ty.map(Wrapper::into_val),
            body: self.body.map(|b| b.into_val().unwrapped()),
        }
    }
}

#[derive_where(Debug, PartialEq)]
pub struct Enum<'src, W: Wrap = Identity> {
    pub name: &'src str,
    pub variants: Box<[W::Inner<EnumVariant<'src>>]>,
}

impl<'src, W: Wrap> Enum<'src, W> {
    pub fn new(name: &'src str, variants: impl Into<Box<[W::Inner<EnumVariant<'src>>]>>) -> Self {
        Self {
            name,
            variants: variants.into(),
        }
    }

    pub fn unwrapped(self) -> Enum<'src> {
        Enum {
            name: self.name,
            variants: self
                .variants
                .into_vec()
                .into_iter()
                .map(Wrapper::into_val)
                .collect(),
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct EnumVariant<'src> {
    pub name: &'src str,
    pub value: Option<i32>,
}

impl<'src> EnumVariant<'src> {
    pub fn new(name: &'src str, value: Option<i32>) -> Self {
        Self { name, value }
    }
}

#[derive_where(Debug, PartialEq)]
pub struct Annotation<'src, W: Wrap = Identity> {
    pub name: &'src str,
    pub args: Box<[ExprT<'src, W>]>,
}

impl<'src, W: Wrap> Annotation<'src, W> {
    pub fn new(name: &'src str, args: impl Into<Box<[ExprT<'src, W>]>>) -> Self {
        Self {
            name,
            args: args.into(),
        }
    }

    pub fn unwrapped(self) -> Annotation<'src> {
        Annotation {
            name: self.name,
            args: self
                .args
                .into_vec()
                .into_iter()
                .map(|a| a.into_val().unwrapped())
                .collect(),
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum Type<'src> {
    Named { name: &'src str, args: Box<[Self]> },
    Array(Box<Self>),
    StaticArray(Box<Self>, usize),
}

impl<'src> Type<'src> {
    pub fn plain(name: &'src str) -> Self {
        Self::Named {
            name,
            args: Box::new([]),
        }
    }
}

#[derive_where(Debug, PartialEq)]
pub struct Param<'src, W: Wrap = Identity> {
    pub name: &'src str,
    pub ty: TypeT<'src, W>,
    pub qualifiers: ParamQualifiers,
}

impl<'src, W: Wrap> Param<'src, W> {
    pub fn new(name: &'src str, ty: TypeT<'src, W>, qualifiers: ParamQualifiers) -> Self {
        Self {
            name,
            ty,
            qualifiers,
        }
    }

    pub fn unwrapped(self) -> Param<'src> {
        Param {
            name: self.name,
            ty: self.ty.into_val(),
            qualifiers: self.qualifiers,
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct Path<'src> {
    pub segments: Box<[&'src str]>,
}

impl<'src> Path<'src> {
    pub fn new(segments: impl Into<Box<[&'src str]>>) -> Self {
        Self {
            segments: segments.into(),
        }
    }
}

#[derive_where(Debug, PartialEq)]
pub struct Block<'src, W: Wrap = Identity> {
    pub stmts: Box<[StmtT<'src, W>]>,
}

impl<'src, W: Wrap> Block<'src, W> {
    pub fn new(stmts: impl Into<Box<[StmtT<'src, W>]>>) -> Self {
        Self {
            stmts: stmts.into(),
        }
    }

    pub fn single(stmt: StmtT<'src, W>) -> Self {
        Self {
            stmts: [stmt].into(),
        }
    }

    pub fn unwrapped(self) -> Block<'src> {
        Block {
            stmts: self
                .stmts
                .into_vec()
                .into_iter()
                .map(|s| s.into_val().unwrapped())
                .collect(),
        }
    }
}

#[derive_where(Debug, PartialEq)]
pub enum Stmt<'src, W: Wrap = Identity> {
    Let {
        name: &'src str,
        ty: Option<TypeT<'src, W>>,
        value: Option<Box<ExprT<'src, W>>>,
    },
    Switch {
        expr: Box<ExprT<'src, W>>,
        cases: Box<[Case<'src, W>]>,
        default: Option<Box<[StmtT<'src, W>]>>,
    },
    If {
        cond: Box<ExprT<'src, W>>,
        then: Block<'src, W>,
        else_: Option<Block<'src, W>>,
    },
    While {
        cond: Box<ExprT<'src, W>>,
        body: Block<'src, W>,
    },
    ForIn {
        name: &'src str,
        iter: Box<ExprT<'src, W>>,
        body: Block<'src, W>,
    },
    Return(Option<Box<ExprT<'src, W>>>),
    Break,
    Expr(Box<ExprT<'src, W>>),
}

impl<'src, W: Wrap> Stmt<'src, W> {
    pub fn unwrapped(self) -> Stmt<'src> {
        match self {
            Stmt::Let { name, ty, value } => Stmt::Let {
                name,
                ty: ty.map(Wrapper::into_val),
                value: value.map(|v| (*v).into_val().unwrapped().into()),
            },
            Stmt::Switch {
                expr,
                cases,
                default,
            } => Stmt::Switch {
                expr: (*expr).into_val().unwrapped().into(),
                cases: cases
                    .into_vec()
                    .into_iter()
                    .map(|c| c.into_val().unwrapped())
                    .collect(),
                default: default.map(|d| {
                    d.into_vec()
                        .into_iter()
                        .map(|s| s.into_val().unwrapped())
                        .collect()
                }),
            },
            Stmt::If { cond, then, else_ } => Stmt::If {
                cond: (*cond).into_val().unwrapped().into(),
                then: then.into_val().unwrapped(),
                else_: else_.map(|e| e.into_val().unwrapped()),
            },
            Stmt::While { cond, body } => Stmt::While {
                cond: (*cond).into_val().unwrapped().into(),
                body: body.into_val().unwrapped(),
            },
            Stmt::ForIn { name, iter, body } => Stmt::ForIn {
                name,
                iter: (*iter).into_val().unwrapped().into(),
                body: body.into_val().unwrapped(),
            },
            Stmt::Return(v) => Stmt::Return(v.map(|v| (*v).into_val().unwrapped().into())),
            Stmt::Break => Stmt::Break,
            Stmt::Expr(e) => Stmt::Expr((*e).into_val().unwrapped().into()),
        }
    }
}

#[derive_where(Debug, PartialEq)]
pub struct Case<'src, W: Wrap = Identity> {
    pub label: ExprT<'src, W>,
    pub body: Box<[StmtT<'src, W>]>,
}

impl<'src, W: Wrap> Case<'src, W> {
    pub fn new(label: ExprT<'src, W>, body: impl Into<Box<[StmtT<'src, W>]>>) -> Self {
        Self {
            label,
            body: body.into(),
        }
    }

    pub fn unwrapped(self) -> Case<'src> {
        Case {
            label: self.label.into_val().unwrapped(),
            body: self
                .body
                .into_vec()
                .into_iter()
                .map(|s| s.into_val().unwrapped())
                .collect(),
        }
    }
}

#[derive_where(Debug, PartialEq)]
pub enum Expr<'src, W: Wrap = Identity> {
    Ident(&'src str),
    Constant(Constant<'src>),
    ArrayLit(Box<[ExprT<'src, W>]>),
    InterpolatedString(Box<[StrPart<'src, W>]>),
    Assign {
        lhs: Box<ExprT<'src, W>>,
        rhs: Box<ExprT<'src, W>>,
    },
    BinOp {
        lhs: Box<ExprT<'src, W>>,
        op: BinOp,
        rhs: Box<ExprT<'src, W>>,
    },
    UnOp {
        op: UnOp,
        expr: Box<ExprT<'src, W>>,
    },
    Call {
        expr: Box<ExprT<'src, W>>,
        args: Box<[ExprT<'src, W>]>,
    },
    Member {
        expr: Box<ExprT<'src, W>>,
        member: &'src str,
    },
    Index {
        expr: Box<ExprT<'src, W>>,
        index: Box<ExprT<'src, W>>,
    },
    DynCast {
        expr: Box<ExprT<'src, W>>,
        ty: TypeT<'src, W>,
    },
    New {
        ty: TypeT<'src, W>,
        args: Box<[ExprT<'src, W>]>,
    },
    Conditional {
        cond: Box<ExprT<'src, W>>,
        then: Box<ExprT<'src, W>>,
        else_: Box<ExprT<'src, W>>,
    },
    This,
    Super,
    Null,

    Error,
}

impl<'src, W: Wrap> Expr<'src, W> {
    pub fn unwrapped(self) -> Expr<'src> {
        match self {
            Expr::Ident(i) => Expr::Ident(i),
            Expr::Constant(c) => Expr::Constant(c),
            Expr::ArrayLit(a) => Expr::ArrayLit(
                a.into_vec()
                    .into_iter()
                    .map(|e| e.into_val().unwrapped())
                    .collect(),
            ),
            Expr::InterpolatedString(parts) => Expr::InterpolatedString(
                parts
                    .into_vec()
                    .into_iter()
                    .map(|p| p.into_val().unwrapped())
                    .collect(),
            ),
            Expr::Assign { lhs, rhs } => Expr::Assign {
                lhs: (*lhs).into_val().unwrapped().into(),
                rhs: (*rhs).into_val().unwrapped().into(),
            },
            Expr::BinOp { lhs, op, rhs } => Expr::BinOp {
                lhs: (*lhs).into_val().unwrapped().into(),
                op,
                rhs: (*rhs).into_val().unwrapped().into(),
            },
            Expr::UnOp { op, expr } => Expr::UnOp {
                op,
                expr: (*expr).into_val().unwrapped().into(),
            },
            Expr::Call { expr: callee, args } => Expr::Call {
                expr: (*callee).into_val().unwrapped().into(),
                args: args
                    .into_vec()
                    .into_iter()
                    .map(|a| a.into_val().unwrapped())
                    .collect(),
            },
            Expr::Member { expr, member } => Expr::Member {
                expr: (*expr).into_val().unwrapped().into(),
                member,
            },
            Expr::Index { expr, index } => Expr::Index {
                expr: (*expr).into_val().unwrapped().into(),
                index: (*index).into_val().unwrapped().into(),
            },
            Expr::DynCast { expr, ty } => Expr::DynCast {
                expr: (*expr).into_val().unwrapped().into(),
                ty: ty.into_val(),
            },
            Expr::New { ty, args } => Expr::New {
                ty: ty.into_val(),
                args: args
                    .into_vec()
                    .into_iter()
                    .map(|a| a.into_val().unwrapped())
                    .collect(),
            },
            Expr::Conditional { cond, then, else_ } => Expr::Conditional {
                cond: (*cond).into_val().unwrapped().into(),
                then: (*then).into_val().unwrapped().into(),
                else_: (*else_).into_val().unwrapped().into(),
            },
            Expr::This => Expr::This,
            Expr::Super => Expr::Super,
            Expr::Null => Expr::Null,
            Expr::Error => Expr::Error,
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum Constant<'src> {
    String(Cow<'src, str>),
    CName(Cow<'src, str>),
    Resource(Cow<'src, str>),
    TweakDbId(Cow<'src, str>),
    F32(f32),
    F64(f64),
    I32(i32),
    I64(i64),
    U32(u32),
    U64(u64),
    Bool(bool),
}

#[derive_where(Debug, PartialEq)]
pub enum StrPart<'src, W: Wrap = Identity> {
    Expr(ExprT<'src, W>),
    Str(Cow<'src, str>),
}

impl<'src, W: Wrap> StrPart<'src, W> {
    pub fn unwrapped(self) -> StrPart<'src> {
        match self {
            StrPart::Expr(e) => StrPart::Expr(e.into_val().unwrapped()),
            StrPart::Str(s) => StrPart::Str(s),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnOp {
    BitNot,
    Not,
    Neg,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    AssignAdd,
    AssignSub,
    AssignMul,
    AssignDiv,
    AssignBitOr,
    AssignBitAnd,
    Or,
    And,
    BitOr,
    BitXor,
    BitAnd,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    Add,
    Sub,
    Mul,
    Div,
    Mod,
}

impl BinOp {
    pub fn precedence(self) -> u8 {
        match self {
            BinOp::AssignAdd
            | BinOp::AssignSub
            | BinOp::AssignMul
            | BinOp::AssignDiv
            | BinOp::AssignBitOr
            | BinOp::AssignBitAnd => 0,
            BinOp::Or => 1,
            BinOp::And => 2,
            BinOp::BitOr => 3,
            BinOp::BitXor => 4,
            BinOp::BitAnd => 5,
            BinOp::Eq | BinOp::Ne => 6,
            BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => 7,
            BinOp::Add | BinOp::Sub => 8,
            BinOp::Mul | BinOp::Div | BinOp::Mod => 9,
        }
    }

    pub fn assoc(self) -> Assoc {
        match self {
            BinOp::AssignAdd
            | BinOp::AssignSub
            | BinOp::AssignMul
            | BinOp::AssignDiv
            | BinOp::AssignBitOr
            | BinOp::AssignBitAnd => Assoc::Right,
            BinOp::Or
            | BinOp::And
            | BinOp::BitOr
            | BinOp::BitXor
            | BinOp::BitAnd
            | BinOp::Eq
            | BinOp::Ne
            | BinOp::Lt
            | BinOp::Le
            | BinOp::Gt
            | BinOp::Ge
            | BinOp::Add
            | BinOp::Sub
            | BinOp::Mul
            | BinOp::Div
            | BinOp::Mod => Assoc::Left,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Visibility {
    Public,
    Protected,
    Private,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Assoc {
    Left,
    Right,
}

bitflags! {
    #[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
    pub struct ItemQualifiers: u16 {
        const ABSTRACT = 1 << 0;
        const CALLBACK = 1 << 1;
        const CONST = 1 << 2;
        const EXEC = 1 << 3;
        const FINAL = 1 << 4;
        const IMPORT_ONLY = 1 << 5;
        const NATIVE = 1 << 6;
        const PERSISTENT = 1 << 7;
        const QUEST = 1 << 8;
        const STATIC = 1 << 9;
    }
}

bitflags! {
    #[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
    pub struct ParamQualifiers: u8 {
        const OPTIONAL = 1 << 0;
        const OUT = 1 << 1;
        const CONST = 1 << 2;
    }

}

pub trait Wrap {
    type Inner<A>: Wrapper<A> + fmt::Debug + PartialEq
    where
        A: fmt::Debug + PartialEq;
}

pub struct Identity;

impl Wrap for Identity {
    type Inner<A> = A
    where
        A: fmt::Debug + PartialEq;
}

pub trait Wrapper<A> {
    fn as_val(&self) -> &A;
    fn into_val(self) -> A;
}

impl<A> Wrapper<A> for A {
    #[inline]
    fn as_val(&self) -> &A {
        self
    }

    #[inline]
    fn into_val(self) -> A {
        self
    }
}

impl<A, B> Wrapper<A> for (A, B) {
    #[inline]
    fn as_val(&self) -> &A {
        &self.0
    }

    #[inline]
    fn into_val(self) -> A {
        self.0
    }
}
