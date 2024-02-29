use std::{borrow::Cow, fmt};

use bitflags::bitflags;
use derive_where::derive_where;

use crate::Spanned;

type AnnotationT<'src, A> = <A as AstKind>::Inner<Annotation<'src, A>>;
type ExprT<'src, A> = <A as AstKind>::Inner<Expr<'src, A>>;
type ItemDeclT<'src, A> = <A as AstKind>::Inner<ItemDecl<'src, A>>;
type ParamT<'src, A> = <A as AstKind>::Inner<Param<'src, A>>;
type StmtT<'src, A> = <A as AstKind>::Inner<Stmt<'src, A>>;
type TypeT<'src, A> = <A as AstKind>::Inner<Type<'src>>;

#[derive_where(Debug, PartialEq)]
pub struct Module<'src, K: AstKind = Identity> {
    pub path: Option<Path<'src>>,
    pub items: Box<[ItemDeclT<'src, K>]>,
}

impl<'src, K: AstKind> Module<'src, K> {
    pub fn new(path: Option<Path<'src>>, items: impl Into<Box<[ItemDeclT<'src, K>]>>) -> Self {
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
pub struct ItemDecl<'src, K: AstKind = Identity> {
    pub annotations: Box<[AnnotationT<'src, K>]>,
    pub visibility: Option<Visibility>,
    pub qualifiers: ItemQualifiers,
    pub item: Item<'src, K>,
}

impl<'src, K: AstKind> ItemDecl<'src, K> {
    pub fn new(
        annotations: impl Into<Box<[AnnotationT<'src, K>]>>,
        visibility: Option<Visibility>,
        qualifiers: ItemQualifiers,
        item: Item<'src, K>,
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
pub enum Item<'src, K: AstKind = Identity> {
    Import(Import<'src>),
    Class(Aggregate<'src, K>),
    Struct(Aggregate<'src, K>),
    Function(Function<'src, K>),
    Let(Field<'src, K>),
    Enum(Enum<'src, K>),
}

impl<'src, K: AstKind> Item<'src, K> {
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
pub struct Aggregate<'src, K: AstKind = Identity> {
    pub name: &'src str,
    pub extends: Option<&'src str>,
    pub items: Box<[ItemDeclT<'src, K>]>,
}

impl<'src, K: AstKind> Aggregate<'src, K> {
    pub fn new(
        name: &'src str,
        extends: Option<&'src str>,
        items: impl Into<Box<[ItemDeclT<'src, K>]>>,
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
pub struct Field<'src, K: AstKind = Identity> {
    pub name: &'src str,
    pub ty: TypeT<'src, K>,
    pub default: Option<ExprT<'src, K>>,
}

impl<'src, K: AstKind> Field<'src, K> {
    pub fn new(name: &'src str, ty: TypeT<'src, K>, default: Option<ExprT<'src, K>>) -> Self {
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
pub struct Function<'src, K: AstKind = Identity> {
    pub name: &'src str,
    pub params: Box<[ParamT<'src, K>]>,
    pub return_ty: Option<TypeT<'src, K>>,
    pub body: Option<FunctionBody<'src, K>>,
}

impl<'src, K: AstKind> Function<'src, K> {
    pub fn new(
        name: &'src str,
        params: impl Into<Box<[ParamT<'src, K>]>>,
        return_ty: Option<TypeT<'src, K>>,
        body: Option<FunctionBody<'src, K>>,
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
pub enum FunctionBody<'src, K: AstKind = Identity> {
    Block(Block<'src, K>),
    Inline(Box<ExprT<'src, K>>),
}

impl<'src, K: AstKind> FunctionBody<'src, K> {
    pub fn unwrapped(self) -> FunctionBody<'src> {
        match self {
            FunctionBody::Block(b) => FunctionBody::Block(b.into_val().unwrapped()),
            FunctionBody::Inline(e) => FunctionBody::Inline((*e).into_val().unwrapped().into()),
        }
    }
}

#[derive_where(Debug, PartialEq)]
pub struct Enum<'src, K: AstKind = Identity> {
    pub name: &'src str,
    pub variants: Box<[K::Inner<EnumVariant<'src>>]>,
}

impl<'src, K: AstKind> Enum<'src, K> {
    pub fn new(name: &'src str, variants: impl Into<Box<[K::Inner<EnumVariant<'src>>]>>) -> Self {
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
pub struct Annotation<'src, K: AstKind = Identity> {
    pub name: &'src str,
    pub args: Box<[ExprT<'src, K>]>,
}

impl<'src, K: AstKind> Annotation<'src, K> {
    pub fn new(name: &'src str, args: impl Into<Box<[ExprT<'src, K>]>>) -> Self {
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
pub struct Param<'src, K: AstKind = Identity> {
    pub name: &'src str,
    pub ty: TypeT<'src, K>,
    pub qualifiers: ParamQualifiers,
}

impl<'src, K: AstKind> Param<'src, K> {
    pub fn new(name: &'src str, ty: TypeT<'src, K>, qualifiers: ParamQualifiers) -> Self {
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
pub struct Block<'src, K: AstKind = Identity> {
    pub stmts: Box<[StmtT<'src, K>]>,
}

impl<'src, K: AstKind> Block<'src, K> {
    pub fn new(stmts: impl Into<Box<[StmtT<'src, K>]>>) -> Self {
        Self {
            stmts: stmts.into(),
        }
    }

    pub fn single(stmt: StmtT<'src, K>) -> Self {
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
pub enum Stmt<'src, K: AstKind = Identity> {
    Let {
        name: &'src str,
        ty: Option<TypeT<'src, K>>,
        value: Option<Box<ExprT<'src, K>>>,
    },
    Switch {
        expr: Box<ExprT<'src, K>>,
        cases: Box<[Case<'src, K>]>,
        default: Option<Box<[StmtT<'src, K>]>>,
    },
    If {
        blocks: Box<[ConditionalBlock<'src, K>]>,
        else_: Option<Block<'src, K>>,
    },
    While(ConditionalBlock<'src, K>),
    ForIn {
        name: &'src str,
        iter: Box<ExprT<'src, K>>,
        body: Block<'src, K>,
    },
    Return(Option<Box<ExprT<'src, K>>>),
    Break,
    Expr(Box<ExprT<'src, K>>),
}

impl<'src, K: AstKind> Stmt<'src, K> {
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
            Stmt::If { blocks, else_ } => Stmt::If {
                blocks: blocks
                    .into_vec()
                    .into_iter()
                    .map(|b| b.into_val().unwrapped())
                    .collect(),
                else_: else_.map(|b| b.into_val().unwrapped()),
            },
            Stmt::While(block) => Stmt::While(block.into_val().unwrapped()),
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
pub struct ConditionalBlock<'src, K: AstKind = Identity> {
    pub cond: ExprT<'src, K>,
    pub body: Block<'src, K>,
}

impl<'src, K: AstKind> ConditionalBlock<'src, K> {
    pub fn new(cond: ExprT<'src, K>, body: Block<'src, K>) -> Self {
        Self { cond, body }
    }

    pub fn unwrapped(self) -> ConditionalBlock<'src> {
        ConditionalBlock {
            cond: self.cond.into_val().unwrapped(),
            body: self.body.into_val().unwrapped(),
        }
    }
}

#[derive_where(Debug, PartialEq)]
pub struct Case<'src, K: AstKind = Identity> {
    pub label: ExprT<'src, K>,
    pub body: Box<[StmtT<'src, K>]>,
}

impl<'src, K: AstKind> Case<'src, K> {
    pub fn new(label: ExprT<'src, K>, body: impl Into<Box<[StmtT<'src, K>]>>) -> Self {
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
pub enum Expr<'src, K: AstKind = Identity> {
    Ident(&'src str),
    Constant(Constant<'src>),
    ArrayLit(Box<[ExprT<'src, K>]>),
    InterpolatedString(Box<[StrPart<'src, K>]>),
    Assign {
        lhs: Box<ExprT<'src, K>>,
        rhs: Box<ExprT<'src, K>>,
    },
    BinOp {
        lhs: Box<ExprT<'src, K>>,
        op: BinOp,
        rhs: Box<ExprT<'src, K>>,
    },
    UnOp {
        op: UnOp,
        expr: Box<ExprT<'src, K>>,
    },
    Call {
        expr: Box<ExprT<'src, K>>,
        args: Box<[ExprT<'src, K>]>,
    },
    Member {
        expr: Box<ExprT<'src, K>>,
        member: &'src str,
    },
    Index {
        expr: Box<ExprT<'src, K>>,
        index: Box<ExprT<'src, K>>,
    },
    DynCast {
        expr: Box<ExprT<'src, K>>,
        ty: TypeT<'src, K>,
    },
    New {
        ty: TypeT<'src, K>,
        args: Box<[ExprT<'src, K>]>,
    },
    Conditional {
        cond: Box<ExprT<'src, K>>,
        then: Box<ExprT<'src, K>>,
        else_: Box<ExprT<'src, K>>,
    },
    This,
    Super,
    Null,

    Error,
}

impl<'src, K: AstKind> Expr<'src, K> {
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
pub enum StrPart<'src, K: AstKind = Identity> {
    Expr(ExprT<'src, K>),
    Str(Cow<'src, str>),
}

impl<'src, K: AstKind> StrPart<'src, K> {
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

pub trait AstKind {
    type Inner<A>: Wrapper<A> + fmt::Debug + PartialEq
    where
        A: fmt::Debug + PartialEq;
}

pub struct Identity;

impl AstKind for Identity {
    type Inner<A> = A
    where
        A: fmt::Debug + PartialEq;
}

pub struct WithSpan;

impl AstKind for WithSpan {
    type Inner<A> = Spanned<A>
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
