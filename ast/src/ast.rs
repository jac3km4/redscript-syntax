use std::{borrow::Cow, fmt};

use bitflags::bitflags;
use derive_where::derive_where;

use crate::{Span, Spanned};

pub(super) type AnnotationT<'src, A> = <A as AstKind>::Inner<Annotation<'src, A>>;
pub(super) type ExprT<'src, A> = <A as AstKind>::Inner<Expr<'src, A>>;
pub(super) type ItemDeclT<'src, A> = <A as AstKind>::Inner<ItemDecl<'src, A>>;
pub(super) type ParamT<'src, A> = <A as AstKind>::Inner<Param<'src, A>>;
pub(super) type StmtT<'src, A> = <A as AstKind>::Inner<Stmt<'src, A>>;
pub(super) type TypeT<'src, A> = <A as AstKind>::Inner<Type<'src, A>>;

#[derive_where(Debug, PartialEq)]
pub struct Module<'src, K: AstKind = Identity> {
    pub path: Option<Path<'src>>,
    pub items: Box<[ItemDeclT<'src, K>]>,
}

impl<'src, K: AstKind> Module<'src, K> {
    #[inline]
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
                .map(|i| i.into_wrapped().unwrapped())
                .collect(),
        }
    }
}

impl<'src> Module<'src, WithSpan> {
    pub fn find_at(&self, pos: u32) -> Option<QueryResult<'_, 'src>> {
        let idx = self
            .items
            .binary_search_by(|(_, sp)| sp.compare_pos(pos))
            .ok()?;
        let (item, _) = &self.items[idx];
        Some(item.find_at(pos))
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
    #[inline]
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
                .map(|a| a.into_wrapped().unwrapped())
                .collect(),
            visibility: self.visibility,
            qualifiers: self.qualifiers,
            item: self.item.into_wrapped().unwrapped(),
        }
    }
}

impl<'src> ItemDecl<'src, WithSpan> {
    pub fn find_at(&self, pos: u32) -> QueryResult<'_, 'src> {
        match &self.item {
            Item::Import(_) | Item::Enum(_) => return QueryResult::ItemDecl(self),
            Item::Class(c) => c.find_at(pos),
            Item::Struct(s) => s.find_at(pos),
            Item::Function(f) => {
                f.params
                    .iter()
                    .filter_map(|(p, _)| p.typ.as_ref())
                    .find_map(|(typ, span)| span.contains(pos).then_some(typ.find_at(pos)));
                f.body.as_ref().and_then(|b| b.find_at(pos))
            }
            Item::Let(l) => l.default.as_ref().and_then(|d| {
                let (d, span) = &**d;
                span.contains(pos).then_some(d.find_at(pos))
            }),
        }
        .unwrap_or(QueryResult::ItemDecl(self))
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
    pub name: K::Inner<&'src str>,
    pub type_params: Box<[TypeParam<'src, K>]>,
    pub extends: Option<Box<TypeT<'src, K>>>,
    pub items: Box<[ItemDeclT<'src, K>]>,
}

impl<'src, K: AstKind> Aggregate<'src, K> {
    #[inline]
    pub fn new(
        name: K::Inner<&'src str>,
        type_params: impl Into<Box<[TypeParam<'src, K>]>>,
        extends: Option<Box<TypeT<'src, K>>>,
        items: impl Into<Box<[ItemDeclT<'src, K>]>>,
    ) -> Self {
        Self {
            name,
            type_params: type_params.into(),
            extends,
            items: items.into(),
        }
    }

    pub fn unwrapped(self) -> Aggregate<'src> {
        Aggregate {
            name: self.name.into_wrapped(),
            type_params: self
                .type_params
                .into_vec()
                .into_iter()
                .map(|p| p.into_wrapped().unwrapped())
                .collect(),
            extends: self
                .extends
                .map(|typ| (*typ).into_wrapped().unwrapped().into()),
            items: self
                .items
                .into_vec()
                .into_iter()
                .map(|m| m.into_wrapped().unwrapped())
                .collect(),
        }
    }
}

impl<'src> Aggregate<'src, WithSpan> {
    pub fn find_at(&self, pos: u32) -> Option<QueryResult<'_, 'src>> {
        let idx = self
            .items
            .binary_search_by(|(_, sp)| sp.compare_pos(pos))
            .ok()?;
        let (item, _) = &self.items[idx];
        Some(item.find_at(pos))
    }
}

#[derive_where(Debug, PartialEq)]
pub struct Field<'src, K: AstKind = Identity> {
    pub name: K::Inner<&'src str>,
    pub typ: Box<TypeT<'src, K>>,
    pub default: Option<Box<ExprT<'src, K>>>,
}

impl<'src, K: AstKind> Field<'src, K> {
    #[inline]
    pub fn new(
        name: K::Inner<&'src str>,
        typ: Box<TypeT<'src, K>>,
        default: Option<Box<ExprT<'src, K>>>,
    ) -> Self {
        Self { name, typ, default }
    }

    pub fn unwrapped(self) -> Field<'src> {
        Field {
            name: self.name.into_wrapped(),
            typ: (*self.typ).into_wrapped().unwrapped().into(),
            default: self.default.map(|d| (*d).into_wrapped().unwrapped().into()),
        }
    }
}

#[derive_where(Debug, PartialEq)]
pub struct Function<'src, K: AstKind = Identity> {
    pub name: K::Inner<&'src str>,
    pub type_params: Box<[TypeParam<'src, K>]>,
    pub params: Box<[ParamT<'src, K>]>,
    pub return_ty: Option<Box<TypeT<'src, K>>>,
    pub body: Option<FunctionBody<'src, K>>,
}

impl<'src, K: AstKind> Function<'src, K> {
    #[inline]
    pub fn new(
        name: K::Inner<&'src str>,
        type_params: impl Into<Box<[TypeParam<'src, K>]>>,
        params: impl Into<Box<[ParamT<'src, K>]>>,
        return_ty: Option<Box<TypeT<'src, K>>>,
        body: Option<FunctionBody<'src, K>>,
    ) -> Self {
        Self {
            name,
            type_params: type_params.into(),
            params: params.into(),
            return_ty,
            body,
        }
    }

    pub fn unwrapped(self) -> Function<'src> {
        Function {
            name: self.name.into_wrapped(),
            params: self
                .params
                .into_vec()
                .into_iter()
                .map(|p| p.into_wrapped().unwrapped())
                .collect(),
            type_params: self
                .type_params
                .into_vec()
                .into_iter()
                .map(|p| p.into_wrapped().unwrapped())
                .collect(),
            return_ty: self
                .return_ty
                .map(|typ| (*typ).into_wrapped().unwrapped().into()),
            body: self.body.map(|b| b.into_wrapped().unwrapped()),
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
            FunctionBody::Block(b) => FunctionBody::Block(b.into_wrapped().unwrapped()),
            FunctionBody::Inline(e) => FunctionBody::Inline((*e).into_wrapped().unwrapped().into()),
        }
    }
}

impl<'src> FunctionBody<'src, WithSpan> {
    pub fn find_at(&self, pos: u32) -> Option<QueryResult<'_, 'src>> {
        match self {
            FunctionBody::Block(b) => b.find_at(pos),
            FunctionBody::Inline(e) => {
                let (e, span) = &**e;
                span.contains(pos).then_some(e.find_at(pos))
            }
        }
    }
}

#[derive_where(Debug, PartialEq)]
pub struct Enum<'src, K: AstKind = Identity> {
    pub name: K::Inner<&'src str>,
    pub variants: Box<[K::Inner<EnumVariant<'src>>]>,
}

impl<'src, K: AstKind> Enum<'src, K> {
    #[inline]
    pub fn new(
        name: K::Inner<&'src str>,
        variants: impl Into<Box<[K::Inner<EnumVariant<'src>>]>>,
    ) -> Self {
        Self {
            name,
            variants: variants.into(),
        }
    }

    pub fn unwrapped(self) -> Enum<'src> {
        Enum {
            name: self.name.into_wrapped(),
            variants: self
                .variants
                .into_vec()
                .into_iter()
                .map(Wrapper::into_wrapped)
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
    #[inline]
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
    #[inline]
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
                .map(|a| a.into_wrapped().unwrapped())
                .collect(),
        }
    }
}

#[derive_where(Debug, PartialEq)]
pub enum Type<'src, K: AstKind = Identity> {
    Named {
        name: &'src str,
        args: Box<[K::Inner<Self>]>,
    },
    Array(Box<K::Inner<Self>>),
    StaticArray(Box<K::Inner<Self>>, usize),
}

impl<'src, K: AstKind> Type<'src, K> {
    #[inline]
    pub fn plain(name: &'src str) -> Self {
        Self::Named {
            name,
            args: Box::new([]),
        }
    }

    pub fn unwrapped(self) -> Type<'src> {
        match self {
            Type::Named { name, args } => Type::Named {
                name,
                args: args
                    .into_vec()
                    .into_iter()
                    .map(|a| a.into_wrapped().unwrapped())
                    .collect(),
            },
            Type::Array(t) => Type::Array((*t).into_wrapped().unwrapped().into()),
            Type::StaticArray(t, size) => {
                Type::StaticArray((*t).into_wrapped().unwrapped().into(), size)
            }
        }
    }
}

impl<'src> Type<'src, WithSpan> {
    pub fn find_at(&self, pos: u32) -> QueryResult<'_, 'src> {
        match self {
            Type::Named { args, .. } => args
                .iter()
                .find_map(|(typ, span)| span.contains(pos).then_some(typ.find_at(pos)))
                .unwrap_or(QueryResult::Type(self)),
            Type::Array(typ) | Type::StaticArray(typ, _) => {
                let (typ, span) = &**typ;
                if span.contains(pos) {
                    return typ.find_at(pos);
                }
                QueryResult::Type(self)
            }
        }
    }
}

#[derive_where(Debug, PartialEq)]
pub struct TypeParam<'src, K: AstKind = Identity> {
    pub variance: Variance,
    pub name: K::Inner<&'src str>,
    pub upper_bound: Option<Box<TypeT<'src, K>>>,
}

impl<'src, K: AstKind> TypeParam<'src, K> {
    #[inline]
    pub fn new(
        variance: Variance,
        name: K::Inner<&'src str>,
        upper_bound: Option<Box<TypeT<'src, K>>>,
    ) -> Self {
        Self {
            variance,
            name,
            upper_bound,
        }
    }

    pub fn unwrapped(self) -> TypeParam<'src> {
        TypeParam {
            variance: self.variance,
            name: self.name.into_wrapped(),
            upper_bound: self
                .upper_bound
                .map(|typ| (*typ).into_wrapped().unwrapped().into()),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Variance {
    Covariant,
    Contravariant,
    Invariant,
}

#[derive_where(Debug, PartialEq)]
pub struct Param<'src, K: AstKind = Identity> {
    pub name: &'src str,
    pub typ: Option<TypeT<'src, K>>,
    pub qualifiers: ParamQualifiers,
}

impl<'src, K: AstKind> Param<'src, K> {
    #[inline]
    pub fn new(name: &'src str, typ: Option<TypeT<'src, K>>, qualifiers: ParamQualifiers) -> Self {
        Self {
            name,
            typ,
            qualifiers,
        }
    }

    pub fn unwrapped(self) -> Param<'src> {
        Param {
            name: self.name,
            typ: self.typ.map(|t| t.into_wrapped().unwrapped()),
            qualifiers: self.qualifiers,
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct Path<'src> {
    pub segments: Box<[&'src str]>,
}

impl<'src> Path<'src> {
    #[inline]
    pub fn new(segments: impl Into<Box<[&'src str]>>) -> Self {
        Self {
            segments: segments.into(),
        }
    }
}

impl<'stc> AsRef<[&'stc str]> for Path<'stc> {
    #[inline]
    fn as_ref(&self) -> &[&'stc str] {
        &self.segments
    }
}

#[derive_where(Debug, PartialEq)]
pub struct Block<'src, K: AstKind = Identity> {
    pub stmts: Box<[StmtT<'src, K>]>,
}

impl<'src, K: AstKind> Block<'src, K> {
    #[inline]
    pub fn new(stmts: impl Into<Box<[StmtT<'src, K>]>>) -> Self {
        Self {
            stmts: stmts.into(),
        }
    }

    #[inline]
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
                .map(|s| s.into_wrapped().unwrapped())
                .collect(),
        }
    }
}

impl<'src> Block<'src, WithSpan> {
    pub fn find_at(&self, pos: u32) -> Option<QueryResult<'_, 'src>> {
        let idx = self
            .stmts
            .binary_search_by(|(_, sp)| sp.compare_pos(pos))
            .ok()?;
        let (stmt, _) = &self.stmts[idx];
        Some(stmt.find_at(pos))
    }

    pub fn bounds_span(&self) -> Option<Span> {
        let (_, fst) = self.stmts.first()?;
        let (_, lst) = self.stmts.last()?;
        Some(fst.merge(lst))
    }
}

#[derive_where(Debug, PartialEq)]
pub enum Stmt<'src, K: AstKind = Identity> {
    Let {
        name: K::Inner<&'src str>,
        typ: Option<Box<TypeT<'src, K>>>,
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
    While(Box<ConditionalBlock<'src, K>>),
    ForIn {
        name: K::Inner<&'src str>,
        iter: Box<ExprT<'src, K>>,
        body: Block<'src, K>,
    },
    Return(Option<Box<ExprT<'src, K>>>),
    Break,
    Continue,
    Expr(Box<ExprT<'src, K>>),
}

impl<'src, K: AstKind> Stmt<'src, K> {
    pub fn unwrapped(self) -> Stmt<'src> {
        match self {
            Stmt::Let { name, typ, value } => Stmt::Let {
                name: name.into_wrapped(),
                typ: typ.map(|typ| (*typ).into_wrapped().unwrapped().into()),
                value: value.map(|v| (*v).into_wrapped().unwrapped().into()),
            },
            Stmt::Switch {
                expr,
                cases,
                default,
            } => Stmt::Switch {
                expr: (*expr).into_wrapped().unwrapped().into(),
                cases: cases
                    .into_vec()
                    .into_iter()
                    .map(|c| c.into_wrapped().unwrapped())
                    .collect(),
                default: default.map(|d| {
                    d.into_vec()
                        .into_iter()
                        .map(|s| s.into_wrapped().unwrapped())
                        .collect()
                }),
            },
            Stmt::If { blocks, else_ } => Stmt::If {
                blocks: blocks
                    .into_vec()
                    .into_iter()
                    .map(|b| b.into_wrapped().unwrapped())
                    .collect(),
                else_: else_.map(|b| b.into_wrapped().unwrapped()),
            },
            Stmt::While(block) => Stmt::While(block.into_wrapped().unwrapped().into()),
            Stmt::ForIn { name, iter, body } => Stmt::ForIn {
                name: name.into_wrapped(),
                iter: (*iter).into_wrapped().unwrapped().into(),
                body: body.into_wrapped().unwrapped(),
            },
            Stmt::Return(v) => Stmt::Return(v.map(|v| (*v).into_wrapped().unwrapped().into())),
            Stmt::Break => Stmt::Break,
            Stmt::Continue => Stmt::Continue,
            Stmt::Expr(e) => Stmt::Expr((*e).into_wrapped().unwrapped().into()),
        }
    }
}

impl<'src> Stmt<'src, WithSpan> {
    pub fn find_at(&self, pos: u32) -> QueryResult<'_, 'src> {
        let res = match self {
            Stmt::Break | Stmt::Continue => return QueryResult::Stmt(self),
            Stmt::Let { value, typ, .. } => {
                if let Some(typ) = typ {
                    let (typ, typ_span) = &**typ;
                    if typ_span.contains(pos) {
                        return typ.find_at(pos);
                    }
                }
                value.as_ref().and_then(|v| {
                    let (v, span) = &**v;
                    span.contains(pos).then_some(v.find_at(pos))
                })
            }
            Stmt::Switch {
                expr,
                cases,
                default,
            } => {
                let (expr, span) = &**expr;
                if span.contains(pos) {
                    return expr.find_at(pos);
                }
                if let Some(res) = cases.iter().find_map(|c| c.find_at(pos)) {
                    return res;
                }
                default.as_deref().and_then(|d| {
                    d.iter()
                        .find_map(|(s, span)| span.contains(pos).then_some(s.find_at(pos)))
                })
            }
            Stmt::If { blocks, else_ } => blocks
                .iter()
                .find_map(|b| b.find_at(pos))
                .or_else(|| else_.as_ref().and_then(|e| e.find_at(pos))),
            Stmt::While(block) => block.find_at(pos),
            Stmt::ForIn { iter, body, .. } => {
                let (iter, iter_span) = &**iter;
                if iter_span.contains(pos) {
                    return iter.find_at(pos);
                }
                body.find_at(pos)
            }
            Stmt::Return(v) => v.as_ref().and_then(|v| {
                let (v, span) = &**v;
                span.contains(pos).then_some(v.find_at(pos))
            }),
            Stmt::Expr(e) => {
                let (e, span) = &**e;
                if span.contains(pos) {
                    return e.find_at(pos);
                }
                return QueryResult::Stmt(self);
            }
        };
        res.unwrap_or(QueryResult::Stmt(self))
    }
}

#[derive_where(Debug, PartialEq)]
pub struct ConditionalBlock<'src, K: AstKind = Identity> {
    pub cond: ExprT<'src, K>,
    pub body: Block<'src, K>,
}

impl<'src, K: AstKind> ConditionalBlock<'src, K> {
    #[inline]
    pub fn new(cond: ExprT<'src, K>, body: Block<'src, K>) -> Self {
        Self { cond, body }
    }

    pub fn unwrapped(self) -> ConditionalBlock<'src> {
        ConditionalBlock {
            cond: self.cond.into_wrapped().unwrapped(),
            body: self.body.into_wrapped().unwrapped(),
        }
    }
}

impl<'src> ConditionalBlock<'src, WithSpan> {
    pub fn find_at(&self, pos: u32) -> Option<QueryResult<'_, 'src>> {
        let (cond, span) = &self.cond;
        if span.contains(pos) {
            return Some(cond.find_at(pos));
        }
        self.body.find_at(pos)
    }
}

#[derive_where(Debug, PartialEq)]
pub struct Case<'src, K: AstKind = Identity> {
    pub label: ExprT<'src, K>,
    pub body: Box<[StmtT<'src, K>]>,
}

impl<'src, K: AstKind> Case<'src, K> {
    #[inline]
    pub fn new(label: ExprT<'src, K>, body: impl Into<Box<[StmtT<'src, K>]>>) -> Self {
        Self {
            label,
            body: body.into(),
        }
    }

    pub fn unwrapped(self) -> Case<'src> {
        Case {
            label: self.label.into_wrapped().unwrapped(),
            body: self
                .body
                .into_vec()
                .into_iter()
                .map(|s| s.into_wrapped().unwrapped())
                .collect(),
        }
    }
}

impl<'src> Case<'src, WithSpan> {
    pub fn find_at(&self, pos: u32) -> Option<QueryResult<'_, 'src>> {
        let (label, span) = &self.label;
        if span.contains(pos) {
            return Some(label.find_at(pos));
        }
        self.body
            .iter()
            .find_map(|(s, span)| span.contains(pos).then_some(s.find_at(pos)))
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
        type_args: Box<[TypeT<'src, K>]>,
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
        typ: Box<TypeT<'src, K>>,
    },
    New {
        typ: Box<TypeT<'src, K>>,
        args: Box<[ExprT<'src, K>]>,
    },
    Conditional {
        cond: Box<ExprT<'src, K>>,
        then: Box<ExprT<'src, K>>,
        else_: Box<ExprT<'src, K>>,
    },
    Lambda {
        params: Box<[ParamT<'src, K>]>,
        body: FunctionBody<'src, K>,
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
                    .map(|e| e.into_wrapped().unwrapped())
                    .collect(),
            ),
            Expr::InterpolatedString(parts) => Expr::InterpolatedString(
                parts
                    .into_vec()
                    .into_iter()
                    .map(|p| p.into_wrapped().unwrapped())
                    .collect(),
            ),
            Expr::Assign { lhs, rhs } => Expr::Assign {
                lhs: (*lhs).into_wrapped().unwrapped().into(),
                rhs: (*rhs).into_wrapped().unwrapped().into(),
            },
            Expr::BinOp { lhs, op, rhs } => Expr::BinOp {
                lhs: (*lhs).into_wrapped().unwrapped().into(),
                op,
                rhs: (*rhs).into_wrapped().unwrapped().into(),
            },
            Expr::UnOp { op, expr } => Expr::UnOp {
                op,
                expr: (*expr).into_wrapped().unwrapped().into(),
            },
            Expr::Call {
                expr,
                type_args,
                args,
            } => Expr::Call {
                expr: (*expr).into_wrapped().unwrapped().into(),
                type_args: type_args
                    .into_vec()
                    .into_iter()
                    .map(|t| t.into_wrapped().unwrapped())
                    .collect(),
                args: args
                    .into_vec()
                    .into_iter()
                    .map(|a| a.into_wrapped().unwrapped())
                    .collect(),
            },
            Expr::Member { expr, member } => Expr::Member {
                expr: (*expr).into_wrapped().unwrapped().into(),
                member,
            },
            Expr::Index { expr, index } => Expr::Index {
                expr: (*expr).into_wrapped().unwrapped().into(),
                index: (*index).into_wrapped().unwrapped().into(),
            },
            Expr::DynCast { expr, typ } => Expr::DynCast {
                expr: (*expr).into_wrapped().unwrapped().into(),
                typ: (*typ).into_wrapped().unwrapped().into(),
            },
            Expr::New { typ, args } => Expr::New {
                typ: (*typ).into_wrapped().unwrapped().into(),
                args: args
                    .into_vec()
                    .into_iter()
                    .map(|a| a.into_wrapped().unwrapped())
                    .collect(),
            },
            Expr::Conditional { cond, then, else_ } => Expr::Conditional {
                cond: (*cond).into_wrapped().unwrapped().into(),
                then: (*then).into_wrapped().unwrapped().into(),
                else_: (*else_).into_wrapped().unwrapped().into(),
            },
            Expr::Lambda { params, body } => Expr::Lambda {
                params: params
                    .into_vec()
                    .into_iter()
                    .map(|p| p.into_wrapped().unwrapped())
                    .collect(),
                body: body.into_wrapped().unwrapped(),
            },
            Expr::This => Expr::This,
            Expr::Super => Expr::Super,
            Expr::Null => Expr::Null,
            Expr::Error => Expr::Error,
        }
    }
}

impl<'src> Expr<'src, WithSpan> {
    pub fn find_at(&self, pos: u32) -> QueryResult<'_, 'src> {
        match self {
            Expr::Ident(_)
            | Expr::Constant(_)
            | Expr::This
            | Expr::Super
            | Expr::Null
            | Expr::Error => QueryResult::Expr(self),
            Expr::ArrayLit(e) => e
                .iter()
                .find_map(|(e, s)| s.contains(pos).then_some(e.find_at(pos)))
                .unwrap_or(QueryResult::Expr(self)),
            Expr::InterpolatedString(parts) => parts
                .iter()
                .find_map(|p| match p {
                    StrPart::Expr((e, s)) if s.contains(pos) => Some(e.find_at(pos)),
                    _ => None,
                })
                .unwrap_or(QueryResult::Expr(self)),
            Expr::BinOp { lhs, rhs, .. }
            | Expr::Assign { lhs, rhs }
            | Expr::Index {
                expr: lhs,
                index: rhs,
            } => {
                let (lhs, lhs_span) = &**lhs;
                let (rhs, rhs_span) = &**rhs;
                if lhs_span.contains(pos) {
                    lhs.find_at(pos)
                } else if rhs_span.contains(pos) {
                    rhs.find_at(pos)
                } else {
                    QueryResult::Expr(self)
                }
            }
            Expr::UnOp { expr, .. } | Expr::Member { expr, .. } => {
                let (expr, span) = &**expr;
                if span.contains(pos) {
                    expr.find_at(pos)
                } else {
                    QueryResult::Expr(self)
                }
            }
            Expr::Call {
                expr,
                type_args,
                args,
            } => {
                let (expr, span) = &**expr;
                if span.contains(pos) {
                    expr.find_at(pos)
                } else {
                    type_args
                        .iter()
                        .find_map(|(typ, s)| s.contains(pos).then_some(typ.find_at(pos)))
                        .or_else(|| {
                            args.iter()
                                .find_map(|(a, s)| s.contains(pos).then_some(a.find_at(pos)))
                        })
                        .unwrap_or(QueryResult::Expr(self))
                }
            }
            Expr::DynCast { expr, typ, .. } => {
                let (expr, span) = &**expr;
                let (typ, typ_span) = &**typ;
                if span.contains(pos) {
                    expr.find_at(pos)
                } else if typ_span.contains(pos) {
                    typ.find_at(pos)
                } else {
                    QueryResult::Expr(self)
                }
            }
            Expr::New { typ, args } => {
                let (typ, typ_span) = &**typ;
                if typ_span.contains(pos) {
                    typ.find_at(pos)
                } else {
                    args.iter()
                        .find_map(|(a, s)| s.contains(pos).then_some(a.find_at(pos)))
                        .unwrap_or(QueryResult::Expr(self))
                }
            }
            Expr::Conditional { cond, then, else_ } => {
                let (cond, span) = &**cond;
                let (then, then_span) = &**then;
                let (else_, else_span) = &**else_;

                if span.contains(pos) {
                    cond.find_at(pos)
                } else if then_span.contains(pos) {
                    then.find_at(pos)
                } else if else_span.contains(pos) {
                    else_.find_at(pos)
                } else {
                    QueryResult::Expr(self)
                }
            }
            Expr::Lambda { body, .. } => body.find_at(pos).unwrap_or(QueryResult::Expr(self)),
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
            StrPart::Expr(e) => StrPart::Expr(e.into_wrapped().unwrapped()),
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
            Self::AssignAdd
            | Self::AssignSub
            | Self::AssignMul
            | Self::AssignDiv
            | Self::AssignBitOr
            | Self::AssignBitAnd => 0,
            Self::Or => 1,
            Self::And => 2,
            Self::BitOr => 3,
            Self::BitXor => 4,
            Self::BitAnd => 5,
            Self::Eq | Self::Ne => 6,
            Self::Lt | Self::Le | Self::Gt | Self::Ge => 7,
            Self::Add | Self::Sub => 8,
            Self::Mul | Self::Div | Self::Mod => 9,
        }
    }

    pub fn assoc(self) -> Assoc {
        match self {
            Self::AssignAdd
            | Self::AssignSub
            | Self::AssignMul
            | Self::AssignDiv
            | Self::AssignBitOr
            | Self::AssignBitAnd => Assoc::Right,
            Self::Or
            | Self::And
            | Self::BitOr
            | Self::BitXor
            | Self::BitAnd
            | Self::Eq
            | Self::Ne
            | Self::Lt
            | Self::Le
            | Self::Gt
            | Self::Ge
            | Self::Add
            | Self::Sub
            | Self::Mul
            | Self::Div
            | Self::Mod => Assoc::Left,
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
    type Inner<A>
        = A
    where
        A: fmt::Debug + PartialEq;
}

pub struct WithSpan;

impl AstKind for WithSpan {
    type Inner<A>
        = Spanned<A>
    where
        A: fmt::Debug + PartialEq;
}

pub trait Wrapper<A> {
    fn as_wrapped(&self) -> &A;
    fn into_wrapped(self) -> A;
}

impl<A> Wrapper<A> for A {
    #[inline]
    fn as_wrapped(&self) -> &A {
        self
    }

    #[inline]
    fn into_wrapped(self) -> A {
        self
    }
}

impl<A, B> Wrapper<A> for (A, B) {
    #[inline]
    fn as_wrapped(&self) -> &A {
        &self.0
    }

    #[inline]
    fn into_wrapped(self) -> A {
        self.0
    }
}

pub enum QueryResult<'a, 'src> {
    ItemDecl(&'a ItemDecl<'src, WithSpan>),
    Stmt(&'a Stmt<'src, WithSpan>),
    Expr(&'a Expr<'src, WithSpan>),
    Type(&'a Type<'src, WithSpan>),
}

#[cfg(test)]
mod tests {
    use std::mem;

    use super::*;

    #[test]
    fn sizes() {
        assert_eq!(mem::size_of::<Expr<'_>>(), 48);
        assert_eq!(mem::size_of::<Stmt<'_>>(), 48);
        assert_eq!(mem::size_of::<Item<'_>>(), 80);
    }
}
