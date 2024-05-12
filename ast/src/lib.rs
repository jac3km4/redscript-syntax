mod ast;
mod files;
mod span;

use ast::WithSpan;
pub use ast::{
    Aggregate, Annotation, Assoc, AstKind, BinOp, Block, Case, ConditionalBlock, Constant, Enum,
    EnumVariant, Expr, Field, Function, FunctionBody, Import, Item, ItemDecl, ItemQualifiers,
    Module, Param, ParamQualifiers, Path, Stmt, StrPart, Type, TypeParam, UnOp, Variance,
    Visibility, Wrapper,
};
pub use files::{File, SourceMap};
pub use span::{FileId, Span};

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
pub type SpannedTypeParam<'src> = TypeParam<'src, WithSpan>;
