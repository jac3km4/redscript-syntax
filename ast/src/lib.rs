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

pub type SourceAggregate<'src> = Aggregate<'src, WithSpan>;
pub type SourceAnnotation<'src> = Annotation<'src, WithSpan>;
pub type SourceBlock<'src> = Block<'src, WithSpan>;
pub type SourceConditionalBlock<'src> = ConditionalBlock<'src, WithSpan>;
pub type SourceCase<'src> = Case<'src, WithSpan>;
pub type SourceEnum<'src> = Enum<'src, WithSpan>;
pub type SourceExpr<'src> = Expr<'src, WithSpan>;
pub type SourceField<'src> = Field<'src, WithSpan>;
pub type SourceFunction<'src> = Function<'src, WithSpan>;
pub type SourceItem<'src> = Item<'src, WithSpan>;
pub type SourceItemDecl<'src> = ItemDecl<'src, WithSpan>;
pub type SourceModule<'src> = Module<'src, WithSpan>;
pub type SourceParam<'src> = Param<'src, WithSpan>;
pub type SourceStmt<'src> = Stmt<'src, WithSpan>;
pub type SourceTypeParam<'src> = TypeParam<'src, WithSpan>;
pub type SourceFunctionBody<'src> = FunctionBody<'src, WithSpan>;
