use std::rc::Rc;

pub type Nat = u64;
pub type Identifier = Rc<String>;

pub type Span = std::ops::Range<usize>;
pub fn merge_span(lhs: &Span, rhs: &Span) -> Span {
    std::ops::Range {
        start: std::cmp::min(lhs.start, rhs.start),
        end: std::cmp::max(lhs.end, rhs.end),
    }
}

#[derive(derive_more::AsRef, Clone, derive_more::Display, Debug)]
#[display(bound = "T: std::fmt::Display")]
#[display(fmt = "{value}")]
pub struct Spanned<T> {
    pub span: Span,
    #[as_ref]
    pub value: T,
}
impl<T> Spanned<T> {
    pub fn forget_span(self) -> T {
        self.value
    }
    pub fn value(&self) -> &T {
        &self.value
    }
    pub fn span(&self) -> Span {
        self.span.clone()
    }
}

pub use chumsky::error::Error as _;
pub type Error<I = String> = chumsky::error::Simple<I, Span>;
pub type Result<T, E = Error> = std::result::Result<T, E>;
