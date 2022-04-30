use std::rc::Rc;

pub type TermRef = Rc<Term>;

#[derive(PartialEq, Eq, Debug)]
pub enum Term {
    /// `x`
    Var(String),
    /// `lambda x. t`
    Abs(String, TermRef),
    /// `t t`
    Apply(TermRef, TermRef),
}
