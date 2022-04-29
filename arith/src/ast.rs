use std::rc::Rc;

pub type TermRef = Rc<Term>;

#[derive(PartialEq, Eq, Debug)]
pub enum Term {
    True,
    False,
    Zero,
    IfThenElse {
        cond: TermRef,
        positive: TermRef,
        negative: TermRef,
    },
    Succ(TermRef),
    Pred(TermRef),
    IsZero(TermRef),
}
