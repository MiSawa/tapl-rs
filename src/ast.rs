use std::rc::Rc;

#[derive(PartialEq, Eq, Debug)]
pub enum Term {
    True,
    False,
    Zero,
    IfThenElse {
        cond: Rc<Term>,
        positive: Rc<Term>,
        negative: Rc<Term>,
    },
    Succ(Rc<Term>),
    Pred(Rc<Term>),
    IsZero(Rc<Term>),
}
