use crate::ast::{Term, TermRef};

fn is_nat_value(term: &Term) -> bool {
    match term {
        Term::Zero => true,
        Term::Succ(v) => is_nat_value(v),
        _ => false,
    }
}

pub fn reduce(term: TermRef) -> Option<TermRef> {
    use Term::*;
    Some(match term.as_ref() {
        True | False | Zero => return None,
        IfThenElse {
            cond,
            positive,
            negative,
        } => match cond.as_ref() {
            True => positive.clone(),
            False => negative.clone(),
            _ => IfThenElse {
                cond: reduce(cond.clone())?,
                positive: positive.clone(),
                negative: negative.clone(),
            }
            .into(),
        },
        Succ(t) => Succ(reduce(t.clone())?).into(),
        Pred(t) => match t.as_ref() {
            Zero => Zero.into(),
            Succ(nv) if is_nat_value(nv) => nv.clone(),
            _ => Pred(reduce(t.clone())?).into(),
        },
        IsZero(t) => match t.as_ref() {
            Zero => True.into(),
            Succ(nv) if is_nat_value(nv) => False.into(),
            _ => IsZero(reduce(t.clone())?).into(),
        },
    })
}

pub fn eval(mut term: TermRef) -> TermRef {
    while let Some(next) = reduce(term.clone()) {
        eprintln!("{next:?}");
        term = next
    }
    term
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::ast::Term::*;

    #[test]
    fn test() {
        assert_eq!(
            reduce(Pred(Succ(Pred(Zero.into()).into()).into()).into()),
            Some(Pred(Succ(Zero.into()).into()).into()),
        );
        assert_eq!(
            eval(Pred(Succ(Pred(Zero.into()).into()).into()).into()),
            Zero.into(),
        );
    }
}
