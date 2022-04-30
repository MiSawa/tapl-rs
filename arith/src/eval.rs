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

fn eval_small(mut term: TermRef) -> TermRef {
    while let Some(next) = reduce(term.clone()) {
        term = next
    }
    term
}

fn eval_big(term: TermRef) -> Option<TermRef> {
    use Term::*;
    Some(match term.as_ref() {
        True | False | Zero => term.clone(),
        IfThenElse {
            cond,
            positive,
            negative,
        } => match eval_big(cond.clone())?.as_ref() {
            True => eval_big(positive.clone())?,
            False => eval_big(negative.clone())?,
            _ => return None,
        },
        Succ(t) => {
            let v = eval_big(t.clone())?;
            is_nat_value(&v).then(|| Succ(v.clone()).into())?
        }
        Pred(t) => {
            let v = eval_big(t.clone())?;
            match v.as_ref() {
                Zero => Zero.into(),
                Succ(v) if is_nat_value(v) => v.clone().into(),
                _ => return None,
            }
        }
        IsZero(t) => {
            let v = eval_big(t.clone())?;
            match v.as_ref() {
                Zero => True.into(),
                Succ(v) if is_nat_value(v) => False.into(),
                _ => return None,
            }
        }
    })
}

pub fn eval(term: TermRef) -> TermRef {
    let a = eval_small(term.clone());
    if let Some(b) = eval_big(term.clone()) {
        assert_eq!(a, b);
    }
    a
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
