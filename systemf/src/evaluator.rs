use crate::term::{Func, Index, Term};

trait VarMapper {
    fn on_var(&mut self, depth: usize, index: Index) -> Term;
}

fn map_var(term: &Term, mapper: &mut impl VarMapper) -> Term {
    fn rec(term: &Term, mapper: &mut impl VarMapper, depth: usize) -> Term {
        match term {
            Term::Unit | Term::Bool(_) | Term::Nat(_) | Term::Func(_) => term.clone(),
            Term::Record(entries) => Term::Record(
                entries
                    .iter()
                    .map(|(k, v)| (k.clone(), rec(v, mapper, depth).into()))
                    .collect(),
            ),
            Term::Access(record, key) => {
                Term::Access(rec(record, mapper, depth).into(), key.clone())
            }
            Term::Variable(i) => mapper.on_var(depth, *i),
            Term::Abstract(body) => Term::Abstract(rec(body, mapper, depth + 1).into()),
            Term::Apply(lhs, rhs) => Term::Apply(
                rec(lhs, mapper, depth).into(),
                rec(rhs, mapper, depth).into(),
            ),
            Term::Pack(body) => Term::Pack(rec(body, mapper, depth).into()),
            Term::Unpack(arg, body) => Term::Unpack(
                rec(arg, mapper, depth).into(),
                rec(body, mapper, depth + 1).into(),
            ),
            Term::If {
                cond,
                positive,
                negative,
            } => Term::If {
                cond: rec(cond, mapper, depth).into(),
                positive: rec(positive, mapper, depth).into(),
                negative: rec(negative, mapper, depth).into(),
            },
            Term::Let { arg, body } => Term::Let {
                arg: rec(arg, mapper, depth).into(),
                body: rec(body, mapper, depth + 1).into(),
            },
            Term::Fix(body) => Term::Fix(rec(body, mapper, depth).into()),
        }
    }
    rec(term, mapper, 0)
}

fn shift(diff: isize, term: &Term) -> Term {
    struct M(isize);
    impl VarMapper for M {
        fn on_var(&mut self, depth: usize, index: Index) -> Term {
            let new_index = if index >= depth {
                (index as isize + self.0)
                    .try_into()
                    .expect("Something went wrong while substituting a type variable")
            } else {
                index
            };
            Term::Variable(new_index)
        }
    }
    map_var(term, &mut M(diff))
}

fn substitute_top(base: &Term, replacement: &Term) -> Term {
    struct M<'a>(&'a Term);
    impl<'a> VarMapper for M<'a> {
        fn on_var(&mut self, depth: usize, index: Index) -> Term {
            if depth == index {
                return self.0.clone();
            }
            let new_index = if depth < index { index - 1 } else { index };
            Term::Variable(new_index)
        }
    }
    map_var(base, &mut M(replacement))
}

fn apply_top(body: &Term, arg: &Term) -> Term {
    shift(-1, &substitute_top(body, &shift(1, arg)))
}

fn apply_func(f: Func, arg: &Term) -> Option<Term> {
    if let Term::Nat(v) = arg {
        return Some(match f {
            Func::Succ => Term::Nat(v.saturating_add(1)),
            Func::Pred => Term::Nat(v.saturating_sub(1)),
            Func::IsZero => Term::Bool(*v == 0),
        });
    }
    None
}

fn reduce(term: &Term) -> Option<Term> {
    match term {
        Term::Unit | Term::Bool(_) | Term::Nat(_) | Term::Func(_) | Term::Abstract(_) => {}
        Term::Record(entries) => {
            let mut ret = vec![];
            let mut reduced = false;
            for (key, val) in entries {
                if reduced {
                    ret.push((key.clone(), val.clone()));
                } else if let Some(v) = reduce(val) {
                    ret.push((key.clone(), v.into()));
                    reduced = true;
                } else {
                    ret.push((key.clone(), val.clone()));
                }
            }
            return reduced.then(|| Term::Record(ret));
        }
        Term::Access(record, key) => {
            if let Some(record) = reduce(record) {
                return Some(Term::Access(record.into(), key.clone()));
            } else if let Term::Record(entries) = record.as_ref() {
                if let Some(v) = entries.iter().find_map(|(k, v)| (k == key).then(|| v)) {
                    return Some(v.as_ref().clone());
                }
            }
        }
        Term::Variable(_) => unreachable!("Something went wrong: Variables should be substituted."),
        Term::Apply(lhs, rhs) => {
            if let Some(rhs) = reduce(rhs) {
                return Some(Term::Apply(lhs.clone(), rhs.into()));
            } else if let Some(lhs) = reduce(lhs) {
                return Some(Term::Apply(lhs.into(), rhs.clone()));
            } else if let Term::Abstract(body) = lhs.as_ref() {
                return Some(apply_top(body, rhs));
            } else if let Term::Func(f) = lhs.as_ref() {
                return apply_func(*f, rhs);
            }
        }
        Term::Pack(body) => {
            if let Some(body) = reduce(body) {
                return Some(Term::Pack(body.into()));
            }
        }
        Term::Unpack(arg, body) => {
            if let Some(arg) = reduce(arg) {
                return Some(Term::Unpack(arg.into(), body.clone()));
            } else if let Term::Pack(arg) = arg.as_ref() {
                return Some(apply_top(body, arg));
            }
        }
        Term::If {
            cond,
            positive,
            negative,
        } => {
            let ret = if let Some(cond) = reduce(cond) {
                Term::If {
                    cond: cond.into(),
                    positive: positive.clone(),
                    negative: negative.clone(),
                }
            } else if let Term::Bool(cond) = cond.as_ref() {
                if *cond {
                    positive.as_ref().clone()
                } else {
                    negative.as_ref().clone()
                }
            } else {
                return None;
            };
            return Some(ret);
        }
        Term::Let { arg, body } => {
            if let Some(arg) = reduce(arg) {
                return Some(Term::Let {
                    arg: arg.into(),
                    body: body.clone(),
                });
            } else {
                return Some(apply_top(body, arg));
            }
        }
        Term::Fix(body) => {
            if let Some(body) = reduce(body) {
                return Some(Term::Fix(body.into()));
            } else if let Term::Abstract(body) = body.as_ref() {
                return Some(apply_top(body, term));
            }
        }
    }
    None
}

fn eval_small(term: &Term) -> Term {
    let mut term = term.clone();
    while let Some(next) = reduce(&term) {
        term = next
    }
    term
}

pub fn evaluate(term: &Term) -> Term {
    eval_small(term)
}

#[cfg(test)]
mod test {
    use crate::{prelude::*, term::Term};

    fn run(input: &str) -> Result<Term, String> {
        let term = crate::parser::parse(input).map_err(|es| format!("{es:?}"))?;
        let term = crate::compiler::compile(&term).map_err(|e| format!("{e:?}"))?;
        let term = crate::evaluator::evaluate(&term);
        Ok(term)
    }

    #[test]
    fn test_letrec() {
        assert_eq!(
            run(r#"
                letrec iseven: Nat->Bool =
                    lambda x: Nat.
                        if iszero x
                        then true
                        else if iszero (pred x)
                        then false
                        else iseven (pred (pred x))
                in iseven 7
            "#)
            .unwrap(),
            Term::Bool(false)
        );
        assert_eq!(
            run(r#"
                letrec add: Nat -> Nat -> Nat =
                    lambda x: Nat.
                        if iszero x
                        then (lambda y: Nat. y)
                        else (lambda y: Nat. (succ (add (pred x) y)))
                in add 2 3
            "#)
            .unwrap(),
            Term::Nat(5)
        )
    }

    #[test]
    fn test_existential() {
        assert_eq!(
            run(r#"
                let {X, x} = {*Nat, {a=5, f=lambda x:Nat. succ(x)}}
                    as {Some X, {a:X, f:X->Nat}}
                in (x.f x.a)
            "#)
            .unwrap(),
            Term::Nat(6)
        );
        assert!(run(r#"
                let {X, x} = {*Nat, {a=5, f=lambda x:Nat. succ(x)}}
                    as {Some X, {a:X, f:X->X}}
                in (x.f x.a)
            "#)
        .is_err())
    }
}
