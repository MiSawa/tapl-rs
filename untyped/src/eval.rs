use std::rc::Rc;

use thiserror::Error;

use crate::ast;

#[derive(Debug, Error)]
pub enum EvalError {
    #[error("Found a free variable `{0}`")]
    FreeVariable(String),
}
pub type Result<T> = std::result::Result<T, EvalError>;

type StringRef = Rc<String>;
type TermRef = Rc<Term>;

#[derive(PartialEq, Eq, Clone, Debug)]
pub enum Term {
    Var(usize),
    Abs(StringRef, TermRef),
    Apply(TermRef, TermRef),
}

impl std::fmt::Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fn fmt_rec<'a>(
            term: &'a Term,
            table: &mut Vec<&'a str>,
            f: &mut std::fmt::Formatter<'_>,
        ) -> std::fmt::Result {
            use Term::*;
            match term {
                Var(i) => f.write_str(&table[table.len() - i - 1]),
                Abs(var, body) => {
                    table.push(var.as_str());
                    f.write_str("lambda ")?;
                    f.write_str(var)?;
                    f.write_str(". ")?;
                    fmt_rec(body, table, f)?;
                    assert_eq!(Some(var.as_str()), table.pop());
                    Ok(())
                }
                Apply(lhs, rhs) => {
                    f.write_str("(")?;
                    fmt_rec(lhs, table, f)?;
                    f.write_str(" ")?;
                    fmt_rec(rhs, table, f)?;
                    f.write_str(")")?;
                    Ok(())
                }
            }
        }
        fmt_rec(self, &mut vec![], f)
    }
}

pub fn anonymize(term: &ast::Term) -> Result<Term> {
    fn anonymize_rec<'a>(table: &mut Vec<&'a str>, term: &'a ast::Term) -> Result<Term> {
        Ok(match term {
            ast::Term::Var(s) => {
                let i = table
                    .iter()
                    .rev()
                    .enumerate()
                    .find_map(|(i, x)| (x == &s).then(|| i))
                    .ok_or_else(|| EvalError::FreeVariable(s.to_string()))?;
                Term::Var(i)
            }
            ast::Term::Abs(x, body) => {
                table.push(x);
                let body = anonymize_rec(table, body)?;
                assert_eq!(Some(x.as_str()), table.pop());
                Term::Abs(x.to_string().into(), body.into())
            }
            ast::Term::Apply(lhs, rhs) => {
                let lhs = anonymize_rec(table, lhs)?;
                let rhs = anonymize_rec(table, rhs)?;
                Term::Apply(lhs.into(), rhs.into())
            }
        })
    }
    anonymize_rec(&mut vec![], &term)
}

fn is_value_abstruction(term: &Term) -> bool {
    matches!(term, &Term::Abs(_, _))
}

fn shift(term: &Term, c: usize, d: isize) -> Term {
    use Term::*;
    match term {
        Var(k) => Var(if *k < c {
            *k
        } else {
            (*k as isize + d).try_into().unwrap()
        }),
        Abs(x, body) => Abs(x.clone(), shift(body, c + 1, d).into()),
        Apply(lhs, rhs) => Apply(shift(lhs, c, d).into(), shift(rhs, c, d).into()),
    }
}

fn shift_all(term: &Term, d: isize) -> Term {
    shift(term, 0, d)
}

fn substitute(base: &Term, target: usize, value: &Term) -> Term {
    use Term::*;
    match base {
        Var(i) if *i == target => value.clone(),
        Var(_) => base.clone(),
        Abs(x, body) => Abs(x.clone(), substitute(body, target + 1, value).into()),
        Apply(lhs, rhs) => Apply(
            substitute(lhs, target, value).into(),
            substitute(rhs, target, value).into(),
        ),
    }
}

fn apply(body: &Term, arg: &Term) -> Term {
    shift_all(&substitute(body, 0, &shift_all(arg, 1)), -1)
}

pub fn reduce(term: &Term) -> Option<Term> {
    use Term::*;
    if let Apply(lhs, rhs) = term {
        // E-APP1
        if let Some(lhs) = reduce(lhs) {
            return Some(Apply(lhs.into(), rhs.clone()));
        }
        // E-APP2
        if is_value_abstruction(lhs) {
            if let Some(rhs) = reduce(rhs) {
                return Some(Apply(lhs.clone(), rhs.into()));
            }
        }
        // E-APP_ABS
        if let Abs(_, body) = lhs.as_ref() {
            return Some(apply(body, rhs));
        }
        None
    } else {
        None
    }
}

fn eval_small(mut term: Term) -> Term {
    while let Some(next) = reduce(&term) {
        term = next
    }
    term
}

fn eval_big(term: &Term) -> Option<Term> {
    use Term::*;
    Some(match term {
        Var(_) => term.clone(),
        Abs(_, _) => term.clone(),
        Apply(lhs, rhs) => {
            let lhs = eval_big(lhs)?;
            let rhs = eval_big(rhs)?;
            if let Abs(_, body) = lhs {
                eval_big(&apply(&body, &rhs))?
            } else {
                return None;
            }
        }
    })
}

pub fn eval(term: Term) -> Term {
    let a = eval_small(term.clone());
    if let Some(b) = eval_big(&term) {
        assert_eq!(a, b);
    }
    a
}

#[cfg(test)]
mod test {
    use super::{Term::*, *};

    macro_rules! var {
        ($n:expr) => {
            Var($n)
        };
    }
    macro_rules! lambda {
        ($x:expr, $body: expr) => {
            Abs(StringRef::new($x.to_string()), $body.into())
        };
    }
    macro_rules! apply {
        ($lhs:expr, $rhs: expr) => {
            Apply($lhs.into(), $rhs.into())
        };
    }

    #[test]
    fn test() {
        assert_eq!(eval(lambda!("x", var!(0))), lambda!("x", var!(0)));
        assert_eq!(
            eval(apply!(lambda!("x", var!(0)), lambda!("y", var!(0)))),
            lambda!("y", var!(0))
        );
    }
}
