use std::rc::Rc;

use crate::prelude::*;

pub type Index = usize;

#[derive(PartialEq, Eq, Clone, Debug)]
pub enum Type {
    Bot,
    Top,
    Unit,
    Bool,
    Nat,
    Record(Vec<(Identifier, Rc<Self>)>),
    Arrow(Rc<Self>, Rc<Self>),
    Variable(Index),
    Abstract(Rc<Self>),
    Apply(Rc<Self>, Rc<Self>),
    Exists(Rc<Self>),
    Forall(Rc<Self>),
}

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Bot => f.write_str("Bot"),
            Type::Top => f.write_str("Top"),
            Type::Unit => f.write_str("Unit"),
            Type::Bool => f.write_str("Bool"),
            Type::Nat => f.write_str("Nat"),
            Type::Record(entries) => {
                f.write_str("{")?;
                for (i, (key, ty)) in entries.iter().enumerate() {
                    if i > 0 {
                        f.write_str(", ")?;
                    }
                    if key.as_ref() == &i.to_string() {
                        f.write_fmt(format_args!("{ty}"))?
                    } else {
                        f.write_fmt(format_args!("{key}: {ty}"))?
                    }
                }
                f.write_str("}")
            }
            Type::Arrow(lhs, rhs) => f.write_fmt(format_args!("({lhs} -> {rhs})")),
            Type::Variable(index) => f.write_fmt(format_args!("T_{index}")),
            Type::Abstract(body) => f.write_fmt(format_args!("lambda _Type. {body}")),
            Type::Apply(lhs, rhs) => f.write_fmt(format_args!("({lhs} {rhs})")),
            Type::Exists(body) => f.write_fmt(format_args!("{{*_Type, {body}}}")),
            Type::Forall(body) => f.write_fmt(format_args!("All _Type. {body}")),
        }
    }
}

#[derive(PartialEq, Eq, Clone, Copy, derive_more::Display, Debug)]
pub enum Func {
    #[display(fmt = "succ")]
    Succ,
    #[display(fmt = "pred")]
    Pred,
    #[display(fmt = "iszero")]
    IsZero,
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub enum Term {
    Unit,
    Bool(bool),
    Nat(Nat),
    Record(Vec<(Identifier, Rc<Self>)>),
    Access(Rc<Self>, Identifier),
    Variable(Index),
    Abstract(Rc<Self>),
    Apply(Rc<Self>, Rc<Self>),
    Pack(Rc<Self>),
    Unpack(Rc<Self>, Rc<Self>),
    If {
        cond: Rc<Self>,
        positive: Rc<Self>,
        negative: Rc<Self>,
    },
    Let {
        arg: Rc<Self>,
        body: Rc<Self>,
    },
    Fix(Rc<Self>),
    Func(Func),
}

impl std::fmt::Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self {
            Term::Unit => f.write_str("unit"),
            Term::Bool(v) => f.write_fmt(format_args!("{v}")),
            Term::Nat(v) => f.write_fmt(format_args!("{v}")),
            Term::Record(entries) => {
                f.write_str("{")?;
                for (i, (key, val)) in entries.iter().enumerate() {
                    if i > 0 {
                        f.write_str(", ")?;
                    }
                    if key.as_ref() == &i.to_string() {
                        f.write_fmt(format_args!("{val}"))?
                    } else {
                        f.write_fmt(format_args!("{key} = {val}"))?
                    }
                }
                f.write_str("}")
            }
            Term::Access(term, key) => f.write_fmt(format_args!("{term}.{key}")),
            Term::Variable(index) => f.write_fmt(format_args!("v_{index}")),
            Term::Abstract(body) => f.write_fmt(format_args!("(lambda _: _. {body})")),
            Term::Apply(lhs, rhs) => f.write_fmt(format_args!("({lhs} {rhs})")),
            Term::Pack(body) => f.write_fmt(format_args!("{{*_, {body}}} as _")),
            Term::Unpack(arg, body) => f.write_fmt(format_args!("let {{*_, _}} = {arg} in {body}")),
            Term::If {
                cond,
                positive,
                negative,
            } => f.write_fmt(format_args!("(if {cond} then {positive} else {negative})")),
            Term::Let { arg, body } => f.write_fmt(format_args!("let _ = {arg} in {body}")),
            Term::Fix(body) => f.write_fmt(format_args!("(fix ({body}))")),
            Term::Func(func) => f.write_fmt(format_args!("{func}")),
        }
    }
}
