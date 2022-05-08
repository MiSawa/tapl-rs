use std::rc::Rc;

use crate::prelude::*;

#[derive(PartialEq, Eq, Hash, Clone, derive_more::Display, Debug)]
pub enum TypeToken {
    #[display(fmt = "Bot")]
    Bot,
    #[display(fmt = "Top")]
    Top,
    #[display(fmt = "Unit")]
    Unit,
    #[display(fmt = "Bool")]
    Bool,
    #[display(fmt = "Nat")]
    Nat,
}

#[derive(PartialEq, Eq, Hash, Clone, derive_more::Display, Debug)]
pub enum ValueToken {
    #[display(fmt = "unit")]
    Unit,
    #[display(fmt = "true")]
    True,
    #[display(fmt = "false")]
    False,
    #[display(fmt = "{_0}")]
    Nat(Nat),
}

#[derive(PartialEq, Eq, Hash, Clone, derive_more::Display, Debug)]
pub enum FuncToken {
    #[display(fmt = "fix")]
    Fix,
    #[display(fmt = "succ")]
    Succ,
    #[display(fmt = "pred")]
    Pred,
    #[display(fmt = "iszero")]
    IsZero,
}

#[derive(PartialEq, Eq, Hash, Clone, derive_more::Display, Debug)]
pub enum Token {
    #[display(fmt = "(")]
    LParen,
    #[display(fmt = ")")]
    RParen,
    #[display(fmt = "{{")]
    LBrace,
    #[display(fmt = "}}")]
    RBrace,
    #[display(fmt = "[")]
    LBracket,
    #[display(fmt = "]")]
    RBracket,
    #[display(fmt = ",")]
    Comma,
    #[display(fmt = ".")]
    Dot,
    #[display(fmt = ";")]
    Semicolon,
    #[display(fmt = ":")]
    Colon,
    #[display(fmt = "_")]
    Underscore,
    #[display(fmt = "=")]
    Equal,
    #[display(fmt = "*")]
    Star,

    #[display(fmt = "->")]
    Arrow,

    #[display(fmt = "lambda")]
    Lambda,
    #[display(fmt = "All")]
    All,
    #[display(fmt = "Some")]
    Some,

    #[display(fmt = "let")]
    Let,
    #[display(fmt = "letrec")]
    LetRec,
    #[display(fmt = "in")]
    In,
    #[display(fmt = "as")]
    As,

    #[display(fmt = "if")]
    If,
    #[display(fmt = "then")]
    Then,
    #[display(fmt = "else")]
    Else,

    #[display(fmt = "{_0}")]
    Type(TypeToken),
    #[display(fmt = "{_0}")]
    Value(ValueToken),
    #[display(fmt = "{_0}")]
    Func(FuncToken),

    #[display(fmt = "{_0}")]
    UpperIdent(Identifier),
    #[display(fmt = "{_0}")]
    LowerIdent(Identifier),
}

#[derive(Clone, Debug)]
pub enum Type {
    Bot,
    Top,
    Unit,
    Bool,
    Nat,
    Record(Vec<(Spanned<Identifier>, Rc<Spanned<Self>>)>),
    Arrow(Rc<Spanned<Self>>, Rc<Spanned<Self>>),
    Variable(Spanned<Identifier>),
    Abstract(Spanned<Identifier>, Rc<Spanned<Self>>),
    Apply(Rc<Spanned<Self>>, Rc<Spanned<Self>>),
    Exists(Spanned<Identifier>, Rc<Spanned<Self>>),
    Forall(Spanned<Identifier>, Rc<Spanned<Self>>),
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
                    if key.value().as_ref() == &i.to_string() {
                        f.write_fmt(format_args!("{ty}"))?
                    } else {
                        f.write_fmt(format_args!("{key}: {ty}"))?
                    }
                }
                f.write_str("}")
            }
            Type::Arrow(lhs, rhs) => f.write_fmt(format_args!("({lhs} -> {rhs})")),
            Type::Variable(name) => f.write_str(name.as_ref()),
            Type::Abstract(ident, body) => f.write_fmt(format_args!("lambda {ident}. {body}")),
            Type::Apply(lhs, rhs) => f.write_fmt(format_args!("({lhs} {rhs})")),
            Type::Exists(ident, body) => f.write_fmt(format_args!("{{*{ident}, {body}}}")),
            Type::Forall(ident, body) => f.write_fmt(format_args!("All {ident}. {body}")),
        }
    }
}

#[derive(Clone, Copy, derive_more::Display, Debug)]
pub enum Func {
    #[display(fmt = "succ")]
    Succ,
    #[display(fmt = "pred")]
    Pred,
    #[display(fmt = "iszero")]
    IsZero,
}

#[derive(Clone, Debug)]
pub enum Term {
    Unit,
    Bool(bool),
    Nat(Nat),
    Record(Vec<(Spanned<Identifier>, Rc<Spanned<Self>>)>),
    Access(Rc<Spanned<Self>>, Spanned<Identifier>),
    Variable(Spanned<Identifier>),
    Abstract(
        Option<Spanned<Identifier>>,
        Rc<Spanned<Type>>,
        Rc<Spanned<Self>>,
    ),
    Apply(Rc<Spanned<Self>>, Rc<Spanned<Self>>),
    Ascribe(Rc<Spanned<Self>>, Rc<Spanned<Type>>),
    Pack {
        inner_type: Rc<Spanned<Type>>,
        body: Rc<Spanned<Self>>,
        exposed_type: Rc<Spanned<Type>>,
    },
    Unpack {
        ty: Spanned<Identifier>,
        var: Spanned<Identifier>,
        arg: Rc<Spanned<Self>>,
        body: Rc<Spanned<Self>>,
    },
    Seq(Rc<Spanned<Self>>, Rc<Spanned<Self>>),
    If {
        cond: Rc<Spanned<Self>>,
        positive: Rc<Spanned<Self>>,
        negative: Rc<Spanned<Self>>,
    },
    Let {
        var: Option<Spanned<Identifier>>,
        arg: Rc<Spanned<Self>>,
        body: Rc<Spanned<Self>>,
    },
    LetRec {
        var: Spanned<Identifier>,
        ty: Rc<Spanned<Type>>,
        arg: Rc<Spanned<Self>>,
        body: Rc<Spanned<Self>>,
    },
    TypeAbstract(Spanned<Identifier>, Rc<Spanned<Self>>),
    TypeApply(Rc<Spanned<Self>>, Rc<Spanned<Type>>),
    Fix(Rc<Spanned<Self>>),
    Func(Spanned<Func>),
}

impl std::fmt::Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Term::Unit => f.write_str("unit"),
            Term::Bool(v) => f.write_fmt(format_args!("{v}")),
            Term::Nat(v) => f.write_fmt(format_args!("{v}")),
            Term::Record(entries) => {
                f.write_str("{")?;
                for (i, (key, val)) in entries.iter().enumerate() {
                    if i > 0 {
                        f.write_str(", ")?;
                    }
                    if key.value().as_ref() == &i.to_string() {
                        f.write_fmt(format_args!("{val}"))?
                    } else {
                        f.write_fmt(format_args!("{key} = {val}"))?
                    }
                }
                f.write_str("}")
            }
            Term::Access(term, key) => f.write_fmt(format_args!("{term}.{key}")),
            Term::Variable(name) => f.write_str(name.as_ref()),
            Term::Abstract(Some(var), ty, body) => {
                f.write_fmt(format_args!("(lambda {var}: {ty}. {body})"))
            }
            Term::Abstract(None, ty, body) => f.write_fmt(format_args!("(lambda _: {ty}. {body})")),
            Term::Apply(lhs, rhs) => f.write_fmt(format_args!("({lhs} {rhs})")),
            Term::Ascribe(body, ty) => f.write_fmt(format_args!("{body} as {ty}")),
            Term::Pack {
                inner_type,
                body,
                exposed_type,
            } => f.write_fmt(format_args!("{{*{inner_type}, {body}}} as {exposed_type}")),
            Term::Unpack { ty, var, arg, body } => {
                f.write_fmt(format_args!("let {{*{ty}, {var}}} = {arg} in {body}"))
            }
            Term::Seq(lhs, rhs) => f.write_fmt(format_args!("({lhs}; {rhs})")),
            Term::If {
                cond,
                positive,
                negative,
            } => f.write_fmt(format_args!("(if {cond} then {positive} else {negative})")),
            Term::Let {
                var: Some(var),
                arg,
                body,
            } => f.write_fmt(format_args!("let {var} = {arg} in {body}")),
            Term::Let {
                var: None,
                arg,
                body,
            } => f.write_fmt(format_args!("let _ = {arg} in {body}")),
            Term::LetRec { var, ty, arg, body } => {
                f.write_fmt(format_args!("letrec {var}: {ty} = {arg} in {body}"))
            }
            Term::TypeAbstract(var, body) => f.write_fmt(format_args!("lambda {var}. {body}")),
            Term::TypeApply(body, ty) => f.write_fmt(format_args!("{body} [{ty}]")),
            Term::Fix(body) => f.write_fmt(format_args!("(fix ({body}))")),
            Term::Func(func) => f.write_fmt(format_args!("{func}")),
        }
    }
}
