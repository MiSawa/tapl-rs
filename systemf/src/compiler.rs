use std::rc::Rc;

use rpds::Stack;

use crate::{lang, prelude::*};

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
            Type::Variable(index) => f.write_fmt(format_args!("{index}")),
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

trait TypeContext {
    fn lookup_type_variable(&self, name: &Identifier) -> Option<Index>;
    fn type_pushed(&self, name: Option<Identifier>) -> Self;
}

trait TermContext {
    fn lookup_variable(&self, name: &Identifier) -> Option<(Index, Rc<Type>)>;
    fn term_pushed(&self, name: Option<Identifier>, ty: Rc<Type>) -> Self;
}

#[derive(Default)]
struct Context {
    types: Stack<Option<Identifier>>,
    variables: Stack<(Option<Identifier>, Rc<Type>)>,
}
impl TypeContext for Context {
    fn lookup_type_variable(&self, name: &Identifier) -> Option<Index> {
        self.types
            .iter()
            .enumerate()
            .find_map(|(i, n)| n.as_ref().filter(|n| n == &name).map(|_| i))
    }
    fn type_pushed(&self, name: Option<Identifier>) -> Self {
        let types = self.types.push(name);
        let variables = self.variables.clone();
        Self { types, variables }
    }
}
impl TermContext for Context {
    fn lookup_variable(&self, name: &Identifier) -> Option<(Index, Rc<Type>)> {
        self.variables
            .iter()
            .enumerate()
            .find_map(|(i, (n, ty))| n.as_ref().filter(|n| n == &name).map(|_| (i, ty.clone())))
    }
    fn term_pushed(&self, name: Option<Identifier>, ty: Rc<Type>) -> Self {
        let types = self.types.clone();
        let variables = self.variables.push((name, ty));
        Self { types, variables }
    }
}

fn compile_type(context: &impl TypeContext, ty: &Spanned<lang::Type>) -> Result<Spanned<Type>> {
    let value = match ty.as_ref() {
        lang::Type::Bot => Type::Bot,
        lang::Type::Top => Type::Top,
        lang::Type::Unit => Type::Unit,
        lang::Type::Bool => Type::Bool,
        lang::Type::Nat => Type::Nat,
        lang::Type::Record(entries) => Type::Record(
            entries
                .iter()
                .map(|(k, v)| {
                    Ok((
                        k.value().clone(),
                        compile_type(context, v)?.forget_span().into(),
                    ))
                })
                .collect::<Result<_>>()?,
        ),
        lang::Type::Arrow(lhs, rhs) => Type::Arrow(
            compile_type(context, lhs)?.forget_span().into(),
            compile_type(context, rhs)?.forget_span().into(),
        ),
        lang::Type::Variable(name) => {
            if let Some(i) = context.lookup_type_variable(name.as_ref()) {
                Type::Variable(i)
            } else {
                return Err(Error::custom(
                    ty.span(),
                    format!("Found a free type {name}"),
                ));
            }
        }
        lang::Type::Abstract(var, body) => Type::Abstract(
            compile_type(&context.type_pushed(Some(var.as_ref().clone())), body)?
                .forget_span()
                .into(),
        ),
        lang::Type::Apply(lhs, rhs) => Type::Apply(
            compile_type(context, lhs)?.forget_span().into(),
            compile_type(context, rhs)?.forget_span().into(),
        ),
        lang::Type::Exists(ident, body) => Type::Exists(
            compile_type(&context.type_pushed(Some(ident.as_ref().clone())), body)?
                .forget_span()
                .into(),
        ),
        lang::Type::Forall(ident, body) => Type::Forall(
            compile_type(&context.type_pushed(Some(ident.as_ref().clone())), body)?
                .forget_span()
                .into(),
        ),
    };
    Ok(Spanned {
        span: ty.span(),
        value,
    })
}

trait TypeVarMapper {
    fn on_var(&mut self, depth: usize, index: Index) -> Type;
}

fn map_type_var(ty: &Type, mapper: &mut impl TypeVarMapper) -> Type {
    fn rec(ty: &Type, mapper: &mut impl TypeVarMapper, depth: usize) -> Type {
        match ty {
            Type::Bot => Type::Bot,
            Type::Top => Type::Top,
            Type::Unit => Type::Unit,
            Type::Bool => Type::Bool,
            Type::Nat => Type::Nat,
            Type::Record(entries) => Type::Record(
                entries
                    .iter()
                    .map(|(k, v)| (k.clone(), rec(v, mapper, depth).into()))
                    .collect(),
            ),
            Type::Arrow(lhs, rhs) => Type::Arrow(
                rec(lhs, mapper, depth).into(),
                rec(rhs, mapper, depth).into(),
            ),
            Type::Variable(i) => mapper.on_var(depth, *i),
            Type::Abstract(body) => Type::Abstract(rec(body, mapper, depth + 1).into()),
            Type::Apply(lhs, rhs) => Type::Apply(
                rec(lhs, mapper, depth).into(),
                rec(rhs, mapper, depth).into(),
            ),
            Type::Exists(body) => Type::Exists(rec(body, mapper, depth + 1).into()),
            Type::Forall(body) => Type::Forall(rec(body, mapper, depth + 1).into()),
        }
    }
    rec(ty, mapper, 0)
}
fn shift_type(diff: isize, ty: &Type) -> Type {
    struct M(isize);
    impl TypeVarMapper for M {
        fn on_var(&mut self, depth: usize, index: Index) -> Type {
            let new_index = if index >= depth {
                (index as isize + self.0)
                    .try_into()
                    .expect("Something went wrong while substituting a type variable")
            } else {
                index
            };
            Type::Variable(new_index)
        }
    }
    map_type_var(ty, &mut M(diff))
}
fn substitute_top_type(base: &Type, replacement: &Type) -> Type {
    struct M<'a>(&'a Type);
    impl<'a> TypeVarMapper for M<'a> {
        fn on_var(&mut self, depth: usize, index: Index) -> Type {
            if depth == index {
                return self.0.clone();
            }
            let new_index = if depth < index { index - 1 } else { index };
            Type::Variable(new_index)
        }
    }
    map_type_var(base, &mut M(replacement))
}
fn apply_top_type(body: &Type, arg: &Type) -> Type {
    shift_type(-1, &substitute_top_type(body, &shift_type(1, arg)))
}

struct TypeSpannedTerm {
    ty: Type,
    span: Span,
    term: Term,
}

fn compile_term(
    context: &(impl TermContext + TypeContext),
    original: &Spanned<lang::Term>,
) -> Result<TypeSpannedTerm> {
    let (ty, term) = match original.as_ref() {
        lang::Term::Unit => (Type::Unit, Term::Unit),
        lang::Term::Bool(v) => (Type::Bool, Term::Bool(*v)),
        lang::Term::Nat(v) => (Type::Nat, Term::Nat(*v)),
        lang::Term::Record(entries) => {
            let mut values = vec![];
            let mut types = vec![];
            for (k, v) in entries {
                let inner = compile_term(context, v)?;
                values.push((k.value().clone(), inner.term.into()));
                types.push((k.value().clone(), inner.ty.into()));
            }
            (Type::Record(types), Term::Record(values))
        }
        lang::Term::Access(term, key) => {
            let inner = compile_term(context, term)?;
            // TODO: realize type
            if let Type::Record(entries) = &inner.ty {
                if let Some(ty) = entries
                    .iter()
                    .find_map(|(k, ty)| (k == key.value()).then(|| ty))
                {
                    (
                        ty.as_ref().clone(),
                        Term::Access(inner.term.into(), key.value().clone()),
                    )
                } else {
                    return Err(Error::custom(
                        term.span(),
                        format!(
                            "Expected a record type that has key {key} but was {}",
                            inner.ty
                        ),
                    ));
                }
            } else {
                return Err(Error::custom(
                    term.span(),
                    format!("Expected a record type but was {}", inner.ty),
                ));
            }
        }
        lang::Term::Variable(name) => {
            if let Some((i, ty)) = context.lookup_variable(name.as_ref()) {
                (ty.as_ref().clone(), Term::Variable(i))
            } else {
                return Err(Error::custom(
                    original.span(),
                    format!("Encounter a free variable {name}"),
                ));
            }
        }
        lang::Term::Abstract(name, ty, body) => {
            let ty: Rc<_> = compile_type(context, ty)?.forget_span().into();
            let body = compile_term(
                &context.term_pushed(name.as_ref().map(Spanned::value).cloned(), ty.clone()),
                body,
            )?;
            (
                Type::Arrow(ty, body.ty.clone().into()),
                Term::Abstract(body.term.into()),
            )
        }
        lang::Term::Apply(lhs, rhs) => {
            let lhs = compile_term(context, lhs)?;
            let rhs = compile_term(context, rhs)?;
            let rtype = &rhs.ty;
            // TODO: realize type
            if let Type::Arrow(dom, codom) = lhs.ty {
                // TODO: subtype
                if dom.as_ref() == rtype {
                    (
                        (*codom).clone(),
                        Term::Apply(lhs.term.into(), rhs.term.into()),
                    )
                } else {
                    return Err(Error::expected_input_found(
                        rhs.span,
                        std::iter::once(Some(format!("{codom}"))),
                        Some(format!("{rtype}")),
                    ));
                }
            } else {
                return Err(Error::expected_input_found(
                    lhs.span,
                    std::iter::once(Some("arrow type".to_string())),
                    Some(format!("{}", lhs.ty)),
                ));
            }
        }
        lang::Term::Ascribe(body, ty) => {
            let body = compile_term(context, body)?;
            let ty = compile_type(context, ty)?.forget_span();
            // TODO: subtype
            if body.ty == ty {
                // We eliminate the ascription in the compile time
                (ty, body.term)
            } else {
                return Err(Error::expected_input_found(
                    body.span,
                    std::iter::once(Some(format!("{ty}"))),
                    Some(format!("{}", body.ty)),
                ));
            }
        }
        lang::Term::Pack {
            inner_type,
            body,
            exposed_type,
        } => {
            let inner_type = compile_type(context, inner_type)?.forget_span();
            let body = compile_term(context, body)?;
            let exposed = compile_type(context, exposed_type)?.forget_span();
            // TODO: realize type
            if let Type::Exists(exposed_inner) = &exposed {
                let exposed_actual = apply_top_type(exposed_inner, &body.ty);
                // TODO: subtype?
                if inner_type != exposed_actual {
                    return Err(Error::expected_input_found(
                        exposed_type.span.clone(),
                        std::iter::once(Some(format!("{exposed_type}"))),
                        Some(format!("{inner_type}")),
                    ));
                }
                (exposed, Term::Pack(body.term.into()))
            } else {
                return Err(Error::expected_input_found(
                    exposed_type.span.clone(),
                    std::iter::once(Some("existential type".to_string())),
                    Some(format!("{exposed_type}")),
                ));
            }
        }
        lang::Term::Unpack { ty, var, arg, body } => {
            let arg = compile_term(context, arg)?;
            // TODO: realize type
            if matches!(arg.ty, Type::Exists(_)) {
                let body = compile_term(
                    &context
                        .term_pushed(Some(var.value().clone()), arg.ty.clone().into())
                        .type_pushed(Some(ty.value().clone())),
                    body,
                )?;
                (
                    body.ty.clone(),
                    Term::Unpack(arg.term.into(), body.term.into()),
                )
            } else {
                return Err(Error::expected_input_found(
                    arg.span,
                    std::iter::once(Some("existential type".to_string())),
                    Some(format!("{}", arg.ty)),
                ));
            }
        }
        lang::Term::Seq(lhs, rhs) => {
            // Converts
            // `(lhs; rhs)`
            // to
            // `(lambda _: Unit. rhs) lhs`
            let rhs_span = rhs.span();
            let rhs = lang::Term::Abstract(
                None,
                Spanned {
                    span: rhs_span.clone(),
                    value: lang::Type::Unit,
                }
                .into(),
                rhs.clone(),
            );
            let seq = lang::Term::Apply(
                Spanned {
                    span: rhs_span,
                    value: rhs,
                }
                .into(),
                lhs.clone(),
            );
            return compile_term(
                context,
                &Spanned {
                    span: original.span(),
                    value: seq,
                },
            );
        }
        lang::Term::If {
            cond,
            positive,
            negative,
        } => {
            let cond = compile_term(context, cond)?;
            let positive = compile_term(context, positive)?;
            let negative = compile_term(context, negative)?;
            if cond.ty != Type::Bool {
                return Err(Error::expected_input_found(
                    cond.span,
                    std::iter::once(Some("Bool".to_string())),
                    Some(format!("{}", cond.ty)),
                ));
            }
            // TODO: join type
            if positive.ty != negative.ty {
                return Err(Error::custom(
                    original.span(),
                    format!(
                        "Mismatch type of positive clause {} and negative clause {}",
                        positive.ty, negative.ty
                    ),
                ));
            }
            (
                positive.ty,
                Term::If {
                    cond: cond.term.into(),
                    positive: positive.term.into(),
                    negative: negative.term.into(),
                },
            )
        }
        lang::Term::Let { var, arg, body } => {
            let arg = compile_term(context, arg)?;
            let body = compile_term(
                &context.term_pushed(var.as_ref().map(Spanned::value).cloned(), arg.ty.into()),
                body,
            )?;
            (
                body.ty.clone(),
                Term::Let {
                    arg: arg.term.into(),
                    body: body.term.into(),
                },
            )
        }
        lang::Term::LetRec { var, ty, arg, body } => {
            // Implement letrec with fix. rewrite
            // `letrec var: Ty = arg in body`
            // with
            // `let var = (fix lambda var: Ty . arg) in body`
            let abs = lang::Term::Abstract(Some(var.clone()), ty.clone(), arg.clone());
            let fix = lang::Term::Fix(
                Spanned {
                    span: arg.span.clone(),
                    value: abs,
                }
                .into(),
            );
            let arg = Spanned {
                span: arg.span.clone(),
                value: fix,
            };
            let rewritten = Spanned {
                span: original.span.clone(),
                value: lang::Term::Let {
                    var: Some(var.clone()),
                    arg: arg.into(),
                    body: body.clone(),
                },
            };
            return compile_term(context, &rewritten);
        }
        lang::Term::TypeAbstract(name, body) => {
            let body = compile_term(&context.type_pushed(Some(name.value.clone())), body)?;
            (Type::Forall(body.ty.into()), body.term)
        }
        lang::Term::TypeApply(body, ty) => {
            let body = compile_term(context, body)?;
            let ty = compile_type(context, ty)?.forget_span();
            if let Type::Forall(inner) = &body.ty {
                let new_ty = apply_top_type(inner, &ty);
                (new_ty, body.term)
            } else {
                return Err(Error::expected_input_found(
                    body.span,
                    std::iter::once(Some("universal type".to_string())),
                    Some(format!("{}", body.ty)),
                ));
            }
        }
        lang::Term::Fix(body) => {
            let body_span = &body.span;
            let body = compile_term(context, body)?;
            // TODO: realize type
            if let Type::Arrow(lhs, rhs) = &body.ty {
                // TODO: subtype
                if lhs == rhs {
                    (lhs.as_ref().clone(), Term::Fix(body.term.into()))
                } else {
                    return Err(Error::custom(
                        body_span.clone(),
                        format!(
                            "Mismatch type of domain {} and codomain {} of arg of fix",
                            lhs, rhs
                        ),
                    ));
                }
            } else {
                return Err(Error::expected_input_found(
                    body_span.clone(),
                    std::iter::once(Some("arrow type".to_string())),
                    Some(format!("{}", body.ty)),
                ));
            }
        }
        lang::Term::Func(func) => {
            fn arrow(dom: Type, codom: Type) -> Type {
                Type::Arrow(dom.into(), codom.into())
            }
            let (ty, func) = match func.value {
                lang::Func::Succ => (arrow(Type::Nat, Type::Nat), Func::Succ),
                lang::Func::Pred => (arrow(Type::Nat, Type::Nat), Func::Pred),
                lang::Func::IsZero => (arrow(Type::Nat, Type::Bool), Func::IsZero),
            };
            (ty, Term::Func(func))
        }
    };
    Ok(TypeSpannedTerm {
        ty,
        span: original.span(),
        term,
    })
}

pub fn compile(term: &Spanned<lang::Term>) -> Result<Term> {
    let context = Context::default();
    compile_term(&context, term).map(|t| t.term)
}

pub fn get_type(term: &Spanned<lang::Term>) -> Result<Type> {
    let context = Context::default();
    compile_term(&context, term).map(|t| t.ty)
}
