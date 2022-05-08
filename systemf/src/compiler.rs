use std::rc::Rc;

use rpds::Stack;

use crate::{lang, prelude::*};

type Index = usize;

#[derive(PartialEq, Eq, derive_more::AsRef, Clone, Debug)]
pub struct Type<I> {
    info: I,
    #[as_ref]
    node: TypeNode<I>,
}
#[derive(PartialEq, Eq, Clone, Debug)]
pub enum TypeNode<I> {
    Bot,
    Top,
    Unit,
    Bool,
    Nat,
    Record(Vec<(Identifier, Rc<Type<I>>)>),
    Arrow(Rc<Type<I>>, Rc<Type<I>>),
    Variable(Index),
    Abstract(Rc<Type<I>>),
    Apply(Rc<Type<I>>, Rc<Type<I>>),
    Exists(Rc<Type<I>>),
    Forall(Rc<Type<I>>),
}

impl<I> Type<I> {
    fn forget(&self) -> Type<()> {
        let node = match &self.node {
            TypeNode::Bot => TypeNode::Bot,
            TypeNode::Top => TypeNode::Top,
            TypeNode::Unit => TypeNode::Unit,
            TypeNode::Bool => TypeNode::Bool,
            TypeNode::Nat => TypeNode::Nat,
            TypeNode::Record(entries) => TypeNode::Record(
                entries
                    .iter()
                    .map(|(k, v)| (k.clone(), v.forget().into()))
                    .collect(),
            ),
            TypeNode::Arrow(lhs, rhs) => TypeNode::Arrow(lhs.forget().into(), rhs.forget().into()),
            TypeNode::Variable(name) => TypeNode::Variable(name.clone()),
            TypeNode::Abstract(body) => TypeNode::Abstract(body.forget().into()),
            TypeNode::Apply(lhs, rhs) => TypeNode::Apply(lhs.forget().into(), rhs.forget().into()),
            TypeNode::Exists(body) => TypeNode::Exists(body.forget().into()),
            TypeNode::Forall(body) => TypeNode::Forall(body.forget().into()),
        };
        Type { info: (), node }
    }
}

impl<T> std::fmt::Display for Type<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.node {
            TypeNode::Bot => f.write_str("Bot"),
            TypeNode::Top => f.write_str("Top"),
            TypeNode::Unit => f.write_str("Unit"),
            TypeNode::Bool => f.write_str("Bool"),
            TypeNode::Nat => f.write_str("Nat"),
            TypeNode::Record(entries) => {
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
            TypeNode::Arrow(lhs, rhs) => f.write_fmt(format_args!("({lhs} -> {rhs})")),
            TypeNode::Variable(index) => f.write_fmt(format_args!("{index}")),
            TypeNode::Abstract(body) => f.write_fmt(format_args!("lambda _Type. {body}")),
            TypeNode::Apply(lhs, rhs) => f.write_fmt(format_args!("({lhs} {rhs})")),
            TypeNode::Exists(body) => f.write_fmt(format_args!("{{*_Type, {body}}}")),
            TypeNode::Forall(body) => f.write_fmt(format_args!("All _Type. {body}")),
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

#[derive(PartialEq, Eq, derive_more::AsRef, Clone, Debug)]
pub struct Term<I> {
    info: I,
    #[as_ref]
    node: TermNode<I>,
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub enum TermNode<I> {
    Unit,
    Bool(bool),
    Nat(Nat),
    Record(Vec<(Identifier, Rc<Term<I>>)>),
    Access(Rc<Term<I>>, Identifier),
    Variable(Index),
    Abstract(Rc<Term<I>>),
    Apply(Rc<Term<I>>, Rc<Term<I>>),
    Pack(Rc<Term<I>>),
    Unpack(Rc<Term<I>>, Rc<Term<I>>),
    If {
        cond: Rc<Term<I>>,
        positive: Rc<Term<I>>,
        negative: Rc<Term<I>>,
    },
    Let {
        arg: Rc<Term<I>>,
        body: Rc<Term<I>>,
    },
    Fix(Rc<Term<I>>),
    Func(Func),
}

impl<I> Term<I> {
    fn forget(&self) -> Term<()> {
        let node = match &self.node {
            TermNode::Unit => TermNode::Unit,
            TermNode::Bool(v) => TermNode::Bool(*v),
            TermNode::Nat(v) => TermNode::Nat(*v),
            TermNode::Record(entries) => TermNode::Record(
                entries
                    .iter()
                    .map(|(k, v)| (k.clone(), v.forget().into()))
                    .collect(),
            ),
            TermNode::Access(record, field) => {
                TermNode::Access(record.forget().into(), field.clone())
            }
            TermNode::Variable(i) => TermNode::Variable(*i),
            TermNode::Abstract(body) => TermNode::Abstract(body.forget().into()),
            TermNode::Apply(lhs, rhs) => TermNode::Apply(lhs.forget().into(), rhs.forget().into()),
            TermNode::Pack(body) => TermNode::Pack(body.forget().into()),
            TermNode::Unpack(arg, body) => {
                TermNode::Unpack(arg.forget().into(), body.forget().into())
            }
            TermNode::If {
                cond,
                positive,
                negative,
            } => TermNode::If {
                cond: cond.forget().into(),
                positive: positive.forget().into(),
                negative: negative.forget().into(),
            },
            TermNode::Let { arg, body } => TermNode::Let {
                arg: arg.forget().into(),
                body: body.forget().into(),
            },
            TermNode::Fix(body) => TermNode::Fix(body.forget().into()),
            TermNode::Func(func) => TermNode::Func(*func),
        };
        Term { info: (), node }
    }
}

impl<T> std::fmt::Display for Term<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.node {
            TermNode::Unit => f.write_str("unit"),
            TermNode::Bool(v) => f.write_fmt(format_args!("{v}")),
            TermNode::Nat(v) => f.write_fmt(format_args!("{v}")),
            TermNode::Record(entries) => {
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
            TermNode::Access(term, key) => f.write_fmt(format_args!("{term}.{key}")),
            TermNode::Variable(index) => f.write_fmt(format_args!("v_{index}")),
            TermNode::Abstract(body) => f.write_fmt(format_args!("(lambda _: _. {body})")),
            TermNode::Apply(lhs, rhs) => f.write_fmt(format_args!("({lhs} {rhs})")),
            TermNode::Pack(body) => f.write_fmt(format_args!("{{*_, {body}}} as _")),
            TermNode::Unpack(arg, body) => {
                f.write_fmt(format_args!("let {{*_, _}} = {arg} in {body}"))
            }
            TermNode::If {
                cond,
                positive,
                negative,
            } => f.write_fmt(format_args!("(if {cond} then {positive} else {negative})")),
            TermNode::Let { arg, body } => f.write_fmt(format_args!("let _ = {arg} in {body}")),
            TermNode::Fix(body) => f.write_fmt(format_args!("(fix ({body}))")),
            TermNode::Func(func) => f.write_fmt(format_args!("{func}")),
        }
    }
}

trait TypeContext {
    fn lookup_type_variable(&self, name: &Identifier) -> Option<Index>;
    fn type_pushed(&self, name: Option<Identifier>) -> Self;
}

trait TermContext<J> {
    fn lookup_variable(&self, name: &Identifier) -> Option<(Index, Rc<Type<J>>)>;
    fn term_pushed(&self, name: Option<Identifier>, ty: Rc<Type<J>>) -> Self;
}

#[derive(Default)]
struct Context<J> {
    types: Stack<Option<Identifier>>,
    variables: Stack<(Option<Identifier>, Rc<Type<J>>)>,
}
impl<J> TypeContext for Context<J> {
    fn lookup_type_variable(&self, name: &Identifier) -> Option<Index> {
        self.types
            .iter()
            .enumerate()
            .find_map(|(i, n)| n.as_ref().filter(|n| n == &name).map(|_| i))
            .clone()
    }
    fn type_pushed(&self, name: Option<Identifier>) -> Self {
        let types = self.types.push(name);
        let variables = self.variables.clone();
        Self { types, variables }
    }
}
impl<J> TermContext<J> for Context<J> {
    fn lookup_variable(&self, name: &Identifier) -> Option<(Index, Rc<Type<J>>)> {
        self.variables
            .iter()
            .enumerate()
            .find_map(|(i, (n, ty))| n.as_ref().filter(|n| n == &name).map(|_| (i, ty.clone())))
    }
    fn term_pushed(&self, name: Option<Identifier>, ty: Rc<Type<J>>) -> Self {
        let types = self.types.clone();
        let variables = self.variables.push((name, ty));
        Self { types, variables }
    }
}

fn compile_type(context: &impl TypeContext, ty: &Spanned<lang::Type>) -> Result<Type<Span>> {
    let node = match ty.as_ref() {
        lang::Type::Bot => TypeNode::Bot,
        lang::Type::Top => TypeNode::Top,
        lang::Type::Unit => TypeNode::Unit,
        lang::Type::Bool => TypeNode::Bool,
        lang::Type::Nat => TypeNode::Nat,
        lang::Type::Record(entries) => TypeNode::Record(
            entries
                .iter()
                .map(|(k, v)| Ok((k.value().clone(), compile_type(context, v)?.into())))
                .collect::<Result<_>>()?,
        ),
        lang::Type::Arrow(lhs, rhs) => TypeNode::Arrow(
            compile_type(context, lhs)?.into(),
            compile_type(context, rhs)?.into(),
        ),
        lang::Type::Variable(name) => {
            if let Some(i) = context.lookup_type_variable(name.as_ref()) {
                TypeNode::Variable(i)
            } else {
                return Err(Error::custom(
                    ty.span(),
                    format!("Found a free type {name}"),
                ));
            }
        }
        lang::Type::Abstract(var, body) => TypeNode::Abstract(
            compile_type(&context.type_pushed(Some(var.as_ref().clone())), body)?.into(),
        ),
        lang::Type::Apply(lhs, rhs) => TypeNode::Apply(
            compile_type(context, lhs)?.into(),
            compile_type(context, rhs)?.into(),
        ),
        lang::Type::Exists(ident, body) => TypeNode::Exists(
            compile_type(&context.type_pushed(Some(ident.as_ref().clone())), body)?.into(),
        ),
        lang::Type::Forall(ident, body) => TypeNode::Forall(
            compile_type(&context.type_pushed(Some(ident.as_ref().clone())), body)?.into(),
        ),
    };
    Ok(Type {
        info: ty.span(),
        node,
    })
}

trait TypeVarMapper<J> {
    fn on_var(&mut self, info: &J, depth: usize, index: Index) -> Type<J>;
}

fn map_type_var<J: Clone>(ty: &Type<J>, mapper: &mut impl TypeVarMapper<J>) -> Type<J> {
    fn rec<J: Clone>(ty: &Type<J>, mapper: &mut impl TypeVarMapper<J>, depth: usize) -> Type<J> {
        let node = match &ty.node {
            TypeNode::Bot => TypeNode::Bot,
            TypeNode::Top => TypeNode::Top,
            TypeNode::Unit => TypeNode::Unit,
            TypeNode::Bool => TypeNode::Bool,
            TypeNode::Nat => TypeNode::Nat,
            TypeNode::Record(entries) => TypeNode::Record(
                entries
                    .iter()
                    .map(|(k, v)| (k.clone(), rec(v, mapper, depth).into()))
                    .collect(),
            ),
            TypeNode::Arrow(lhs, rhs) => TypeNode::Arrow(
                rec(lhs, mapper, depth).into(),
                rec(rhs, mapper, depth).into(),
            ),
            TypeNode::Variable(i) => return mapper.on_var(&ty.info, depth, *i),
            TypeNode::Abstract(body) => TypeNode::Abstract(rec(body, mapper, depth + 1).into()),
            TypeNode::Apply(lhs, rhs) => TypeNode::Apply(
                rec(lhs, mapper, depth).into(),
                rec(rhs, mapper, depth).into(),
            ),
            TypeNode::Exists(body) => TypeNode::Exists(rec(body, mapper, depth + 1).into()),
            TypeNode::Forall(body) => TypeNode::Forall(rec(body, mapper, depth + 1).into()),
        };
        Type {
            info: ty.info.clone(),
            node,
        }
    }
    rec(ty, mapper, 0)
}
fn shift_type<J: Clone>(diff: isize, ty: &Type<J>) -> Type<J> {
    struct M(isize);
    impl<'a, J: Clone> TypeVarMapper<J> for M {
        fn on_var(&mut self, info: &J, depth: usize, index: Index) -> Type<J> {
            let new_index = if index >= depth {
                (index as isize + self.0) as usize
            } else {
                index
            };
            Type {
                info: info.clone(),
                node: TypeNode::Variable(new_index),
            }
        }
    }
    map_type_var(ty, &mut M(diff))
}
fn replace_top_type<J: Clone>(ty: &Type<J>, replacement: &Type<J>) -> Type<J> {
    struct M<'a, J>(&'a Type<J>);
    impl<'a, J: Clone> TypeVarMapper<J> for M<'a, J> {
        fn on_var(&mut self, info: &J, depth: usize, index: Index) -> Type<J> {
            if depth == index {
                return self.0.clone();
            }
            let new_index = if depth < index { index - 1 } else { index };
            Type {
                info: info.clone(),
                node: TypeNode::Variable(new_index),
            }
        }
    }
    map_type_var(ty, &mut M(replacement))
}
fn substitute_top_type<J: Clone>(ty: &Type<J>, replacement: &Type<J>) -> Type<J> {
    shift_type(-1, &replace_top_type(ty, &shift_type(1, replacement)))
}

type TypeSpanedTerm = Term<(Type<()>, Span)>;
fn compile_term(
    context: &(impl TermContext<()> + TypeContext),
    term: &Spanned<lang::Term>,
) -> Result<TypeSpanedTerm> {
    let (ty, node) = match term.as_ref() {
        lang::Term::Unit => (TypeNode::Unit, TermNode::Unit),
        lang::Term::Bool(v) => (TypeNode::Bool, TermNode::Bool(*v)),
        lang::Term::Nat(v) => (TypeNode::Nat, TermNode::Nat(*v)),
        lang::Term::Record(entries) => {
            let entries = entries
                .iter()
                .map(|(k, v)| Ok((k.value().clone(), compile_term(context, v)?.into())))
                .collect::<Result<Vec<(_, Rc<Term<_>>)>>>()?;
            let ty = TypeNode::Record(
                entries
                    .iter()
                    .map(|(k, v)| (k.clone(), v.info.0.clone().into()))
                    .collect(),
            );
            let node = TermNode::Record(entries);
            (ty, node)
        }
        lang::Term::Access(term, key) => {
            let inner = Rc::new(compile_term(context, term)?);
            // TODO: realize type
            if let TypeNode::Record(entries) = &inner.info.0.node {
                if let Some(ty) = entries
                    .iter()
                    .find_map(|(k, ty)| (k == key.value()).then(|| ty))
                {
                    (
                        ty.node.clone(),
                        TermNode::Access(inner, key.value().clone()),
                    )
                } else {
                    return Err(Error::custom(
                        term.span(),
                        format!(
                            "Expected a record type that has key {key} but was {}",
                            inner.info.0
                        ),
                    ));
                }
            } else {
                return Err(Error::custom(
                    term.span(),
                    format!("Expected a record type but was {}", inner.info.0),
                ));
            }
        }
        lang::Term::Variable(name) => {
            if let Some((i, ty)) = context.lookup_variable(name.as_ref()) {
                (ty.node.clone(), TermNode::Variable(i))
            } else {
                return Err(Error::custom(
                    term.span(),
                    format!("Encounter a free variable {name}"),
                ));
            }
        }
        lang::Term::Abstract(name, ty, body) => {
            let ty: Rc<_> = compile_type(context, ty)?.forget().into();
            let body = compile_term(
                &context.term_pushed(name.as_ref().map(Spanned::value).cloned(), ty.clone()),
                body,
            )?;
            (
                TypeNode::Arrow(ty.into(), body.info.0.clone().into()),
                TermNode::Abstract(body.into()),
            )
        }
        lang::Term::Apply(lhs, rhs) => {
            let lhs = compile_term(context, lhs)?;
            let ltype = &lhs.info.0;
            let rhs = compile_term(context, rhs)?;
            let rtype = &rhs.info.0;
            // TODO: realize type
            if let TypeNode::Arrow(dom, codom) = &ltype.node {
                // TODO: subtype
                if dom.as_ref() == rtype {
                    (codom.node.clone(), TermNode::Apply(lhs.into(), rhs.into()))
                } else {
                    return Err(Error::expected_input_found(
                        rhs.info.1,
                        std::iter::once(Some(format!("{codom}"))),
                        Some(format!("{rtype}")),
                    ));
                }
            } else {
                return Err(Error::expected_input_found(
                    lhs.info.1,
                    std::iter::once(Some("Arrow type".to_string())),
                    Some(format!("{ltype}")),
                ));
            }
        }
        lang::Term::Ascribe(body, ty) => {
            let body = compile_term(context, body)?;
            let ty = compile_type(context, ty)?.forget();
            // TODO: subtype
            if body.info.0 == ty {
                // We eliminate the ascription in the compile time
                (ty.node.clone(), body.node)
            } else {
                return Err(Error::expected_input_found(
                    body.info.1,
                    std::iter::once(Some(format!("{ty}"))),
                    Some(format!("{}", body.info.0)),
                ));
            }
        }
        lang::Term::Pack {
            inner_type,
            body,
            exposed_type,
        } => {
            let inner_type = compile_type(context, inner_type)?.forget();
            let body = compile_term(context, body)?;
            let exposed = compile_type(context, exposed_type)?.forget();
            // TODO: realize type
            if let TypeNode::Exists(exposed_inner) = &exposed.node {
                let exposed_actual = substitute_top_type(exposed_inner, &body.info.0.forget());
                // TODO: subtype?
                if inner_type != exposed_actual {
                    return Err(Error::expected_input_found(
                        exposed_type.span.clone(),
                        std::iter::once(Some(format!("{exposed_type}"))),
                        Some(format!("{inner_type}")),
                    ));
                }
                (exposed.node, TermNode::Pack(body.into()))
            } else {
                return Err(Error::expected_input_found(
                    exposed_type.span.clone(),
                    std::iter::once(Some(format!("Existential type"))),
                    Some(format!("{exposed_type}")),
                ));
            }
        }
        lang::Term::Unpack { ty, var, arg, body } => {
            let arg = compile_term(context, arg)?;
            // TODO: realize type
            if matches!(arg.info.0.node, TypeNode::Exists(_)) {
                let body = compile_term(
                    &context
                        .term_pushed(Some(var.value().clone()), arg.info.0.clone().into())
                        .type_pushed(Some(ty.value().clone())),
                    body,
                )?;
                (
                    body.info.0.node.clone(),
                    TermNode::Unpack(arg.into(), body.into()),
                )
            } else {
                return Err(Error::expected_input_found(
                    arg.info.1,
                    std::iter::once(Some(format!("Existential type"))),
                    Some(format!("{}", arg.info.0)),
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
                    value: rhs.into(),
                }
                .into(),
                lhs.clone().into(),
            );
            return compile_term(
                context,
                &Spanned {
                    span: term.span(),
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
            if cond.info.0.node != TypeNode::Bool {
                return Err(Error::expected_input_found(
                    cond.info.1,
                    std::iter::once(Some(format!("Bool"))),
                    Some(format!("{}", cond.info.0)),
                ));
            }
            // TODO: join type
            if positive.info.0 != negative.info.0 {
                return Err(Error::custom(
                    term.span(),
                    format!(
                        "Mismatch type of positive clause {} and negative clause {}",
                        positive.info.0, negative.info.0
                    ),
                ));
            }
            (
                positive.info.0.node.clone(),
                TermNode::If {
                    cond: cond.into(),
                    positive: positive.into(),
                    negative: negative.into(),
                },
            )
        }
        lang::Term::Let { var, arg, body } => {
            let arg = compile_term(context, arg)?;
            let body = compile_term(
                &context.term_pushed(
                    var.as_ref().map(Spanned::value).cloned(),
                    arg.info.0.clone().into(),
                ),
                body,
            )?;
            (
                body.info.0.node.clone(),
                TermNode::Let {
                    arg: arg.into(),
                    body: body.into(),
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
                span: term.span.clone(),
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
            (TypeNode::Forall(body.info.0.into()), body.node)
        }
        lang::Term::TypeApply(body, ty) => {
            let body = compile_term(context, body)?;
            let ty = compile_type(context, ty)?.forget();
            if let TypeNode::Forall(inner) = &body.info.0.node {
                let new_ty = substitute_top_type(&inner, &ty);
                (new_ty.node, body.node)
            } else {
                return Err(Error::expected_input_found(
                    body.info.1,
                    std::iter::once(Some(format!("Forall type"))),
                    Some(format!("{}", body.info.0)),
                ));
            }
        }
        lang::Term::Fix(body) => {
            let body_span = &body.span;
            let body = compile_term(context, body)?;
            // TODO: realize type
            if let TypeNode::Apply(lhs, rhs) = &body.info.0.node {
                // TODO: subtype
                if lhs == rhs {
                    (lhs.node.clone(), TermNode::Fix(body.into()).into())
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
                    std::iter::once(Some(format!("arrow type"))),
                    Some(format!("{}", body.info.0)),
                ));
            }
        }
        lang::Term::Func(func) => {
            fn arrow(from: TypeNode<()>, to: TypeNode<()>) -> TypeNode<()> {
                TypeNode::Arrow(
                    Type {
                        info: (),
                        node: from,
                    }
                    .into(),
                    Type { info: (), node: to }.into(),
                )
            }
            let (ty, func) = match func.value {
                lang::Func::Succ => (arrow(TypeNode::Nat, TypeNode::Nat), Func::Succ),
                lang::Func::Pred => (arrow(TypeNode::Nat, TypeNode::Nat), Func::Pred),
                lang::Func::IsZero => (arrow(TypeNode::Nat, TypeNode::Bool), Func::IsZero),
            };
            (ty, TermNode::Func(func))
        }
    };
    Ok(Term {
        info: (Type { info: (), node: ty }, term.span()),
        node,
    })
}

pub fn compile(term: &Spanned<lang::Term>) -> Result<Term<()>> {
    let context = Context::default();
    compile_term(&context, term).map(|t| t.forget())
}

pub fn get_type(term: &Spanned<lang::Term>) -> Result<Type<()>> {
    let context = Context::default();
    compile_term(&context, term).map(|t| t.info.0)
}
