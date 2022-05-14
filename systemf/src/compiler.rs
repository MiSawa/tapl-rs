use std::rc::Rc;

use rpds::{HashTrieMap, Stack};

use crate::{lang, prelude::*, term::*};

#[derive(Clone, derive_more::Display, Debug)]
enum Binding {
    #[display(fmt = "Type({_0}{_1})")]
    Type(Identifier, Rc<Bound>),
    #[display(fmt = "Variable({_0:?}, {_1})")]
    Variable(Option<Identifier>, Rc<Type>),
}
#[derive(Default, Clone, derive_more::Display, Debug)]
#[display(
    fmt = "{{bindings={bindings}, type_aliases={type_aliases:?}, term_aliases={term_aliases:?}}}"
)]
pub struct Context {
    bindings: Stack<Binding>,
    type_aliases: HashTrieMap<Identifier, Rc<Type>>,
    term_aliases: HashTrieMap<Identifier, (Rc<Term>, Rc<Type>)>,
}
impl Context {
    pub fn add_type_alias(&mut self, name: Identifier, ty: Type) {
        self.type_aliases = self.type_aliases.insert(name, ty.into());
    }
    pub fn add_term_alias(&mut self, name: Identifier, term: Term, ty: Type) {
        self.term_aliases = self.term_aliases.insert(name, (term.into(), ty.into()));
    }

    fn lookup_type_variable(&self, name: impl AsRef<Identifier>) -> Option<(Index, Rc<Bound>)> {
        self.bindings
            .iter()
            .filter_map(|b| {
                if let Binding::Type(ty, bound) = b {
                    Some((ty, bound))
                } else {
                    None
                }
            })
            .enumerate()
            .find_map(|(i, (n, bound))| (n == name.as_ref()).then(|| (i, bound.clone())))
    }
    fn lookup_type_alias(&self, name: impl AsRef<Identifier>) -> Option<Rc<Type>> {
        self.type_aliases.get(name.as_ref()).cloned() // TODO: Kind
    }
    fn type_pushed(&self, name: Identifier, bound: Rc<Bound>) -> Self {
        let mut ret = self.clone();
        ret.bindings = ret.bindings.push(Binding::Type(name, bound));
        ret
    }

    fn lookup_variable(&self, name: impl AsRef<Identifier>) -> Option<(Index, Type)> {
        let mut type_shift = 0;
        let mut var_depth = 0;
        for binding in &self.bindings {
            match binding {
                Binding::Type(..) => type_shift += 1,
                Binding::Variable(Some(n), ty) if n == name.as_ref() => {
                    return Some((var_depth, shift_type(type_shift, ty).unwrap()))
                }
                Binding::Variable(..) => var_depth += 1,
            }
        }
        None
    }
    fn lookup_term_alias(&self, name: impl AsRef<Identifier>) -> Option<(Rc<Term>, Rc<Type>)> {
        self.term_aliases.get(name.as_ref()).cloned()
    }
    fn term_pushed(&self, name: Option<Identifier>, ty: Rc<Type>) -> Self {
        let mut ret = self.clone();
        ret.bindings = ret.bindings.push(Binding::Variable(name, ty));
        ret
    }
}

fn compile_kind(kind: &Spanned<lang::Kind>) -> Spanned<Kind> {
    let k = match kind.as_ref() {
        lang::Kind::Star => Kind::Star,
        lang::Kind::Arrow(lhs, rhs) => Kind::Arrow(
            compile_kind(lhs).forget_span().into(),
            compile_kind(rhs).forget_span().into(),
        ),
    };
    Spanned {
        value: k,
        span: kind.span(),
    }
}

fn compile_type_bound(context: &Context, type_bound: &lang::TypeBound) -> Result<Bound> {
    Ok(match type_bound {
        lang::TypeBound::Unbounded => Bound::Unbounded,
        lang::TypeBound::Type(ty) => Bound::Type(compile_type(context, ty)?.ty.into()),
        lang::TypeBound::Kind(kind) => Bound::Kind(compile_kind(kind).forget_span().into()),
    })
}

fn get_kind(context: &Context, ty: &Type) -> Kind {
    match ty {
        Type::Bot
        | Type::Top
        | Type::Unit
        | Type::Bool
        | Type::Nat
        | Type::Record(_)
        | Type::Arrow(_, _) => Kind::Star,
        Type::Variable { bound, .. } => match bound.as_ref() {
            Bound::Unbounded | Bound::Type(_) => Kind::Star,
            Bound::Kind(kind) => kind.as_ref().clone(),
        },
        Type::Abstract { body, arg_kind } => {
            Kind::Arrow(arg_kind.clone(), get_kind(context, body).into())
        }
        Type::Exists { .. } | Type::Forall { .. } => Kind::Star,
    }
}

fn check_bound(context: &Context, ty: &TypeExtra, bound: &Bound) -> Result<(), String> {
    match &bound {
        Bound::Unbounded => Ok(()),
        Bound::Type(bound_ty) => check_subtype(context, &ty.ty, bound_ty),
        Bound::Kind(k) if k.as_ref() == &ty.kind => Ok(()),
        Bound::Kind(k) => Err(format!("Expected kind {} but got {}", k, ty.kind)),
    }
}

pub struct TypeExtra {
    pub span: Span,
    pub kind: Kind,
    pub ty: Type,
}

impl TypeExtra {
    fn check_star(self) -> Result<Type> {
        match &self.kind {
            Kind::Star => Ok(self.ty),
            Kind::Arrow(..) => Err(Error::expected_input_found(
                self.span,
                std::iter::once(Some(format!("Star kind"))),
                Some(format!("{}", self.kind)),
            )),
        }
    }
}

pub fn compile_type(context: &Context, ty: &Spanned<lang::Type>) -> Result<TypeExtra> {
    let (kind, value) = match ty.as_ref() {
        lang::Type::Bot => (Kind::Star, Type::Bot),
        lang::Type::Top => (Kind::Star, Type::Top),
        lang::Type::Unit => (Kind::Star, Type::Unit),
        lang::Type::Bool => (Kind::Star, Type::Bool),
        lang::Type::Nat => (Kind::Star, Type::Nat),
        lang::Type::Record(entries) => (
            Kind::Star,
            Type::Record(
                entries
                    .iter()
                    .map(|(k, v)| {
                        Ok((
                            k.value().clone(),
                            compile_type(context, v)?.check_star()?.into(),
                        ))
                    })
                    .collect::<Result<_>>()?,
            ),
        ),
        lang::Type::Arrow(lhs, rhs) => (
            Kind::Star,
            Type::Arrow(
                compile_type(context, lhs)?.check_star()?.into(),
                compile_type(context, rhs)?.check_star()?.into(),
            ),
        ),
        lang::Type::Variable(name) => {
            if let Some((index, bound)) = context.lookup_type_variable(name) {
                (bound.get_kind().clone(), Type::Variable { index, bound })
            } else if let Some(ty) = context.lookup_type_alias(name) {
                // TODO: kind
                (Kind::Star, ty.as_ref().clone())
            } else {
                return Err(Error::custom(
                    ty.span(),
                    format!("Found a free type {name}"),
                ));
            }
        }
        lang::Type::Abstract(var, kind, body) => {
            let arg_kind: Rc<_> = kind
                .as_ref()
                .map(|k| compile_kind(k).forget_span())
                .unwrap_or(Kind::Star)
                .into();
            let body = compile_type(
                &context.type_pushed(var.as_ref().clone(), Bound::Kind(arg_kind.clone()).into()),
                body,
            )?;
            let whole_kind = Kind::Arrow(arg_kind.clone(), body.kind.into());
            (
                whole_kind,
                Type::Abstract {
                    body: body.ty.into(),
                    arg_kind: arg_kind.into(),
                },
            )
        }
        lang::Type::Apply(lhs, rhs) => {
            let lhs = compile_type(context, lhs)?;
            let rhs = compile_type(context, rhs)?;
            let ret_kind = if let Kind::Arrow(arg, res) = lhs.kind {
                if arg.as_ref() == &rhs.kind {
                    res.as_ref().clone()
                } else {
                    return Err(Error::expected_input_found(
                        rhs.span,
                        std::iter::once(Some(format!("{arg}"))),
                        Some(format!("{}", rhs.kind)),
                    ));
                }
            } else {
                return Err(Error::expected_input_found(
                    rhs.span,
                    std::iter::once(Some("Arrow kind".to_string())),
                    Some(format!("{}", lhs.kind)),
                ));
            };
            if let Type::Abstract {
                body: lhs,
                arg_kind,
            } = lhs.ty
            {
                if let Err(_) = check_bound(context, &rhs, &Bound::Kind(arg_kind.clone())) {
                    return Err(Error::expected_input_found(
                        rhs.span,
                        std::iter::once(Some(format!("{}", arg_kind))),
                        Some(format!("{}", rhs.kind)),
                    ));
                }
                (ret_kind, apply_top_type(lhs.as_ref(), &rhs.ty))
            } else {
                return Err(Error::expected_input_found(
                    lhs.span,
                    std::iter::once(Some("Type abstraction".into())),
                    Some(format!("{}", lhs.ty)),
                ));
            }
        }
        lang::Type::Exists(ident, bound, body) => {
            let bound: Rc<_> = compile_type_bound(context, bound.value())?.into();
            (
                Kind::Star,
                Type::Exists {
                    bound: bound.clone(),
                    body: compile_type(&context.type_pushed(ident.as_ref().clone(), bound), body)?
                        .check_star()?
                        .into(),
                },
            )
        }
        lang::Type::Forall(ident, bound, body) => {
            let bound: Rc<_> = compile_type_bound(context, bound.value())?.into();
            (
                Kind::Star,
                Type::Forall {
                    bound: bound.clone(),
                    body: compile_type(&context.type_pushed(ident.as_ref().clone(), bound), body)?
                        .check_star()?
                        .into(),
                },
            )
        }
    };
    Ok(TypeExtra {
        span: ty.span(),
        kind,
        ty: value,
    })
}

trait TypeVarMapper<E> {
    fn on_var(&mut self, depth: usize, index: Index, bound: &Rc<Bound>) -> Result<Type, E>;
}

fn map_type_var<E>(ty: &Type, mapper: &mut impl TypeVarMapper<E>) -> Result<Type, E> {
    fn rec<E>(ty: &Type, mapper: &mut impl TypeVarMapper<E>, depth: usize) -> Result<Type, E> {
        Ok(match ty {
            Type::Bot => Type::Bot,
            Type::Top => Type::Top,
            Type::Unit => Type::Unit,
            Type::Bool => Type::Bool,
            Type::Nat => Type::Nat,
            Type::Record(entries) => Type::Record(
                entries
                    .iter()
                    .map::<Result<_, _>, _>(|(k, v)| Ok((k.clone(), rec(v, mapper, depth)?.into())))
                    .collect::<Result<_, _>>()?,
            ),
            Type::Arrow(lhs, rhs) => Type::Arrow(
                rec(lhs, mapper, depth)?.into(),
                rec(rhs, mapper, depth)?.into(),
            ),
            Type::Variable { index, bound } => mapper.on_var(depth, *index, bound)?,
            Type::Abstract { body, arg_kind } => Type::Abstract {
                body: rec(body, mapper, depth + 1)?.into(),
                arg_kind: arg_kind.clone(),
            },
            Type::Exists { bound, body } => Type::Exists {
                bound: bound.clone(),
                body: rec(body, mapper, depth + 1)?.into(),
            },
            Type::Forall { bound, body } => Type::Forall {
                bound: bound.clone(),
                body: rec(body, mapper, depth + 1)?.into(),
            },
        })
    }
    rec(ty, mapper, 0)
}

#[derive(Debug)]
struct ShiftFail;
fn shift_type(diff: isize, ty: &Type) -> Result<Type, ShiftFail> {
    struct M(isize);
    impl TypeVarMapper<ShiftFail> for M {
        fn on_var(
            &mut self,
            depth: usize,
            index: Index,
            bound: &Rc<Bound>,
        ) -> Result<Type, ShiftFail> {
            let new_index = if index >= depth {
                usize::try_from(index as isize + self.0).map_err(|_| ShiftFail)?
            } else {
                index
            };
            Ok(Type::Variable {
                index: new_index,
                bound: bound.clone(),
            })
        }
    }
    map_type_var(ty, &mut M(diff))
}
fn substitute_top_type(base: &Type, replacement: &Type) -> Type {
    // TODO: Use never type once stabilized
    type Never = ();
    struct M<'a>(&'a Type);
    impl<'a> TypeVarMapper<Never> for M<'a> {
        fn on_var(&mut self, depth: usize, index: Index, bound: &Rc<Bound>) -> Result<Type, Never> {
            if depth == index {
                return Ok(
                    shift_type(1 + depth as isize, self.0).expect("Positive shift shouldn't fail")
                );
            }
            Ok(Type::Variable {
                index,
                bound: bound.clone(),
            })
        }
    }
    map_type_var(base, &mut M(replacement)).expect("Shouldn't fail")
}
fn apply_top_type(body: &Type, arg: &Type) -> Type {
    shift_type(-1, &substitute_top_type(body, arg)).expect("Apply shouldn't fail")
}
fn join_type(_context: &Context, lhs: &Type, rhs: &Type) -> Type {
    if lhs == rhs {
        lhs.clone()
    } else {
        Type::Top
    }
}
fn meet_type(_context: &Context, lhs: &Type, rhs: &Type) -> Type {
    if lhs == rhs {
        lhs.clone()
    } else {
        Type::Bot
    }
}
fn check_subtype(_context: &Context, sub: &Type, sup: &Type) -> Result<(), String> {
    if sub == sup {
        Ok(())
    } else {
        Err("Subtype is currently not supported".to_string())
    }
}
fn expose_type(_context: &Context, ty: &Type) -> Type {
    ty.clone()
}

pub struct TypeSpannedTerm {
    pub span: Span,
    pub ty: Type,
    pub term: Term,
}

pub fn compile_term(context: &Context, original: &Spanned<lang::Term>) -> Result<TypeSpannedTerm> {
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
            if let Type::Record(entries) = expose_type(context, &inner.ty) {
                if let Some(ty) = entries
                    .into_iter()
                    .find_map(|(k, ty)| (&k == key.value()).then(|| ty))
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
            if let Some((i, ty)) = context.lookup_variable(name) {
                (ty, Term::Variable(i))
            } else if let Some((term, ty)) = context.lookup_term_alias(name) {
                (ty.as_ref().clone(), term.as_ref().clone())
            } else {
                return Err(Error::custom(
                    original.span(),
                    format!("Encounter a free variable {name}"),
                ));
            }
        }
        lang::Term::Abstract(name, ty, body) => {
            let ty: Rc<_> = compile_type(context, ty)?.ty.into();
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
            if let Type::Arrow(dom, codom) = expose_type(context, &lhs.ty) {
                match check_subtype(context, rtype, &dom) {
                    Ok(_) => (
                        (*codom).clone(),
                        Term::Apply(lhs.term.into(), rhs.term.into()),
                    ),
                    Err(msg) => {
                        return Err(Error::custom(
                            rhs.span,
                            format!(
                                "Type mismatch: {msg}. Expected a subtype of {dom} but was {rtype}"
                            ),
                        ));
                    }
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
            let ty = compile_type(context, ty)?.ty;
            match check_subtype(context, &body.ty, &ty) {
                Ok(_) => {
                    // We eliminate the ascription in the compile time
                    (ty, body.term)
                }
                Err(msg) => {
                    return Err(Error::custom(
                        body.span,
                        format!(
                            "Type mismatch: {msg}. Expected a subtype of {ty} but was {}",
                            body.ty
                        ),
                    ));
                }
            }
        }
        lang::Term::Pack {
            inner_type,
            body,
            exposed_type,
        } => {
            let inner_type = compile_type(context, inner_type)?;
            let body = compile_term(context, body)?;
            let exposed = compile_type(context, exposed_type)?.ty;
            if let Type::Exists {
                bound,
                body: exposed_inner,
            } = expose_type(context, &exposed)
            {
                let exposed_actual = apply_top_type(&exposed_inner, &inner_type.ty);
                if let Err(msg) = check_bound(context, &inner_type, bound.as_ref()) {
                    return Err(Error::custom(
                        inner_type.span,
                        format!("Bounding error: {msg}"),
                    ));
                }
                match check_subtype(context, &body.ty, &exposed_actual) {
                    Ok(_) => (exposed, Term::Pack(body.term.into())),
                    Err(msg) => {
                        return Err(Error::custom(
                            exposed_type.span(),
                            format!(
                                "Type mismatch: {msg}. Expected a supertype of {} but was {}",
                                inner_type.ty, exposed_type
                            ),
                        ));
                    }
                }
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
            if let Type::Exists {
                bound,
                body: arg_inner,
            } = expose_type(context, &arg.ty)
            {
                let body = compile_term(
                    &context
                        .type_pushed(ty.value().clone(), bound)
                        .term_pushed(Some(var.value().clone()), arg_inner),
                    body,
                )?;
                let body_ty = shift_type(-1, &body.ty).map_err(|_| {
                    Error::custom(
                        body.span,
                        format!(
                            "Scoping error: The type of unpack body {} contains the package type",
                            body.ty
                        ),
                    )
                })?;
                (body_ty, Term::Unpack(arg.term.into(), body.term.into()))
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
            // TODO: lambda _: Top instead?
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
            if let Err(_) = check_subtype(context, &cond.ty, &Type::Bool) {
                return Err(Error::expected_input_found(
                    cond.span,
                    std::iter::once(Some("Bool".to_string())),
                    Some(format!("{}", cond.ty)),
                ));
            }
            (
                join_type(context, &positive.ty, &negative.ty),
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
        lang::Term::TypeAbstract { var, bound, body } => {
            let bound: Rc<_> = compile_type_bound(context, bound.value())?.into();
            // wrap with lambda so that the type abstract doesn't get evaluated until it get the
            // type argument passed.
            let body = compile_term(
                &context
                    .type_pushed(var.value.clone(), bound.clone())
                    .term_pushed(None, Type::Unit.into()),
                body,
            )?;
            let wrapped = Term::Abstract(body.term.into());
            (
                Type::Forall {
                    bound,
                    body: body.ty.into(),
                },
                wrapped,
            )
        }
        lang::Term::TypeApply(body, ty) => {
            let body = compile_term(context, body)?;
            let ty = compile_type(context, ty)?.ty;
            if let Type::Forall { body: inner, .. } = expose_type(context, &body.ty) {
                // TODO: check kind
                let new_ty = apply_top_type(&inner, &ty);
                // unwrap the lambda introduced in the corresponding TypeAbstract
                let unwrapped = Term::Apply(body.term.into(), Term::Unit.into());
                (new_ty, unwrapped)
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
            if let Type::Arrow(lhs, rhs) = &expose_type(context, &body.ty) {
                match check_subtype(context, rhs, lhs) {
                    Ok(_) => (rhs.as_ref().clone(), Term::Fix(body.term.into())),
                    Err(msg) => {
                        return Err(Error::custom(
                                body_span.clone(),
                                format!(
                                    "Type mismatch: {msg}. Domain of fix {} should be a super type of codomain {}.",
                                    lhs, rhs
                                ),
                        ));
                    }
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
