use std::rc::Rc;

use rpds::{HashTrieMap, Stack};

use crate::{lang, prelude::*, term::*};

#[derive(Clone, derive_more::Display, Debug)]
enum Binding {
    #[display(fmt = "Type({_0})")]
    Type(Identifier),
    #[display(fmt = "Variable({_0:?}, {_1})")]
    Variable(Option<Identifier>, Rc<Type>),
}
#[derive(Default, Clone, derive_more::Display, Debug)]
#[display(
    fmt = "{{bindings={bindings}, type_aliases={type_aliases}, term_aliases={term_aliases:?}}}"
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

    fn lookup_type_variable(&self, name: impl AsRef<Identifier>) -> Option<Index> {
        self.bindings
            .iter()
            .filter_map(|b| {
                if let Binding::Type(ty) = b {
                    Some(ty)
                } else {
                    None
                }
            })
            .enumerate()
            .find_map(|(i, n)| (n == name.as_ref()).then(|| i))
    }
    fn lookup_type_alias(&self, name: impl AsRef<Identifier>) -> Option<Rc<Type>> {
        self.type_aliases.get(name.as_ref()).cloned()
    }
    fn type_pushed(&self, name: Identifier) -> Self {
        let mut ret = self.clone();
        ret.bindings = ret.bindings.push(Binding::Type(name));
        ret
    }

    fn lookup_variable(&self, name: impl AsRef<Identifier>) -> Option<(Index, Type)> {
        let mut type_shift = 0;
        let mut var_depth = 0;
        for binding in &self.bindings {
            match binding {
                Binding::Type(_) => type_shift += 1,
                Binding::Variable(Some(n), ty) if n == name.as_ref() => {
                    return Some((var_depth, shift_type(type_shift, ty).unwrap()))
                }
                Binding::Variable(_, _) => var_depth += 1,
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

pub fn compile_type(context: &Context, ty: &Spanned<lang::Type>) -> Result<Spanned<Type>> {
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
            if let Some(i) = context.lookup_type_variable(name) {
                Type::Variable(i)
            } else if let Some(ty) = context.lookup_type_alias(name) {
                ty.as_ref().clone()
            } else {
                return Err(Error::custom(
                    ty.span(),
                    format!("Found a free type {name}"),
                ));
            }
        }
        lang::Type::Abstract(var, body) => Type::Abstract(
            compile_type(&context.type_pushed(var.as_ref().clone()), body)?
                .forget_span()
                .into(),
        ),
        lang::Type::Apply(lhs, rhs) => {
            let lhs = compile_type(context, lhs)?;
            let rhs = compile_type(context, rhs)?;
            if let Type::Abstract(lhs) = lhs.value() {
                // TODO: Fix shifting
                apply_top_type(lhs.as_ref(), rhs.as_ref())
            } else {
                return Err(Error::expected_input_found(
                    lhs.span(),
                    std::iter::once(Some("Type abstraction".into())),
                    Some(format!("{lhs}")),
                ));
            }
        }
        lang::Type::Exists(ident, body) => Type::Exists(
            compile_type(&context.type_pushed(ident.as_ref().clone()), body)?
                .forget_span()
                .into(),
        ),
        lang::Type::Forall(ident, body) => Type::Forall(
            compile_type(&context.type_pushed(ident.as_ref().clone()), body)?
                .forget_span()
                .into(),
        ),
    };
    Ok(Spanned {
        span: ty.span(),
        value,
    })
}

trait TypeVarMapper<E> {
    fn on_var(&mut self, depth: usize, index: Index) -> Result<Type, E>;
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
            Type::Variable(i) => mapper.on_var(depth, *i)?,
            Type::Abstract(body) => Type::Abstract(rec(body, mapper, depth + 1)?.into()),
            Type::Exists(body) => Type::Exists(rec(body, mapper, depth + 1)?.into()),
            Type::Forall(body) => Type::Forall(rec(body, mapper, depth + 1)?.into()),
        })
    }
    rec(ty, mapper, 0)
}

#[derive(Debug)]
struct ShiftFail;
fn shift_type(diff: isize, ty: &Type) -> Result<Type, ShiftFail> {
    struct M(isize);
    impl TypeVarMapper<ShiftFail> for M {
        fn on_var(&mut self, depth: usize, index: Index) -> Result<Type, ShiftFail> {
            let new_index = if index >= depth {
                usize::try_from(index as isize + self.0).map_err(|_| ShiftFail)?
            } else {
                index
            };
            Ok(Type::Variable(new_index))
        }
    }
    map_type_var(ty, &mut M(diff))
}
fn substitute_top_type(base: &Type, replacement: &Type) -> Type {
    // TODO: Use never type once stabilized
    type Never = ();
    struct M<'a>(&'a Type);
    impl<'a> TypeVarMapper<Never> for M<'a> {
        fn on_var(&mut self, depth: usize, index: Index) -> Result<Type, Never> {
            if depth == index {
                return Ok(
                    shift_type(1 + depth as isize, self.0).expect("Positive shift shouldn't fail")
                );
            }
            Ok(Type::Variable(index))
        }
    }
    map_type_var(base, &mut M(replacement)).expect("Shouldn't fail")
}
fn apply_top_type(body: &Type, arg: &Type) -> Type {
    shift_type(-1, &substitute_top_type(body, arg)).expect("Apply shouldn't fail")
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
                        std::iter::once(Some(format!("{dom}"))),
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
                let exposed_actual = apply_top_type(exposed_inner, &inner_type);
                // TODO: subtype?
                if body.ty != exposed_actual {
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
            if let Type::Exists(arg_inner) = arg.ty {
                let body = compile_term(
                    &context
                        .type_pushed(ty.value().clone())
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
            // wrap with lambda so that the type abstract doesn't get evaluated until it get the
            // type argument passed.
            let body = compile_term(
                &context
                    .type_pushed(name.value.clone())
                    .term_pushed(None, Type::Unit.into()),
                body,
            )?;
            let wrapped = Term::Abstract(body.term.into());
            (Type::Forall(body.ty.into()), wrapped)
        }
        lang::Term::TypeApply(body, ty) => {
            let body = compile_term(context, body)?;
            let ty = compile_type(context, ty)?.forget_span();
            // TODO: realize type
            if let Type::Forall(inner) = &body.ty {
                let new_ty = apply_top_type(inner, &ty);
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
