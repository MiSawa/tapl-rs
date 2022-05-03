use std::{collections::HashMap, rc::Rc};

use crate::parser::{self, Span, Spanned};

type Result<T, E = chumsky::error::Simple<String>> = std::result::Result<T, E>;

#[derive(PartialEq, Eq, Hash, Clone, derive_more::Display)]
pub enum Type {
    #[display(fmt = "Bot")]
    Bot,
    #[display(fmt = "Top")]
    Top,
    #[display(fmt = "Bool")]
    Bool,
    #[display(fmt = "{}", "display_record(_0)")]
    Record(Vec<(Rc<String>, Rc<Type>)>),
    #[display(fmt = "({} -> {})", "_0", "_1")]
    Arrow(Rc<Type>, Rc<Type>),
}

fn display_record<'a>(entries: &'a [(Rc<String>, Rc<Type>)]) -> impl std::fmt::Display + 'a {
    struct Wrapper<'a>(&'a [(Rc<String>, Rc<Type>)]);
    impl<'a> std::fmt::Display for Wrapper<'a> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            f.write_str("{")?;
            let mut first = true;
            for (key, val) in self.0 {
                if first {
                    first = false;
                } else {
                    f.write_str(", ")?;
                }
                f.write_str(key)?;
                f.write_str(":")?;
                std::fmt::Display::fmt(val, f)?;
            }
            f.write_str("}")
        }
    }
    Wrapper(entries)
}

#[derive(PartialEq, Eq, Clone, derive_more::Deref, Debug)]
pub struct ContextTerm<C> {
    context: C,
    #[deref]
    node: Rc<Node<C>>,
}
impl<C> ContextTerm<C> {
    pub fn new(context: C, node: Rc<Node<C>>) -> Self {
        Self { context, node }
    }
}
pub type Term = ContextTerm<()>;
#[derive(PartialEq, Eq, Debug)]
pub enum Node<C> {
    True,
    False,
    Var(usize),
    Abs(ContextTerm<C>),
    App(ContextTerm<C>, ContextTerm<C>),
    Record(Vec<(Rc<String>, ContextTerm<C>)>),
    Project(ContextTerm<C>, Rc<String>),
    If {
        cond: ContextTerm<C>,
        positive: ContextTerm<C>,
        negative: ContextTerm<C>,
    },
}
pub trait ContextTermVisitor<C, T> {
    fn visit_true(&mut self, context: &C) -> T;
    fn visit_false(&mut self, context: &C) -> T;
    fn visit_var(&mut self, context: &C, index: usize) -> T;
    fn visit_abs(&mut self, context: &C, body: &ContextTerm<C>) -> T;
    fn visit_app(&mut self, context: &C, lhs: &ContextTerm<C>, rhs: &ContextTerm<C>) -> T;
    fn visit_record(&mut self, context: &C, entries: &[(Rc<String>, ContextTerm<C>)]) -> T;
    fn visit_project(&mut self, context: &C, term: &ContextTerm<C>, key: Rc<String>) -> T;
    fn visit_if(
        &mut self,
        context: &C,
        cond: &ContextTerm<C>,
        positive: &ContextTerm<C>,
        negative: &ContextTerm<C>,
    ) -> T;
}
impl<C> ContextTerm<C> {
    pub fn accept<T>(&self, visitor: &mut impl ContextTermVisitor<C, T>) -> T {
        match self.node.as_ref() {
            Node::True => visitor.visit_true(&self.context),
            Node::False => visitor.visit_false(&self.context),
            Node::Var(index) => visitor.visit_var(&self.context, *index),
            Node::Abs(body) => visitor.visit_abs(&self.context, body),
            Node::App(lhs, rhs) => visitor.visit_app(&self.context, lhs, rhs),
            Node::Record(entries) => visitor.visit_record(&self.context, entries),
            Node::Project(term, key) => visitor.visit_project(&self.context, term, key.clone()),
            Node::If {
                cond,
                positive,
                negative,
            } => visitor.visit_if(&self.context, cond, positive, negative),
        }
    }

    pub fn map_context<D>(&self, f: impl FnMut(&C) -> D) -> ContextTerm<D> {
        struct V<C, D, F>(F, std::marker::PhantomData<(C, D)>);
        impl<C, D, F: FnMut(&C) -> D> ContextTermVisitor<C, ContextTerm<D>> for V<C, D, F> {
            fn visit_true(&mut self, context: &C) -> ContextTerm<D> {
                ContextTerm::new(self.0(context), Node::True.into())
            }

            fn visit_false(&mut self, context: &C) -> ContextTerm<D> {
                ContextTerm::new(self.0(context), Node::False.into())
            }

            fn visit_var(&mut self, context: &C, index: usize) -> ContextTerm<D> {
                ContextTerm::new(self.0(context), Node::Var(index).into())
            }

            fn visit_abs(&mut self, context: &C, body: &ContextTerm<C>) -> ContextTerm<D> {
                ContextTerm::new(self.0(context), Node::Abs(body.accept(self)).into())
            }

            fn visit_app(
                &mut self,
                context: &C,
                lhs: &ContextTerm<C>,
                rhs: &ContextTerm<C>,
            ) -> ContextTerm<D> {
                ContextTerm::new(
                    self.0(context),
                    Node::App(lhs.accept(self), rhs.accept(self)).into(),
                )
            }

            fn visit_record(
                &mut self,
                context: &C,
                entries: &[(Rc<String>, ContextTerm<C>)],
            ) -> ContextTerm<D> {
                ContextTerm::new(
                    self.0(context),
                    Node::Record(
                        entries
                            .iter()
                            .map(|(key, val)| (key.clone(), val.accept(self)))
                            .collect(),
                    )
                    .into(),
                )
            }

            fn visit_project(
                &mut self,
                context: &C,
                term: &ContextTerm<C>,
                key: Rc<String>,
            ) -> ContextTerm<D> {
                ContextTerm::new(
                    self.0(context),
                    Node::Project(term.accept(self), key.clone()).into(),
                )
            }

            fn visit_if(
                &mut self,
                context: &C,
                cond: &ContextTerm<C>,
                positive: &ContextTerm<C>,
                negative: &ContextTerm<C>,
            ) -> ContextTerm<D> {
                ContextTerm::new(
                    self.0(context),
                    Node::If {
                        cond: cond.accept(self),
                        positive: positive.accept(self),
                        negative: negative.accept(self),
                    }
                    .into(),
                )
            }
        }
        self.accept(&mut V(f, std::marker::PhantomData))
    }

    pub fn forget_context(&self) -> Term {
        self.map_context(|_| ())
    }
}

pub trait TermVisitor<T> {
    fn visit_true(&mut self) -> T;
    fn visit_false(&mut self) -> T;
    fn visit_var(&mut self, index: usize) -> T;
    fn visit_abs(&mut self, body: &Term) -> T;
    fn visit_app(&mut self, lhs: &Term, rhs: &Term) -> T;
    fn visit_record(&mut self, entries: &[(Rc<String>, Term)]) -> T;
    fn visit_project(&mut self, term: &Term, key: Rc<String>) -> T;
    fn visit_if(&mut self, cond: &Term, positive: &Term, negative: &Term) -> T;
}

impl<T, V: TermVisitor<T>> ContextTermVisitor<(), T> for V {
    fn visit_true(&mut self, _: &()) -> T {
        self.visit_true()
    }

    fn visit_false(&mut self, _: &()) -> T {
        self.visit_false()
    }

    fn visit_var(&mut self, _: &(), index: usize) -> T {
        self.visit_var(index)
    }

    fn visit_abs(&mut self, _: &(), body: &ContextTerm<()>) -> T {
        self.visit_abs(body)
    }

    fn visit_app(&mut self, _: &(), lhs: &ContextTerm<()>, rhs: &ContextTerm<()>) -> T {
        self.visit_app(lhs, rhs)
    }

    fn visit_record(&mut self, _: &(), entries: &[(Rc<String>, ContextTerm<()>)]) -> T {
        self.visit_record(entries)
    }

    fn visit_project(&mut self, _: &(), term: &ContextTerm<()>, key: Rc<String>) -> T {
        self.visit_project(term, key)
    }

    fn visit_if(
        &mut self,
        _: &(),
        cond: &ContextTerm<()>,
        positive: &ContextTerm<()>,
        negative: &ContextTerm<()>,
    ) -> T {
        self.visit_if(cond, positive, negative)
    }
}

impl From<Node<()>> for Term {
    fn from(n: Node<()>) -> Self {
        Self::new((), n.into())
    }
}

fn check_subtype(sub: &Type, sup: &Type) -> Result<(), String> {
    if sub == sup {
        return Ok(());
    }
    match (sub, sup) {
        (Type::Bot, _) | (_, Type::Top) => {}
        (Type::Record(lhs), Type::Record(rhs)) => {
            for (k, t) in lhs {
                if let Some(tt) = rhs.iter().find_map(|(kk, tt)| (k == kk).then(|| tt)) {
                    check_subtype(t, tt)?;
                } else {
                    return Err(format!("Key {} not found in {}", k, sup));
                }
            }
        }
        (Type::Arrow(la, lb), Type::Arrow(ra, rb)) => {
            check_subtype(ra, la)?; // Contravariant!!
            check_subtype(lb, rb)?;
        }
        _ => return Err(format!("{} is not a subtype of {}", sub, sup)),
    };
    Ok(())
}

fn meet_type(lhs: &Type, rhs: &Type) -> Type {
    match (lhs, rhs) {
        (Type::Bot, _) | (_, Type::Bot) => Type::Bot,
        (Type::Top, x) | (x, Type::Top) => x.clone(),
        (Type::Bool, Type::Bool) => Type::Bool,
        (Type::Record(lhs), Type::Record(rhs)) => {
            let mut rhs_map: HashMap<_, _> = rhs.iter().cloned().collect();
            let mut entries: Vec<_> = lhs
                .iter()
                .map(|(k, ltype)| {
                    let meet = rhs_map
                        .remove(k)
                        .map(|rtype| meet_type(ltype, &rtype).into())
                        .unwrap_or_else(|| ltype.clone());
                    (k.clone(), meet)
                })
                .collect();
            entries.extend(rhs.iter().filter_map(|(k, rtype)| {
                rhs_map.contains_key(k).then(|| (k.clone(), rtype.clone()))
            }));
            Type::Record(entries)
        }
        (Type::Arrow(la, lb), Type::Arrow(ra, rb)) => {
            Type::Arrow(join_type(la, ra).into(), meet_type(lb, rb).into())
        }
        _ => Type::Top,
    }
}

fn join_type(lhs: &Type, rhs: &Type) -> Type {
    match (lhs, rhs) {
        (Type::Bot, x) | (x, Type::Bot) => x.clone(),
        (Type::Top, _) | (_, Type::Top) => Type::Top,
        (Type::Bool, Type::Bool) => Type::Bool,
        (Type::Record(lhs), Type::Record(rhs)) => {
            let rhs: HashMap<_, _> = rhs.iter().cloned().collect();
            let entries = lhs
                .iter()
                .filter_map(|(k, ltype)| {
                    rhs.get(k)
                        .map(|rtype| (k.clone(), join_type(ltype, rtype).into()))
                })
                .collect();
            Type::Record(entries)
        }
        (Type::Arrow(la, lb), Type::Arrow(ra, rb)) => {
            Type::Arrow(meet_type(la, ra).into(), join_type(lb, rb).into())
        }
        _ => Type::Top,
    }
}

pub fn compile(term: &Spanned<parser::Term>) -> Result<ContextTerm<(Span, Type)>> {
    use chumsky::Error;
    struct ConvertType;
    impl parser::TypeVisitor<Type> for ConvertType {
        fn visit_bot(&mut self) -> Type {
            Type::Bot
        }

        fn visit_top(&mut self) -> Type {
            Type::Top
        }

        fn visit_bool(&mut self) -> Type {
            Type::Bool
        }

        fn visit_record(
            &mut self,
            entries: &[(parser::Identifier, Rc<Spanned<parser::Type>>)],
        ) -> Type {
            Type::Record(
                entries
                    .iter()
                    .map(|(key, val)| (key.clone(), val.accept(self).into()))
                    .collect(),
            )
        }

        fn visit_arrow(
            &mut self,
            lhs: &Rc<parser::Spanned<parser::Type>>,
            rhs: &Rc<parser::Spanned<parser::Type>>,
        ) -> Type {
            Type::Arrow(lhs.accept(self).into(), rhs.accept(self).into())
        }
    }

    #[derive(Default)]
    struct Context {
        variables: Vec<(parser::Identifier, Type)>,
    }
    impl parser::TermVisitor<Result<ContextTerm<(Span, Type)>>> for Context {
        fn visit_true(&mut self, span: Span) -> Result<ContextTerm<(Span, Type)>> {
            Ok(ContextTerm::new((span, Type::Bool), Node::True.into()))
        }

        fn visit_false(&mut self, span: Span) -> Result<ContextTerm<(Span, Type)>> {
            Ok(ContextTerm::new((span, Type::Bool), Node::False.into()))
        }

        fn visit_var(
            &mut self,
            span: Span,
            name: &parser::Spanned<parser::Identifier>,
        ) -> Result<ContextTerm<(Span, Type)>> {
            let search = self
                .variables
                .iter()
                .rev()
                .enumerate()
                .find_map(|(i, (v, ty))| (name.value() == v).then(|| (i, ty)));

            if let Some((i, ty)) = search {
                Ok(ContextTerm::new((span, ty.clone()), Node::Var(i).into()))
            } else {
                Err(chumsky::error::Simple::custom(
                    name.span(),
                    format!("Found a free variable {}", name.value()),
                ))
            }
        }

        fn visit_abs(
            &mut self,
            span: Span,
            name: &parser::Spanned<parser::Identifier>,
            ty: &Rc<parser::Spanned<parser::Type>>,
            body: &Rc<parser::Spanned<parser::Term>>,
        ) -> Result<ContextTerm<(Span, Type)>> {
            let arg_type = ty.accept(&mut ConvertType);
            self.variables.push((name.value().clone(), arg_type));
            let body = body.accept(self)?;
            let arg_type = self.variables.pop().expect("Something went wrong").1;
            Ok(ContextTerm::new(
                (
                    span,
                    Type::Arrow(arg_type.into(), body.context.1.clone().into()),
                ),
                Node::Abs(body).into(),
            ))
        }

        fn visit_app(
            &mut self,
            span: Span,
            lhs: &Rc<parser::Spanned<parser::Term>>,
            rhs: &Rc<parser::Spanned<parser::Term>>,
        ) -> Result<ContextTerm<(Span, Type)>> {
            let lhs = lhs.accept(self)?;
            let rhs = rhs.accept(self)?;
            Ok(match lhs.context.1.clone() {
                Type::Bot => ContextTerm::new((span, Type::Bot.into()), Node::App(lhs, rhs).into()),
                Type::Arrow(lambda_arg_type, lambda_result_type) => {
                    if let Err(e) = check_subtype(&rhs.context.1, &lambda_arg_type) {
                        return Err(chumsky::error::Simple::custom(
                            rhs.context.0,
                            format!(
                                "Type mismatch on apply: {} is not a subtype of {}: {}",
                                rhs.context.1, lambda_arg_type, e
                            ),
                        ));
                    }
                    ContextTerm::new(
                        (span, lambda_result_type.as_ref().clone()),
                        Node::App(lhs, rhs).into(),
                    )
                }
                _ => {
                    return Err(chumsky::error::Simple::custom(
                        lhs.context.0,
                        format!(
                            "Expect an arrow type of arg {} but was {}",
                            rhs.context.1, lhs.context.1
                        ),
                    ))
                }
            })
        }

        fn visit_record(
            &mut self,
            span: Span,
            entries: &[(Spanned<parser::Identifier>, Rc<Spanned<parser::Term>>)],
        ) -> Result<ContextTerm<(Span, Type)>> {
            let entries = entries
                .iter()
                .map(|(key, val)| {
                    let val = val.accept(self)?;
                    Ok((key.value().clone(), val))
                })
                .collect::<Result<Vec<_>>>()?;
            let ty = entries
                .iter()
                .map(|(key, val)| (key.clone(), val.context.1.clone().into()))
                .collect();
            Ok(ContextTerm::new(
                (span, Type::Record(ty)),
                Node::Record(entries).into(),
            ))
        }

        fn visit_proj(
            &mut self,
            span: Span,
            term: &Rc<Spanned<parser::Term>>,
            key: &Spanned<parser::Identifier>,
        ) -> Result<ContextTerm<(Span, Type)>> {
            let term = term.accept(self)?;
            if term.context.1 == Type::Bot {
                return Ok(ContextTerm::new(
                    (span, Type::Bot.into()),
                    Node::Project(term, key.value().clone()).into(),
                ));
            }
            if let Type::Record(entries) = &term.context.1 {
                if let Some(ty) = entries
                    .iter()
                    .find_map(|(k, t)| (k == key.value()).then(|| t))
                {
                    return Ok(ContextTerm::new(
                        (span, ty.as_ref().clone()),
                        Node::Project(term, key.value().clone()).into(),
                    ));
                }
            }
            Err(chumsky::error::Simple::expected_input_found(
                term.context.0,
                std::iter::once(Some(format!("A record including a key {}", key.value()))),
                Some(term.context.1.to_string()),
            ))
        }

        fn visit_if(
            &mut self,
            span: Span,
            cond: &Rc<parser::Spanned<parser::Term>>,
            positive: &Rc<parser::Spanned<parser::Term>>,
            negative: &Rc<parser::Spanned<parser::Term>>,
        ) -> Result<ContextTerm<(Span, Type)>> {
            let cond = cond.accept(self)?;
            let positive = positive.accept(self)?;
            let negative = negative.accept(self)?;
            if check_subtype(&cond.context.1, &Type::Bool).is_err() {
                return Err(chumsky::error::Simple::expected_input_found(
                    cond.context.0,
                    std::iter::once(Some(Type::Bool.to_string())),
                    Some(cond.context.1.to_string()),
                ));
            }
            let join = join_type(&positive.context.1, &negative.context.1);
            Ok(ContextTerm::new(
                (span, join),
                Node::If {
                    cond,
                    positive,
                    negative,
                }
                .into(),
            ))
        }
    }
    term.accept(&mut Context::default())
}

pub fn get_type(term: &Spanned<parser::Term>) -> Result<Type> {
    Ok(compile(term)?.context.1)
}
