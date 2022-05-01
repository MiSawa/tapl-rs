use std::rc::Rc;

use crate::parser::{self, Span, Spanned};

type Result<T> = std::result::Result<T, chumsky::error::Simple<String>>;

#[derive(PartialEq, Eq, Hash, Clone, derive_more::Display)]
pub enum Type {
    #[display(fmt = "Bool")]
    Bool,
    #[display(fmt = "({} -> {})", "_0", "_1")]
    Arrow(Rc<Type>, Rc<Type>),
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

pub fn compile(term: &Spanned<parser::Term>) -> Result<ContextTerm<(Span, Type)>> {
    use chumsky::Error;
    struct ConvertType;
    impl parser::TypeVisitor<Type> for ConvertType {
        fn visit_bool(&mut self) -> Type {
            Type::Bool
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
            match lhs.context.1.clone() {
                Type::Bool => {
                    return Err(chumsky::error::Simple::custom(
                        lhs.context.0,
                        format!(
                            "Expect an arrow type of arg {} but was a Bool",
                            rhs.context.1
                        ),
                    ))
                }
                Type::Arrow(lambda_arg_type, lambda_result_type) => {
                    if lambda_arg_type.as_ref() != &rhs.context.1 {
                        return Err(chumsky::error::Simple::expected_input_found(
                            rhs.context.0,
                            std::iter::once(Some(lambda_arg_type.to_string())),
                            Some(rhs.context.1.to_string()),
                        ));
                    }
                    Ok(ContextTerm::new(
                        (span, lambda_result_type.as_ref().clone()),
                        Node::App(lhs, rhs).into(),
                    ))
                }
            }
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
            if cond.context.1 != Type::Bool {
                return Err(chumsky::error::Simple::expected_input_found(
                    cond.context.0,
                    std::iter::once(Some(Type::Bool.to_string())),
                    Some(cond.context.1.to_string()),
                ));
            }
            if positive.context.1 != negative.context.1 {
                return Err(chumsky::error::Simple::expected_input_found(
                    negative.context.0,
                    std::iter::once(Some(positive.context.1.to_string())),
                    Some(negative.context.1.to_string()),
                ));
            }
            Ok(ContextTerm::new(
                (span, positive.context.1.clone()),
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
