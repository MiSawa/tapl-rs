use std::{collections::HashMap, rc::Rc};

use crate::parser::{self, Span};

pub struct Index(usize);

pub enum Term {
    True,
    False,
    Var(Index),
    Abs(Index, Rc<Term>),
    App {
        lhs: Rc<Term>,
        rhs: Rc<Term>,
    },
    If {
        cond: Rc<Term>,
        positive: Rc<Term>,
        negative: Rc<Term>,
    },
}

#[derive(PartialEq, Eq, Hash, Clone, derive_more::Display)]
pub enum Type {
    #[display(fmt = "Bool")]
    Bool,
    #[display(fmt = "({} -> {})", "_0", "_1")]
    Arrow(Rc<Type>, Rc<Type>),
}

pub fn check_type(term: &parser::Term) -> Result<Type, chumsky::error::Simple<Type>> {
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
        var_type: HashMap<parser::Identifier, Type>,
    }
    impl parser::TermVisitor<Result<Type, chumsky::error::Simple<Type, Span>>> for Context {
        fn visit_true(&mut self) -> Result<Type, chumsky::error::Simple<Type, Span>> {
            Ok(Type::Bool)
        }

        fn visit_false(&mut self) -> Result<Type, chumsky::error::Simple<Type, Span>> {
            Ok(Type::Bool)
        }

        fn visit_var(
            &mut self,
            name: &parser::Spanned<parser::Identifier>,
        ) -> Result<Type, chumsky::error::Simple<Type, Span>> {
            self.var_type.get(name.value()).cloned().ok_or_else(|| {
                chumsky::error::Simple::custom(
                    name.span(),
                    format!("Found a free variable {}", name.value()),
                )
            })
        }

        fn visit_abs(
            &mut self,
            name: &parser::Spanned<parser::Identifier>,
            ty: &Rc<parser::Spanned<parser::Type>>,
            body: &Rc<parser::Spanned<parser::Term>>,
        ) -> Result<Type, chumsky::error::Simple<Type, Span>> {
            let key = name.value();
            let arg_type = ty.accept(&mut ConvertType);
            let prev = self.var_type.insert(key.clone(), arg_type);
            let body_type = body.accept(self);
            let arg_type = if let Some(prev) = prev {
                self.var_type.insert(key.clone(), prev)
            } else {
                self.var_type.remove(key)
            }
            .expect("something went wrong");
            body_type.map(|t| Type::Arrow(arg_type.into(), t.into()))
        }

        fn visit_app(
            &mut self,
            lhs: &Rc<parser::Spanned<parser::Term>>,
            rhs: &Rc<parser::Spanned<parser::Term>>,
        ) -> Result<Type, chumsky::error::Simple<Type, Span>> {
            let lambda_type = lhs.accept(self)?;
            let arg_type = rhs.accept(self)?;
            match lambda_type {
                Type::Bool => {
                    return Err(chumsky::error::Simple::custom(
                        lhs.span(),
                        format!("Expect an arrow type of arg {arg_type} but was a Bool"),
                    ))
                }
                Type::Arrow(lambda_arg_type, lambda_result_type) => {
                    if lambda_arg_type.as_ref() != &arg_type {
                        return Err(chumsky::error::Simple::expected_input_found(
                            rhs.span(),
                            std::iter::once(Some(lambda_arg_type.as_ref().clone())),
                            Some(arg_type),
                        ));
                    }
                    Ok(lambda_result_type.as_ref().clone())
                }
            }
        }

        fn visit_if(
            &mut self,
            cond: &Rc<parser::Spanned<parser::Term>>,
            positive: &Rc<parser::Spanned<parser::Term>>,
            negative: &Rc<parser::Spanned<parser::Term>>,
        ) -> Result<Type, chumsky::error::Simple<Type, Span>> {
            let cond_type = cond.accept(self)?;
            let positive_type = positive.accept(self)?;
            let negative_type = negative.accept(self)?;
            if cond_type != Type::Bool {
                return Err(chumsky::error::Simple::expected_input_found(
                    cond.span(),
                    std::iter::once(Some(Type::Bool)),
                    Some(cond_type),
                ));
            }
            if positive_type != negative_type {
                return Err(chumsky::error::Simple::expected_input_found(
                    negative.span(),
                    std::iter::once(Some(positive_type)),
                    Some(negative_type),
                ));
            }
            Ok(positive_type)
        }
    }

    term.accept(&mut Context::default())
}
