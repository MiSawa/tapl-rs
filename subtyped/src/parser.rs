use std::rc::Rc;

use chumsky::prelude::*;

pub type Span = std::ops::Range<usize>;
#[derive(derive_more::Deref, Clone, Debug)]
pub struct Spanned<T>(#[deref] T, Span);
impl<T> Spanned<T> {
    pub fn forget(self) -> T {
        self.0
    }
    pub fn value(&self) -> &T {
        &self.0
    }
    pub fn span(&self) -> Span {
        self.1.clone()
    }
}
impl<T> From<Spanned<T>> for (T, Span) {
    fn from(Spanned(value, span): Spanned<T>) -> Self {
        (value, span)
    }
}

pub trait SimpleParser<I: Clone + std::hash::Hash, O>: Parser<I, O, Error = Simple<I>> {}
impl<I: Clone + std::hash::Hash, O, T> SimpleParser<I, O> for T where
    T: Parser<I, O, Error = Simple<I>>
{
}

pub type Identifier = Rc<String>;

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
    #[display(fmt = ",")]
    Comma,
    #[display(fmt = ".")]
    Dot,
    #[display(fmt = ":")]
    Colon,
    #[display(fmt = "=")]
    Equal,
    #[display(fmt = "if")]
    If,
    #[display(fmt = "then")]
    Then,
    #[display(fmt = "else")]
    Else,
    #[display(fmt = "lambda")]
    Lambda,
    #[display(fmt = "Bot")]
    Bot,
    #[display(fmt = "Top")]
    Top,
    #[display(fmt = "true")]
    True,
    #[display(fmt = "false")]
    False,
    #[display(fmt = "Bool")]
    Bool,
    #[display(fmt = "->")]
    Arrow,
    #[display(fmt = "{}", "_0")]
    Ident(Identifier),
}

pub fn lexer() -> impl SimpleParser<char, Vec<Spanned<Token>>> {
    let token = choice((
        just('(').to(Token::LParen),
        just(')').to(Token::RParen),
        just('{').to(Token::LBrace),
        just('}').to(Token::RBrace),
        just(',').to(Token::Comma),
        just('.').to(Token::Dot),
        just(':').to(Token::Colon),
        just('=').to(Token::Equal),
        text::keyword("if").to(Token::If),
        text::keyword("then").to(Token::Then),
        text::keyword("else").to(Token::Else),
        text::keyword("lambda").to(Token::Lambda),
        text::keyword("Bot").to(Token::Bot),
        text::keyword("Top").to(Token::Top),
        text::keyword("true").to(Token::True),
        text::keyword("false").to(Token::False),
        text::keyword("Bool").to(Token::Bool),
        just("->").to(Token::Arrow),
        text::ident().map(Identifier::new).map(Token::Ident),
    ));
    token
        .map_with_span(Spanned)
        .padded()
        .repeated()
        .then_ignore(end())
}

#[derive(Clone, Debug)]
pub enum Type {
    Bot,
    Top,
    Bool,
    Record(Vec<(Identifier, Rc<Spanned<Type>>)>),
    Arrow(Rc<Spanned<Type>>, Rc<Spanned<Type>>),
}
pub trait TypeVisitor<T> {
    fn visit_bot(&mut self) -> T;
    fn visit_top(&mut self) -> T;
    fn visit_bool(&mut self) -> T;
    fn visit_record(&mut self, entries: &[(Identifier, Rc<Spanned<Type>>)]) -> T;
    fn visit_arrow(&mut self, lhs: &Rc<Spanned<Type>>, rhs: &Rc<Spanned<Type>>) -> T;
}
impl Type {
    pub fn accept<T>(&self, visitor: &mut impl TypeVisitor<T>) -> T {
        match self {
            Type::Bot => visitor.visit_bot(),
            Type::Top => visitor.visit_top(),
            Type::Bool => visitor.visit_bool(),
            Type::Record(entries) => visitor.visit_record(entries),
            Type::Arrow(lhs, rhs) => visitor.visit_arrow(lhs, rhs),
        }
    }
}

fn type_parser() -> impl SimpleParser<Token, Spanned<Type>> {
    recursive(|ty| {
        let key = select! {
            Token::Ident(ident) => ident,
        }
        .labelled("key");
        let atom = choice((
            just(Token::Bot).to(Type::Bot),
            just(Token::Top).to(Type::Top),
            just(Token::Bool).to(Type::Bool),
            key.then_ignore(just(Token::Colon))
                .then(ty.clone().map(Rc::new))
                .separated_by(just(Token::Comma))
                .allow_trailing()
                .delimited_by(just(Token::LBrace), just(Token::RBrace))
                .map(Type::Record),
            ty.clone()
                .map(Spanned::forget)
                .delimited_by(just(Token::LParen), just(Token::RParen)),
        ))
        .map_with_span(Spanned);
        atom.clone()
            .then_ignore(just(Token::Arrow))
            .repeated()
            .then(atom)
            .foldr(|lhs, rhs| {
                let span = lhs.span().start..rhs.span().end;
                Spanned(Type::Arrow(lhs.into(), rhs.into()), span)
            })
    })
    .labelled("type")
}

#[derive(Clone, Debug)]
pub enum Term {
    True,
    False,
    Var(Spanned<Identifier>),
    Abs(Spanned<Identifier>, Rc<Spanned<Type>>, Rc<Spanned<Term>>),
    App(Rc<Spanned<Term>>, Rc<Spanned<Term>>),
    Record(Vec<(Spanned<Identifier>, Rc<Spanned<Term>>)>),
    Proj(Rc<Spanned<Term>>, Spanned<Identifier>),
    If {
        cond: Rc<Spanned<Term>>,
        positive: Rc<Spanned<Term>>,
        negative: Rc<Spanned<Term>>,
    },
}
pub trait TermVisitor<T> {
    fn visit_true(&mut self, span: Span) -> T;
    fn visit_false(&mut self, span: Span) -> T;
    fn visit_var(&mut self, span: Span, name: &Spanned<Identifier>) -> T;
    fn visit_abs(
        &mut self,
        span: Span,
        name: &Spanned<Identifier>,
        ty: &Rc<Spanned<Type>>,
        body: &Rc<Spanned<Term>>,
    ) -> T;
    fn visit_app(&mut self, span: Span, lhs: &Rc<Spanned<Term>>, rhs: &Rc<Spanned<Term>>) -> T;
    fn visit_record(
        &mut self,
        span: Span,
        entries: &[(Spanned<Identifier>, Rc<Spanned<Term>>)],
    ) -> T;
    fn visit_proj(&mut self, span: Span, term: &Rc<Spanned<Term>>, key: &Spanned<Identifier>) -> T;
    fn visit_if(
        &mut self,
        span: Span,
        cond: &Rc<Spanned<Term>>,
        positive: &Rc<Spanned<Term>>,
        negative: &Rc<Spanned<Term>>,
    ) -> T;
}
impl Spanned<Term> {
    pub fn accept<T>(&self, visitor: &mut impl TermVisitor<T>) -> T {
        match self.value() {
            Term::True => visitor.visit_true(self.span()),
            Term::False => visitor.visit_false(self.span()),
            Term::Var(name) => visitor.visit_var(self.span(), name),
            Term::Abs(name, ty, body) => visitor.visit_abs(self.span(), name, ty, body),
            Term::App(lhs, rhs) => visitor.visit_app(self.span(), lhs, rhs),
            Term::Record(entries) => visitor.visit_record(self.span(), entries),
            Term::Proj(term, key) => visitor.visit_proj(self.span(), term, key),
            Term::If {
                cond,
                positive,
                negative,
            } => visitor.visit_if(self.span(), cond, positive, negative),
        }
    }
}

fn term_parser() -> impl SimpleParser<Token, Spanned<Term>> {
    use Term::*;
    recursive(|term: Recursive<_, Spanned<Term>, _>| {
        let ident = select! { Token::Ident(ident) => ident }.map_with_span(Spanned);
        let var = ident.labelled("var");
        let key = ident.labelled("key");

        let atom = choice((
            var.map(Var),
            just(Token::True).to(True),
            just(Token::False).to(False),
            key.then_ignore(just(Token::Equal))
                .then(term.clone().map(Rc::new))
                .separated_by(just(Token::Comma))
                .allow_trailing()
                .delimited_by(just(Token::LBrace), just(Token::RBrace))
                .map(Term::Record),
            term.clone()
                .map(Spanned::forget)
                .delimited_by(just(Token::LParen), just(Token::RParen)),
        ))
        .map_with_span(Spanned);
        let atom_maybe_proj = atom
            .then(just(Token::Dot).ignore_then(key).repeated())
            .foldl(|term, key| {
                let span = term.span().start..key.span().end;
                Spanned(Term::Proj(term.into(), key).into(), span)
            });

        let ifthenelse = just(Token::If)
            .ignore_then(term.clone())
            .then_ignore(just(Token::Then))
            .then(term.clone())
            .then_ignore(just(Token::Else))
            .then(term.clone())
            .map(|((cond, positive), negative)| If {
                cond: cond.into(),
                positive: positive.into(),
                negative: negative.into(),
            })
            .map_with_span(Spanned)
            .labelled("ifthenelse");

        let abs = just(Token::Lambda)
            .ignore_then(var)
            .then_ignore(just(Token::Colon))
            .then(type_parser())
            .then_ignore(just(Token::Dot))
            .then(term)
            .map(|((var, ty), body)| Abs(var, ty.into(), body.into()))
            .map_with_span(Spanned)
            .labelled("abs");

        let apply = atom_maybe_proj
            .clone()
            .then(atom_maybe_proj.clone().repeated().at_least(1))
            .foldl(|lhs, rhs| {
                let span = lhs.span().start..rhs.span().end;
                Spanned(App(lhs.into(), rhs.into()), span)
            })
            .labelled("apply");

        choice((ifthenelse, abs, apply, atom_maybe_proj))
    })
    .labelled("term")
    .then_ignore(end())
}

pub fn parse(s: &str) -> Result<Spanned<Term>, Vec<Simple<String>>> {
    let len = s.chars().count();
    let eoi = len..len + 1;
    let tokens = lexer().parse(s).map_err(|es| {
        es.into_iter()
            .map(|e| e.map(|e| e.to_string()))
            .collect::<Vec<_>>()
    })?;
    let terms = term_parser()
        .parse(chumsky::Stream::from_iter(
            eoi,
            tokens.into_iter().map(|v| v.into()),
        ))
        .map_err(|es| {
            es.into_iter()
                .map(|e| e.map(|e| e.to_string()))
                .collect::<Vec<_>>()
        })?;
    Ok(terms)
}

#[cfg(test)]
mod test {
    use super::*;
    fn lex(s: &str) -> Result<Vec<Token>, Vec<Simple<char>>> {
        Ok(lexer()
            .parse(s)?
            .iter()
            .map(Spanned::value)
            .cloned()
            .collect::<Vec<_>>())
    }

    #[test]
    fn test_lexer() {
        assert_eq!(
            lex("ifthenelse").unwrap(),
            vec![Token::Ident(Identifier::new("ifthenelse".into()))]
        );
        assert_eq!(
            lex("if true then else").unwrap(),
            vec![Token::If, Token::True, Token::Then, Token::Else]
        );
        assert_eq!(
            lex("Bool -> Bool").unwrap(),
            vec![Token::Bool, Token::Arrow, Token::Bool]
        );
    }

    #[test]
    fn test_type_parser() {
        use chumsky::stream::Stream;
        #[derive(PartialEq, Eq, Debug)]
        enum Ty {
            Bot,
            Top,
            Bool,
            Record(Vec<(String, Box<Ty>)>),
            Arrow(Box<Ty>, Box<Ty>),
        }
        struct ToTy;
        impl TypeVisitor<Ty> for ToTy {
            fn visit_bot(&mut self) -> Ty {
                Ty::Bot
            }

            fn visit_top(&mut self) -> Ty {
                Ty::Top
            }

            fn visit_bool(&mut self) -> Ty {
                Ty::Bool
            }

            fn visit_record(&mut self, entries: &[(Identifier, Rc<Spanned<Type>>)]) -> Ty {
                Ty::Record(
                    entries
                        .iter()
                        .map(|(key, val)| (key.to_string(), val.accept(self).into()))
                        .collect(),
                )
            }

            fn visit_arrow(&mut self, lhs: &Rc<Spanned<Type>>, rhs: &Rc<Spanned<Type>>) -> Ty {
                Ty::Arrow(lhs.0.accept(self).into(), rhs.0.accept(self).into())
            }
        }
        fn parse(s: &str) -> Result<Ty, String> {
            let len = s.chars().count();
            let eoi = len..len + 1;
            let tokens = lexer().parse(s).map_err(|e| format!("{e:?}"))?;
            type_parser()
                .then_ignore(end())
                .parse(Stream::from_iter(eoi, tokens.into_iter().map(|v| v.into())))
                .map_err(|e| format!("{e:?}"))
                .map(|ty| ty.value().accept(&mut ToTy))
        }

        assert_eq!(
            parse("Bool -> Bool -> Bool").unwrap(),
            Ty::Arrow(
                Ty::Bool.into(),
                Ty::Arrow(Ty::Bool.into(), Ty::Bool.into()).into()
            )
        );
        assert_eq!(
            parse("(Bool -> Bool) -> Bool -> Bool").unwrap(),
            Ty::Arrow(
                Ty::Arrow(Ty::Bool.into(), Ty::Bool.into()).into(),
                Ty::Arrow(Ty::Bool.into(), Ty::Bool.into()).into()
            )
        );
        assert_eq!(
            parse("{x: Bool} -> Top").unwrap(),
            Ty::Arrow(
                Ty::Record(vec![("x".into(), Ty::Bool.into())]).into(),
                Ty::Top.into()
            )
        );
    }
}
