use std::rc::Rc;

use chumsky::prelude::*;

use crate::{
    lang::{Func, FuncToken, Term, Token, Type, TypeToken, ValueToken},
    prelude::*,
};

pub trait SimpleParser<I: Clone + std::hash::Hash, O>:
    Parser<I, O, Error = Error<I>> + Clone
{
    #[allow(clippy::type_complexity)]
    fn spanned(self) -> chumsky::combinator::MapWithSpan<Self, fn(O, Span) -> Spanned<O>, O>
    where
        Self: Sized,
        I: std::cmp::Eq,
    {
        self.map_with_span(|value, span| Spanned { span, value })
    }

    fn refcounted(self) -> chumsky::combinator::Map<Self, fn(O) -> std::rc::Rc<O>, O>
    where
        Self: Sized,
        I: std::cmp::Eq,
    {
        self.map(Rc::new)
    }
}
impl<I: Clone + std::hash::Hash, O, T> SimpleParser<I, O> for T where
    T: Parser<I, O, Error = Error<I>> + Clone
{
}

pub fn lexer() -> impl SimpleParser<char, Vec<Spanned<Token>>> {
    let symbols = choice((
        just('(').to(Token::LParen),
        just(')').to(Token::RParen),
        just('{').to(Token::LBrace),
        just('}').to(Token::RBrace),
        just('[').to(Token::LBracket),
        just(']').to(Token::RBracket),
        just(',').to(Token::Comma),
        just('.').to(Token::Dot),
        just(';').to(Token::Semicolon),
        just(':').to(Token::Colon),
        just('_').to(Token::Underscore),
        just('=').to(Token::Equal),
        just('*').to(Token::Star),
        just("->").to(Token::Arrow),
    ));
    let keywords = choice((
        text::keyword("lambda").to(Token::Lambda),
        text::keyword("All").to(Token::All),
        text::keyword("Some").to(Token::Some),
        text::keyword("let").to(Token::Let),
        text::keyword("letrec").to(Token::LetRec),
        text::keyword("in").to(Token::In),
        text::keyword("as").to(Token::As),
        text::keyword("if").to(Token::If),
        text::keyword("then").to(Token::Then),
        text::keyword("else").to(Token::Else),
        text::keyword("Bot").to(Token::Type(TypeToken::Bot)),
        text::keyword("Top").to(Token::Type(TypeToken::Top)),
        text::keyword("Unit").to(Token::Type(TypeToken::Unit)),
        text::keyword("Bool").to(Token::Type(TypeToken::Bool)),
        text::keyword("Nat").to(Token::Type(TypeToken::Nat)),
        text::keyword("true").to(Token::Value(ValueToken::True)),
        text::keyword("false").to(Token::Value(ValueToken::False)),
        text::keyword("unit").to(Token::Value(ValueToken::Unit)),
        text::keyword("fix").to(Token::Func(FuncToken::Fix)),
        text::keyword("succ").to(Token::Func(FuncToken::Succ)),
        text::keyword("pred").to(Token::Func(FuncToken::Pred)),
        text::keyword("iszero").to(Token::Func(FuncToken::IsZero)),
    ));
    let others = choice((
        text::int::<char, _>(10)
            .from_str()
            .try_map(|r, span| r.map_err(|e| Error::custom(span, format!("{e}"))))
            .map(|n| Token::Value(ValueToken::Nat(n))),
        text::ident().map(Identifier::new).map(|ident| {
            if ident.starts_with(|c: char| c.is_uppercase()) {
                Token::UpperIdent(ident)
            } else {
                Token::LowerIdent(ident)
            }
        }),
    ));
    let token = choice((symbols, keywords, others));
    token.spanned().padded().repeated().then_ignore(end())
}

fn type_parser() -> impl SimpleParser<Token, Spanned<Type>> {
    recursive(|ty: Recursive<_, Spanned<Type>, _>| {
        // ident
        let upper_ident = select! { Token::UpperIdent(ident) => ident, }.spanned();

        // type variable
        let variable = upper_ident.map(Type::Variable).labelled("type_variable");

        // { Ty, ident: Ty, ... }
        let label = select! { Token::LowerIdent(ident) => ident, }.spanned();
        let labelled_entry = label
            .then_ignore(just(Token::Colon))
            .then(ty.clone().refcounted())
            .map(|(k, t)| (Some(k), t));
        let unlabelled_entry = ty.clone().refcounted().map(|t| (None, t));
        let record = choice((labelled_entry, unlabelled_entry))
            .separated_by(just(Token::Comma))
            .allow_trailing()
            .map(|es| {
                es.into_iter()
                    .enumerate()
                    .map(|(i, (l, t))| {
                        (
                            l.unwrap_or_else(|| Spanned {
                                span: t.span(),
                                value: Identifier::new(i.to_string()),
                            }),
                            t,
                        )
                    })
                    .collect()
            })
            .delimited_by(just(Token::LBrace), just(Token::RBrace))
            .map(Type::Record)
            .labelled("record_type");

        // { Some Ident, Ty }
        let exists = just(Token::Some)
            .ignore_then(upper_ident)
            .then_ignore(just(Token::Comma))
            .then(ty.clone().refcounted())
            .delimited_by(just(Token::LBrace), just(Token::RBrace))
            .map(|(ident, body)| Type::Exists(ident, body))
            .labelled("exists_type");

        let atom = choice((
            just(Token::Type(TypeToken::Bot)).to(Type::Bot),
            just(Token::Type(TypeToken::Top)).to(Type::Top),
            just(Token::Type(TypeToken::Unit)).to(Type::Unit),
            just(Token::Type(TypeToken::Bool)).to(Type::Bool),
            just(Token::Type(TypeToken::Nat)).to(Type::Nat),
            variable,
            record,
            exists,
            ty.clone()
                .map(Spanned::forget_span)
                .delimited_by(just(Token::LParen), just(Token::RParen)),
        ))
        .spanned();

        // Ty Ty
        let apply = atom.clone().then(atom.repeated()).foldl(|lhs, rhs| {
            let span = merge_span(&lhs.span(), &rhs.span());
            Spanned {
                span,
                value: Type::Apply(lhs.into(), rhs.into()),
            }
        });
        // Ty -> Ty
        let arrow = apply
            .clone()
            .then_ignore(just(Token::Arrow))
            .repeated()
            .then(apply)
            .foldr(|lhs, rhs| {
                let span = merge_span(&lhs.span(), &rhs.span());
                Spanned {
                    span,
                    value: Type::Arrow(lhs.into(), rhs.into()),
                }
            });

        // All Ident . Ty
        let forall = just(Token::All)
            .ignore_then(upper_ident)
            .then_ignore(just(Token::Dot))
            .then(ty.clone().refcounted())
            .map(|(ident, body)| Type::Forall(ident, body))
            .spanned()
            .labelled("forall_type");

        // lambda Ident. Ty
        let lambda = just(Token::Lambda)
            .ignore_then(upper_ident)
            .then_ignore(just(Token::Dot))
            .then(ty.clone().refcounted())
            .map(|(ident, body)| Type::Abstract(ident, body))
            .spanned()
            .labelled("abstract_type");

        choice((arrow, forall, lambda))
    })
    .labelled("type")
}

fn term_parser() -> impl SimpleParser<Token, Spanned<Term>> {
    let ty = type_parser();
    recursive(|term: Recursive<_, Spanned<Term>, _>| {
        let lower_ident = select! { Token::LowerIdent(ident) => ident, }.spanned();
        let upper_ident = select! { Token::UpperIdent(ident) => ident, }.spanned();

        // variable
        let variable = lower_ident.map(Term::Variable).labelled("variable");

        // unit, true, false, nat
        let val = select! {
            Token::Value(v) => match v {
                ValueToken::Unit => Term::Unit,
                ValueToken::True => Term::Bool(true),
                ValueToken::False => Term::Bool(false),
                ValueToken::Nat(v) => Term::Nat(v),
            }
        }
        .labelled("value");

        // { term, ident = term, ... }
        let labelled_entry = lower_ident
            .then_ignore(just(Token::Equal))
            .then(term.clone().refcounted())
            .map(|(k, t)| (Some(k), t));
        let unlabelled_entry = term.clone().refcounted().map(|t| (None, t));
        let record = choice((labelled_entry, unlabelled_entry))
            .separated_by(just(Token::Comma))
            .allow_trailing()
            .map(|es| {
                es.into_iter()
                    .enumerate()
                    .map(|(i, (l, t))| {
                        (
                            l.unwrap_or_else(|| Spanned {
                                span: t.span(),
                                value: Identifier::new(i.to_string()),
                            }),
                            t,
                        )
                    })
                    .collect()
            })
            .delimited_by(just(Token::LBrace), just(Token::RBrace))
            .map(Term::Record)
            .labelled("record");

        // {*Ty, term} as Ty
        let pack = just(Token::Star)
            .ignore_then(ty.clone().refcounted())
            .then_ignore(just(Token::Comma))
            .then(term.clone().refcounted())
            .delimited_by(just(Token::LBrace), just(Token::RBrace))
            .then_ignore(just(Token::As))
            .then(ty.clone().refcounted())
            .map(|((inner_type, body), exposed_type)| Term::Pack {
                inner_type,
                body,
                exposed_type,
            })
            .labelled("pack");

        let sequence = term
            .clone()
            .then_ignore(just(Token::Semicolon))
            .repeated()
            .then(term.clone())
            .delimited_by(just(Token::LParen), just(Token::RParen))
            .foldr(|lhs, rhs| {
                let span = merge_span(&lhs.span(), &rhs.span());
                Spanned {
                    span,
                    value: Term::Seq(lhs.into(), rhs.into()),
                }
            })
            .map(Spanned::forget_span)
            .labelled("sequence");

        let atom = choice((val, variable, record, pack, sequence)).spanned();

        // term as Ty
        let maybe_ascribed = atom
            .then(
                just(Token::As)
                    .ignore_then(ty.clone().refcounted())
                    .or_not(),
            )
            .map_with_span(|(term, ty), span| match ty {
                Some(ty) => Spanned {
                    span,
                    value: Term::Ascribe(term.into(), ty),
                },
                None => term,
            });

        let key = select! {
            Token::LowerIdent(ident) => ident,
            Token::Value(ValueToken::Nat(v)) => Identifier::new(v.to_string()),
        }
        .spanned();
        let maybe_accessed = maybe_ascribed
            .then(just(Token::Dot).ignore_then(key).repeated())
            .foldl(|term, key| {
                let span = term.span().start..key.span().end;
                Spanned {
                    span,
                    value: Term::Access(term.into(), key),
                }
            });

        let intrinsic_func = select! {
            Token::Func(FuncToken::Succ) => Func::Succ,
            Token::Func(FuncToken::Pred) => Func::Pred,
            Token::Func(FuncToken::IsZero) => Func::IsZero,
        }
        .spanned()
        .map(Term::Func)
        .spanned();

        enum Apply {
            Term(Rc<Spanned<Term>>),
            Type(Rc<Spanned<Type>>),
        }
        let maybe_applied = choice((intrinsic_func, maybe_accessed.clone()))
            .then(
                choice((
                    maybe_accessed.refcounted().map(Apply::Term),
                    ty.clone()
                        .refcounted()
                        .delimited_by(just(Token::LBracket), just(Token::RBracket))
                        .map(Apply::Type),
                ))
                .spanned()
                .repeated(),
            )
            .foldl(|lhs, rhs| {
                let span = merge_span(&lhs.span(), &rhs.span());
                match rhs.as_ref() {
                    Apply::Term(rhs) => Spanned {
                        span,
                        value: Term::Apply(lhs.into(), rhs.clone()),
                    },
                    Apply::Type(rhs) => Spanned {
                        span,
                        value: Term::TypeApply(lhs.into(), rhs.clone()),
                    },
                }
            });

        // let {Ty, var} = term in term
        let unpack = just(Token::Let)
            .ignore_then(
                upper_ident
                    .then_ignore(just(Token::Comma))
                    .then(lower_ident)
                    .delimited_by(just(Token::LBrace), just(Token::RBrace)),
            )
            .then_ignore(just(Token::Equal))
            .then(term.clone().refcounted())
            .then_ignore(just(Token::In))
            .then(term.clone().refcounted())
            .map(|(((ty, var), arg), body)| Term::Unpack { ty, var, arg, body })
            .spanned()
            .labelled("unpack");

        let ifthenelse = just(Token::If)
            .ignore_then(term.clone())
            .then_ignore(just(Token::Then))
            .then(term.clone())
            .then_ignore(just(Token::Else))
            .then(term.clone())
            .map(|((cond, positive), negative)| Term::If {
                cond: cond.into(),
                positive: positive.into(),
                negative: negative.into(),
            })
            .spanned()
            .labelled("ifthenelse");

        let maybe_anonymous_lower_ident =
            choice((lower_ident.map(Some), just(Token::Underscore).to(None)));
        let abs = just(Token::Lambda)
            .ignore_then(maybe_anonymous_lower_ident.clone())
            .then_ignore(just(Token::Colon))
            .then(type_parser())
            .then_ignore(just(Token::Dot))
            .then(term.clone())
            .map(|((var, ty), body)| Term::Abstract(var, ty.into(), body.into()))
            .spanned()
            .labelled("abstract");

        let type_abs = just(Token::Lambda)
            .ignore_then(upper_ident)
            .then_ignore(just(Token::Dot))
            .then(term.clone())
            .map(|(var, body)| Term::TypeAbstract(var, body.into()))
            .spanned()
            .labelled("type_abstract");

        let let_in = just(Token::Let)
            .ignore_then(maybe_anonymous_lower_ident)
            .then_ignore(just(Token::Equal))
            .then(term.clone().refcounted())
            .then_ignore(just(Token::In))
            .then(term.clone().refcounted())
            .map(|((var, arg), body)| Term::Let { var, arg, body })
            .spanned()
            .labelled("let");

        let letrec = just(Token::LetRec)
            .ignore_then(lower_ident)
            .then_ignore(just(Token::Colon))
            .then(ty.clone().refcounted())
            .then_ignore(just(Token::Equal))
            .then(term.clone().refcounted())
            .then_ignore(just(Token::In))
            .then(term.clone().refcounted())
            .map(|(((var, ty), arg), body)| Term::LetRec { var, ty, arg, body })
            .spanned()
            .labelled("letrec");

        choice((
            ifthenelse,
            abs,
            type_abs,
            unpack,
            let_in,
            letrec,
            maybe_applied,
        ))
    })
    .labelled("term")
}

#[derive(Clone, derive_more::Display, Debug)]
pub enum Command {
    #[display(fmt = "{_0}")]
    Term(Spanned<Term>),
    #[display(fmt = "{_0} = {_1}")]
    TypeAlias(Spanned<Identifier>, Spanned<Type>),
    #[display(fmt = "{_0} = {_1}")]
    TermAlias(Spanned<Identifier>, Spanned<Term>),
}

fn command_parser() -> impl SimpleParser<Token, Command> {
    let upper_ident = select! { Token::UpperIdent(ident) => ident }.spanned();
    let lower_ident = select! { Token::LowerIdent(ident) => ident }.spanned();
    let term = term_parser().map(Command::Term);
    let type_alias = upper_ident
        .then_ignore(just(Token::Equal))
        .then(type_parser())
        .map(|(name, ty)| Command::TypeAlias(name, ty));
    let term_alias = lower_ident
        .then_ignore(just(Token::Equal))
        .then(term_parser())
        .map(|(name, term)| Command::TermAlias(name, term));
    choice((type_alias, term_alias, term))
}

fn commands_parser() -> impl SimpleParser<Token, Vec<Command>> {
    command_parser()
        .separated_by(just(Token::Semicolon))
        .allow_trailing()
}

fn parse_full<T>(s: &str, parser: impl SimpleParser<Token, T>) -> Result<T, Vec<Error<String>>> {
    let len = s.chars().count();
    let eoi = Span {
        start: len,
        end: len + 1,
    };
    let tokens = lexer().parse(s).map_err(|es| {
        es.into_iter()
            .map(|e| e.map(|e| e.to_string()))
            .collect::<Vec<_>>()
    })?;
    let value = parser
        .then_ignore(end())
        .parse(chumsky::Stream::from_iter(
            eoi,
            tokens
                .into_iter()
                .map(|Spanned { span, value }| (value, span)),
        ))
        .map_err(|es| {
            es.into_iter()
                .map(|e| e.map(|e| e.to_string()))
                .collect::<Vec<_>>()
        })?;
    Ok(value)
}

pub fn parse_term(s: &str) -> Result<Spanned<Term>, Vec<Error<String>>> {
    parse_full(s, term_parser())
}

pub fn parse_commands(s: &str) -> Result<Vec<Command>, Vec<Error<String>>> {
    parse_full(s, commands_parser())
}

#[cfg(test)]
mod test {
    use super::*;
    fn lex(s: &str) -> Result<Vec<Token>, Vec<Error<char>>> {
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
            vec![Token::LowerIdent(Identifier::new("ifthenelse".into()))]
        );
        assert_eq!(
            lex("if true then else").unwrap(),
            vec![
                Token::If,
                Token::Value(ValueToken::True),
                Token::Then,
                Token::Else
            ]
        );
        assert_eq!(
            lex("Bool -> Bool").unwrap(),
            vec![
                Token::Type(TypeToken::Bool),
                Token::Arrow,
                Token::Type(TypeToken::Bool)
            ]
        );
    }

    #[test]
    fn test_type_parser() {
        use chumsky::stream::Stream;
        fn parse(s: &str) -> Result<String, String> {
            let len = s.chars().count();
            let eoi = len..len + 1;
            let tokens = lexer().parse(s).map_err(|e| format!("{e:?}"))?;
            type_parser()
                .then_ignore(end())
                .parse(Stream::from_iter(
                    eoi,
                    tokens
                        .into_iter()
                        .map(|Spanned { span, value }| (value, span)),
                ))
                .map_err(|e| format!("{e:?}"))
                .map(|ty| format!("{ty}"))
        }

        assert_eq!(
            parse("Bool -> Bool -> Bool").unwrap(),
            "(Bool -> (Bool -> Bool))".to_string()
        );
        assert_eq!(
            parse("(Bool -> Bool) -> Bool -> Bool").unwrap(),
            "((Bool -> Bool) -> (Bool -> Bool))".to_string()
        );
        assert_eq!(
            parse("{x: Bool, Unit} -> Top").unwrap(),
            "({x: Bool, Unit} -> Top)".to_string()
        );
    }
}
