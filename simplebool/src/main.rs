use anyhow::Result;
use ariadne::{Color, Fmt, Label, Report, ReportKind, Source};
use chumsky::Parser;
use parser::{lexer, Spanned};
use util::repl;

mod compiler;
mod evaluator;
mod parser;

fn build_report(e: chumsky::error::Simple<String>) -> Report {
    use chumsky::error::SimpleReason;
    let report = Report::build(ReportKind::Error, (), e.span().start);
    match e.reason() {
        SimpleReason::Unexpected => {
            let found = e.found().map(String::as_str).unwrap_or("end of the input");
            let expected = e
                .expected()
                .map(|t| t.as_ref().map(String::as_str).unwrap_or("end of the input"))
                .collect::<Vec<_>>()
                .join(", ");
            let expected = if expected.is_empty() {
                "something else"
            } else {
                &expected
            };
            report
                .with_message(format!("Unexpected {found}, expected {expected}",))
                .with_label(
                    Label::new(e.span())
                        .with_message(format!("Unexpected {}", found.fg(Color::Red)))
                        .with_color(Color::Red),
                )
        }
        SimpleReason::Unclosed { span, delimiter } => report
            .with_message(format!("Unclosed dlimiter {}", delimiter.fg(Color::Yellow)))
            .with_label(
                Label::new(span.clone())
                    .with_message(format!(
                        "Unclosed delimiter {}",
                        delimiter.fg(Color::Yellow)
                    ))
                    .with_color(Color::Yellow),
            )
            .with_label(
                Label::new(span.clone())
                    .with_message(format!(
                        "Must be closed before this {}",
                        e.found()
                            .map(String::as_str)
                            .unwrap_or("end of the input")
                            .fg(Color::Red)
                    ))
                    .with_color(Color::Red),
            ),
        SimpleReason::Custom(msg) => report.with_message(msg).with_label(
            Label::new(e.span())
                .with_message(format!("{}", msg.fg(Color::Red)))
                .with_color(Color::Red),
        ),
    }
    .finish()
}

fn eval(input: String) -> Result<()> {
    fn inner(input: &str) -> Result<(), (&str, Vec<chumsky::error::Simple<String>>)> {
        if let Some(input) = input.strip_prefix("tokenize") {
            let tokens = lexer()
                .parse(input)
                .map_err(|es| {
                    (
                        input,
                        es.into_iter().map(|e| e.map(|e| e.to_string())).collect(),
                    )
                })?
                .iter()
                .map(Spanned::value)
                .cloned()
                .collect::<Vec<_>>();
            println!("{tokens:?}")
        } else if let Some(input) = input.strip_prefix("parse") {
            let term = parser::parse(input).map_err(|es| (input, es))?;
            println!("{term:?}")
        } else if let Some(input) = input.strip_prefix("typeof") {
            let term = parser::parse(input).map_err(|es| (input, es))?;
            let ty = compiler::get_type(&term).map_err(|e| (input, vec![e]))?;
            println!("{ty}")
        } else if let Some(input) = input.strip_prefix("eval") {
            let term = parser::parse(input).map_err(|es| (input, es))?;
            let term = compiler::compile(&term).map_err(|e| (input, vec![e]))?;
            let evaluated = evaluator::eval(term.forget_context());
            println!("{evaluated:?}")
        }

        Ok(())
    }
    if let Err((input, es)) = inner(&input) {
        for e in es {
            build_report(e).eprint(Source::from(&input))?;
        }
    }
    Ok(())
}

fn main() -> Result<()> {
    struct R;
    impl repl::Repl for R {
        type Error = anyhow::Error;
        fn evaluate(&mut self, input: String) -> Result<(), Self::Error> {
            eval(input)
        }
    }
    repl::start_repl(R)?;
    Ok(())
}
