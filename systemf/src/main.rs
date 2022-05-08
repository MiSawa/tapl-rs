use anyhow::Result;
use ariadne::{Color, Fmt, Label, Report, ReportKind, Source};
use chumsky::Parser;
use util::repl;

use crate::prelude::*;

mod compiler;
mod lang;
mod parser;
mod prelude;

fn build_report(e: chumsky::error::Simple<String, Span>) -> Report<Span> {
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

type CommandResult<'a> = Result<(), (&'a str, Vec<chumsky::error::Simple<String, Span>>)>;
fn tokenize(input: &str) -> CommandResult {
    let tokens = parser::lexer()
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
    println!("{tokens:?}");
    Ok(())
}

fn parse(input: &str) -> CommandResult {
    let term = parser::parse(input).map_err(|es| (input, es))?;
    println!("{term:?}");
    Ok(())
}

fn gettype(input: &str) -> CommandResult {
    let term = parser::parse(input).map_err(|es| (input, es))?;
    let ty = compiler::get_type(&term).map_err(|e| (input, vec![e]))?;
    println!("{ty}");
    Ok(())
}

fn compile(input: &str) -> CommandResult {
    let term = parser::parse(input).map_err(|es| (input, es))?;
    let term = compiler::compile(&term).map_err(|e| (input, vec![e]))?;
    println!("{term}");
    Ok(())
}

fn show_help() {
    println!(
        r#"
:tokenize term      -- show tokenized term
:parse term         -- show parsed term
:typeof term        -- show the type of the compiled term
:compile term       -- show the compilation result of the term
:help               -- show this message
"#
    );
}

fn eval(input: String) -> Result<()> {
    fn inner(input: &str) -> CommandResult {
        let (cmd, input) = if let Some(stripped) = input.strip_prefix(':') {
            stripped.trim_start().split_once(' ').unwrap_or(("", input))
        } else {
            ("", input)
        };
        match cmd {
            "to" | "tokenize" => {
                tokenize(input)?;
            }
            "p" | "parse" => {
                parse(input)?;
            }
            "t" | "typeof" => {
                gettype(input)?;
            }
            "c" | "compile" => {
                compile(input)?;
            }
            "h" | "he" | "hel" | "help" => {
                show_help();
            }
            _ => {
                eprintln!("Unknwon command {cmd}");
                show_help();
            }
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
    repl::start_repl(eval)?;
    Ok(())
}
