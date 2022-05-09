use anyhow::Result;
use ariadne::{Color, Fmt, Label, Report, ReportKind, Source};
use chumsky::Parser;
use util::repl;

use crate::{compiler::Context, prelude::*};

mod compiler;
mod evaluator;
mod lang;
mod parser;
mod prelude;
mod term;

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

#[derive(Default)]
struct Repl {
    context: Context,
}
impl Repl {
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
        let term = parser::parse_term(input).map_err(|es| (input, es))?;
        println!("{term}");
        Ok(())
    }

    fn gettype(input: &str) -> CommandResult {
        let term = parser::parse_term(input).map_err(|es| (input, es))?;
        let ty = compiler::get_type(&term).map_err(|e| (input, vec![e]))?;
        println!("{ty}");
        Ok(())
    }

    fn compile(input: &str) -> CommandResult {
        let term = parser::parse_term(input).map_err(|es| (input, es))?;
        let term = compiler::compile(&term).map_err(|e| (input, vec![e]))?;
        println!("{term}");
        Ok(())
    }

    fn evaluate<'i>(&mut self, input: &'i str) -> CommandResult<'i> {
        let commands = parser::parse_commands(input).map_err(|es| (input, es))?;
        for command in commands {
            match command {
                parser::Command::Term(term) => {
                    let term = compiler::compile_term(&self.context, &term)
                        .map_err(|e| (input, vec![e]))?;
                    let term = evaluator::evaluate(&term.term);
                    println!("{term}");
                }
                parser::Command::TypeAlias(name, ty) => {
                    let ty =
                        compiler::compile_type(&self.context, &ty).map_err(|e| (input, vec![e]))?;
                    println!("{ty}");
                    self.context
                        .add_type_alias(name.forget_span(), ty.forget_span());
                }
                parser::Command::TermAlias(name, term) => {
                    let term = compiler::compile_term(&self.context, &term)
                        .map_err(|e| (input, vec![e]))?;
                    println!("{} : {}", term.term, term.ty);
                    self.context
                        .add_term_alias(name.forget_span(), term.term, term.ty);
                }
            }
        }
        Ok(())
    }

    fn show_help() {
        println!(
            "{}",
            r#"
term                -- same as :evaluate term
:tokenize   term    -- show tokenized term
:parse      term    -- show parsed term
:typeof     term    -- show the type of the compiled term
:compile    term    -- show the compilation result of the term
:evaluate   term    -- show the evaluation result
:help               -- show this message
        "#
            .trim()
        );
    }

    fn handle_repl_input<'i>(&mut self, input: &'i str) -> CommandResult<'i> {
        let (cmd, input) = if let Some(stripped) = input.strip_prefix(':') {
            stripped
                .trim_start()
                .split_once(' ')
                .unwrap_or((stripped, ""))
        } else {
            ("", input)
        };
        match cmd {
            "to" | "tokenize" => {
                Self::tokenize(input)?;
            }
            "p" | "parse" => {
                Self::parse(input)?;
            }
            "t" | "typeof" => {
                Self::gettype(input)?;
            }
            "c" | "compile" => {
                Self::compile(input)?;
            }
            "" | "r" | "run" | "e" | "eval" | "evaluate" => {
                self.evaluate(input)?;
            }
            "h" | "he" | "hel" | "help" => {
                Self::show_help();
            }
            _ => {
                eprintln!("Unknwon command {cmd}");
                Self::show_help();
            }
        }
        Ok(())
    }
}
impl repl::Repl for Repl {
    type Error = anyhow::Error;
    const HISTORY: Option<&'static str> = Some("/tmp/systemf.history");
    fn evaluate(&mut self, input: String) -> Result<(), Self::Error> {
        if input.is_empty() {
            return Ok(());
        }
        if let Err((input, es)) = self.handle_repl_input(&input) {
            for e in es {
                build_report(e).eprint(Source::from(&input))?;
            }
        }
        Ok(())
    }
}

fn main() -> Result<()> {
    println!("Hi, this is a System F REPL. :h to show help");
    println!();
    repl::start_repl(Repl::default())?;
    Ok(())
}
