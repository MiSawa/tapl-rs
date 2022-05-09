use anyhow::Result;
use lalrpop_util::lalrpop_mod;
use util::{repl, ResultExt as _};

mod ast;
mod eval;
mod lexer;

lalrpop_mod!(
    #[allow(unused, clippy::all)]
    parser
);

fn parse(s: &str) -> Result<ast::Term> {
    let lexer = lexer::Lexer::new(s);
    parser::TermParser::new().parse(lexer).staticalize()
}

fn eval(input: String) -> Result<()> {
    let inner = |input: String| -> Result<()> {
        if let Some(input) = input.strip_prefix("parse") {
            let term = parse(input)?;
            println!("{term:?}");
        } else if let Some(input) = input.strip_prefix("reduce") {
            let term = parse(input)?;
            let term = eval::anonymize(&term)?;
            let reduced = eval::reduce(&term);
            println!("{reduced:?}");
        } else if let Some(input) = input.strip_prefix("eval") {
            let term = parse(input)?;
            let term = eval::anonymize(&term)?;
            let evaluated = eval::eval(term);
            println!("{evaluated}");
        }
        Ok(())
    };
    if let Err(e) = inner(input) {
        eprintln!("{e:?}");
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
