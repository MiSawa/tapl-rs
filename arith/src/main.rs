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
            let reduced = eval::reduce(term.into());
            println!("{reduced:?}");
        } else if let Some(input) = input.strip_prefix("eval") {
            let term = parse(input)?;
            let evaluated = eval::eval(term.into());
            println!("{evaluated:?}");
        }
        Ok(())
    };
    if let Err(e) = inner(input) {
        eprintln!("{e:?}");
    }
    Ok(())
}

fn main() -> Result<()> {
    repl::start_repl(eval)?;
    Ok(())
}

#[cfg(test)]
mod test {
    use std::rc::Rc;

    use super::{ast::Term::*, *};

    #[test]
    fn test_parse() {
        assert_eq!(parse("true").unwrap(), True);
        assert_eq!(
            parse("if false then 0 else 1").unwrap(),
            IfThenElse {
                cond: Rc::new(False),
                positive: Rc::new(Zero),
                negative: Rc::new(Succ(Rc::new(Zero))),
            }
        );
    }

    #[test]
    fn test_space_required() {
        assert!(parse("iftruethentrueelsefalse").is_err());
    }
}
