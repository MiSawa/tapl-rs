use anyhow::{anyhow, bail, Result};
use lalrpop_util::lalrpop_mod;
use rustyline::{error::ReadlineError, Editor};

mod ast;
mod eval;
mod lexer;

lalrpop_mod!(
    #[allow(unused, clippy::all)]
    parser
);

trait ResultExt<T> {
    fn staticalize(self) -> anyhow::Result<T>;
}
impl<T, E: std::fmt::Debug> ResultExt<T> for std::result::Result<T, E> {
    fn staticalize(self) -> anyhow::Result<T> {
        self.map_err(|e| anyhow!("{e:?}"))
    }
}

fn parse(s: &str) -> Result<ast::Term> {
    let lexer = lexer::Lexer::new(s);
    parser::TermParser::new().parse(lexer).staticalize()
}

fn exec(input: String) -> Result<()> {
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
}

fn main() -> Result<()> {
    let mut editor = Editor::<()>::new();
    editor.load_history("history.txt").ok();
    let mut input: Option<String> = None;
    loop {
        match editor.readline(">> ") {
            Ok(mut line) if line.ends_with('\\') => {
                line.pop();
                line.push('\n');
                if let Some(input) = input.as_mut() {
                    input.push_str(line.as_str());
                } else {
                    input = Some(line);
                }
            }
            Ok(line) => {
                let input = if let Some(mut input) = input.take() {
                    input.push_str(line.as_str());
                    input
                } else {
                    line
                };
                editor.add_history_entry(input.as_str());
                if let Err(e) = exec(input) {
                    eprintln!("Error: {e:?}")
                }
            }
            Err(ReadlineError::Interrupted) => {
                println!("Bye!");
                break;
            }
            Err(ReadlineError::Eof) => {
                println!("Bye!");
                break;
            }
            Err(e) => {
                bail!(e);
            }
        }
    }
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
