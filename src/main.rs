use anyhow::{bail, Result};
use lalrpop_util::lalrpop_mod;
use rustyline::{error::ReadlineError, Editor};

mod ast;

lalrpop_mod!(
    #[allow(unused, clippy::all)]
    parser,
    "/tapl.rs"
);

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
                match parser::TermParser::new().parse(&input) {
                    Ok(term) => println!("{term:?}"),
                    Err(e) => eprintln!("Error: {e:?}"),
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
        assert_eq!(parser::TermParser::new().parse("true").unwrap(), True);
        assert_eq!(
            parser::TermParser::new()
                .parse("if false then 0 else 1")
                .unwrap(),
            IfThenElse {
                cond: Rc::new(False),
                positive: Rc::new(Zero),
                negative: Rc::new(Succ(Rc::new(Zero))),
            }
        );
    }
}
