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
    loop {
        match editor.readline(">> ") {
            Ok(line) => {
                editor.add_history_entry(line.as_str());
                match parser::TermParser::new().parse(&line) {
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
