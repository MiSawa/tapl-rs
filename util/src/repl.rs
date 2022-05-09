use rustyline::{error::ReadlineError, Editor};
use thiserror::Error;

#[derive(Error, Debug)]
pub enum Error<E> {
    #[error(transparent)]
    Readline(ReadlineError),
    #[error("Eval failed: {0:?}")]
    EvalError(E),
}

pub trait Repl {
    type Error: std::fmt::Debug;
    const HISTORY: Option<&'static str> = None;
    fn evaluate(&mut self, input: String) -> Result<(), Self::Error>;
}

pub fn start_repl<R: Repl>(mut repl: R) -> Result<(), Error<R::Error>> {
    let mut editor = Editor::<()>::new();
    if let Some(history) = R::HISTORY {
        editor.load_history(history).ok();
    }
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
                repl.evaluate(input).map_err(Error::EvalError)?;
                if let Some(history) = R::HISTORY {
                    editor.save_history(history).map_err(Error::Readline)?;
                }
            }
            Err(ReadlineError::Interrupted | ReadlineError::Eof) => {
                println!("Bye!");
                break Ok(());
            }
            Err(e) => break Err(Error::Readline(e)),
        }
    }
}
