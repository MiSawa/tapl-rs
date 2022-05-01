use rustyline::{error::ReadlineError, Editor};
use thiserror::Error;

#[derive(Error, Debug)]
pub enum Error<E> {
    #[error(transparent)]
    Readline(ReadlineError),
    #[error("Eval failed: {0:?}")]
    EvalError(E),
}

pub fn start_repl<E: std::fmt::Debug>(
    mut eval: impl FnMut(String) -> Result<(), E>,
) -> Result<(), Error<E>> {
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
                eval(input).map_err(Error::EvalError)?
            }
            Err(ReadlineError::Interrupted | ReadlineError::Eof) => {
                println!("Bye!");
                break Ok(());
            }
            Err(e) => break Err(Error::Readline(e)),
        }
    }
}
