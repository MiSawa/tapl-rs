use lexgen::lexer;
use thiserror::Error;

pub type Loc = lexgen_util::Loc;
pub type LexerError = lexgen_util::LexerError<LexicalError>;

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Token {
    LParen,
    RParen,
    Lambda,
    Dot,
    Identifier(String),
}

#[derive(Debug, Error)]
pub enum LexicalError {}

lexer! {
    pub Lexer -> Token;
    type Error = LexicalError;
    let ws = [' ' '\t' '\n'] | "\r\n";
    let non_ident = $ | _ # ['0'-'9' 'a'-'z' 'A'-'Z'];

    $ws,
    "(" = Token::LParen,
    ")" = Token::RParen,
    "lambda" > $non_ident = Token::Lambda,
    "." = Token::Dot,
    ['a'-'z' 'A'-'Z'] => |lexer| lexer.return_(Token::Identifier(lexer.match_().to_string())),
}
