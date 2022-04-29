use lexgen::lexer;
use thiserror::Error;

pub type Loc = lexgen_util::Loc;
pub type LexerError = lexgen_util::LexerError<LexicalError>;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Token {
    LParen,
    RParen,
    True,
    False,
    If,
    Then,
    Else,
    Succ,
    Pred,
    IsZero,
    Nat(u32),
}

#[derive(Debug, Error)]
pub enum LexicalError {
    #[error("Unable to parse number: `{0}`")]
    InvalidNumber(String),
}

lexer! {
    pub Lexer -> Token;
    type Error = LexicalError;
    let digit = ['0'-'9'];
    let ws = [' ' '\t' '\n'] | "\r\n";
    let non_ident = $ | _ # ['0'-'9' 'a'-'z' 'A'-'Z'];

    $ws,
    "(" = Token::LParen,
    ")" = Token::RParen,
    "true" > $non_ident = Token::True,
    "false" > $non_ident = Token::False,
    "if" > $non_ident = Token::If,
    "then" > $non_ident = Token::Then,
    "else" > $non_ident = Token::Else,
    "succ" > $non_ident = Token::Succ,
    "pred" > $non_ident = Token::Pred,
    "iszero" > $non_ident = Token::IsZero,
    $digit+ =? |lexer| {
        use std::str::FromStr;
        let parsed = u32::from_str(lexer.match_())
            .map_err(|_| LexicalError::InvalidNumber(lexer.match_().to_string()))
            .map(Token::Nat);
        lexer.return_(parsed)
    },
}
