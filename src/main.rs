use lalrpop_util::lalrpop_mod;

mod ast;

lalrpop_mod!(
    #[allow(unused, clippy::all)]
    parser,
    "/tapl.rs"
);

fn main() {
    println!("Hello, world!");
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
