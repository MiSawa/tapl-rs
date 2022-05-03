use crate::compiler::{Node, Term, TermVisitor};

fn is_value<C>(term: &Node<C>) -> bool {
    use Node::*;
    matches!(term, &(True | False | Abs(_) | Record(_)))
}

fn map_var(term: &Term, f: impl FnMut(usize, usize) -> Term) -> Term {
    struct V<F>(usize, F);
    impl<F: FnMut(usize, usize) -> Term> TermVisitor<Term> for V<F> {
        fn visit_true(&mut self) -> Term {
            Node::True.into()
        }

        fn visit_false(&mut self) -> Term {
            Node::False.into()
        }

        fn visit_var(&mut self, index: usize) -> Term {
            self.1(self.0, index)
        }

        fn visit_abs(&mut self, body: &Term) -> Term {
            self.0 += 1;
            let body = body.accept(self);
            self.0 -= 1;
            Node::Abs(body).into()
        }

        fn visit_app(&mut self, lhs: &Term, rhs: &Term) -> Term {
            let lhs = lhs.accept(self);
            let rhs = rhs.accept(self);
            Node::App(lhs, rhs).into()
        }

        fn visit_record(&mut self, entries: &[(std::rc::Rc<String>, Term)]) -> Term {
            let entries = entries
                .iter()
                .map(|(key, val)| (key.clone(), val.accept(self)))
                .collect();
            Node::Record(entries).into()
        }

        fn visit_project(&mut self, term: &Term, key: std::rc::Rc<String>) -> Term {
            let term = term.accept(self);
            Node::Project(term, key).into()
        }

        fn visit_if(&mut self, cond: &Term, positive: &Term, negative: &Term) -> Term {
            let cond = cond.accept(self);
            let positive = positive.accept(self);
            let negative = negative.accept(self);
            Node::If {
                cond,
                positive,
                negative,
            }
            .into()
        }
    }
    term.accept(&mut V(0, f))
}

fn shift(diff: isize, term: &Term) -> Term {
    map_var(term, |depth, index| {
        let new_index = if index < depth {
            index
        } else {
            (index as isize + diff)
                .try_into()
                .expect("Something went wrong")
        };
        Node::Var(new_index).into()
    })
}
fn substitute_top(base: &Term, value: &Term) -> Term {
    map_var(base, |depth, index| {
        if index == depth {
            value.clone()
        } else {
            Node::Var(index).into()
        }
    })
}
fn apply(body: &Term, arg: &Term) -> Term {
    shift(-1, &substitute_top(body, &shift(1, arg)))
}
fn reduce(term: &Term) -> Option<Term> {
    struct Reducer;
    impl TermVisitor<Option<Term>> for Reducer {
        fn visit_true(&mut self) -> Option<Term> {
            None
        }

        fn visit_false(&mut self) -> Option<Term> {
            None
        }

        fn visit_var(&mut self, _index: usize) -> Option<Term> {
            unreachable!("Should already be substituted")
        }

        fn visit_abs(&mut self, _body: &Term) -> Option<Term> {
            None
        }

        fn visit_app(&mut self, lhs: &Term, rhs: &Term) -> Option<Term> {
            Some(if let Some(lhs) = lhs.accept(self) {
                Node::App(lhs, rhs.clone()).into()
            } else if let Some(rhs) = rhs.accept(self) {
                Node::App(lhs.clone(), rhs).into()
            } else if let Node::Abs(body) = lhs.as_ref() {
                apply(body, rhs)
            } else {
                unreachable!("Something went wrong")
            })
        }

        fn visit_record(&mut self, entries: &[(std::rc::Rc<String>, Term)]) -> Option<Term> {
            let mut ret = vec![];
            let mut reduced = false;
            for (key, val) in entries {
                if reduced {
                    ret.push((key.clone(), val.clone()));
                } else if let Some(v) = val.accept(self) {
                    ret.push((key.clone(), v.clone()));
                    reduced = true;
                } else {
                    ret.push((key.clone(), val.clone()));
                }
            }
            reduced.then(|| Node::Record(ret).into())
        }

        fn visit_project(&mut self, term: &Term, key: std::rc::Rc<String>) -> Option<Term> {
            if let Some(term) = term.accept(self) {
                return Some(Node::Project(term, key.clone()).into());
            } else if let Node::Record(entries) = term.as_ref() {
                if let Some(v) = entries.iter().find_map(|(k, v)| (k == &key).then(|| v)) {
                    return Some(v.clone());
                }
            }
            unreachable!(
                "Something went wrong trying to look up {} from {:?}",
                key, term
            );
        }

        fn visit_if(&mut self, cond: &Term, positive: &Term, negative: &Term) -> Option<Term> {
            Some(if let Some(cond) = cond.accept(self) {
                Node::If {
                    cond,
                    positive: positive.clone(),
                    negative: negative.clone(),
                }
                .into()
            } else if matches!(cond.as_ref(), Node::True) {
                positive.clone()
            } else if matches!(cond.as_ref(), Node::False) {
                negative.clone()
            } else {
                unreachable!("Something went worng")
            })
        }
    }
    term.accept(&mut Reducer)
}

fn eval_small(mut term: Term) -> Term {
    while let Some(next) = reduce(&term) {
        term = next
    }
    term
}

fn eval_big(term: &Term) -> Option<Term> {
    use Node::*;
    Some(match term.as_ref() {
        _ if is_value(term) => term.clone(),
        App(lhs, rhs) => {
            let lhs = eval_big(lhs)?;
            let rhs = eval_big(rhs)?;
            if let Abs(body) = lhs.as_ref() {
                eval_big(&apply(&body, &rhs))?
            } else {
                unreachable!()
            }
        }
        Project(term, key) => {
            let term = eval_big(term)?;
            if let Node::Record(entries) = term.as_ref() {
                entries
                    .iter()
                    .find_map(|(k, v)| (key == k).then(|| v.clone()))
                    .expect("???")
            } else {
                unreachable!()
            }
        }
        If {
            cond,
            positive,
            negative,
        } => {
            let cond = eval_big(cond)?;
            if matches!(cond.as_ref(), Node::True) {
                eval_big(positive)?
            } else if matches!(cond.as_ref(), Node::False) {
                eval_big(negative)?
            } else {
                unreachable!()
            }
        }
        _ => unreachable!(),
    })
}

pub fn eval(term: Term) -> Term {
    let a = eval_small(term.clone());
    if let Some(b) = eval_big(&term) {
        assert_eq!(a, b);
    }
    a
}
