//!
//! Expression parsing proceeds in recursive manner in the order of operator precedence:
//! `<=>`, `=>`, `|`, `&` and `^`. For each operator, if there is no occurrence in the root of the
//! token tree, we forward the tree to next operator. If there is an occurrence, we split
//! the token tree at this point. Left part goes to the next operator, right part is processed
//! by the same operator to extract additional occurrences.

use super::super::NOT_IN_VAR_NAME;
use super::BooleanExpression;
use super::BooleanExpression::*;
use std::iter::Peekable;
use std::str::Chars;

/// **(internal)** Tokens that can appear in the boolean expression.
/// The tokens form a token tree defined by parenthesis groups.
#[derive(Debug, Eq, PartialEq)]
enum ExprToken {
    Not,                    // '!'
    And,                    // '&'
    Or,                     // '|'
    Xor,                    // '^'
    Imp,                    // '=>'
    Iff,                    // '<=>'
    Id(String),             // 'variable'
    Tokens(Vec<ExprToken>), // A block of tokens inside parentheses
}

/// Takes a `String` and turns it into a `BooleanExpression` or `Error` if the string is not valid.
///
/// Syntax for the formula is described in the tutorial.
pub fn parse_boolean_expression(from: &str) -> Result<BooleanExpression, String> {
    let tokens = tokenize_group(&mut from.chars().peekable(), true)?;
    Ok(*(parse_formula(&tokens)?))
}

/// **(internal)** Process a peekable iterator of characters into a vector of `ExprToken`s.
///
/// The outer method always consumes the opening parenthesis and the recursive call consumes the
/// closing parenthesis. Use `top_level` to indicate that there will be no closing parenthesis.
fn tokenize_group(data: &mut Peekable<Chars>, top_level: bool) -> Result<Vec<ExprToken>, String> {
    let mut output = Vec::new();
    while let Some(c) = data.next() {
        match c {
            c if c.is_whitespace() => { /* skip whitespace */ }
            // single char operators
            '!' => output.push(ExprToken::Not),
            '&' => output.push(ExprToken::And),
            '|' => output.push(ExprToken::Or),
            '^' => output.push(ExprToken::Xor),
            '=' => {
                if Some('>') == data.next() {
                    output.push(ExprToken::Imp);
                } else {
                    return Result::Err("Expected '>' after '='.".to_string());
                }
            }
            '<' => {
                if Some('=') == data.next() {
                    if Some('>') == data.next() {
                        output.push(ExprToken::Iff)
                    } else {
                        return Result::Err("Expected '>' after '='.".to_string());
                    }
                } else {
                    return Result::Err("Expected '=' after '<'.".to_string());
                }
            }
            // '>' is invalid as a start of a token
            '>' => return Result::Err("Unexpected '>'.".to_string()),
            ')' => {
                return if !top_level {
                    Result::Ok(output)
                } else {
                    Result::Err("Unexpected ')'.".to_string())
                }
            }
            '(' => {
                // start a nested token group
                let tokens = tokenize_group(data, false)?;
                output.push(ExprToken::Tokens(tokens));
            }
            _ => {
                // start of a variable name
                let mut name = vec![c];
                while let Some(c) = data.peek() {
                    if c.is_whitespace() || NOT_IN_VAR_NAME.contains(&c) {
                        break;
                    } else {
                        name.push(*c);
                        data.next(); // advance iterator
                    }
                }
                output.push(ExprToken::Id(name.into_iter().collect()));
            }
        }
    }
    if top_level {
        Result::Ok(output)
    } else {
        Result::Err("Expected ')'.".to_string())
    }
}

/// **(internal)** Parse a `ExprToken` tree into a `BooleanExpression` (or error if invalid).
fn parse_formula(data: &[ExprToken]) -> Result<Box<BooleanExpression>, String> {
    iff(data)
}

/// **(internal)** Utility method to find first occurrence of a specific token in the token tree.
fn index_of_first(data: &[ExprToken], token: ExprToken) -> Option<usize> {
    data.iter().position(|t| *t == token)
}

/// **(internal)** Recursive parsing step 1: extract `<=>` operators.
fn iff(data: &[ExprToken]) -> Result<Box<BooleanExpression>, String> {
    let iff_token = index_of_first(data, ExprToken::Iff);
    Ok(if let Some(iff_token) = iff_token {
        Box::new(Iff(
            imp(&data[..iff_token])?,
            iff(&data[(iff_token + 1)..])?,
        ))
    } else {
        imp(data)?
    })
}

/// **(internal)** Recursive parsing step 2: extract `=>` operators.
fn imp(data: &[ExprToken]) -> Result<Box<BooleanExpression>, String> {
    let imp_token = index_of_first(data, ExprToken::Imp);
    Ok(if let Some(imp_token) = imp_token {
        Box::new(Imp(or(&data[..imp_token])?, imp(&data[(imp_token + 1)..])?))
    } else {
        or(data)?
    })
}

/// **(internal)** Recursive parsing step 3: extract `|` operators.
fn or(data: &[ExprToken]) -> Result<Box<BooleanExpression>, String> {
    let or_token = index_of_first(data, ExprToken::Or);
    Ok(if let Some(or_token) = or_token {
        Box::new(Or(and(&data[..or_token])?, or(&data[(or_token + 1)..])?))
    } else {
        and(data)?
    })
}

/// **(internal)** Recursive parsing step 4: extract `&` operators.
fn and(data: &[ExprToken]) -> Result<Box<BooleanExpression>, String> {
    let and_token = index_of_first(data, ExprToken::And);
    Ok(if let Some(and_token) = and_token {
        Box::new(And(
            xor(&data[..and_token])?,
            and(&data[(and_token + 1)..])?,
        ))
    } else {
        xor(data)?
    })
}

/// **(internal)** Recursive parsing step 5: extract `^` operators.
fn xor(data: &[ExprToken]) -> Result<Box<BooleanExpression>, String> {
    let xor_token = index_of_first(data, ExprToken::Xor);
    Ok(if let Some(xor_token) = xor_token {
        Box::new(Xor(
            terminal(&data[..xor_token])?,
            xor(&data[(xor_token + 1)..])?,
        ))
    } else {
        terminal(data)?
    })
}

/// **(internal)** Recursive parsing step 6: extract terminals and negations.
fn terminal(data: &[ExprToken]) -> Result<Box<BooleanExpression>, String> {
    if data.is_empty() {
        Err("Expected formula, found nothing :(".to_string())
    } else if data[0] == ExprToken::Not {
        Ok(Box::new(Not(terminal(&data[1..])?)))
    } else if data.len() > 1 {
        Err(format!(
            "Expected variable name or (...), but found {:?}.",
            data
        ))
    } else {
        match &data[0] {
            ExprToken::Id(name) => {
                if name == "true" {
                    Ok(Box::new(Const(true)))
                } else if name == "false" {
                    Ok(Box::new(Const(false)))
                } else {
                    Ok(Box::new(Variable(name.clone())))
                }
            }
            ExprToken::Tokens(inner) => Ok(parse_formula(inner)?),
            _ => unreachable!(
                "Other tokens are matched by remaining functions, nothing else should remain."
            ),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_boolean_formula_basic() {
        let inputs = vec![
            "v_1+{14}",      // just a variable name with fancy symbols
            "!v_1",          // negation
            "true",          // true
            "false",         // false
            "(v_1 & v_2)",   // and
            "(v_1 | v_2)",   // or
            "(v_1 ^ v_2)",   // xor
            "(v_1 => v_2)",  // imp
            "(v_1 <=> v_2)", // iff
        ];
        for input in inputs {
            assert_eq!(
                input,
                format!("{}", parse_boolean_expression(input).unwrap())
            );
        }
    }

    #[test]
    fn parse_boolean_formula_operator_priority() {
        assert_eq!(
            "(((((!a ^ !b) & !c) | !d) => !e) <=> !f)",
            format!(
                "{}",
                parse_boolean_expression("!a ^ !b & !c | !d => !e <=> !f").unwrap()
            )
        )
    }

    #[test]
    fn parse_boolean_formula_operator_associativity() {
        assert_eq!(
            "(a & (b & c))",
            format!("{}", parse_boolean_expression("a & b & c").unwrap())
        );
        assert_eq!(
            "(a | (b | c))",
            format!("{}", parse_boolean_expression("a | b | c").unwrap())
        );
        assert_eq!(
            "(a ^ (b ^ c))",
            format!("{}", parse_boolean_expression("a ^ b ^ c").unwrap())
        );
        assert_eq!(
            "(a => (b => c))",
            format!("{}", parse_boolean_expression("a => b => c").unwrap())
        );
        assert_eq!(
            "(a <=> (b <=> c))",
            format!("{}", parse_boolean_expression("a <=> b <=> c").unwrap())
        );
    }

    #[test]
    fn parse_boolean_formula_complex() {
        assert_eq!(
            "((a & !!b) => (!(t | (!!a & b)) <=> (x ^ y)))",
            format!(
                "{}",
                parse_boolean_expression("a &!(!b)   => (!(t | !!a&b) <=> x^y)").unwrap()
            )
        )
    }

    #[test]
    #[should_panic]
    fn parse_boolean_formula_invalid_token_1() {
        parse_boolean_expression("a = b").unwrap();
    }

    #[test]
    #[should_panic]
    fn parse_boolean_formula_invalid_token_2() {
        parse_boolean_expression("a < b").unwrap();
    }

    #[test]
    #[should_panic]
    fn parse_boolean_formula_invalid_token_3() {
        parse_boolean_expression("a <= b").unwrap();
    }

    #[test]
    #[should_panic]
    fn parse_boolean_formula_invalid_token_4() {
        parse_boolean_expression("a > b").unwrap();
    }

    #[test]
    #[should_panic]
    fn parse_boolean_formula_invalid_parentheses_1() {
        parse_boolean_expression("(a").unwrap();
    }

    #[test]
    #[should_panic]
    fn parse_boolean_formula_invalid_parentheses_2() {
        parse_boolean_expression("b)").unwrap();
    }

    #[test]
    #[should_panic]
    fn parse_boolean_formula_invalid_parentheses_3() {
        parse_boolean_expression("(a & (b)").unwrap();
    }

    #[test]
    #[should_panic]
    fn parse_boolean_formula_invalid_parentheses_4() {
        parse_boolean_expression("a & (b))").unwrap();
    }

    #[test]
    #[should_panic]
    fn parse_boolean_formula_invalid_formula_1() {
        parse_boolean_expression("a & & b").unwrap();
    }

    #[test]
    #[should_panic]
    fn parse_boolean_formula_invalid_formula_2() {
        parse_boolean_expression("a & c d & b").unwrap();
    }
}
