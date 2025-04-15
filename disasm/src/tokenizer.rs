use std::str::{Chars, FromStr};

use anyhow::Result;
use num_bigint::BigInt;
use smol_str::SmolStr;

pub fn tokenize(mut text: &str) -> Result<OpcodeTokens, LexerError> {
    text = text.trim();
    let Some((name, args)) = text.split_once(' ') else {
        // Opcode has no args.
        return Ok(OpcodeTokens {
            name: SmolStr::from(text),
            args: Vec::new(),
        });
    };

    let mut res = Vec::new();

    let mut has_comma = false;
    let mut lexer = Lexer::new(args);
    loop {
        let Some(first_char) = lexer.bump() else {
            break;
        };

        match first_char {
            // ci - control registers
            'c' => {
                has_comma = false;
                res.push(lexer.read_control_reg()?);
            }
            // si, s-i - stack items
            's' => {
                has_comma = false;
                res.push(lexer.read_stack_item()?)
            }
            // (...
            '(' => {
                has_comma = false;
                match lexer.first() {
                    // xASD_,refs=123 - cell slice
                    'x' => {
                        lexer.bump();
                        res.push(lexer.read_slice(true)?);
                    }
                    // a0b1..hash..8c9d - cell
                    _ => res.push(lexer.read_cell()?),
                }

                // ...)
                match lexer.bump() {
                    Some(')') => {}
                    Some(_) => return Err(LexerError::UnclosedParen),
                    None => return Err(LexerError::UnexpectedEof),
                }
            }
            // xASD_ - cell slice (without refs)
            'x' => {
                has_comma = false;
                res.push(lexer.read_slice(false)?);
            }
            // Whitespace
            c if c.is_ascii_whitespace() => {}
            // Comma
            ',' => {
                if has_comma {
                    return Err(LexerError::ArgumentSkipped);
                }
                has_comma = true;
            }
            // Everyting else is number
            c => {
                has_comma = false;
                res.push(lexer.read_number(c)?);
            }
        }
    }

    Ok(OpcodeTokens {
        name: SmolStr::new(name),
        args: res,
    })
}

struct Lexer<'a> {
    input: &'a str,
    chars: Chars<'a>,
}

impl<'a> Lexer<'a> {
    fn new(input: &'a str) -> Self {
        Self {
            input,
            chars: input.chars(),
        }
    }

    fn first(&self) -> char {
        self.chars.clone().next().unwrap_or(EOF_CHAR)
    }

    fn bump(&mut self) -> Option<char> {
        let c = self.chars.next()?;
        Some(c)
    }

    fn pos(&self) -> usize {
        self.input.len() - self.chars.as_str().len()
    }

    fn read_control_reg(&mut self) -> Result<OpcodeArgToken, LexerError> {
        match self.bump() {
            Some(c) if c.is_ascii_digit() => Ok(OpcodeArgToken::Reg {
                idx: c as u8 - b'0',
            }),
            Some(c) => Err(LexerError::UnexpectedToken(c)),
            None => Err(LexerError::UnexpectedEof),
        }
    }

    fn read_stack_item(&mut self) -> Result<OpcodeArgToken, LexerError> {
        let from = self.pos();
        let mut has_digits = false;
        match self.bump() {
            Some('-') => {}
            Some('0'..='9') => has_digits = true,
            Some(c) => return Err(LexerError::UnexpectedToken(c)),
            None => return Err(LexerError::UnexpectedEof),
        }

        loop {
            match self.first() {
                '0'..='9' => {
                    self.bump();
                    has_digits = true;
                }
                _ if has_digits => {
                    let to = self.pos();
                    break Ok(OpcodeArgToken::Stack {
                        idx: self.input[from..to].parse::<i32>().unwrap(),
                    });
                }
                _ => match self.bump() {
                    Some(c) => break Err(LexerError::UnexpectedToken(c)),
                    None => break Err(LexerError::UnexpectedEof),
                },
            }
        }
    }

    fn read_cell(&mut self) -> Result<OpcodeArgToken, LexerError> {
        for _ in 0..64 {
            match self.bump() {
                Some('0'..='9' | 'a'..='f' | 'A'..='F') => {}
                Some(c) => return Err(LexerError::UnexpectedToken(c)),
                None => return Err(LexerError::UnexpectedEof),
            }
        }
        Ok(OpcodeArgToken::Cell)
    }

    fn read_slice(&mut self, wrapped: bool) -> Result<OpcodeArgToken, LexerError> {
        loop {
            match self.first() {
                '0'..='9' | 'a'..='f' | 'A'..='F' => {
                    self.bump();
                }
                '_' => {
                    self.bump();
                    break;
                }
                ')' if wrapped => return Ok(OpcodeArgToken::Slice),
                _ => break,
            }
        }

        if !wrapped {
            return Ok(OpcodeArgToken::Slice);
        }

        match self.bump() {
            Some(',') => {}
            Some(c) => return Err(LexerError::UnexpectedToken(c)),
            None => return Err(LexerError::UnexpectedEof),
        }

        match self.bump() {
            Some('0'..='9') => Ok(OpcodeArgToken::Slice),
            Some(c) => Err(LexerError::UnexpectedToken(c)),
            None => Err(LexerError::UnexpectedEof),
        }
    }

    fn read_number(&mut self, first_digit: char) -> Result<OpcodeArgToken, LexerError> {
        let from = self.pos() - 1;
        let mut has_digits = false;

        match first_digit {
            '-' => {}
            '0'..='9' => has_digits = true,
            c => return Err(LexerError::UnexpectedToken(c)),
        }

        loop {
            match self.first() {
                '0'..='9' => {
                    self.bump();
                    has_digits = true;
                }
                _ if has_digits => {
                    let to = self.pos();
                    break Ok(OpcodeArgToken::Int(
                        BigInt::from_str(&self.input[from..to]).unwrap(),
                    ));
                }
                _ => match self.bump() {
                    Some(c) => break Err(LexerError::UnexpectedToken(c)),
                    None => break Err(LexerError::UnexpectedEof),
                },
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OpcodeTokens {
    pub name: SmolStr,
    pub args: Vec<OpcodeArgToken>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OpcodeArgToken {
    Int(BigInt),
    Stack { idx: i32 },
    Reg { idx: u8 },
    Cell,
    Slice,
}

#[derive(thiserror::Error, Debug)]
pub enum LexerError {
    #[error("unexpected opcode EOF")]
    UnexpectedEof,
    #[error("unexpected token: {0}")]
    UnexpectedToken(char),
    #[error("unclosed paren")]
    UnclosedParen,
    #[error("argument skipped")]
    ArgumentSkipped,
}

const EOF_CHAR: char = '\0';

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tokenize_works() {
        assert_eq!(tokenize("DUP").unwrap(), OpcodeTokens {
            name: SmolStr::new("DUP"),
            args: Vec::new(),
        });

        assert_eq!(tokenize("PUSHINT 123").unwrap(), OpcodeTokens {
            name: SmolStr::new("PUSHINT"),
            args: vec![OpcodeArgToken::Int(123i32.into())],
        });

        assert_eq!(tokenize("PUSHSLICECONST x").unwrap(), OpcodeTokens {
            name: SmolStr::new("PUSHSLICECONST"),
            args: vec![OpcodeArgToken::Slice],
        });
        assert_eq!(tokenize("PUSHSLICECONST x6").unwrap(), OpcodeTokens {
            name: SmolStr::new("PUSHSLICECONST"),
            args: vec![OpcodeArgToken::Slice],
        });

        assert_eq!(
            tokenize("DICTPUSHCONST 19 (xC_,1)").unwrap(),
            OpcodeTokens {
                name: SmolStr::new("DICTPUSHCONST"),
                args: vec![OpcodeArgToken::Int(19.into()), OpcodeArgToken::Slice],
            }
        );

        assert_eq!(
            tokenize(
                "PUSHREFCONT (96a296d224f285c67bee93c30f8a309157f0daa35dc5b87e410b78630a09cfc7)"
            )
            .unwrap(),
            OpcodeTokens {
                name: SmolStr::new("PUSHREFCONT"),
                args: vec![OpcodeArgToken::Cell],
            }
        );

        assert_eq!(
            tokenize(
                "IFREFELSEREF (96a296d224f285c67bee93c30f8a309157f0daa35dc5b87e410b78630a09cfc7) \
                (96a296d224f285c67bee93c30f8a309157f0daa35dc5b87e410b78630a09cfc7)"
            )
            .unwrap(),
            OpcodeTokens {
                name: SmolStr::new("IFREFELSEREF"),
                args: vec![OpcodeArgToken::Cell, OpcodeArgToken::Cell],
            }
        );
    }
}
