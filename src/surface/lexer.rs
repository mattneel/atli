use crate::surface::ast::Span;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TokenKind {
    Ident(String),
    Number(u64),
    Pub,
    Fn,
    Effect,
    Handle,
    Case,
    Return,
    Measure,
    Div,
    If,
    Else,
    Type,
    Use,
    Move,
    Inplace,
    Freeze,
    Spawn,
    Scope,
    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket,
    RBracket,
    Comma,
    Colon,
    Dot,
    Bang,
    Caret,
    Eq,
    Underscore,
    Arrow,
    PipeGt,
    Semi,
    Plus,
    Minus,
    Star,
    Eof,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LexError {
    pub span: Span,
    pub message: String,
}

/// Lexical structure for the reduced subset of `docs/syntax.md §1`.
pub fn lex(src: &str) -> Result<Vec<Token>, LexError> {
    let bytes = src.as_bytes();
    let mut out = Vec::new();
    let mut idx = 0;
    while idx < bytes.len() {
        let ch = bytes[idx] as char;
        match ch {
            ' ' | '\t' | '\r' | '\n' => idx += 1,
            '/' if bytes.get(idx + 1) == Some(&b'/') => {
                idx += 2;
                while idx < bytes.len() && bytes[idx] != b'\n' {
                    idx += 1;
                }
            }
            '0'..='9' => {
                let start = idx;
                let mut digits = String::new();
                while idx < bytes.len() {
                    let c = bytes[idx] as char;
                    if c.is_ascii_digit() {
                        digits.push(c);
                        idx += 1;
                    } else if c == '_' {
                        idx += 1;
                    } else {
                        break;
                    }
                }
                let value = digits.parse::<u64>().map_err(|_| LexError {
                    span: Span::new(start, idx),
                    message: "Nat literal is too large".into(),
                })?;
                out.push(Token {
                    kind: TokenKind::Number(value),
                    span: Span::new(start, idx),
                });
            }
            'A'..='Z' | 'a'..='z' => {
                let start = idx;
                idx += 1;
                while idx < bytes.len() {
                    let c = bytes[idx] as char;
                    if c.is_ascii_alphanumeric() || c == '_' {
                        idx += 1;
                    } else {
                        break;
                    }
                }
                let text = &src[start..idx];
                out.push(Token {
                    kind: keyword_or_ident(text),
                    span: Span::new(start, idx),
                });
            }
            '_' => {
                out.push(Token {
                    kind: TokenKind::Underscore,
                    span: Span::new(idx, idx + 1),
                });
                idx += 1;
            }
            '(' => push_one(&mut out, TokenKind::LParen, idx, &mut idx),
            ')' => push_one(&mut out, TokenKind::RParen, idx, &mut idx),
            '{' => push_one(&mut out, TokenKind::LBrace, idx, &mut idx),
            '}' => push_one(&mut out, TokenKind::RBrace, idx, &mut idx),
            '[' => push_one(&mut out, TokenKind::LBracket, idx, &mut idx),
            ']' => push_one(&mut out, TokenKind::RBracket, idx, &mut idx),
            ',' => push_one(&mut out, TokenKind::Comma, idx, &mut idx),
            ':' => push_one(&mut out, TokenKind::Colon, idx, &mut idx),
            '.' => push_one(&mut out, TokenKind::Dot, idx, &mut idx),
            '!' => push_one(&mut out, TokenKind::Bang, idx, &mut idx),
            '^' => push_one(&mut out, TokenKind::Caret, idx, &mut idx),
            '=' => push_one(&mut out, TokenKind::Eq, idx, &mut idx),
            ';' => push_one(&mut out, TokenKind::Semi, idx, &mut idx),
            '+' => push_one(&mut out, TokenKind::Plus, idx, &mut idx),
            '*' => push_one(&mut out, TokenKind::Star, idx, &mut idx),
            '-' if bytes.get(idx + 1) == Some(&b'>') => {
                out.push(Token {
                    kind: TokenKind::Arrow,
                    span: Span::new(idx, idx + 2),
                });
                idx += 2;
            }
            '|' if bytes.get(idx + 1) == Some(&b'>') => {
                out.push(Token {
                    kind: TokenKind::PipeGt,
                    span: Span::new(idx, idx + 2),
                });
                idx += 2;
            }
            '-' => push_one(&mut out, TokenKind::Minus, idx, &mut idx),
            '/' | '%' | '<' | '>' | '"' | '\'' => {
                return Err(LexError {
                    span: Span::new(idx, idx + ch.len_utf8()),
                    message: format!("`{ch}` is not yet in the reduced surface"),
                });
            }
            _ => {
                return Err(LexError {
                    span: Span::new(idx, idx + ch.len_utf8()),
                    message: format!("unexpected character `{ch}`"),
                });
            }
        }
    }
    out.push(Token {
        kind: TokenKind::Eof,
        span: Span::new(src.len(), src.len()),
    });
    Ok(out)
}

fn push_one(out: &mut Vec<Token>, kind: TokenKind, start: usize, idx: &mut usize) {
    out.push(Token {
        kind,
        span: Span::new(start, start + 1),
    });
    *idx += 1;
}

fn keyword_or_ident(text: &str) -> TokenKind {
    match text {
        "pub" => TokenKind::Pub,
        "fn" => TokenKind::Fn,
        "effect" => TokenKind::Effect,
        "handle" => TokenKind::Handle,
        "case" => TokenKind::Case,
        "return" => TokenKind::Return,
        "measure" => TokenKind::Measure,
        "div" => TokenKind::Div,
        "if" => TokenKind::If,
        "else" => TokenKind::Else,
        "type" => TokenKind::Type,
        "use" => TokenKind::Use,
        "move" => TokenKind::Move,
        "inplace" => TokenKind::Inplace,
        "freeze" => TokenKind::Freeze,
        "spawn" => TokenKind::Spawn,
        "scope" => TokenKind::Scope,
        _ => TokenKind::Ident(text.into()),
    }
}
