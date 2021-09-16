//! Tools for working with `lox` source code

use crate::{
    span::Span,
    util::peek::{Peekable1, Peekable2},
};
use smol_str::SmolStr;
use std::{
    collections::HashMap, convert::TryFrom, fmt, iter::Fuse, num::ParseFloatError, str::CharIndices,
};

/// Errors that can occur during the scanning process
#[derive(Debug, Clone, PartialEq, thiserror::Error)]
pub enum ScanError {
    /// An unexpected character was present in the input
    #[error("unexpected character: '{}'", .0)]
    UnexpectedChar(char),
    /// A string literal did not have a closing `"`
    #[error("unterminated string")]
    UnterminatedString,
    #[error("failed to parse number: {}", .0)]
    /// A failure occured while parsing a floating point number
    F64ParseFailure(#[from] ParseFloatError),
}

/// The `Scanner` takes raw text input and produces a sequence of `Token`s
pub struct Scanner<'s> {
    characters: Peekable2<Fuse<CharIndices<'s>>>,
    original: &'s str,
    line: u32,
    keywords: HashMap<&'static str, TokenType>,
    /// The list of comments collected during scanning of source
    pub comments: Vec<&'s str>,
}

impl<'s> Scanner<'s> {
    /// Create a new `Scanner` for the given text
    pub fn new(text: &'s str) -> Self {
        Scanner {
            characters: Peekable2::new(text.char_indices().fuse()),
            original: text,
            line: 1,
            keywords: TokenType::keywords(),
            comments: Vec::new(),
        }
    }

    fn advance(&mut self) -> Option<(usize, char)> {
        self.characters.next()
    }

    fn advance_if(&mut self, expected: char) -> bool {
        self.characters.next_if(|(_, c)| c == &expected).is_some()
    }

    fn peek(&mut self) -> Option<(usize, char)> {
        self.characters.peek(0).copied()
    }

    fn peek2(&mut self) -> Option<(usize, char)> {
        self.characters.peek(1).copied()
    }

    fn next_pos(&mut self) -> usize {
        self.peek()
            .map(|(pos, _)| pos)
            .unwrap_or_else(|| self.original.len())
    }

    /// Consume the input and return the next `Token`, if it exists
    ///
    /// This function will return the `EOF` token a single time
    pub fn scan_token(&mut self) -> Result<Option<Token>, ScanError> {
        'outer: loop {
            let (pos, c) = match self.advance() {
                None => return Ok(None),
                Some(v) => v,
            };

            let r#type = match c {
                '(' => Some(TokenType::LeftParen),
                ')' => Some(TokenType::RightParen),
                '{' => Some(TokenType::LeftBrace),
                '}' => Some(TokenType::RightBrace),
                ',' => Some(TokenType::Comma),
                '.' => Some(TokenType::Dot),
                '-' => Some(TokenType::Minus),
                '+' => Some(TokenType::Plus),
                ';' => Some(TokenType::Semicolon),
                '*' => Some(TokenType::Star),
                '/' => {
                    if self.advance_if('/') {
                        loop {
                            let p = self.peek().map(|(_, c)| c);
                            if p.is_none() || p == Some('\n') {
                                let end_pos = self.next_pos();
                                let comment = self.original[pos..end_pos]
                                    .trim()
                                    .trim_start_matches(&['/', ' '][..]);
                                self.comments.push(comment);

                                // Restart looking for a token again
                                continue 'outer;
                            } else {
                                self.advance();
                            }
                        }
                    } else if self.advance_if('*') {
                        loop {
                            let p1 = self.peek().map(|(_, c)| c);
                            let p2 = self.peek2().map(|(_, c)| c);

                            match (p1, p2) {
                                (Some('*'), Some('/')) => {
                                    let _ = self.advance();
                                    let _ = self.advance();

                                    let end_pos = self.next_pos();
                                    self.comments.push(&self.original[pos..end_pos]);

                                    continue 'outer;
                                },
                                (None, _) => continue 'outer,
                                _ => {
                                    let _ = self.advance();
                                },
                            }
                        }
                    } else {
                        Some(TokenType::Slash)
                    }
                },
                // Skip whitespace
                ' ' | '\t' | '\r' => {
                    continue 'outer;
                },
                '\n' => {
                    self.line += 1;
                    continue 'outer;
                },
                _ => None,
            };

            // Handle the single char case
            if let Some(r#type) = r#type {
                return Ok(Some(Token {
                    r#type,
                    literal: None,
                    error: None,
                    span: Span::new(self.line, pos..(pos + 1)),
                }));
            }

            let r#type = match c {
                '!' => Some(if self.advance_if('=') {
                    TokenType::BangEqual
                } else {
                    TokenType::Bang
                }),
                '=' => Some(if self.advance_if('=') {
                    TokenType::EqualEqual
                } else {
                    TokenType::Equal
                }),
                '<' => Some(if self.advance_if('=') {
                    TokenType::LessEqual
                } else {
                    TokenType::Less
                }),
                '>' => Some(if self.advance_if('=') {
                    TokenType::GreaterEqual
                } else {
                    TokenType::Greater
                }),
                _ => None,
            };

            // Handle the double (or single) char case
            if let Some(r#type) = r#type {
                let len = r#type.length().unwrap();
                return Ok(Some(Token {
                    r#type,
                    literal: None,
                    error: None,
                    span: Span::new(self.line, pos..(pos + len)),
                }));
            }

            // Handle long tokens
            match c {
                '"' => return self.scan_string(pos),
                x if x.is_digit(10) => return self.scan_number(pos),
                x if Self::is_ident_start(x) => return Ok(Some(self.scan_identifer(pos))),
                _ => {},
            };

            return Err(ScanError::UnexpectedChar(c));
        }
    }

    fn scan_string(&mut self, start_pos: usize) -> Result<Option<Token>, ScanError> {
        loop {
            let p = self.peek().map(|(_, c)| c);

            if p == Some('"') || p.is_none() {
                break;
            }

            if p == Some('\n') {
                self.line += 1;
            }

            let _ = self.advance();
        }

        if self.peek().is_none() {
            Err(ScanError::UnterminatedString)
        } else {
            let (end_pos, _) = self.advance().unwrap();
            // exclude the start and end `"` from the literal
            let literal = Literal::String(self.original[(start_pos + 1)..end_pos].into());

            Ok(Some(Token {
                r#type: TokenType::String,
                literal: Some(literal),
                error: None,
                span: Span::new(self.line, start_pos..=end_pos),
            }))
        }
    }

    fn scan_number(&mut self, start_pos: usize) -> Result<Option<Token>, ScanError> {
        let mut end_pos = start_pos;
        loop {
            let p = self.peek().map(|(_, c)| c);

            if p.map_or(true, |c| !c.is_digit(10)) {
                break;
            }

            end_pos = self.advance().map(|(pos, _)| pos).unwrap();
        }

        let p1 = self.peek().map(|(_, c)| c);
        let p2 = self.peek2().map(|(_, c)| c);

        if p1 == Some('.') && p2.map_or(false, |c| c.is_digit(10)) {
            let _ = self.advance();

            loop {
                let p = self.peek().map(|(_, c)| c);

                if p.map_or(true, |c| !c.is_digit(10)) {
                    break;
                }

                end_pos = self.advance().map(|(pos, _)| pos).unwrap();
            }
        }

        let lexeme = &self.original[start_pos..=end_pos];
        let literal = Literal::Number(lexeme.parse().map_err(ScanError::from)?);

        Ok(Some(Token {
            r#type: TokenType::Number,
            literal: Some(literal),
            error: None,
            span: Span::new(self.line, start_pos..=end_pos),
        }))
    }

    fn is_ident_start(c: char) -> bool {
        c.is_ascii_alphabetic() || c == '_'
    }

    fn is_ident_continue(c: char) -> bool {
        c.is_ascii_alphanumeric() || c == '_'
    }

    fn scan_identifer(&mut self, start_pos: usize) -> Token {
        let mut end_pos = start_pos;
        loop {
            let p = self.peek().map(|(_, c)| c);

            if p.map_or(true, |c| !Self::is_ident_continue(c)) {
                break;
            }

            end_pos = self.advance().map(|(pos, _)| pos).unwrap();
        }

        let lexeme = &self.original[start_pos..=end_pos];

        if let Some(r#type) = self.keywords.get(lexeme).copied() {
            Token {
                span: Span::new(self.line, start_pos..=end_pos),
                r#type,
                error: None,
                literal: None,
            }
        } else {
            let literal = Literal::Identifier(lexeme.into());
            Token {
                span: Span::new(self.line, start_pos..=end_pos),
                r#type: TokenType::Identifier,
                error: None,
                literal: Some(literal),
            }
        }
    }
}

impl<'s> Iterator for Scanner<'s> {
    type Item = Token;

    fn next(&mut self) -> Option<Self::Item> {
        match self.scan_token() {
            Ok(Some(t)) => Some(t),
            Ok(None) => None,
            Err(e) => Some(Token {
                literal: None,
                error: Some(e),
                // TODO: pipe span information into the error token
                span: Span::dummy(),
                r#type: TokenType::Error,
            }),
        }
    }
}

/// A `Token` is an instance of a chunk of text with meaning, which cannot be
/// subdivided
#[derive(Debug, Clone, PartialEq)]
pub struct Token {
    /// The type of token
    pub r#type: TokenType,
    /// The value of the token, if it is a `Literal`
    pub literal: Option<Literal>,
    /// The error from the token, if it is a `TokenType::Error`,
    pub error: Option<ScanError>,
    /// The `Span` that the token occupies in the source code
    pub span: Span,
}

impl Token {
    /// Unwrap the `Identifier` literal inner `String` value, consuming this
    /// `Token`
    pub fn unwrap_identifier_name(self) -> SmolStr {
        match (self.r#type, self.literal) {
            (TokenType::Identifier, Some(Literal::Identifier(n))) => n,
            (r#type, literal) => panic!(
                "Attempted to unwrap identifier name with [{:?}] token type and [{:?}] literal",
                r#type, literal
            ),
        }
    }
}

/// A literal value embedded in the source code
#[derive(Debug, Clone, PartialEq)]
pub enum Literal {
    /// A numeric value
    Number(f64),
    /// A text value
    String(SmolStr),
    /// A name
    Identifier(SmolStr),
}

impl fmt::Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Literal::Number(n) => write!(f, "{}", n),
            Literal::String(s) => write!(f, "\"{}\"", s),
            Literal::Identifier(s) => write!(f, "{}", s),
        }
    }
}

/// The `TokenType` represent the type of the chunks of text
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum TokenType {
    // Single-character tokens
    /// `(`
    LeftParen = 0,
    /// `)`
    RightParen,
    /// `{`
    LeftBrace,
    /// `}`
    RightBrace,
    /// `,`
    Comma,
    /// `.`
    Dot,
    /// `-`
    Minus,
    /// `+`
    Plus,
    /// `;`
    Semicolon,
    /// `/`
    Slash,
    /// `*`
    Star,

    // One or two character tokens
    /// `!`
    Bang,
    /// `!=`
    BangEqual,
    /// `=`
    Equal,
    /// `==`
    EqualEqual,
    /// `>`
    Greater,
    /// `>=`
    GreaterEqual,
    /// `<`
    Less,
    /// `<=`
    LessEqual,

    // Literals
    /// An identifier is a name, such as `abc`, `a23`, `brownCowNow`
    Identifier,
    /// A piece of embedded text in the source, `"Stinsdlksjdlfkjsd"`
    String,
    /// A numerical value, `123`, `1.234`, `0.0`
    Number,

    // Keywords
    /// `and`
    And,
    /// `class`
    Class,
    /// `else`
    Else,
    /// `false`
    False,
    /// `fun`
    Fun,
    /// `for`
    For,
    /// `if`
    If,
    /// `nil`
    Nil,
    /// `or`
    Or,
    /// `print`
    Print,
    /// `return`
    Return,
    /// `super`
    Super,
    /// `this`
    This,
    /// `true`
    True,
    /// `var`
    Var,
    /// `while`
    While,

    /// Error token, used to transmit error through `Token` iterator
    // The `Error` token type must be last in the enum, as it is used as a bounds check
    Error,
}

impl TokenType {
    /// Return the mapping from keyword strings to `TokenType`s.
    pub fn keywords() -> HashMap<&'static str, TokenType> {
        let mut map = HashMap::new();
        let _ = map.insert("and", TokenType::And);
        let _ = map.insert("class", TokenType::Class);
        let _ = map.insert("else", TokenType::Else);
        let _ = map.insert("false", TokenType::False);
        let _ = map.insert("fun", TokenType::Fun);
        let _ = map.insert("for", TokenType::For);
        let _ = map.insert("if", TokenType::If);
        let _ = map.insert("nil", TokenType::Nil);
        let _ = map.insert("or", TokenType::Or);
        let _ = map.insert("print", TokenType::Print);
        let _ = map.insert("return", TokenType::Return);
        let _ = map.insert("super", TokenType::Super);
        let _ = map.insert("this", TokenType::This);
        let _ = map.insert("true", TokenType::True);
        let _ = map.insert("var", TokenType::Var);
        let _ = map.insert("while", TokenType::While);
        map
    }

    /// Return the length of the token if it is known statically
    pub fn length(self) -> Option<usize> {
        match self {
            TokenType::LeftParen => Some(1),
            TokenType::RightParen => Some(1),
            TokenType::LeftBrace => Some(1),
            TokenType::RightBrace => Some(1),
            TokenType::Comma => Some(1),
            TokenType::Dot => Some(1),
            TokenType::Minus => Some(1),
            TokenType::Plus => Some(1),
            TokenType::Semicolon => Some(1),
            TokenType::Slash => Some(1),
            TokenType::Star => Some(1),
            TokenType::Bang => Some(1),
            TokenType::BangEqual => Some(2),
            TokenType::Equal => Some(1),
            TokenType::EqualEqual => Some(2),
            TokenType::Greater => Some(1),
            TokenType::GreaterEqual => Some(2),
            TokenType::Less => Some(1),
            TokenType::LessEqual => Some(2),
            TokenType::Identifier => None,
            TokenType::String => None,
            TokenType::Number => None,
            TokenType::And => Some(3),
            TokenType::Class => Some(5),
            TokenType::Else => Some(4),
            TokenType::False => Some(5),
            TokenType::Fun => Some(3),
            TokenType::For => Some(3),
            TokenType::If => Some(2),
            TokenType::Nil => Some(3),
            TokenType::Or => Some(2),
            TokenType::Print => Some(5),
            TokenType::Return => Some(5),
            TokenType::Super => Some(5),
            TokenType::This => Some(4),
            TokenType::True => Some(4),
            TokenType::Var => Some(3),
            TokenType::While => Some(5),

            TokenType::Error => None,
        }
    }
}

impl TryFrom<u8> for TokenType {
    type Error = TokenTryFromError;

    fn try_from(value: u8) -> Result<Self, <Self as TryFrom<u8>>::Error> {
        if value <= (TokenType::Error as u8) {
            use TokenType::*;
            #[rustfmt::skip]
            const LOOKUP: [TokenType; 39] = [
                LeftParen, RightParen, LeftBrace, RightBrace, Comma, Dot, Minus,
                Plus, Semicolon, Slash, Star, Bang, BangEqual, Equal, EqualEqual,
                Greater, GreaterEqual, Less, LessEqual, Identifier, String, Number,
                And, Class, Else, False, Fun, For, If, Nil, Or, Print, Return, Super,
                This, True, Var, While, Error,
            ];

            Ok(LOOKUP[usize::try_from(value).expect("unable to fit u8 value into usize index")])
        } else {
            Err(TokenTryFromError(value))
        }
    }
}

/// An error that occurs when trying to convert from `u8` to `TokenType`.
#[derive(Debug, Copy, Clone, PartialEq, Hash, thiserror::Error)]
#[error("Attempted to convert invalid u8 [{}] to TokenType.", .0)]
pub struct TokenTryFromError(pub u8);

/// A struct which manages the state of the `Token` iterator and provides common
/// utilities
#[derive(Debug, Clone)]
pub struct Cursor<I: Iterator<Item = Token>> {
    tokens: Peekable1<I>,
    previous: Option<Token>,
}

impl<I> Cursor<I>
where
    I: Iterator<Item = Token>,
{
    /// Create a new `Cursor`
    pub fn new(tokens: impl IntoIterator<Item = Token, IntoIter = I>) -> Self {
        Cursor {
            tokens: Peekable1::new(tokens.into_iter()),
            previous: None,
        }
    }

    /// Look at the next token without advancing
    pub fn peek(&mut self) -> Option<&Token> {
        self.tokens.peek(0)
    }

    /// Advance the token stream
    pub fn advance(&mut self) -> Option<Token> {
        let o = self.tokens.next();
        self.previous = o.clone();
        o
    }

    /// Return true if the next token type matches the provided type
    pub fn check(&mut self, r#type: TokenType) -> bool {
        self.peek().map(|t| t.r#type == r#type).unwrap_or(false)
    }

    /// Advance the token stream, if the next token matches one of the provided
    /// types
    pub fn advance_if(&mut self, types: &[TokenType]) -> Option<Token> {
        for r#type in types {
            if self.check(*r#type) {
                return self.advance();
            }
        }

        None
    }

    /// Return a reference to the last `Token` that was produced, if it exists
    pub fn previous(&self) -> Option<&Token> {
        self.previous.as_ref()
    }

    /// Advance the token stream if the next token matches the provided type,
    /// otherwise throw an error
    pub fn consume(
        &mut self,
        r#type: TokenType,
        msg: &'static str,
    ) -> Result<Token, MissingTokenError> {
        if self.check(r#type) {
            Ok(self.advance().unwrap())
        } else {
            let span = self
                .peek()
                .map(|tok| tok.span.clone())
                .unwrap_or_else(Span::dummy);
            Err(MissingTokenError { msg, span })
        }
    }

    /// Return true if the token stream is empty
    pub fn is_empty(&mut self) -> bool {
        self.tokens.peek(0).is_none()
    }
}

/// A `Cursor` expected a `TokenType` that was not found
#[derive(Debug, Clone, PartialEq, Hash, thiserror::Error)]
#[error("Missing token: {} @ {:?}", .msg, .span)]
pub struct MissingTokenError {
    /// The accompanying message to the error
    pub msg: &'static str,
    /// The span of the expected token.
    ///
    /// Only the start of the span region is useful for error message, for
    /// showing where the token should have been
    pub span: Span,
}
