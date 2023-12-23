use std::fmt::Display;

use chumsky::prelude::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Token<'a> {
    Id(&'a str),
    Num(i32),
    Keyword(Keyword),
    Ampersand,
    Star,
    Pipeline,
    Plus,
    Minus,
    Slash,
    Colon,
    Semicolon,
    Percent,
    Gt, Ge, Lt, Le, Eq, Ne,
    DotDot,
    Comma,
    Equal,
    LBracket,
    RBracket,
    LParen,
    RParen,
    LBrace,
    RBrace,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Keyword {
    Struct, Union, Enum, If, For, In, Continue, Break, Loop
}

impl Keyword {
    pub fn token(self) -> Token<'static> {
        Token::Keyword(self)
    }
}

impl Display for Token<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Token as T;
        match self {
            T::Id(s)      => write!(f, "{s}"),
            T::Num(n)     => write!(f, "{n}"),
            T::Keyword(k) => write!(f, "{k:?}"),
            T::Ampersand  => write!(f, "&"),
            T::Star       => write!(f, "*"),
            T::Pipeline   => write!(f, "|>"),
            T::Plus       => write!(f, "+"),
            T::Minus      => write!(f, "-"),
            T::Slash      => write!(f, "/"),
            T::Colon      => write!(f, ":"),
            T::Semicolon  => write!(f, ";"),
            T::Percent    => write!(f, "%"),
            T::Gt         => write!(f, ">"),
            T::Ge         => write!(f, ">="),
            T::Lt         => write!(f, "<"),
            T::Le         => write!(f, "<="),
            T::Eq         => write!(f, "=="),
            T::Ne         => write!(f, "!="),
            T::DotDot     => write!(f, ".."),
            T::Comma      => write!(f, ","),
            T::Equal      => write!(f, "="),
            T::LBracket   => write!(f, "["),
            T::RBracket   => write!(f, "]"),
            T::LParen     => write!(f, "("),
            T::RParen     => write!(f, ")"),
            T::LBrace     => write!(f, "{{"),
            T::RBrace     => write!(f, "}}"),
        }
    }
}

pub fn lexer<'a>() -> impl Parser<'a, &'a str, Vec<(Token<'a>, SimpleSpan)>, extra::Err<Rich<'a, char>>> {
    let ident = text::ident().map(|id: &str| match id {
        "struct" => Keyword::Struct.token(),
        "union" => Keyword::Union.token(),
        "enum" => Keyword::Enum.token(),
        "if" => Keyword::If.token(),
        "for" => Keyword::For.token(),
        "in" => Keyword::In.token(),
        "continue" => Keyword::Continue.token(),
        "break" => Keyword::Break.token(),
        "loop" => Keyword::Loop.token(),
        _ => Token::Id(id)
    });

    let num = text::digits(10).to_slice().map(|s: &str| s.parse().unwrap()).map(Token::Num);

    let symbol = choice([
        just("&").to(Token::Ampersand),
        just("*").to(Token::Star),
        just("|>").to(Token::Pipeline),
        just("+").to(Token::Plus),
        just("-").to(Token::Minus),
        just("/").to(Token::Slash),
        just(":").to(Token::Colon),
        just(";").to(Token::Semicolon),
        just("%").to(Token::Percent),
        just(">=").to(Token::Ge), just(">").to(Token::Gt),
        just("<=").to(Token::Le), just("<").to(Token::Lt),
        just("==").to(Token::Eq), just("!=").to(Token::Ne),
        just("..").to(Token::DotDot),
        just(",").to(Token::Comma),
        just("=").to(Token::Equal),
        just("[").to(Token::LBracket), just("]").to(Token::RBracket),
        just("(").to(Token::LParen), just(")").to(Token::RParen),
        just("{").to(Token::LBrace), just("}").to(Token::RBrace),
    ]);

    // let comment = just("//").then(none_of("\n\r").repeated()).padded();

    let token = ident.or(num).or(symbol);

    token
        .map_with(|t, e| (t, e.span()))
        // .padded_by(comment)
        .padded()
        .repeated().collect()
        .then_ignore(end())
}
