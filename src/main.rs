use std::fmt::Display;

use ariadne::{Report, ReportKind, Label, Color};
use ast::parser;
use chumsky::{Parser, prelude::{Input, Rich}};
use lexer::lexer;

mod lexer;
mod ast;
mod ir;

fn show_errs<T: Clone + Display>(src: &str, filename: &str, errs: Vec<Rich<T>>) {
    let mut cache = (filename, src.into());

    errs.into_iter()
        .map(|e| e.map_token(|c| c.to_string()))
        .for_each(|e| {
            Report::build(ReportKind::Error, filename, e.span().start)
                .with_message(e.to_string())
                .with_label(
                    Label::new((filename, e.span().into_range()))
                        .with_message(format!("Expected: {:?}", e.expected().collect::<Vec<_>>()))
                        .with_color(Color::Red),
                )
                .finish()
                .eprint(&mut cache)
                .unwrap()
        });
}

fn main() {
    let input = r#"
enum Piece {
    Pawn = 1,
    Bishop = 2,
    Knight = 4,
    Rook = 8,
    Queen = 16,
    King = 32
}

union Option {
    Piece some;
    void none;
}

struct Selected {
    int cursorx;
    int cursory;
    Option selected;
}

void printf(char[] msg) { 
    // ...
}

void main() {
    int i = 0;
    loop {
        if i >= 5 { break }

        printf("\"message!\"\n");

        i = i + 1;
    }
}
    "#;

    println!("lexing");
    let (lexed, errs) = lexer().parse(input).into_output_errors();
    show_errs(input, "stdin", errs);

    let Some(lexed) = lexed else { return };

    println!("parsing");
    let (parsed, errs) = parser().parse(Input::spanned(&lexed, (input.len()..input.len()).into())).into_output_errors();
    show_errs(input, "stdin", errs);

    let Some(parsed) = parsed else { return };
    for parsed in parsed {
        println!("{parsed}");
    }
}
