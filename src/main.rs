use std::fmt::Display;

use ariadne::{Report, ReportKind, Label, Color};
use ast::parser;
use chumsky::{Parser, prelude::{Input, Rich}};
use lexer::lexer;

mod lexer;
mod ast;

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
struct Piece {
    i32 x;
    i32 y;
    PieceValue value;
}

enum PieceValue {
    Pawn = 1,
    Bishop = 2,
    Rook = 4,
    Queen = 8,
    King = 16
}

void imgui_sdjk(char[] msg, before: char[] prefix, x: int posx = 0, y: int posy = 0) {

}

void main() {
    Piece[64] board;

    int i = 0;
    loop {
        if i >= 64 { break }
        
        board[i] = Piece(x = i % 8, y = i / 8, value = Pawn);

        i = i + 1;
    }

    if i == 64 {
        print(great)
    }
}
    "#;

    let (lexed, errs) = lexer().parse(input).into_output_errors();
    show_errs(input, "stdin", errs);

    let Some(lexed) = lexed else { return };

    let (parsed, errs) = parser().parse(Input::spanned(&lexed, (input.len()..input.len()).into())).into_output_errors();
    show_errs(input, "stdin", errs);

    let Some(parsed) = parsed else { return };
    println!("{parsed:#?}");
}
