use std::{fmt::{Display, Debug}, ops::Range};

use ariadne::{Report, ReportKind, Label, Color};
use ast::parser;
use chumsky::{Parser, prelude::{Input, Rich}, span::SimpleSpan};
use lexer::lexer;

mod lexer;
mod ast;
mod ir;

trait CompilerError: Sized {
    fn map(self) -> impl CompilerError { self }
    fn span(&self) -> SimpleSpan;
    fn message(&self) -> String;
    fn labels(self, filename: &str) -> Vec<Label<(&str, Range<usize>)>>;
}

impl<T: Clone + Display + Debug> CompilerError for Rich<'_, T> {
    fn map(self) -> impl CompilerError { self.map_token(|c| c.to_string()) }
    fn span(&self) -> SimpleSpan { *self.span() }
    fn message(&self) -> String { self.to_string() }
    fn labels(self, filename: &str) -> Vec<Label<(&str, Range<usize>)>> {
        vec![
            Label::new((filename, self.span().into_range()))
                .with_message(format!("Expected: {:?}", self.expected().collect::<Vec<_>>()))
                .with_color(Color::Red)
        ]
    }
}

impl CompilerError for ir::lower::Error {
    fn span(&self) -> SimpleSpan {
        self.label.as_ref().map(|x| x.0).unwrap_or(SimpleSpan::new(0, 0))
    }
    fn message(&self) -> String { self.message.clone() }
    fn labels(self, filename: &str) -> Vec<Label<(&str, Range<usize>)>> {
        self.label.into_iter().map(|(span, message)| 
            Label::new((filename, span.into_range()))
                .with_message(message)
                .with_color(Color::Red)
        ).collect()
    }
}

fn show_errs(src: &str, filename: &str, errs: Vec<impl CompilerError>) {
    let mut cache = (filename, src.into());

    errs.into_iter()
        .map(|e| e.map())
        .for_each(|e| {
            Report::build(ReportKind::Error, filename, e.span().start)
                .with_message(e.message())
                .with_labels(e.labels(filename))
                .finish()
                .eprint(&mut cache)
                .unwrap()
        });
}

fn main() {
    let input = r#"
union OptionInt {
    i32 some;
    void none;
}

enum PieceKind {
    None,
    Pawn,
    Bishop,
    Knight = 4,
    Rook = 8,
    Queen = 16,
    King = 32
}

struct Piece {
    PieceKind kind;
    i32 x;
    i32 y;
    OptionInt count;
}

struct Vec2 {
    i32 x;
    i32 y;
}

struct Vec3 {
    Vec2 v;
    i32 z;
}

Vec3 Vec3(v: Vec2 v, z: i32 z) {
    Vec3 self;
    // do stuff
    self
}

Vec2 Vec2(x: i32 x, y: i32 y) {
    Vec2 self;
    // do stuff
    self
}

void printf(i32 x) {
    // do stuff
}

void main() {
    i32 x = ---;

    printf(x); // hmmm

    i32 i = 0;
    //loop {
        break i * 4 + 1;

        printf("\"message!\"\n");

        i = i + 1;
    //}
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
    for parsed in &parsed {
        println!("{parsed}");
    }

    let p = ir::Program::lower(&parsed);
    let p = match p {
        Ok(p) => p,
        Err(e) => {
            show_errs(input, "stdin", vec![e]);
            return;
        }
    };

    println!("{p}");
}
