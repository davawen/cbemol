use ast::parser;
use chumsky::{Parser, prelude::Input};
use lexer::lexer;
use error::show_errs;

mod lexer;
mod ast;
mod ir;
mod error;

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

void main() {
    i32 a = 0;
    bool b;
    i32 c = a + b;
    i32& d = &(&a);
    *d = 10;
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
    let mut p = match p {
        Ok(p) => p,
        Err(e) => {
            show_errs(input, "stdin", vec![e]);
            return;
        }
    };
    println!("{p}");

    let type_errs = p.typecheck();
    if !type_errs.is_empty() {
        show_errs(input, "stdin", type_errs);
    }
    // println!("{p}");
}
