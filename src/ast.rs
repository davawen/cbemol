
use chumsky::combinator;
use chumsky::input::MapExtra;
use chumsky::input::SpannedInput;
use chumsky::prelude::*;
use chumsky::pratt::*;

use crate::lexer::{Token, Keyword};

pub type Span = SimpleSpan;

#[derive(Debug, Clone)]
pub enum Type<'inp> {
    Id(&'inp str),
    Pointer(Box<Type<'inp>>),
    FunctionPointer {
        ret: Box<Type<'inp>>,
        args: Vec<Type<'inp>>
    },
    Array {
        ty: Box<Type<'inp>>,
        len: i32
    },
    Slice(Box<Type<'inp>>)
}

pub type BAst<'inp> = Box<Ast<'inp>>;

#[derive(Debug, Clone)]
pub enum Ast<'inp> {
    Id(&'inp str, Span),
    Num(i32, Span),
    Literal(String, Span),
    UnaryExpr(UnaryOp, BAst<'inp>, Span),
    BinExpr(BAst<'inp>, BinOp, BAst<'inp>, Span),
    Declare {
        var: &'inp str,
        ty: Type<'inp>,
        value: Option<BAst<'inp>>,
        span: Span
    },
    Assign {
        var: LValue<'inp>,
        value: BAst<'inp>,
        span: Span
    },
    IfExpr {
        cond: BAst<'inp>,
        block: Block<'inp>,
        span: Span
    },
    LoopExpr(Block<'inp>, Span),
    ForExpr {
        decl: (Type<'inp>, &'inp str),
        it: BAst<'inp>,
        body: Block<'inp>,
        span: Span
    },
    Break(Option<BAst<'inp>>, Span),
    Continue(Option<BAst<'inp>>, Span),
    Block(Block<'inp>, Span),
    FuncCall {
        name: &'inp str,
        args: Vec<(Option<&'inp str>, Ast<'inp>)>,
        span: Span
    },
    FunctionDef {
        name: &'inp str,
        ret: Type<'inp>,
        params: Vec<Parameter<'inp>>,
        body: Block<'inp>,
        span: Span
    },
    StructDef {
        name: &'inp str,
        fields: Vec<(Type<'inp>, &'inp str)>,
        span: Span
    },
    EnumDef {
        name: &'inp str,
        variants: Vec<(&'inp str, Option<i32>)>,
        span: Span
    },
    UnionDef {
        name: &'inp str,
        variants: Vec<(Type<'inp>, &'inp str)>,
        span: Span
    },
}

/// A parameter is in the function definition, an argument is in the function call
#[derive(Debug, Clone)]
pub struct Parameter<'inp> {
    outward_name: Option<&'inp str>,
    ty: Type<'inp>,
    name: &'inp str,
    value: Option<Ast<'inp>>
}

#[derive(Debug, Clone)]
pub enum LValue<'inp> {
    Id(&'inp str),
    Deref(BAst<'inp>),
    Index(BAst<'inp>, BAst<'inp>)
}

#[derive(Debug, Clone)]
pub struct Block<'inp>(Vec<Ast<'inp>>, Option<BAst<'inp>>);

#[derive(Debug, Clone)]
pub enum UnaryOp {
    AddressOf,
    Deref,
    Negate,
    Not
}

#[derive(Debug, Clone)]
pub enum BinOp {
    Add, Sub, Mul, Div, Mod,
    BinAnd, BinOr, BinXor,
    And, Or, Xor,
    Eq, Ne, Gt, Ge, Lt, Le,
    Range,
    Pipe
}

type TInput<'a> = SpannedInput<Token<'a>, SimpleSpan, &'a [(Token<'a>, SimpleSpan)]>;
type Extra<'a> = chumsky::extra::Err<Rich<'a, Token<'a>>>;

fn in_parens<'a, T, P: Parser<'a, TInput<'a>, T, Extra<'a>> + Clone>(p: P) -> impl Parser<'a, TInput<'a>, T, Extra<'a>> + Clone {
    p.delimited_by(just(Token::LParen), just(Token::RParen))
}

fn in_braces<'a, T, P: Parser<'a, TInput<'a>, T, Extra<'a>> + Clone>(p: P) -> impl Parser<'a, TInput<'a>, T, Extra<'a>> + Clone {
    p.delimited_by(just(Token::LBrace), just(Token::RBrace))
}

fn in_brackets<'a, T, P: Parser<'a, TInput<'a>, T, Extra<'a>> + Clone>(p: P) -> impl Parser<'a, TInput<'a>, T, Extra<'a>> + Clone {
    p.delimited_by(just(Token::LBracket), just(Token::RBracket))
}

fn comma_list<'a, T, P: Parser<'a, TInput<'a>, T, Extra<'a>>+ Clone>(p: P) -> impl Parser<'a, TInput<'a>, Vec<T>, Extra<'a>> + Clone {
    p.separated_by(just(Token::Comma)).collect()
}

/// Horrible hack to allow taking a |input, span| -> output closure without creating a custom parser type
trait ParserSpan<'a, I: Input<'a>, O, E: extra::ParserExtra<'a, I>>: Sized + Parser<'a, I, O, E> {
    fn map_with_span<U, F: Clone + Fn(O, I::Span) -> U>(self, f: F) -> impl Parser<'a, I, U, E>;
}

impl<'a, I: Input<'a>, O, E: extra::ParserExtra<'a, I>, P: Parser<'a, I, O, E> + Clone> ParserSpan<'a, I, O, E> for P {
    #[inline(always)]
    fn map_with_span<U, F: Clone + Fn(O, I::Span) -> U>(self, f: F) -> impl Parser<'a, I, U, E> + Clone {
        self
            .map_with(|o, e| (o, e.span()))
            .map(move |(o, span)| f(o, span))
    }
}

pub fn parser<'a>() -> impl Parser<'a, TInput<'a>, Vec<Ast<'a>>, Extra<'a>> {
    let id = any().filter(|x| matches!(x, Token::Id(_))).map(|x| if let Token::Id(s) = x { s } else { unreachable!() });
    let num = any().filter(|x| matches!(x, Token::Num(_))).map(|x| if let Token::Num(n) = x { n } else { unreachable!() });
    let literal = any().filter(|x| matches!(x, Token::StrLiteral(_))).map(|x| if let Token::StrLiteral(s) = x { s } else { unreachable!() });

    let ty = recursive(|ty| id.map(Type::Id).pratt((
        postfix(3, just(Token::Ampersand), |ty| Type::Pointer(Box::new(ty))),
        postfix(2, in_brackets(num), |ty, len| Type::Array { ty: Box::new(ty), len }),
        postfix(2, in_brackets(empty()), |ty| Type::Slice(Box::new(ty))),
        postfix(1, in_parens(comma_list(ty)), |ret, args| Type::FunctionPointer { ret: Box::new(ret), args })
    )));

    let mut block = Recursive::declare();
    let mut expr = Recursive::declare();

    {
        let atom_with_block = choice((
            just(Keyword::If.token())
                .ignore_then(expr.clone())
                .then(block.clone())
                .map_with_span(|(cond, block), span| Ast::IfExpr { cond: Box::new(cond), block, span }),
            just(Keyword::For.token())
                .ignore_then(ty.clone().then(id))
                .then_ignore(just(Keyword::In.token()))
                .then(expr.clone())
                .then(block.clone())
                .map_with_span(|((decl, it), body), span| Ast::ForExpr { decl, it: Box::new(it), body, span }),
            just(Keyword::Loop.token())
                .ignore_then(block.clone())
                .map_with_span(Ast::LoopExpr),
            block.clone().map_with_span(Ast::Block)
        ));

        let func_call = id.then(in_parens(
            comma_list(id.then_ignore(just(Token::Equal)).or_not().then(expr.clone()))
        ))
            .map_with_span(|(name, args), span| Ast::FuncCall { name, args, span });

        let box_expr = expr.clone().map(Box::new);

        let atom_without_block = choice((
            func_call,
            just(Keyword::Break.token()).ignore_then(box_expr.clone().or_not()).map_with_span(Ast::Break),
            just(Keyword::Continue.token()).ignore_then(box_expr.clone().or_not()).map_with_span(Ast::Continue),
            id.map_with_span(Ast::Id),
            num.map_with_span(Ast::Num),
            literal.map_with_span(Ast::Literal),
            in_parens(expr.clone())
        ));

        let atom = atom_with_block.clone().or(atom_without_block);

        macro_rules! op {
            ($unary:ident, $value:expr, $span:expr) => {
                Ast::UnaryExpr(UnaryOp::$unary, Box::new($value), $span)
            };
            ($a:expr, $binary:ident, $b: expr, $span:expr) => {
                Ast::BinExpr(Box::new($a), BinOp::$binary, Box::new($b), $span)
            }
        }

        expr.define(atom.pratt((
            prefix(9, just(Token::Minus),       |_, r, s| op!(Negate, r, s)),
            prefix(9, just(Token::Ampersand),   |_, r, s| op!(AddressOf, r, s)),
            prefix(9, just(Token::Star),        |_, r, s| op!(Deref, r, s)),
            prefix(9, just(Token::Exclamation), |_, r, s| op!(Not, r, s)),

            infix(left(8), just(Token::Ampersand), |l, _, r, s| op!(l, And, r, s)),
            infix(left(8), just(Token::Pipe),      |l, _, r, s| op!(l, Or, r, s)),
            infix(left(8), just(Token::Caret),     |l, _, r, s| op!(l, Xor, r, s)),

            infix(left(7), just(Token::Percent), |l, _, r, s| op!(l, Mod, r, s)),

            infix(left(6), just(Token::Star),  |l, _, r, s| op!(l, Mul, r, s)),
            infix(left(6), just(Token::Slash), |l, _, r, s| op!(l, Div, r, s)),
            infix(left(5), just(Token::Plus),  |l, _, r, s| op!(l, Add, r, s)),
            infix(left(5), just(Token::Minus), |l, _, r, s| op!(l, Sub, r, s)),

            infix(left(4), just(Token::DotDot), |l, _, r, s| op!(l, Range, r, s)),

            infix(left(3), just(Token::Pipeline), |l, _, r, s| op!(l, Pipe, r, s)),

            infix(left(2), just(Token::Gt), |l, _, r, s| op!(l, Gt, r, s)),
            infix(left(2), just(Token::Ge), |l, _, r, s| op!(l, Ge, r, s)),
            infix(left(2), just(Token::Lt), |l, _, r, s| op!(l, Lt, r, s)),
            infix(left(2), just(Token::Le), |l, _, r, s| op!(l, Le, r, s)),

            infix(left(1), just(Token::Eq), |l, _, r, s| op!(l, Eq, r, s)),
            infix(left(1), just(Token::Ne), |l, _, r, s| op!(l, Ne, r, s)),

            infix(left(0), just(Token::DoubleAmpersand), |l, _, r, s| op!(l, BinAnd, r, s)),
            infix(left(0), just(Token::DoublePipe),      |l, _, r, s| op!(l, BinOr, r, s)),
            infix(left(0), just(Token::DoubleCaret),     |l, _, r, s| op!(l, BinXor, r, s)),
        )));

        let lvalue = choice((
            box_expr.clone()
                .then(in_brackets(box_expr.clone()))
                .map(|(array, index)| LValue::Index(array, index)),
            just(Token::Star)
                .ignore_then(box_expr.clone())
                .map(LValue::Deref),
            id.map(LValue::Id)
        ));

        let statement = choice((
            ty.clone()
                .then(id)
                .then(just(Token::Equal).ignore_then(box_expr.clone()).or_not())
                .then_ignore(just(Token::Semicolon))
                .map_with_span(|((ty, var), value), span| Ast::Declare { ty, var, value, span }),
            lvalue
                .then_ignore(just(Token::Equal))
                .then(box_expr.clone())
                .then_ignore(just(Token::Semicolon))
                .map_with_span(|(var, value), span| Ast::Assign { var, value, span }),
            expr.clone().then_ignore(just(Token::Semicolon)),
            atom_with_block.clone() // block exprs are allowed to be statements without a semicolon
        ));

        block.define(
            in_braces(
                atom_with_block.then(just(Token::RBrace)).not().rewind() // however, this makes sure that a block expression at the end of a block will be counted as the end expr
                    .ignore_then(statement)
                    .repeated().collect().then(box_expr.or_not())
            )
                .map(|(statements, expr)| Block(statements, expr))
        );
    }

    let definition = {
        let struct_def = just(Keyword::Struct.token())
            .ignore_then(id)
            .then(in_braces(
                ty.clone().then(id).then_ignore(just(Token::Semicolon))
                    .repeated().collect()
            ))
            .map_with_span(|(name, fields), span| Ast::StructDef { name, fields, span });

        let union_def = just(Keyword::Union.token())
            .ignore_then(id)
            .then(in_braces(
                ty.clone().then(id).then_ignore(just(Token::Semicolon))
                    .repeated().collect()
            ))
            .map_with_span(|(name, variants), span| Ast::UnionDef { name, variants, span });

        let enum_def = just(Keyword::Enum.token())
            .ignore_then(id)
            .then(in_braces(comma_list(
                id.then(just(Token::Equal).ignore_then(num).or_not())
            )))
            .map_with_span(|(name, variants), span| Ast::EnumDef { name, variants, span });

        let function_def = ty.clone()
            .then(id)
            .then(in_parens(comma_list(
                id
                    .then_ignore(just(Token::Colon)).or_not()
                    .then(ty.then(id))
                    .then(just(Token::Equal).ignore_then(expr.clone()).or_not())
                    .map(|((outward_name, (ty, name)), value)| Parameter { outward_name, ty, name, value })
            )))
            .then(block)
            .map_with_span(|(((ret, name), params), body), span| Ast::FunctionDef { ret, name, params, body, span });

        choice((struct_def, union_def, enum_def, function_def))
    };

    definition.repeated().collect()
}

impl std::fmt::Display for Ast<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        const GRAY: &str = "\x1b[90m";
        const RESET: &str = "\x1b[0m";
        const ORANGE: &str = "\x1b[33m";
        const GREEN: &str = "\x1b[32m";
        const MAGENTA: &str = "\x1b[34m";
        const CYAN: &str = "\x1b[36m";

        use Ast as A;
        match self {
            A::Id(id, span)                 => write!(f, "{GRAY}{span} {MAGENTA}IDENT {RESET}{id}"),
            A::Num(n, span)                 => write!(f, "{GRAY}{span} {MAGENTA}NUM {ORANGE}{n}{RESET}"),
            A::Literal(l, span)             => write!(f, "{GRAY}{span} {MAGENTA}LITERAL {GREEN}{l:?}{RESET}"),
            A::UnaryExpr(op, e, span)       => write!(f, "{GRAY}{span} {MAGENTA}OP {RESET}{op} {e}"),
            A::BinExpr(a, op, b, span)      => write!(f, "{GRAY}{span} {MAGENTA}OP {RESET}{op} {a} {b}"),
            A::Assign { var, value, span }  => write!(f, "{GRAY}{span} {MAGENTA}ASSIGN {RESET}{var} = {value}"),
            A::IfExpr { cond, block, span } => write!(f, "{GRAY}{span} {MAGENTA}IF {RESET}{cond} THEN {block}"),
            A::LoopExpr(block, span)        => write!(f, "{GRAY}{span} {MAGENTA}LOOP {RESET}{block}"),
            A::Break(Some(e), span)         => write!(f, "{GRAY}{span} {MAGENTA}BREAK {RESET}{e}"),
            A::Break(None, span)            => write!(f, "{GRAY}{span} {MAGENTA}BREAK {RESET}"),
            A::Continue(Some(e), span)      => write!(f, "{GRAY}{span} {MAGENTA}CONTINUE{RESET} {e}"),
            A::Continue(None, span)         => write!(f, "{GRAY}{span} {MAGENTA}CONTINUE{RESET}"),
            A::Block(b, span)               => write!(f, "{GRAY}{span} {RESET}{b}"),
            A::ForExpr { decl: (ty, name), it, body, span } => 
                write!(f, "{GRAY}{span} {MAGENTA}FOR {CYAN}{ty} {RESET}{name} IN {it} {body}"),
            A::Declare { var, ty, value: Some(value), span } => 
                write!(f, "{GRAY}{span} {MAGENTA}DECLARE {CYAN}{ty} {RESET}{var} = {value}"),
            A::Declare { var, ty, value: None, span } => 
                write!(f, "{GRAY}{span} {MAGENTA}DECLARE {CYAN}{ty} {RESET}{var}"),
            A::FuncCall { name, args, span } => {
                write!(f, "{GRAY}{span} {MAGENTA}CALL {RESET}{name} (")?;
                for arg in args {
                    if let (Some(arg), expr) = arg {
                        write!(f, "{arg} = {expr}, ")?;
                    } else {
                        write!(f, "{}", arg.1)?;
                    }
                }
                write!(f, ")")
            }
            A::FunctionDef { name, ret, params, body, span } => {
                write!(f, "{GRAY}{span} {MAGENTA}DEFINE FUNC {CYAN}{ret} {RESET}{name} (")?;
                for param in params {
                    write!(f, "{param}")?;
                }
                write!(f, ") {body}")
            }
            A::StructDef { name, fields, span } => {
                write!(f, "{GRAY}{span} {MAGENTA}DEFINE STRUCT {CYAN}{name}{RESET} {{")?;
                for (ty, name) in fields {
                    writeln!(f, "  {CYAN}{ty} {RESET}{name};")?;
                }
                write!(f, "}}")
            }
            A::EnumDef { name, variants, span } => {
                writeln!(f, "{GRAY}{span} {MAGENTA}DEFINE ENUM {CYAN}{name} {RESET}{{")?;
                for (name, value) in variants {
                    write!(f, "  {name}")?;
                    if let Some(value) = value {
                        write!(f, " = {ORANGE}{value}{RESET}")?;
                    }
                    writeln!(f, ";")?;
                }
                write!(f, "}}")
            }
            A::UnionDef { name, variants, span } => {
                writeln!(f, "{GRAY}{span} {MAGENTA}DEFINE UNION {CYAN}{name} {RESET}{{")?;
                for (ty, name) in variants {
                    writeln!(f, "  {CYAN}{ty} {RESET}{name};")?;
                }
                write!(f, "}}")
            }
        }
    }
}

impl std::fmt::Display for Parameter<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        const CYAN: &str = "\x1b[36m";
        const RESET: &str = "\x1b[0m";
        if let Some(name) = self.outward_name {
            write!(f, "{name}: ")?;
        }
        write!(f, "{CYAN}{} {RESET}{}", self.ty, self.name)?;
        if let Some(value) = &self.value {
            write!(f, " = {value}")?;
        }
        Ok(())
    }
}

impl std::fmt::Display for Block<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use std::fmt::Write;
        let mut s = String::new();
        for statement in &self.0 {
            writeln!(s, "{statement};")?;
        }

        if let Some(expr) = &self.1 {
            writeln!(s, "{expr}")?;
        }

        writeln!(f, "{{")?;
        for line in s.lines() {
            writeln!(f, "  {line}")?;
        }
        write!(f, "}}")
    }
}

impl std::fmt::Display for Type<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Type as T;
        match self {
            T::Id(id) => write!(f, "{id}"),
            T::Pointer(ty) => write!(f, "{ty}&"),
            T::FunctionPointer { ret, args } => {
                write!(f, "{ret}(")?;
                for arg in args {
                    write!(f, "{arg}, ")?;
                }
                write!(f, ")")
            }
            T::Array { ty, len } => write!(f, "{ty}[{len}]"),
            T::Slice(ty) => write!(f, "{ty}[]")
        }
    }
}

impl std::fmt::Display for LValue<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use LValue as L;
        match self {
            L::Id(id) => write!(f, "{id}"),
            L::Deref(l) => write!(f, "*{l}"),
            L::Index(l, i) => write!(f, "{l}[{i}]")
        }
    }
}

impl std::fmt::Display for UnaryOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use UnaryOp as O;
        let s = match self {
            O::Not => "!", O::Deref => "*",
            O::Negate => "-", O::AddressOf => "&"
        };
        write!(f, "{s}")
    }
}

impl std::fmt::Display for BinOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use BinOp as O;
        let s = match self {
            O::Add => "+", O::Sub => "-", O::Mul => "*", O::Div => "/", O::Mod => "%",
            O::BinAnd => "&&", O::BinOr => "||", O::BinXor => "^^",
            O::And => "&", O::Or => "|", O::Xor => "^",
            O::Eq => "==", O::Ne => "!=", O::Gt => ">", O::Ge => ">=", O::Lt => "<", O::Le => "<=",
            O::Range => "..",
            O::Pipe => "|>"
        };
        write!(f, "{s}")
    }
}
