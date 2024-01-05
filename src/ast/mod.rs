use chumsky::input::SpannedInput;
use chumsky::prelude::*;
use chumsky::pratt::*;

use crate::lexer::{Token, Keyword};

pub mod display;

pub type Span = SimpleSpan;

#[derive(Debug, Clone)]
pub enum Type<'inp> {
    Id(&'inp str, Span),
    Pointer(Box<Type<'inp>>, Span),
    FunctionPointer {
        ret: Box<Type<'inp>>,
        args: Vec<Type<'inp>>,
        span: Span
    },
    Array {
        ty: Box<Type<'inp>>,
        len: i32,
        span: Span
    },
    Slice(Box<Type<'inp>>, Span)
}

pub type BAst<'inp> = Box<Ast<'inp>>;

#[derive(Debug, Clone)]
pub enum Ast<'inp> {
    Id(&'inp str, Span),
    Num(i32, Span),
    Literal(String, Span),
    Shorthand(Span),
    Uninit(Span),
    UnaryExpr(UnaryOp, BAst<'inp>, Span),
    BinExpr(BAst<'inp>, BinOp, BAst<'inp>, Span),
    Access(BAst<'inp>, &'inp str, Span),
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
        /// either an `Ast::IfExpr` if it's an "else if", or an `Ast::Block` if it's an "else".
        /// multiple else ifs will be stored as recursive else blocks
        else_branch: Option<Box<Ast<'inp>>>,
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
        args: Vec<(Option<&'inp str>, Ast<'inp>, Span)>,
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

impl Ast<'_> {
    pub fn span(&self) -> Span {
        match self {
            Ast::Id(_, span)              => *span,
            Ast::Num(_, span)             => *span,
            Ast::Literal(_, span)         => *span,
            Ast::Shorthand(span)          => *span,
            Ast::Uninit(span)             => *span,
            Ast::UnaryExpr(_, _, span)    => *span,
            Ast::BinExpr(_, _, _, span)   => *span,
            Ast::Access(_, _, span)       => *span,
            Ast::Declare { span, .. }     => *span,
            Ast::Assign { span, .. }      => *span,
            Ast::IfExpr { span, .. }      => *span,
            Ast::LoopExpr(_, span)        => *span,
            Ast::ForExpr { span, .. }     => *span,
            Ast::Break(_, span)           => *span,
            Ast::Continue(_, span)        => *span,
            Ast::Block(_, span)           => *span,
            Ast::FuncCall { span, .. }    => *span,
            Ast::FunctionDef { span, .. } => *span,
            Ast::StructDef { span, .. }   => *span,
            Ast::EnumDef { span, .. }     => *span,
            Ast::UnionDef { span, .. }    => *span,
        }
    }
}

/// A parameter is in the function definition, an argument is in the function call
#[derive(Debug, Clone)]
pub struct Parameter<'inp> {
    pub outward_name: Option<&'inp str>,
    pub ty: Type<'inp>,
    pub name: &'inp str,
    pub value: Option<Ast<'inp>>,
    pub span: SimpleSpan
}

#[derive(Debug, Clone)]
pub enum LValue<'inp> {
    Id(&'inp str),
    Deref(BAst<'inp>),
    Index(BAst<'inp>, BAst<'inp>),
    Field(BAst<'inp>, &'inp str)
}

#[derive(Debug, Clone)]
pub struct Block<'inp>(pub Vec<Ast<'inp>>, pub Option<BAst<'inp>>);

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
    LogicAnd, LogicOr, LogicXor,
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

/// Dirty hack to allow taking an |input, span| closure without creating a custom parser type
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

    let ty = recursive(|ty| id.map_with_span(Type::Id).pratt((
        postfix(3, just(Token::Star),         |ty, _,     span| Type::Pointer(Box::new(ty), span)),
        postfix(2, in_brackets(num),          |ty, len,   span| Type::Array { ty: Box::new(ty), len, span }),
        postfix(2, in_brackets(empty()),      |ty, _,     span| Type::Slice(Box::new(ty), span)),
        postfix(1, in_parens(comma_list(ty)), |ret, args, span| Type::FunctionPointer { ret: Box::new(ret), args, span })
    )));

    let mut block = Recursive::declare();
    let mut expr = Recursive::declare();

    {
        let if_expr = recursive(|if_expr| {
            just(Keyword::If.token())
                .ignore_then(expr.clone())
                .then(block.clone())
                .then(just(Keyword::Else.token())
                    .ignore_then(choice((
                        block.clone().map_with_span(Ast::Block), // else block
                        if_expr // else if block
                    )).map(Box::new)).or_not()
                )
                .map_with_span(|((cond, block), else_branch), span| Ast::IfExpr { cond: Box::new(cond), block, span, else_branch })
        });

        let atom_with_block = choice((
            if_expr,
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
            comma_list(
                id.then_ignore(just(Token::Equal)).or_not().then(expr.clone())
                    .map_with_span(|(name, arg), span| (name, arg, span))
            )
        )).map_with_span(|(name, args), span| Ast::FuncCall { name, args, span });

        let box_expr = expr.clone().map(Box::new);

        let atom_without_block = choice((
            func_call,
            just(Keyword::Break.token()).ignore_then(box_expr.clone().or_not()).map_with_span(Ast::Break),
            just(Keyword::Continue.token()).ignore_then(box_expr.clone().or_not()).map_with_span(Ast::Continue),
            id.map_with_span(Ast::Id),
            num.map_with_span(Ast::Num),
            literal.map_with_span(Ast::Literal),
            just(Token::Underscore).to_span().map(Ast::Shorthand),
            just(Token::TripleDash).to_span().map(Ast::Uninit),
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
            postfix(10, just(Token::Dot).ignore_then(id), |r, f, s| Ast::Access(Box::new(r), f, s)),

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

            infix(left(0), just(Token::DoubleAmpersand), |l, _, r, s| op!(l, LogicAnd, r, s)),
            infix(left(0), just(Token::DoublePipe),      |l, _, r, s| op!(l, LogicOr, r, s)),
            infix(left(0), just(Token::DoubleCaret),     |l, _, r, s| op!(l, LogicXor, r, s)),
        )));

        let lvalue = choice((
            box_expr.clone()
                .then(in_brackets(box_expr.clone()))
                .map(|(array, index)| LValue::Index(array, index)),
            just(Token::Star)
                .ignore_then(box_expr.clone())
                .map(LValue::Deref),
            expr.clone()
                .filter(|expr| matches!(expr, Ast::Access(..)))
                .map(|expr| if let Ast::Access(expr, field, _) = expr {
                    LValue::Field(expr, field)
                } else { unreachable!() }),
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
                    .map_with_span(|((outward_name, (ty, name)), value), span| Parameter { outward_name, ty, name, value, span })
            )))
            .then(block)
            .map_with_span(|(((ret, name), params), body), span| Ast::FunctionDef { ret, name, params, body, span });

        choice((struct_def, union_def, enum_def, function_def))
    };

    definition.repeated().collect()
}
