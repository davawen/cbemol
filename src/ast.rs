use chumsky::input::MapExtra;
use chumsky::input::SpannedInput;
use chumsky::prelude::*;
use chumsky::pratt::*;

use crate::lexer::{Token, Keyword};

pub type Spanned<T> = (T, SimpleSpan);

fn spanned<'a, T, I: Input<'a>, E: extra::ParserExtra<'a, I>>(t: T, e: &mut MapExtra<'a, '_, I, E>) -> (T, I::Span) {
    (t, e.span())
}

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

pub type SAst<'inp> = Spanned<Ast<'inp>>;
pub type BAst<'inp> = Box<SAst<'inp>>;

#[derive(Debug, Clone)]
pub enum Ast<'inp> {
    Id(&'inp str),
    Num(i32),
    Literal(String),
    UnaryExpr(UnaryOp, BAst<'inp>),
    BinExpr(BAst<'inp>, BinOp, BAst<'inp>),
    Declare {
        var: &'inp str,
        ty: Type<'inp>,
        value: Option<BAst<'inp>>
    },
    Assign {
        var: LValue<'inp>,
        value: BAst<'inp>
    },
    IfExpr {
        cond: BAst<'inp>,
        block: Block<'inp>
    },
    LoopExpr(Block<'inp>),
    ForExpr {
        decl: (Type<'inp>, &'inp str),
        it: BAst<'inp>,
        body: Block<'inp>
    },
    Break(Option<BAst<'inp>>),
    Continue(Option<BAst<'inp>>),
    Block(Block<'inp>),
    FuncCall {
        name: &'inp str,
        args: Vec<(Option<&'inp str>, SAst<'inp>)>
    },
    FunctionDef {
        name: &'inp str,
        ret: Type<'inp>,
        params: Vec<Parameter<'inp>>,
        body: Block<'inp>
    },
    StructDef {
        name: &'inp str,
        fields: Vec<(Type<'inp>, &'inp str)>
    },
    EnumDef {
        name: &'inp str,
        variants: Vec<(&'inp str, Option<i32>)>
    },
    UnionDef {
        name: &'inp str,
        variants: Vec<(Type<'inp>, &'inp str)>
    },
}

/// A parameter is in the function definition, an argument is in the function call
#[derive(Debug, Clone)]
pub struct Parameter<'inp> {
    outward_name: Option<&'inp str>,
    ty: Type<'inp>,
    name: &'inp str,
    value: Option<SAst<'inp>>
}

#[derive(Debug, Clone)]
pub enum LValue<'inp> {
    Id(&'inp str),
    Deref(BAst<'inp>),
    Index(BAst<'inp>, BAst<'inp>)
}

#[derive(Debug, Clone)]
pub struct Block<'inp>(Vec<SAst<'inp>>, Option<BAst<'inp>>);

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

pub fn parser<'a>() -> impl Parser<'a, TInput<'a>, Vec<SAst<'a>>, Extra<'a>> {
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
                .map(|(cond, block)| Ast::IfExpr { cond: Box::new(cond), block }),
            just(Keyword::For.token())
                .ignore_then(ty.clone().then(id))
                .then_ignore(just(Keyword::In.token()))
                .then(expr.clone())
                .then(block.clone())
                .map(|((decl, it), body)| Ast::ForExpr { decl, it: Box::new(it), body }),
            just(Keyword::Loop.token())
                .ignore_then(block.clone())
                .map(Ast::LoopExpr),
            block.clone().map(Ast::Block)
        )).map_with(spanned);

        let func_call = id.then(in_parens(
            comma_list(id.then_ignore(just(Token::Equal)).or_not().then(expr.clone()))
        ))
            .map(|(name, args)| Ast::FuncCall { name, args });

        let box_expr = expr.clone().map(Box::new);

        let atom_without_block = choice((
            func_call,
            just(Keyword::Break.token()).ignore_then(box_expr.clone().or_not()).map(Ast::Break),
            just(Keyword::Continue.token()).ignore_then(box_expr.clone().or_not()).map(Ast::Continue),
            id.map(Ast::Id),
            num.map(Ast::Num),
            literal.map(Ast::Literal)
        )).map_with(spanned).or(in_parens(expr.clone()));

        let atom = atom_with_block.clone().or(atom_without_block);

        macro_rules! op {
            ($unary:ident, $value:expr, $span:expr) => {
                (Ast::UnaryExpr(UnaryOp::$unary, Box::new($value)), $span)
            };
            ($a:expr, $binary:ident, $b: expr, $span:expr) => {
                (Ast::BinExpr(Box::new($a), BinOp::$binary, Box::new($b)), $span)
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
                .map(|((ty, var), value)| Ast::Declare { ty, var, value })
                .map_with(spanned),
            lvalue
                .then_ignore(just(Token::Equal))
                .then(box_expr.clone())
                .then_ignore(just(Token::Semicolon))
                .map(|(var, value)| Ast::Assign { var, value })
                .map_with(spanned),
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
            .map(|(name, fields)| Ast::StructDef { name, fields });

        let union_def = just(Keyword::Union.token())
            .ignore_then(id)
            .then(in_braces(
                ty.clone().then(id).then_ignore(just(Token::Semicolon))
                    .repeated().collect()
            ))
            .map(|(name, variants)| Ast::UnionDef { name, variants });

        let enum_def = just(Keyword::Enum.token())
            .ignore_then(id)
            .then(in_braces(comma_list(
                id.then(just(Token::Equal).ignore_then(num).or_not())
            )))
            .map(|(name, variants)| Ast::EnumDef { name, variants });

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
            .map(|(((ret, name), params), body)| Ast::FunctionDef { ret, name, params, body });

        choice((struct_def, union_def, enum_def, function_def)).map_with(spanned)
    };

    definition.repeated().collect()
}
