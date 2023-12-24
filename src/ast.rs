use chumsky::input::SpannedInput;
use chumsky::prelude::*;
use chumsky::pratt::*;

use crate::lexer::{Token, Keyword};

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
    Id(&'inp str),
    Num(i32),
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
        args: Vec<(Option<&'inp str>, Ast<'inp>)>
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

type Input<'a> = SpannedInput<Token<'a>, SimpleSpan, &'a [(Token<'a>, SimpleSpan)]>;
type Extra<'a> = chumsky::extra::Err<Rich<'a, Token<'a>>>;

fn in_parens<'a, T, P: Parser<'a, Input<'a>, T, Extra<'a>> + Clone>(p: P) -> impl Parser<'a, Input<'a>, T, Extra<'a>> + Clone {
    p.delimited_by(just(Token::LParen), just(Token::RParen))
}

fn in_braces<'a, T, P: Parser<'a, Input<'a>, T, Extra<'a>> + Clone>(p: P) -> impl Parser<'a, Input<'a>, T, Extra<'a>> + Clone {
    p.delimited_by(just(Token::LBrace), just(Token::RBrace))
}

fn in_brackets<'a, T, P: Parser<'a, Input<'a>, T, Extra<'a>> + Clone>(p: P) -> impl Parser<'a, Input<'a>, T, Extra<'a>> + Clone {
    p.delimited_by(just(Token::LBracket), just(Token::RBracket))
}

fn comma_list<'a, T, P: Parser<'a, Input<'a>, T, Extra<'a>>+ Clone>(p: P) -> impl Parser<'a, Input<'a>, Vec<T>, Extra<'a>> + Clone {
    p.separated_by(just(Token::Comma)).collect()
}

pub fn parser<'a>() -> impl Parser<'a, Input<'a>, Vec<Ast<'a>>, Extra<'a>> {
    let id = any().filter(|x| matches!(x, Token::Id(_))).map(|x| if let Token::Id(s) = x { s } else { unreachable!() });
    let num = any().filter(|x| matches!(x, Token::Num(_))).map(|x| if let Token::Num(n) = x { n } else { unreachable!() });

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
        ));

        let func_call = id.then(in_parens(
            comma_list(id.then_ignore(just(Token::Equal)).or_not().then(expr.clone()))
        )).map(|(name, args)| Ast::FuncCall { name, args });

        let box_expr = expr.clone().map(Box::new);

        let atom_without_block = choice((
            func_call,
            just(Keyword::Break.token()).ignore_then(box_expr.clone().or_not()).map(Ast::Break),
            just(Keyword::Continue.token()).ignore_then(box_expr.clone().or_not()).map(Ast::Continue),
            id.map(Ast::Id),
            num.map(Ast::Num),
            in_parens(expr.clone()),
        ));

        let atom = atom_with_block.clone().or(atom_without_block);

        expr.define(atom.pratt((
            prefix(9, just(Token::Minus),       |r| Ast::UnaryExpr(UnaryOp::Negate, Box::new(r))),
            prefix(9, just(Token::Ampersand),   |r| Ast::UnaryExpr(UnaryOp::AddressOf, Box::new(r))),
            prefix(9, just(Token::Star),        |r| Ast::UnaryExpr(UnaryOp::Deref, Box::new(r))),
            prefix(9, just(Token::Exclamation), |r| Ast::UnaryExpr(UnaryOp::Not, Box::new(r))),

            infix(left(8), just(Token::Ampersand), |l, r| Ast::BinExpr(Box::new(l), BinOp::And, Box::new(r))),
            infix(left(8), just(Token::Pipe),      |l, r| Ast::BinExpr(Box::new(l), BinOp::Or, Box::new(r))),
            infix(left(8), just(Token::Caret),     |l, r| Ast::BinExpr(Box::new(l), BinOp::Xor, Box::new(r))),

            infix(left(7), just(Token::Percent), |l, r| Ast::BinExpr(Box::new(l), BinOp::Mod, Box::new(r))),

            infix(left(6), just(Token::Star),  |l, r| Ast::BinExpr(Box::new(l), BinOp::Mul, Box::new(r))),
            infix(left(6), just(Token::Slash), |l, r| Ast::BinExpr(Box::new(l), BinOp::Div, Box::new(r))),
            infix(left(5), just(Token::Plus),  |l, r| Ast::BinExpr(Box::new(l), BinOp::Add, Box::new(r))),
            infix(left(5), just(Token::Minus), |l, r| Ast::BinExpr(Box::new(l), BinOp::Sub, Box::new(r))),

            infix(left(4), just(Token::DotDot), |l, r| Ast::BinExpr(Box::new(l), BinOp::Range, Box::new(r))),

            infix(left(3), just(Token::Pipeline), |l, r| Ast::BinExpr(Box::new(l), BinOp::Pipe, Box::new(r))),

            infix(left(2), just(Token::Gt), |l, r| Ast::BinExpr(Box::new(l), BinOp::Gt, Box::new(r))),
            infix(left(2), just(Token::Ge), |l, r| Ast::BinExpr(Box::new(l), BinOp::Ge, Box::new(r))),
            infix(left(2), just(Token::Lt), |l, r| Ast::BinExpr(Box::new(l), BinOp::Lt, Box::new(r))),
            infix(left(2), just(Token::Le), |l, r| Ast::BinExpr(Box::new(l), BinOp::Le, Box::new(r))),

            infix(left(1), just(Token::Eq), |l, r| Ast::BinExpr(Box::new(l), BinOp::Eq, Box::new(r))),
            infix(left(1), just(Token::Ne), |l, r| Ast::BinExpr(Box::new(l), BinOp::Ne, Box::new(r))),

            infix(left(0), just(Token::DoubleAmpersand), |l, r| Ast::BinExpr(Box::new(l), BinOp::BinAnd, Box::new(r))),
            infix(left(0), just(Token::DoublePipe),      |l, r| Ast::BinExpr(Box::new(l), BinOp::BinOr, Box::new(r))),
            infix(left(0), just(Token::DoubleCaret),     |l, r| Ast::BinExpr(Box::new(l), BinOp::BinXor, Box::new(r))),
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
                .map(|((ty, var), value)| Ast::Declare { ty, var, value }),
            lvalue
                .then_ignore(just(Token::Equal))
                .then(box_expr.clone())
                .then_ignore(just(Token::Semicolon))
                .map(|(var, value)| Ast::Assign { var, value }),
            expr.clone().then_ignore(just(Token::Semicolon)),
            atom_with_block.clone() // block exprs are allowed to be statements without a semicolon
        ));

        block.define(
            in_braces(
                atom_with_block.then(just(Token::RBrace)).not().rewind() // however, this makes sure that a block expression at the end of a block will be counted as the end expr
                    .ignore_then(statement)
                    .repeated().collect().then(box_expr.or_not())
            ).map(|(statements, expr)| Block(statements, expr))
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

        choice((struct_def, union_def, enum_def, function_def))
    };

    definition.repeated().collect()
}
