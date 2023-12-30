use std::collections::HashMap;

use slotmap::{SlotMap, new_key_type};

pub mod lower;
pub mod display;

new_key_type! {
    pub struct TypeKey; 
    struct FuncKey;
    struct Var;
}

#[derive(Default, Debug)]
pub struct Program<'a> {
    function_decls: HashMap<&'a str, FunctionDecl<'a>>,
    functions: SlotMap<FuncKey, Function<'a>>,
    pub type_decls: HashMap<&'a str, TypeKey>,
    pub types: SlotMap<TypeKey, UserType<'a>>
}

#[derive(Debug)]
pub enum UserType<'a> {
    Struct {
        fields: Vec<(&'a str, Type)>
    },
    Union {
        variants: Vec<(&'a str, Type)>
    },
    Enum {
        variants: Vec<(&'a str, i32)>
    },
    Primitive(PrimitiveType),
    /// `---`
    Uninit,
    /// `void` type is unit type
    Unit,
    /// type of `break`, `continue` and `return` expressions
    /// can be cast to any type
    Never
}

#[derive(Debug)]
pub enum PrimitiveType {
    I32, F32
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type {
    Direct(TypeKey),
    Ptr(Box<Type>),
    Slice(Box<Type>),
    Array { ty: Box<Type>, len: i32 },
    Func {
        ret: Box<Type>,
        params: Vec<Type>
    },
    /// The type is yet unknown, but should get determined during type checking
    /// Using a variable with an undeclared type is an immediate compilation error (and should in theory never happen)
    Undeclared
}

#[derive(Debug)]
struct FunctionDecl<'a> {
    ret: Type,
    params: Vec<Param<'a>>,
    key: FuncKey
}

#[derive(Debug)]
struct Param<'a> {
    outward_name: Option<&'a str>,
    name: &'a str,
    ty: Type
    // value: Option<()>
}

#[derive(Debug, Default)]
struct Function<'a> {
    variables: SlotMap<Var, Variable>,
    body: Block<'a>
}

#[derive(Debug, Default)]
struct Block<'a> {
    stmts: Vec<Statement<'a>>
}

#[derive(Debug)]
struct Variable {
    ty: Type,
    // TODO: metadata: initialized, moved, etc...
}

#[derive(Debug)]
enum Statement<'a> {
    /// Assigns the value of expr to a variable
    Assign(Var, Expr<'a>),
    /// Assigns the value of expr to the location in memory pointed to by a variable
    SetDeref(Var, Expr<'a>),
    Do(Expr<'a>),
    Block(Block<'a>),
    // If {
    //     cond: Expr<'a>,
    //     block: Block<'a>
    // }
    //Loop(Block<'a>)
}

#[derive(Debug)]
enum Expr<'a> {
    Var(Var),
    Num(i32),
    Literal(String),
    Uninit,
    FieldAccess(Var, &'a str),
    PathAccess(TypeKey, &'a str),
    FuncCall(FuncKey, Vec<Var>),
    Return(Option<Var>),
    Break(Option<Var>),
    Continue(Option<Var>),
    BinOp(Var, BinOp, Var),
    UnaryOp(UnaryOp, Var)
}

#[derive(Debug)]
enum UnaryOp { AddressOf, Deref, Negate, Not }

#[derive(Debug)]
enum BinOp { Add, Sub, Mul, Div }
