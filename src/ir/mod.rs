use std::collections::HashMap;

use slotmap::{SlotMap, new_key_type, SecondaryMap};

pub mod lower;
pub mod display;
pub mod typecheck;

new_key_type! {
    pub struct TypeKey; 
    struct FuncKey;
    struct LiteralKey;
    struct Var;
}

#[derive(Default, Debug)]
pub struct Program<'a> {
    function_names: HashMap<&'a str, FuncKey>,
    functions: SlotMap<FuncKey, Function<'a>>,
    function_decls: SecondaryMap<FuncKey, FunctionDecl<'a>>,
    type_decls: HashMap<&'a str, TypeKey>,
    types: SlotMap<TypeKey, DirectType<'a>>,
    literals: SlotMap<LiteralKey, String>
}

#[derive(Debug)]
pub enum DirectType<'a> {
    Struct {
        fields: Vec<(&'a str, Type)>
    },
    Union {
        variants: Vec<(&'a str, Type)>
    },
    Enum {
        variants: Vec<(&'a str, i32)>
    },
    Type(Type)
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PrimitiveType {
    I32, F32, Bool, U8
}

#[derive(Clone, Debug)]
pub enum Type {
    Direct(TypeKey),
    Primitive(PrimitiveType),
    /// `---`
    Uninit,
    /// `void` type is unit type
    Unit,
    /// type of `break`, `continue` and `return` expressions
    /// can be cast to any type
    Never,
    /// The type is yet unknown, but should get determined during type checking
    /// Using a variable with an undeclared type is an immediate compilation error (and should in theory never happen)
    Undeclared,
    Ptr(Box<Type>),
    Slice(Box<Type>),
    Array { ty: Box<Type>, len: i32 },
    Func {
        ret: Box<Type>,
        params: Vec<Type>
    }
}

#[derive(Debug, Clone)]
struct FunctionDecl<'a> {
    ret: Type,
    params: Vec<Param<'a>>
}

#[derive(Debug, Clone)]
struct Param<'a> {
    outward_name: Option<&'a str>,
    name: &'a str,
    ty: Type
    // value: Option<()>
}

#[derive(Default, Debug)]
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
    DerefAssign(Value, Expr<'a>),
    Do(Expr<'a>),
    Block(Block<'a>),
    If {
        cond: Expr<'a>,
        block: Block<'a>,
        else_block: Option<Block<'a>>
    },
    Loop(Block<'a>)
}

#[derive(Debug, Clone, Copy)]
enum Value {
    Var(Var),
    Num(i32),
    Literal(LiteralKey),
    Uninit,
    Unit
}

#[derive(Debug)]
enum Expr<'a> {
    Value(Value),
    FieldAccess(Value, &'a str),
    PathAccess(TypeKey, &'a str),
    FuncCall(FuncKey, Vec<Value>),
    Return(Option<Value>),
    Break,
    Continue,
    BinOp(Value, BinOp, Value),
    UnaryOp(UnaryOp, Value)
}

impl From<Value> for Expr<'_> {
    fn from(value: Value) -> Self {
        Expr::Value(value)
    }
}

#[derive(Debug)]
enum UnaryOp { AddressOf, Deref, Negate, Not }

#[derive(Debug)]
enum BinOp { 
    Add, Sub, Mul, Div, Mod,
    LogicAnd, LogicOr, LogicXor,
    And, Or, Xor,
    Eq, Ne, Gt, Ge, Lt, Le
}
