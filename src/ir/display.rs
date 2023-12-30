use std::fmt::Display;

use super::{Program, Block, Statement, Expr, UnaryOp, BinOp, Type, UserType, PrimitiveType, Function};

/// permits drilling the Program struct through the Display trait
struct WithProgram<'a, T>(&'a T, &'a Program<'a>);

trait DisplayProgram: Sized {
    fn with<'a>(&'a self, p: &'a Program) -> WithProgram<'a, Self> {
        WithProgram(self, p)
    }
}

impl<'a, T> DisplayProgram for T where WithProgram<'a, T>: Display + 'a {}

impl Display for Program<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (name, key) in &self.type_decls {
            let ty = &self.types[*key];
            writeln!(f, "{name} -> {key:?}: {ty}")?;
        }

        for (name, decl) in &self.function_decls {
            let func = &self.functions[decl.key];
            write!(f, "{} {name} (", decl.ret)?;
            for param in &decl.params {
                write!(f, "{}, ", param.ty)?;
            }
            writeln!(f, ") -> {:?}:\n{}", decl.key, func.with(self))?;
        }

        Ok(())
    }
}

impl Display for UserType<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use UserType as Ty;
        match self {
            Ty::Unit => write!(f, "void"),
            Ty::Never => write!(f, "never"),
            Ty::Uninit => write!(f, "---"),
            Ty::Primitive(ty) => write!(f, "{ty}"),
            Ty::Struct { fields } => {
                writeln!(f, "struct {{")?;
                for (field, ty) in fields {
                    writeln!(f, "  {field}: {ty}")?;
                }
                write!(f, "}}")
            }
            Ty::Union { variants } => {
                writeln!(f, "union {{")?;
                for (field, ty) in variants {
                    writeln!(f, "  {field}: {ty}")?;
                }
                write!(f, "}}")
            }
            Ty::Enum { variants } => {
                writeln!(f, "enum {{")?;
                for (name, value) in variants {
                    writeln!(f, "  {name} = {value}")?;
                }
                write!(f, "}}")
            }
        }
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Type as Ty;
        match self {
            Ty::Undeclared => write!(f, "undeclared"),
            Ty::Direct(ty) => write!(f, "{ty:?}"),
            Ty::Ptr(ty) => write!(f, "{ty}&"),
            Ty::Array { ty, len } => write!(f, "{ty}[{len}]"),
            Ty::Slice(ty) => write!(f, "{ty}[]"),
            Ty::Func { ret, params } => {
                write!(f, "{ret}(")?;
                for param in params {
                    write!(f, "{param}, ")?;
                }
                write!(f, ")")
            }
        }
    }
}

impl Display for PrimitiveType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use PrimitiveType as Ty;
        let s = match self {
            Ty::I32 => "i32",
            Ty::F32 => "f32"
        };
        write!(f, "{s}")
    }
}

impl Display for WithProgram<'_, Function<'_>> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use std::fmt::Write;
        let mut s = String::new();
        for (key, var) in &self.0.variables {
            writeln!(s, "{key:?} -> {}", var.ty)?;
        }
        writeln!(s, "{}", self.0.body.with(self.1))?;
        for line in s.lines() {
            writeln!(f, "    {line}")?;
        }
        Ok(())
    }
}

impl Display for WithProgram<'_, Block<'_>> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        use std::fmt::Write;
        let mut s = String::new();
        for stmt in &self.0.stmts {
            write!(s, "{}", stmt.with(self.1))?;
        }

        writeln!(f, "{{")?;
        for line in s.lines() {
            writeln!(f, "    {line}")?;
        }
        write!(f, "}}")
    }
}

impl Display for WithProgram<'_, Statement<'_>> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match &self.0 {
            Statement::Do(e) => writeln!(f, "DO {}", e.with(self.1)),
            Statement::Assign(var, e) => writeln!(f, "{var:?} = {}", e.with(self.1)),
            Statement::SetDeref(var, e) => writeln!(f, "*{var:?} = {}", e.with(self.1)),
            Statement::Block(b) => writeln!(f, "{}", b.with(self.1))
        }
    }
}

impl Display for WithProgram<'_, Expr<'_>> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match &self.0 {
            Expr::Var(v) => write!(f, "{v:?}"),
            Expr::Num(n) => write!(f, "{n}"),
            Expr::Literal(l) => write!(f, "{l:?}"),
            Expr::Uninit => write!(f, "---"),
            Expr::Break(e) => match e {
                Some(e) => write!(f, "break with {e:?}"),
                None => write!(f, "break")
            }
            Expr::Continue(e) => match e {
                Some(e) => write!(f, "continue with {e:?}"),
                None => write!(f, "continue")
            }
            Expr::Return(e) => match e {
                Some(e) => write!(f, "return with {e:?}"),
                None => write!(f, "return")
            }
            Expr::FieldAccess(var, field) => write!(f, "{var:?}.{field}"),
            Expr::PathAccess(ty, field) => write!(f, "get constant {field} from {ty:?}"),
            Expr::FuncCall(func, args) => {
                write!(f, "call {func:?} with (")?;
                for arg in args {
                    write!(f, "{arg:?}, ")?;
                }
                write!(f, ")")
            }
            Expr::UnaryOp(op, var) => write!(f, "{op} {var:?}"),
            Expr::BinOp(a, op, b) => write!(f, "{a:?} {op} {b:?}")
        }
    }
}

impl Display for UnaryOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use UnaryOp as O;
        let s = match self {
            O::Deref => "*",
            O::Negate => "-",
            O::AddressOf => "&",
            O::Not => "!"
        };
        write!(f, "{s}")
    }
}

impl Display for BinOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use BinOp as O;
        let s = match self {
            O::Add => "+", O::Sub => "-",
            O::Mul => "*", O::Div => "/"
        };
        write!(f, "{s}")
    }
}
