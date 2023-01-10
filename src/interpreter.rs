//! Tree-walking interpreter for the AST

mod environment;
pub mod native_funcs;
mod value;

use smol_str::SmolStr;

pub use self::{environment::*, value::*};
use crate::ast::{
    visit::{Visitable, Visitor},
    AssignExpr, BinaryExpr, BinaryOpKind, BlockStatement, CallExpr, ClassDeclaration,
    ExprStatement, FunctionDeclaration, GetExpr, GroupingExpr, IfStatement, LiteralExpr,
    LogicalExpr, LogicalOpKind, PrintStatement, ReturnStatement, SetExpr, Statement, SuperExpr,
    ThisExpr, UnaryExpr, UnaryOpKind, VarDeclaration, VarExpr, WhileStatement,
};
use std::{fmt, io::Write, mem, sync::Arc};

/// The AST interpreter
pub struct Interpreter<W: Write> {
    /// The environment, which holds the complete set of variable bindings
    pub env: Environment,
    /// The standard out buffer, used to print things to screen
    pub stdout: W,
}

impl<W> Interpreter<W>
where
    W: Write,
{
    /// Create a new `Interpreter` with the default set of `NativeFunction`s.
    pub fn new(stdout: W) -> Self {
        let env = Environment::global();

        for func_constructor in native_funcs::DEFAULTS {
            let native_func = (func_constructor)();

            // Defining bindings in the global environment should never fail
            env.define(
                &SmolStr::new(native_func.name),
                Value::NativeFunction(native_func),
            )
        }

        Interpreter { env, stdout }
    }

    /// Visit the given AST fragments and evaluate them
    pub fn interpret(&mut self, statements: &[Statement]) -> Result<Value, RuntimeException> {
        for stmnt in statements {
            let v = stmnt.visit_with(self)?;

            assert_eq!(v, Value::Null, "Statement returned non-nil value!");
        }

        Ok(Value::Null)
    }

    /// Mutably access the environment of this `Interpreter`
    pub fn env(&mut self) -> &mut Environment {
        &mut self.env
    }

    /// Mutable access the stdout of this `Interpreter`
    pub fn stdout(&mut self) -> &mut dyn Write {
        &mut self.stdout
    }
}

impl<W> fmt::Debug for Interpreter<W>
where
    W: Write,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut state = f.debug_struct("Interpreter");
        state.field("env", &self.env);
        state.field("stdout", &"[stdout]");
        state.finish()
    }
}

impl<W> Visitor for Interpreter<W>
where
    W: Write,
{
    type Output = Result<Value, RuntimeControlFlow>;

    fn default_output(&self) -> Self::Output {
        Ok(Value::Null)
    }

    // This combiner should only join outputs from null statements
    fn combine_output(&self, o1: Self::Output, o2: Self::Output) -> Self::Output {
        match (o1?, o2?) {
            (Value::Null, Value::Null) => Ok(Value::Null),
            _ => panic!("Unsupported operation"),
        }
    }

    fn visit_print_stmnt(&mut self, d: &PrintStatement) -> Self::Output {
        let PrintStatement { expr } = d;

        let value = expr.visit_with(self)?;

        writeln!(self.stdout, "{value}").expect("failed to write to stdout");

        Ok(Value::Null)
    }

    fn visit_expr_stmnt(&mut self, d: &ExprStatement) -> Self::Output {
        let ExprStatement { expr } = d;

        let _ = expr.visit_with(self)?;

        Ok(Value::Null)
    }

    fn visit_var_decl(&mut self, d: &VarDeclaration) -> Self::Output {
        let VarDeclaration { name, initializer } = d;

        let value: Value = initializer
            .as_ref()
            .map_or(Ok(Value::Null), |e| e.visit_with(self))?;

        self.env().define(name, value);

        Ok(Value::Null)
    }

    fn visit_block_stmnt(&mut self, d: &BlockStatement) -> Self::Output {
        let BlockStatement { statements } = d;

        let new_env = Environment::new_child(self.env());

        let old_env = mem::replace(&mut self.env, new_env);
        let outputs: Vec<_> = statements
            .iter()
            .map(|stmnt| stmnt.visit_with(self))
            .collect();
        *self.env() = old_env;

        self.combine_many_output(outputs)
    }

    fn visit_if_stmnt(&mut self, d: &IfStatement) -> Self::Output {
        let IfStatement {
            condition,
            then_branch,
            else_branch,
        } = d;
        let condition_value = condition.visit_with(self)?;

        if condition_value.is_truthy() {
            then_branch.visit_with(self)
        } else {
            else_branch.visit_with(self)
        }
    }

    fn visit_while_stmnt(&mut self, d: &WhileStatement) -> Self::Output {
        let WhileStatement { condition, body } = d;

        loop {
            let condition_value = condition.visit_with(self)?;
            if !condition_value.is_truthy() {
                break;
            }

            let _ = body.visit_with(self)?;
        }

        Ok(Value::Null)
    }

    fn visit_func_decl(&mut self, d: &FunctionDeclaration) -> Self::Output {
        self.env().define(&d.name, Value::Null);

        // Defining the function before creating the child environment means that the
        // function can call itself recursively.
        let func = UserFunction {
            declaration: Arc::new(d.clone()),
            closure: Environment::new_child(self.env()),
            function_type: FunctionType::Function,
        };

        self.env().assign(&d.name, func.into())?;

        Ok(Value::Null)
    }

    fn visit_return_stmnt(&mut self, d: &ReturnStatement) -> Self::Output {
        let ReturnStatement { value } = d;

        let value = if let Some(value) = value {
            value.visit_with(self)?
        } else {
            Value::Null
        };

        Err(RuntimeControlFlow::Return(value))
    }

    fn visit_class_decl(&mut self, d: &ClassDeclaration) -> Self::Output {
        let ClassDeclaration {
            name,
            methods,
            superclass,
        } = d;

        let superclass = superclass
            .as_ref()
            .map(|superclass| match superclass.visit_with(self)? {
                Value::Class(class) => Ok(class),
                x => Err(RuntimeControlFlow::from(
                    RuntimeException::NonClassSuperClass(x.r#type()),
                )),
            })
            .transpose()?;

        self.env().define(name, Value::Null);

        let class_env = Environment::new_child(self.env());
        if let Some(superclass) = superclass.as_ref() {
            class_env.define(&SmolStr::new("super"), Arc::clone(superclass).into());
        }

        let methods = methods
            .iter()
            .map(|m| {
                let name = m.name.clone();
                let function_type = if name == ClassDeclaration::INITIALIZER_METHOD_NAME {
                    FunctionType::Initializer
                } else {
                    FunctionType::Method
                };

                (
                    name,
                    UserFunction {
                        declaration: Arc::clone(m),
                        closure: Environment::new_child(&class_env),
                        function_type,
                    },
                )
            })
            .collect();

        let class = Arc::new(Class {
            name: name.clone(),
            methods,
            superclass,
        });

        self.env().assign(name, class.into())?;

        Ok(Value::Null)
    }

    fn visit_binary_expr(&mut self, d: &BinaryExpr) -> Self::Output {
        let BinaryExpr {
            left,
            operator,
            right,
        } = d;

        let left_value = left.visit_with(self)?;
        let right_value = right.visit_with(self)?;

        // TODO: implement control flow boolean operators

        let v = match (operator, left_value, right_value) {
            (BinaryOpKind::Mult, Value::Number(l), Value::Number(r)) => (l * r).into(),
            (BinaryOpKind::Add, Value::Number(l), Value::Number(r)) => (l + r).into(),
            (BinaryOpKind::Add, Value::String(l), Value::String(r)) => {
                SmolStr::new(format!("{l}{r}")).into()
            },
            (BinaryOpKind::Sub, Value::Number(l), Value::Number(r)) => (l - r).into(),
            (BinaryOpKind::Div, Value::Number(l), Value::Number(r)) => (l / r).into(),

            // comparisons
            (BinaryOpKind::Greater, Value::Number(l), Value::Number(r)) => (l > r).into(),
            (BinaryOpKind::GreaterEqual, Value::Number(l), Value::Number(r)) => (l >= r).into(),
            (BinaryOpKind::Less, Value::Number(l), Value::Number(r)) => (l < r).into(),
            (BinaryOpKind::LessEqual, Value::Number(l), Value::Number(r)) => (l <= r).into(),

            // equality
            (BinaryOpKind::Equal, l, r) => (l.eq(&r)).into(),
            (BinaryOpKind::NotEqual, l, r) => (l.ne(&r)).into(),

            // operation undefined for value types
            (op, l, r) => {
                return Err(RuntimeException::from(InvalidOperationForType {
                    operation: op.symbol(),
                    first_arg: Some(l.r#type()),
                    second_arg: Some(r.r#type()),
                })
                .into())
            },
        };

        Ok(v)
    }

    fn visit_grouping_expr(&mut self, d: &GroupingExpr) -> Self::Output {
        let GroupingExpr { inner } = d;

        inner.visit_with(self)
    }

    fn visit_literal_expr(&mut self, d: &LiteralExpr) -> Self::Output {
        Ok(Value::from(d))
    }

    fn visit_unary_expr(&mut self, d: &UnaryExpr) -> Self::Output {
        let UnaryExpr { operator, right } = d;

        let right_value = right.visit_with(self)?;

        let v = match (operator, right_value) {
            (UnaryOpKind::Negate, Value::Number(r)) => Value::Number(-r),
            (UnaryOpKind::Not, r) => Value::Boolean(!r.is_truthy()),

            // operation undefined for value types
            (op, r) => {
                return Err(RuntimeException::from(InvalidOperationForType {
                    operation: op.symbol(),
                    first_arg: Some(r.r#type()),
                    second_arg: None,
                })
                .into())
            },
        };

        Ok(v)
    }

    fn visit_logical_expr(&mut self, d: &LogicalExpr) -> Self::Output {
        let LogicalExpr {
            left,
            right,
            operator,
        } = d;

        let left_value = left.visit_with(self)?;

        match operator {
            LogicalOpKind::And => {
                if !left_value.is_truthy() {
                    Ok(left_value)
                } else {
                    right.visit_with(self)
                }
            },
            LogicalOpKind::Or => {
                if left_value.is_truthy() {
                    Ok(left_value)
                } else {
                    right.visit_with(self)
                }
            },
        }
    }

    fn visit_var_expr(&mut self, d: &VarExpr) -> Self::Output {
        let VarExpr { name } = d;

        self.env().lookup(name.as_str()).map_err(Into::into)
    }

    fn visit_assign_expr(&mut self, d: &AssignExpr) -> Self::Output {
        let AssignExpr { name, value } = d;

        let value = value.visit_with(self)?;

        self.env().assign(name, value.clone())?;

        Ok(value)
    }

    fn visit_call_expr(&mut self, d: &CallExpr) -> Self::Output {
        let CallExpr { callee, arguments } = d;

        // Evaluate the callee (the thing to call) and the arguments

        let callee_value = callee.visit_with(self)?;
        let arg_values: Vec<_> = arguments
            .iter()
            .map(|e| e.visit_with(self))
            .collect::<Result<_, _>>()?;

        match callee_value {
            Value::NativeFunction(f) => f.call(arg_values),
            Value::UserFunction(f) => f.call(self, arg_values),
            Value::Class(c) => c.constructor(self, arg_values),
            x => Err(RuntimeException::CalledNonFunctionType(x.r#type()).into()),
        }
    }

    fn visit_get_expr(&mut self, d: &GetExpr) -> Self::Output {
        let GetExpr { object, property } = d;

        let object = object.visit_with(self)?;

        match object {
            Value::Instance(inst) => inst.get(property),
            v => Err(RuntimeException::AccessPropertyNonObject(v.r#type()).into()),
        }
    }

    fn visit_set_expr(&mut self, d: &SetExpr) -> Self::Output {
        let SetExpr {
            object,
            property,
            value,
        } = d;

        let object = object.visit_with(self)?;

        match object {
            Value::Instance(inst) => {
                let value = value.visit_with(self)?;

                inst.set(property.clone(), value.clone());

                Ok(value)
            },
            v => Err(RuntimeException::SetPropertyNonObject(v.r#type()).into()),
        }
    }

    fn visit_this_expr(&mut self, _: &ThisExpr) -> Self::Output {
        self.env()
            .lookup(ThisExpr::VARIABLE_NAME)
            .map_err(Into::into)
    }

    fn visit_super_expr(&mut self, d: &SuperExpr) -> Self::Output {
        let SuperExpr { method } = d;

        let superclass = match self
            .env()
            .lookup("super")
            .map_err(RuntimeControlFlow::from)?
        {
            Value::Class(class) => class,
            x => {
                return Err(RuntimeException::NonClassSuperClass(x.r#type()).into());
            },
        };

        let instance = match self
            .env()
            .get_child(0)
            .ok_or(RuntimeException::MissingChildEnvironment)?
            .lookup("this")
            .map_err(RuntimeControlFlow::from)?
        {
            Value::Instance(instance) => instance,
            _ => {
                panic!("Should never have a non-Instance value for `this`.");
            },
        };

        let method =
            superclass
                .find_method(method)
                .ok_or_else(|| RuntimeException::AccessMissingField {
                    field_name: method.clone(),
                })?;

        Ok(method.bind(&instance).into())
    }
}

/// Errors that can occur during the course of interpretation
#[derive(Debug, Clone, PartialEq)]
pub enum RuntimeControlFlow {
    /// An exception immediately unwinds the interpreter, without stopping
    Exception(RuntimeException),

    /// A return immediately unwinds the interpreter to the function above the
    /// current one.
    ///
    /// If no outer function exists, this becomes a `RuntimeException`.
    Return(Value),
}

impl From<Value> for RuntimeControlFlow {
    fn from(v: Value) -> Self {
        RuntimeControlFlow::Return(v)
    }
}

impl From<RuntimeException> for RuntimeControlFlow {
    fn from(v: RuntimeException) -> Self {
        RuntimeControlFlow::Exception(v)
    }
}

/// Errors that can occur during the course of interpretation
#[derive(Debug, Clone, PartialEq, thiserror::Error)]
pub enum RuntimeException {
    /// An error that occurs when performing an operation between incompatible
    /// types
    #[error("{}", .0)]
    InvalidOperationForType(#[from] InvalidOperationForType),
    /// A variable lookup failed because the name is not bound
    #[error("undefined variable [{}]", .0)]
    UndefinedVariable(String),
    /// Attempted to call a non-function type failed
    #[error("attempted to call [{}] as a function", .0)]
    CalledNonFunctionType(&'static str),
    /// Attempted to a call a `Function` with too many or too few argumets
    #[error("a function [{}] expected [{}] arguments but got [{}]", .callee_name, .expected, .provided)]
    MismatchedArity {
        /// The function that attempted to call
        callee_name: SmolStr,
        /// The number of arguments provided
        provided: usize,
        /// The number of arguments expected
        expected: usize,
    },
    /// Attempted to return without a containing function
    #[error("attempted to return from top-level code")]
    TopLevelReturn,
    /// Attempted to access a property on a `Value` that was not an `Instance`.
    #[error("attempted to access a property on a [{}]", .0)]
    AccessPropertyNonObject(&'static str),
    /// Attempted to access a field which did not exist on the `Instance`
    #[error("attempted to access missing field [{}]", .field_name)]
    AccessMissingField {
        /// The property that was attempted access with
        field_name: SmolStr,
    },
    /// Attempted to set a property on a `Value` that was not an `Instance`.
    #[error("attempted to set a property on a [{}]", .0)]
    SetPropertyNonObject(&'static str),
    /// Attempted to define a new variable binding on a frozen environment
    #[error("attempted to define a new variable binding on a frozen environment")]
    DefineBindingInFrozenEnvironment,
    /// Attempted to define a non-class value as superclass
    #[error("attempted to define a [{}] value as superclass", .0)]
    NonClassSuperClass(&'static str),
    /// Missing child environment on `super` lookup
    #[error("attempted a 'super' lookup and was missing a child environment")]
    MissingChildEnvironment,
}

impl From<RuntimeControlFlow> for RuntimeException {
    fn from(v: RuntimeControlFlow) -> Self {
        match v {
            RuntimeControlFlow::Exception(e) => e,
            RuntimeControlFlow::Return(_) => RuntimeException::TopLevelReturn,
        }
    }
}

/// An error that occurs when performing an operation between incompatible types
#[derive(Debug, Clone, PartialEq, thiserror::Error)]
pub struct InvalidOperationForType {
    operation: &'static str,
    first_arg: Option<&'static str>,
    second_arg: Option<&'static str>,
}

// #[error("unsupported operand type(s) for {}: {:?}", .operation,
// .operand_types)]
impl fmt::Display for InvalidOperationForType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match (self.first_arg, self.second_arg) {
            (None, None) => panic!("Unsupported error report with no arguments!"),
            (Some(v), None) | (None, Some(v)) => write!(
                f,
                "unsupported operand type for [{}]: [{}]",
                self.operation, v
            ),
            (Some(l), Some(r)) => write!(
                f,
                "unsupported operand type for [{}]: [{}] and [{}]",
                self.operation, l, r
            ),
        }
    }
}
