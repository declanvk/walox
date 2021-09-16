//! Utilities for the single-pass compiler

mod parse;
mod precedence;

use std::convert::TryInto;

use crate::{
    scanner::{Cursor, MissingTokenError, ScanError, Token, TokenType},
    util::drain_filter,
    vm::{ChunkBuilder, ChunkError, FunctionObject, Heap, ObjectRef, OpCode, StringObject},
};
pub use parse::{
    and, binary, block_statement, declaration, expression, grouping, if_statement, literal, number,
    or, parse_precedence, print_statement, statement, string, unary,
};
pub use precedence::Precedence;
use smol_str::SmolStr;

/// A single-pass compiler into `lox` bytecode.
pub struct Compiler<'h, 'p, I: Iterator<Item = Token>> {
    /// The stream of token from the source code.
    pub cursor: Cursor<I>,
    /// The chunk being built.
    pub current: FunctionBuilder<'h, 'p>,
}

/// A container for a `FunctionObject` in the process of being compiled.
pub struct FunctionBuilder<'h, 'p> {
    /// The type of the function being built
    pub fn_type: FunctionType,
    /// The parent function of this function or None if this is
    /// `FunctionType::Script`.
    pub enclosing: Option<&'p FunctionBuilder<'h, 'p>>,
    /// The chunk being built.
    pub chunk: ChunkBuilder<'h>,
    /// The set of local variables in scope
    pub locals: Vec<LocalVariable>,
    /// How many scopes deep the compiler currently is
    pub scope_depth: usize,
    /// The function name
    pub name: ObjectRef<StringObject>,
    /// The number of input parameters for this function
    pub arity: u16,

    heap: &'h Heap,
}

impl<'h, 'p> FunctionBuilder<'h, 'p> {
    /// Create a new context for constructing functions
    ///
    /// # Panics
    /// Panics if the given `name` is not a pointer to a `StringObject`.
    pub fn new(heap: &'h Heap, fn_type: FunctionType, name: ObjectRef<StringObject>) -> Self {
        FunctionBuilder {
            fn_type,
            enclosing: None,
            chunk: ChunkBuilder::new(heap),
            // initialize the locals stack with a reserved slot for ____ purpose
            locals: vec![LocalVariable {
                depth: None,
                name: "".into(),
            }],
            scope_depth: 0,
            arity: 0,
            heap,
            name,
        }
    }

    /// Finalize the function being constructed and return an `Object` pointing
    /// to the function
    pub fn build(mut self, last_line: usize) -> Result<ObjectRef<FunctionObject>, CompilerError> {
        self.chunk.return_inst(last_line);

        let chunk = self.chunk.build()?;

        Ok(self
            .heap
            .allocate_function(self.name, self.arity, chunk)
            .cast()
            .unwrap())
    }
}

/// The type of function being compiled
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum FunctionType {
    /// A function that encapsulates all the top-level code in the source file
    Script,
    /// A function that is defined within the source file as a function
    /// declaration or method
    Function,
}

impl<'h, I> Compiler<'h, '_, I>
where
    I: Iterator<Item = Token>,
{
    /// Create a new compiler for the given source of tokens.
    pub fn new(tokens: I, heap: &'h Heap) -> Self {
        // This function should be called a minimal number of times, so we won't have
        // too many instances of the "script" string on the heap.
        let top_level_name = heap
            .allocate_string("script")
            .cast::<StringObject>()
            .unwrap();

        Compiler {
            cursor: Cursor::new(tokens),
            current: FunctionBuilder::new(heap, FunctionType::Script, top_level_name),
        }
    }

    /// Start a new scope
    pub fn begin_scope(&mut self) {
        self.current.scope_depth += 1;
    }

    /// End the current scope and emit instructions to clean up all local
    /// variables.
    ///
    /// # Panics
    /// This function will panic if called without a matching `begin_scope`.
    pub fn end_scope(&mut self) {
        self.current.scope_depth -= 1;

        let last_line = self.current.chunk.get_last_line();
        let current_depth = self.current.scope_depth;
        let current_chunk = &mut self.current.chunk;
        drain_filter::rev_drain_filter(&mut self.current.locals, |local| {
            local.depth.unwrap_or(0) > current_depth
        })
        .for_each(|_| {
            current_chunk.simple_inst(OpCode::Pop, last_line);
        });
    }

    /// Returns `true` if the Compiler is in the context of a global scope.
    ///
    /// This is opposed to a block or nested block scope.
    pub fn is_global_scope(&self) -> bool {
        self.current.scope_depth == 0
    }

    /// Declare a new variable in the current scope and prepare for later
    /// initialization.
    ///    1. Global: create a new string value in the current chunk constant
    /// table
    ///    2. Local: create a new local variable object and check for
    /// name clash
    pub fn declare_variable(&mut self, name: SmolStr) -> Result<VariableRef, CompilerError> {
        if self.is_global_scope() {
            // Create a new string in the global constant table to represent the name of the
            // global variable
            Ok(VariableRef::Global(
                self.current.chunk.define_global_variable(name),
            ))
        } else {
            // Check that there are no existing variables with the same name in the same
            // local scope. This does not apply to globals because global variables are
            // allowed to redeclare
            for local in &self.current.locals {
                if local.depth.is_some() && local.depth.unwrap() < self.current.scope_depth {
                    break;
                }

                if local.name.eq(&name) {
                    return Err(CompilerError::RedeclareLocalVariable { name });
                }
            }

            self.current
                .locals
                .push(LocalVariable { name, depth: None });

            Ok(VariableRef::Local(self.current.locals.len() - 1))
        }
    }

    /// For an already declared variable in the current scope:
    ///   1. Global: emit a new instruction which defines the global variable
    ///   2. Local: finalize the local variable depth information
    pub fn define_variable(&mut self, variable: VariableRef, line_number: usize) {
        match variable {
            VariableRef::Global(global_idx) => {
                // Write variable name and global def instruction to chunk
                self.current
                    .chunk
                    .variable_inst(OpCode::DefineGlobal, global_idx, line_number);
            },
            VariableRef::Local(local_idx) => {
                self.current.locals[local_idx].depth = Some(self.current.scope_depth);
            },
        }
    }

    /// Search for a variable with the matching name.
    ///
    /// Search order is from the innermost scope to the outermost (not including
    /// the global scope). If no local variable resolves, then this variable is
    /// assumed to be a global. Because of late-binding semantics of global
    /// variables, we don't validate here whether the global variable
    /// actually exists.
    pub fn resolve_variable(&mut self, name: SmolStr) -> VariableRef {
        let local_idx = self
            .current
            .locals
            .iter()
            .enumerate()
            .rev()
            .find(|(_, local)| local.name.eq(&name))
            .map(|(idx, _)| idx);
        if let Some(local_idx) = local_idx {
            VariableRef::Local(local_idx)
        } else {
            let global_idx = self.current.chunk.define_global_variable(name);

            VariableRef::Global(global_idx)
        }
    }
}

/// A reference to a variable, either global or local.
#[derive(Debug)]
pub enum VariableRef {
    /// A reference to a global variable, using the current chunk constant index
    /// as the pointer
    Global(u8),
    /// A reference to a local variable, using the `locals` array index as the
    /// pointer
    Local(usize),
}

/// A record of a compiled local variable
#[derive(Debug)]
pub struct LocalVariable {
    /// The depth that this variable was recorded
    pub depth: Option<usize>,
    /// The name of the variable
    pub name: SmolStr,
}

type ParseFunc<I> = Option<fn(&mut Compiler<I>, bool) -> Result<(), CompilerError>>;

/// A rule for parsing in the case of a specific `TokenType`.
pub struct ParseRule<I: Iterator<Item = Token>> {
    /// The function that will be used to parse a prefix instance of the
    /// `TokenType`.
    pub prefix_fn_impl: ParseFunc<I>,
    /// The function that will be used to parse an infix instance of the
    /// `TokenType`.
    pub infix_fn_impl: ParseFunc<I>,
    /// The priority of this rule.
    pub precedence: Precedence,
}

/// Errors that occur during the course of parsing and emitting bytecode.
#[derive(Debug, Clone, PartialEq, thiserror::Error)]
pub enum CompilerError {
    /// An error which occurs because a `Literal` was not present in a
    /// `Token`
    #[error("token was missing the `literal` field")]
    MissingLiteral,
    /// An error which occurs when encountering an unexpected `TokenType`
    #[error("encountered unexpected token [{:?}], expected {}", .actual, .expected)]
    UnexpectedToken {
        /// The `TokenType` encountered in the stream.
        actual: TokenType,
        /// The expected `TokenType` in a static message.
        expected: &'static str,
    },
    /// An error which occurs because a specific `TokenType` was not found.
    #[error("{}", .0)]
    MissingToken(#[from] MissingTokenError),
    /// An error which occurs because of something in the scanning process.
    #[error("{}", .0)]
    ScanError(#[from] ScanError),
    /// This error occurs because of a failure in the chunk construction
    /// process.
    #[error("{}", .0)]
    ChunkError(#[from] ChunkError),
    /// Attempted to assign to an invalid piece of syntax
    #[error("invalid assignment target")]
    InvalidAssignmentTarget,
    /// This error occurs when attempting to declare a variable when one already
    /// exists with the same name in the local scope
    #[error("variable with this name [{}] already exists in this scope.", .name)]
    RedeclareLocalVariable {
        /// The name of the existing variable.
        name: SmolStr,
    },
}

/// Compile `lox` source
#[tracing::instrument(level = "debug", skip(tokens, heap))]
pub fn compile(
    tokens: impl IntoIterator<Item = Token>,
    heap: &Heap,
) -> Result<ObjectRef<FunctionObject>, Vec<CompilerError>> {
    let mut compiler = Compiler::new(tokens.into_iter(), heap);
    let mut errors = Vec::new();

    while !compiler.cursor.is_empty() {
        match declaration(&mut compiler) {
            Ok(()) => {},
            Err(e) => {
                errors.push(e);
            },
        }
    }

    if errors.is_empty() {
        // Emit a return on the last line, as we're only compiling single Chunk right
        // now
        let last_line = compiler
            .cursor
            .previous()
            .map(|prev| prev.span.line())
            .unwrap_or(0);

        match compiler.current.build(last_line.try_into().unwrap()) {
            Ok(f) => Ok(f),
            Err(err) => {
                errors.push(err);

                Err(errors)
            },
        }
    } else {
        Err(errors)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        scanner::Scanner,
        vm::{Chunk, OpCode, StringObject},
    };

    macro_rules! assert_instructions {
        ($chunk:ident => {$($op:expr $(, [$($data:expr)*])? ;)+}) => {
            {
                let mut instructions = $chunk.into_iter();
                $(
                    {
                        let (_, inst) = instructions.next().expect("unable to get next instruction");
                        let inst = inst.expect("error in chunk iter");
                        assert_eq!(inst.op, $op);
                        $(
                            assert_eq!(inst.arguments, &[$($data)*][..]);
                        )?

                    }
                )+
            }

        };
    }

    fn compile_expression(heap: &Heap, src: &str) -> Chunk {
        let tokens = Scanner::new(src);
        let mut compiler = Compiler::new(tokens, &heap);

        expression(&mut compiler).expect("unable to parse expression from tokens");

        compiler.current.chunk.return_inst(1);

        let chunk = compiler
            .current
            .chunk
            .build()
            .expect("unable to build compiled chunk");

        chunk
    }

    #[test]
    fn simple_arith_compile() {
        let heap = Heap::new();
        let chunk = compile_expression(&heap, "10 + 20");
        assert_eq!(&*chunk.constants, &[10.0.into(), 20.0.into()][..]);
        assert_instructions!(chunk => {
            OpCode::Constant, [0];
            OpCode::Constant, [1];
            OpCode::Add;
        });
    }

    #[test]
    fn paren_arith_compile() {
        let heap = Heap::new();
        let chunk = compile_expression(&heap, "10 * (20 + (30 - 2))");
        assert_eq!(
            &*chunk.constants,
            &[10.0.into(), 20.0.into(), 30.0.into(), 2.0.into()][..]
        );
        assert_instructions!(chunk => {
            OpCode::Constant, [0];
            OpCode::Constant, [1];
            OpCode::Constant, [2];
            OpCode::Constant, [3];
            OpCode::Subtract;
            OpCode::Add;
            OpCode::Multiply;
        });
    }

    #[test]
    fn comparison_compile() {
        let heap = Heap::new();
        let chunk = compile_expression(&heap, "(10.0 < 2) == ((1.2 - 3.2) <= 0)");
        assert_eq!(
            &*chunk.constants,
            &[10.0.into(), 2.0.into(), 1.2.into(), 3.2.into(), 0.0.into()][..]
        );
        assert_instructions!(chunk => {
            OpCode::Constant, [0];
            OpCode::Constant, [1];
            OpCode::Less;
            OpCode::Constant, [2];
            OpCode::Constant, [3];
            OpCode::Subtract;
            OpCode::Constant, [4];
            OpCode::Greater;
            OpCode::Not;
            OpCode::Equal;
        });
    }

    #[test]
    fn negation_compile() {
        let heap = Heap::new();
        let chunk = compile_expression(&heap, "!(5 - 4 > 3 * 2 == !nil)");
        assert_eq!(
            &*chunk.constants,
            &[5.0.into(), 4.0.into(), 3.0.into(), 2.0.into()][..]
        );
        assert_instructions!(chunk => {
            OpCode::Constant, [0];
            OpCode::Constant, [1];
            OpCode::Subtract;
            OpCode::Constant, [2];
            OpCode::Constant, [3];
            OpCode::Multiply;
            OpCode::Greater;
            OpCode::Nil;
            OpCode::Not;
            OpCode::Equal;
            OpCode::Not;
        });
    }

    #[test]
    fn string_concat_compile() {
        let heap = Heap::new();
        let chunk = compile_expression(&heap, r##" "a" + "b" + "c" "##);

        assert_eq!(chunk.constants.len(), 3);
        assert_eq!(
            chunk.constants[0]
                .to_object_type::<StringObject>()
                .unwrap()
                .value
                .as_ref(),
            "a"
        );
        assert_eq!(
            chunk.constants[1]
                .to_object_type::<StringObject>()
                .unwrap()
                .value
                .as_ref(),
            "b"
        );
        assert_eq!(
            chunk.constants[2]
                .to_object_type::<StringObject>()
                .unwrap()
                .value
                .as_ref(),
            "c"
        );
        assert_instructions!(chunk => {
            OpCode::Constant, [0];
            OpCode::Constant, [1];
            OpCode::Add;
            OpCode::Constant, [2];
            OpCode::Add;
        });
    }
}
