//! Virtual machine implementation

mod chunk;
mod op;
mod value;

pub use chunk::{Chunk, ChunkBuilder, ChunkError, ChunkIter};
pub use op::{Instruction, OpCode, TryFromByteError};
use std::{
    collections::HashMap,
    convert::{TryFrom, TryInto},
    io::Write,
};
pub use value::{
    ConcreteObject, FunctionObject, Heap, ObjectBase, ObjectRef, ObjectType, OpaqueObject,
    StringObject, Value,
};

/// The virtual machine that executions `Instructions`
///
/// # Safety
///
/// Due to `Value::Object`s pointing to `Heap` allocated data, it is
/// required that no `Value::Object` is used/read after a call to `VM::clear`.
/// The backing memory will have been deallocated, and a use-after-free will
/// result.
///
/// This is mostly relevant to reads from the the `stack` field, as that is the
/// only current fields for `Value`s to escape. Technically this would make use
/// of the `clear` function unsafe, but chosen not to mark it as such
/// because of the unclear boundaries of the safety requirements.
pub struct VM<'h, W: Write> {
    /// The stack of `Value`s.
    pub stack: Vec<Value>,
    /// The standard out buffer, used to print things to screen
    pub stdout: W,
    /// The stack of functions being executed
    pub frames: Vec<CallFrame>,
    /// The heap memory region, containing `Value`s separate from the stack.
    pub heap: &'h mut Heap,
    /// Current set of global variables
    pub globals: HashMap<String, Value>,
}

/// The call frame tracks the live information needed for executing a single
/// function call
#[derive(Debug)]
pub struct CallFrame {
    /// Instruction pointer
    pub ip: *const u8,
    /// The offset into the `stack` array this frame uses to access locals
    pub stack_offset: usize,
    /// The function being executed
    pub function: ObjectRef<FunctionObject>,
}

impl CallFrame {
    /// Create a new function call frame
    pub fn new(function: ObjectRef<FunctionObject>, stack_offset: usize) -> Self {
        let ip = function.chunk.first_instruction_pointer();
        CallFrame {
            ip,
            stack_offset,
            function,
        }
    }
}

impl<'h, W: Write> VM<'h, W> {
    /// Create a new `VM` with the given output and code `Chunk`.
    pub fn new(stdout: W, script: ObjectRef<FunctionObject>, heap: &'h mut Heap) -> Self {
        let stack = vec![script.to_opaque().into()];
        let frames = vec![CallFrame::new(script, stack.len() - 1)];

        VM {
            stdout,
            heap,
            frames,
            stack,
            globals: HashMap::new(),
        }
    }

    /// Reset all the state of the `VM`, deallocating some excess memory.
    ///
    /// # Safety
    ///
    /// See the safety documentation on the `VM` struct.
    pub fn clear(&mut self) {
        self.stack.clear();
        self.globals.clear();
        // # Safety
        //
        // 1. `heap.clear`
        //   - by calling `stack.clear` prior to this, all the live copies of `Object`s
        //     will have been removed from circulation
        unsafe { self.heap.clear() };
    }

    /// Safely execute the current `Chunk` to completion.
    pub fn interpret(&mut self) -> Result<(), RuntimeError> {
        // The `validate_instructions` will never return an empty list of errors
        self.frames
            .last_mut()
            .expect("frames vec should always be non-empty")
            .function
            .chunk
            .validate_instructions()
            .map_err(|errs| errs[0])?;

        let result = unsafe { self.interpret_inner_unchecked() };

        if result.is_err() {
            // Reset the VM on error
            self.clear();
        }

        result
    }

    /// Execute the current `Chunk` to completion.
    ///
    /// # Safety
    ///
    /// If the `VM` is constructed with a malformed `Chunk` then this function
    /// runs a very real danger of performing out-of-bounds memory accesses
    /// and otherwise dangerous operations.
    unsafe fn interpret_inner_unchecked(&mut self) -> Result<(), RuntimeError> {
        macro_rules! binary_op {
            ($op:expr; $($p:pat => $e:expr;)+) => {{
                let rhs = self.stack.pop().unwrap();
                let lhs = self.stack.pop().unwrap();

                let output = match (lhs, rhs) {
                    $(
                        $p => $e,
                    )+
                    (a, b) => {
                        return Err(RuntimeError::IncompatibleTypes(format!(
                            "unsupported operand type for [{}]: [{}] and [{}]",
                            $op,
                            a.type_str(),
                            b.type_str(),
                        )))
                    },
                };

                self.stack.push(output);
            }};
        }

        loop {
            let current_frame = self
                .frames
                .last_mut()
                .expect("frames vec should always be non-empty");
            let (new_ip, inst) =
                unsafe { chunk::decode_instruction_at_unchecked(current_frame.ip) };
            current_frame.ip = new_ip;

            match inst.op {
                OpCode::Constant => self
                    .stack
                    .push(current_frame.function.chunk.constants[inst.arguments[0] as usize]),
                OpCode::GetGlobal => {
                    // Read variable name from constants table
                    let var_name = current_frame.function.chunk.constants
                        [inst.arguments[0] as usize]
                        .to_object_type::<StringObject>()
                        .expect("Unable to read `StringObject` from reference!");

                    match self.globals.get(var_name.value.as_ref()) {
                        Some(value) => {
                            self.stack.push(*value);
                        },
                        None => return Err(RuntimeError::UndefinedVariable(var_name.to_string())),
                    }
                },
                OpCode::SetGlobal => {
                    // Read variable name from constants table
                    let var_name = current_frame.function.chunk.constants
                        [inst.arguments[0] as usize]
                        .to_object_type::<StringObject>()
                        .expect("Unable to read `StringObject` from reference!");

                    // Write variable value to globals table, using variable name as the hash table
                    // key
                    if self.globals.contains_key(var_name.value.as_ref()) {
                        self.globals
                            .insert(var_name.to_string(), self.stack.last().cloned().unwrap());
                    } else {
                        return Err(RuntimeError::UndefinedVariable(var_name.to_string()));
                    }
                    // This instruction specifically does not pop its value off
                    // the stack as it is supposed to be an expression, which
                    // does not affect the stack.
                },
                OpCode::GetLocal => {
                    let slot = inst.arguments[0] as usize + current_frame.stack_offset;
                    let value = self.stack[slot];
                    self.stack.push(value);
                },
                OpCode::SetLocal => {
                    let slot = inst.arguments[0] as usize + current_frame.stack_offset;
                    let value = self.stack.last().cloned().unwrap();
                    self.stack[slot] = value;
                },
                OpCode::DefineGlobal => {
                    // Read variable name from constants table
                    let var_name = current_frame.function.chunk.constants
                        [inst.arguments[0] as usize]
                        .to_object_type::<StringObject>()
                        .expect("Unable to read `StringObject` from reference!");

                    // Write variable value to globals table, using variable name as the hash table
                    // key
                    self.globals
                        .insert(var_name.to_string(), self.stack.last().cloned().unwrap());
                    self.stack.pop().unwrap();
                },
                OpCode::Add => binary_op! {
                    "+";
                    (Value::Number(a), Value::Number(b)) => Value::from(a + b);
                    (Value::Object(a), Value::Object(b)) => {
                        match (a.read::<StringObject>(), b.read::<StringObject>()) {
                            (Some(a), Some(b)) => {
                                let mut res = String::from(&*a.value);
                                res.push_str(&*b.value);

                                self.heap.allocate_string(res).into()
                            },
                            _ => {
                                return Err(RuntimeError::IncompatibleTypes(format!(
                                    "unsupported operand type for [+]: [{}] and [{}]",
                                    a.type_str(), b.type_str()
                                )));
                            }
                        }
                    };
                },
                OpCode::Subtract => binary_op! {
                    "-";
                    (Value::Number(a), Value::Number(b)) => Value::from(a - b);
                },
                OpCode::Multiply => binary_op! {
                    "*";
                    (Value::Number(a), Value::Number(b)) => Value::from(a * b);
                },
                OpCode::Divide => binary_op! {
                    "/";
                    (Value::Number(a), Value::Number(b)) => Value::from(a / b);
                },
                OpCode::Negate => {
                    let v = self.stack.pop().unwrap();
                    if let Value::Number(n) = v {
                        self.stack.push((-n).into());
                    } else {
                        return Err(RuntimeError::IncompatibleTypes(format!(
                            "unsupported operand type for [-]: [{}]",
                            v.type_str()
                        )));
                    }
                },
                OpCode::Not => {
                    let v = self.stack.pop().unwrap();
                    self.stack.push(v.is_falsey().into());
                },
                OpCode::Return => {
                    // Just in case `interpret` is called again.
                    current_frame.ip = current_frame.function.chunk.first_instruction_pointer();
                    return Ok(());
                },
                OpCode::True => self.stack.push(true.into()),
                OpCode::False => self.stack.push(false.into()),
                OpCode::Nil => self.stack.push(Value::Nil),
                OpCode::Equal => {
                    let rhs = self.stack.pop().unwrap();
                    let lhs = self.stack.pop().unwrap();

                    self.stack.push((rhs == lhs).into());
                },
                OpCode::Greater => binary_op! {
                    ">";
                    (Value::Number(a), Value::Number(b)) => Value::from(a > b);
                },
                OpCode::Less => binary_op! {
                    "<";
                    (Value::Number(a), Value::Number(b)) => Value::from(a < b);
                },
                OpCode::Print => {
                    let value = self.stack.pop().unwrap();
                    writeln!(self.stdout, "{}", value).expect("unable to write to stdout");
                },
                OpCode::Pop => {
                    self.stack.pop().unwrap();
                },
                OpCode::JumpIfFalse => {
                    let offset = inst
                        .read_u16_argument()
                        .expect("insufficient bytes to read u16");
                    if self.stack.last().map(|v| v.is_falsey()).unwrap_or(false) {
                        current_frame.ip = current_frame
                            .ip
                            .offset(offset.try_into().expect("unable to convert u16 to isize"));
                    }
                },
                OpCode::Jump => {
                    let offset = inst
                        .read_u16_argument()
                        .expect("insufficient bytes to read u16");
                    current_frame.ip = current_frame
                        .ip
                        .offset(offset.try_into().expect("unable to convert u16 to isize"));
                },
                OpCode::Loop => {
                    let offset = inst
                        .read_u16_argument()
                        .expect("insufficient bytes to read u16");
                    current_frame.ip = current_frame.ip.offset(
                        -(isize::try_from(offset).expect("unable to convert u16 to isize")),
                    );
                },
            }
        }
    }
}

/// Errors that can occur during the execution of bytecode.
#[derive(Debug, Clone, PartialEq, thiserror::Error)]
pub enum RuntimeError {
    /// Error that occured while validating a chunk before execution
    #[error("validation error [{}]", .0)]
    Validation(#[from] ChunkError),
    /// Attempted an operation with incompatible types
    #[error("incompatible types [{}]", .0)]
    IncompatibleTypes(String),
    /// Attempted to read a global variable which did not exist
    #[error("undefined variable [{}]", .0)]
    UndefinedVariable(String),
}
