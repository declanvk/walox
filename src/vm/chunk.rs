use super::{Heap, Instruction, OpCode, TryFromByteError, Value};
use core::slice;
use std::{convert::TryFrom, io, iter};

/// An immutable structure that contains compiled `Instruction`s and other
/// relevant data needed to execute a program.
#[derive(Debug, PartialEq)]
pub struct Chunk {
    /// A run-length encoding of the line numbers for each byte of instruction
    /// data.
    pub line_numbers: Box<[LineNumber]>,
    /// The instructions data, filled with `OpCode`s and arguments.
    pub instructions: Box<[u8]>,
    /// The list of constants that are referenced by `Instruction`s in this
    /// `Chunk`.
    pub constants: Box<[Value]>,
}

impl Chunk {
    /// Write to the given output a specially formatted version of the `Chunk`
    /// that decodes each `Instruction` with its arguments.
    pub fn write_disassembled(
        &self,
        output: &mut dyn io::Write,
        name: Option<&str>,
    ) -> io::Result<()> {
        if let Some(name) = name {
            writeln!(output, "== {} ==", name)?
        } else {
            writeln!(output, "======")?
        }

        let full_line_numbers: Vec<_> = self
            .line_numbers
            .iter()
            .flat_map(|LineNumber { line_number, count }| {
                iter::repeat(*line_number).take(*count as usize)
            })
            .collect();

        let mut last_line = 0;

        for (offset, inst) in self {
            write!(output, "{:0>4} ", offset)?;

            let line_num = full_line_numbers[offset];
            if offset > 0 && line_num == last_line {
                write!(output, "   | ")?;
            } else {
                last_line = line_num;
                write!(output, "{:>4} ", line_num)?;
            }

            match inst {
                Ok(inst) => {
                    write!(output, "{:<16} ", inst.op)?;

                    // Write extra op data
                    match inst.op {
                        OpCode::Constant => {
                            let constant_idx = inst.arguments[0];
                            let constant_data = &self.constants[constant_idx as usize];
                            write!(output, "{} '{}'", constant_idx, constant_data)?;
                        },
                        OpCode::Return
                        | OpCode::Add
                        | OpCode::Subtract
                        | OpCode::Multiply
                        | OpCode::Divide
                        | OpCode::Negate
                        | OpCode::Not
                        | OpCode::True
                        | OpCode::False
                        | OpCode::Nil
                        | OpCode::Equal
                        | OpCode::Greater
                        | OpCode::Print
                        | OpCode::Pop
                        | OpCode::Less => {},
                    }
                },
                Err(err) => {
                    write!(output, "{}", err)?;
                },
            }

            writeln!(output)?;
        }

        Ok(())
    }

    /// Return an iterator over all the instructions contained in this chunk.
    pub fn iter(&self) -> ChunkIter {
        ChunkIter {
            instructions: &self.instructions,
            offset: 0,
        }
    }

    /// Validate the instruction in this chunk, returning `Ok(())` if there are
    /// no issues, otherwise returning `Err` with a list of the errors.
    pub fn validate_instructions(&self) -> Result<(), Vec<ChunkError>> {
        let errors: Vec<_> = self
            .iter()
            .filter_map(|(_, inst)| match inst {
                Ok(_) => None,
                Err(e) => Some(e),
            })
            .collect();

        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }

    /// Attempt to decode an instruction at the given offset and return the new
    /// offset.
    pub fn decode_instruction_at(&self, offset: usize) -> (usize, Result<Instruction, ChunkError>) {
        decode_instruction_at(&self.instructions, offset)
    }

    /// Return a pointer to the first byte of instructions of this `Chunk`.
    pub fn first_instruction_pointer(&self) -> *const u8 {
        self.instructions.as_ptr()
    }
}

impl<'d> IntoIterator for &'d Chunk {
    type IntoIter = ChunkIter<'d>;
    type Item = (usize, Result<Instruction<'d>, ChunkError>);

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// Attempt to decode an instruction at the given offset and return the new
/// offset.
fn decode_instruction_at(
    instructions: &[u8],
    offset: usize,
) -> (usize, Result<Instruction, ChunkError>) {
    if instructions.is_empty() || offset >= instructions.len() {
        // TODO: should this panic or do something else? An empty chunk sounds like
        // something went very wrong
        return (
            offset,
            Err(ChunkError::InsufficientRemainingData {
                expected: 1,
                actual: 0,
            }),
        );
    }

    let op = match OpCode::try_from(instructions[offset]) {
        Ok(op) => op,
        Err(e) => {
            return (offset + 1, Err(e.into()));
        },
    };

    let args_size = op.arguments_size();
    if instructions.len() < (offset + 1 + args_size) {
        return (
            instructions.len(),
            Err(ChunkError::InsufficientRemainingData {
                expected: args_size,
                actual: instructions.len() - (offset + 1),
            }),
        );
    }

    let arguments = &instructions[(offset + 1)..(offset + 1 + args_size)];
    (offset + 1 + args_size, Ok(Instruction { op, arguments }))
}

/// Attempt to decode an instruction at the given pointer, and then optionally
/// read arguments data.
///
/// # Safety
/// Calling this function requires that the `Instruction`s in this byte array
/// are valid.
pub unsafe fn decode_instruction_at_unchecked<'d>(
    instructions_ptr: *const u8,
) -> (*const u8, Instruction<'d>) {
    let op = OpCode::try_from_byte_unchecked(*instructions_ptr);

    let args_size = op.arguments_size();
    let args_ptr = instructions_ptr.offset(1);

    let arguments = slice::from_raw_parts(args_ptr, args_size);
    (
        instructions_ptr.add(1 + args_size),
        Instruction { op, arguments },
    )
}

/// This struct represents a line number along with a count of how many
/// consecutive bytes have the same line number.
#[derive(Debug, Copy, Clone, PartialEq, Hash)]
pub struct LineNumber {
    line_number: usize,
    count: u32,
}

/// An iterator over all the instructions in a `Chunk`.
pub struct ChunkIter<'d> {
    instructions: &'d [u8],
    offset: usize,
}

impl<'d> Iterator for ChunkIter<'d> {
    type Item = (usize, Result<Instruction<'d>, ChunkError>);

    fn next(&mut self) -> Option<Self::Item> {
        if self.offset >= self.instructions.len() {
            return None;
        }

        let old_offset = self.offset;
        let (new_offset, inst) = decode_instruction_at(self.instructions, old_offset);
        self.offset = new_offset;

        Some((old_offset, inst))
    }
}

/// Errors that occur while iterating overing `Instruction`s.
#[derive(Debug, Copy, Clone, PartialEq, thiserror::Error)]
pub enum ChunkError {
    /// Error converting a byte to a valid `OpCode`
    #[error("error converting to opcode: {}", .0)]
    Conversion(#[from] TryFromByteError),
    /// Error when attempting to read `Instruction` arguments data, not enough
    /// bytes left in the buffer
    #[error("insufficient data remaining, expected {} bytes, found {} bytes", .expected, .actual)]
    InsufficientRemainingData {
        /// How many bytes were expected
        expected: usize,
        /// How many bytes were actually in the buffer
        actual: usize,
    },
    /// A `Chunk` is not valid unless it has a `Opcode::Return` at the very end
    #[error("no `OpCode::Return` found at the end of the chunk")]
    MissingFinalReturn,
}

/// A builder structure that represents a `Chunk` in the process of being built.
#[derive(Debug)]
pub struct ChunkBuilder<'h> {
    line_numbers: Vec<LineNumber>,
    instructions: Vec<u8>,
    constants: Vec<Value>,
    heap: &'h Heap,
}

impl<'h> ChunkBuilder<'h> {
    /// Create a new `ChunkBuilder` with the given `Heap`.
    pub fn new(heap: &'h Heap) -> Self {
        ChunkBuilder {
            line_numbers: Vec::new(),
            instructions: Vec::new(),
            constants: Vec::new(),
            heap,
        }
    }

    /// Write a new `OpCode::Return` instruction to the chunk.
    pub fn return_inst(&mut self, line_number: usize) -> &mut Self {
        self.simple_inst(OpCode::Return, line_number)
    }

    /// Write a new `OpCode::Constant` instruction to the chunk.
    pub fn constant_inst(&mut self, value: impl Into<Value>, line_number: usize) -> &mut Self {
        self.write_line_number(line_number, 2);
        let constant_idx = self.constants.len();
        assert!(constant_idx <= u8::MAX as usize);

        self.constants.push(value.into());
        self.instructions.push(OpCode::Constant.into());
        self.instructions.push(constant_idx as u8);

        self
    }

    /// Allocate a new constant `StringObject` and write a new
    /// `OpCode::Constant` instruction to the chunk that references it.
    pub fn constant_string_inst(&mut self, s: impl Into<String>, line_number: usize) -> &mut Self {
        let value = self.heap.allocate_string(s);
        self.constant_inst(value, line_number)
    }

    /// Write a new simple (no extra data) instruction to the chunk.
    pub fn simple_inst(&mut self, op: OpCode, line_number: usize) -> &mut Self {
        self.write_line_number(line_number, 1);

        self.instructions.push(op.into());

        self
    }

    /// Consume this `ChunkBuilder` and return an immutable `Chunk`.
    pub fn build(self) -> Result<Chunk, ChunkError> {
        let chunk = Chunk {
            line_numbers: self.line_numbers.into_boxed_slice(),
            instructions: self.instructions.into_boxed_slice(),
            constants: self.constants.into_boxed_slice(),
        };

        if let Err(errs) = chunk.validate_instructions() {
            return Err(errs[0]);
        }

        let (_, last_inst) = chunk.iter().last().ok_or(ChunkError::MissingFinalReturn)?;

        if last_inst?.op != OpCode::Return {
            return Err(ChunkError::MissingFinalReturn);
        }

        Ok(chunk)
    }

    fn write_line_number(&mut self, line_number: usize, num_lines: u32) {
        if let Some(LineNumber {
            line_number: last_line_no,
            count,
        }) = self.line_numbers.last_mut()
        {
            if *last_line_no == line_number {
                *count += num_lines;
            } else {
                self.line_numbers.push(LineNumber {
                    line_number,
                    count: num_lines,
                });
            }
        } else {
            self.line_numbers.push(LineNumber {
                line_number,
                count: num_lines,
            });
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn small_chunk_disassembly() {
        let heap = Heap::new();
        let mut builder = ChunkBuilder::new(&heap);

        builder
            .constant_inst(32.0, 123)
            .constant_inst(64.0, 123)
            .return_inst(123);

        let chunk = builder.build().unwrap();

        let mut output = Vec::<u8>::new();
        chunk
            .write_disassembled(&mut output, Some("test chunk"))
            .unwrap();

        assert_eq!(
            String::from_utf8(output).unwrap(),
            "== test chunk ==
0000  123 OP_CONSTANT      0 '32'
0002    | OP_CONSTANT      1 '64'
0004    | OP_RETURN        
"
        )
    }
}
