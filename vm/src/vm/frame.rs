use std::io::{self, Read, Write};

use types::*;
use vm::memory::Memory;
use errors::FrameError;
use program::{StackOp, MemOp};

pub type Result<T> = ::std::result::Result<T, FrameError>;

#[derive(Debug)]
pub struct Frame {
    pub mem_location: usize,
    size: u32
}

impl Frame {
    pub fn new(mem: &mut Memory, size: u32) -> Result<Frame> {
        let pointer = mem.alloc((size+1) as usize)?;
        Ok(Frame {
            mem_location: pointer+1,
            size: size
        })
    }

    pub fn destroy(self, mem: &mut Memory) -> Result<()> {
        mem.free(self.mem_location - 1, (self.size+1) as usize); Ok(())
    }
}

#[derive(Debug)]
pub struct Stack(Vec<StackVal>);

impl Stack {
    pub fn new() -> Stack {
        Stack(Vec::new())
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn pop(&mut self, pos: ProgPos) -> Result<StackVal> {
        self.0.pop().ok_or(FrameError::StackUnderflow(pos))
    }

    pub fn push(&mut self, v: StackVal) -> Result<()> {
        Ok(self.0.push(v))
    }

    fn apply_monop<F>(&mut self, f: F, pos: usize) -> Result<()>
        where F: Fn(StackVal) -> StackVal
    {
        let x = self.pop(pos)?;
        self.push(f(x))
    }

    fn apply_binop<F>(&mut self, f: F, pos: usize) -> Result<()>
        where F: Fn(StackVal, StackVal) -> StackVal
    {
        let x1 = self.pop(pos)?;
        let x2 = self.pop(pos)?;
        self.push(f(x1, x2))
    }

    pub fn stack_op(&mut self, op: StackOp, pos: usize) -> Result<()> {
        match op {
            StackOp::NOP => Ok(()),
            StackOp::SWAP => {
                let x1 = self.pop(pos)?;
                let x2 = self.pop(pos)?;
                self.push(x1)?;
                self.push(x2)
            }
            StackOp::DUP => {
                let x1 = self.pop(pos)?;
                self.push(x1.clone())?;
                self.push(x1)
            }
            StackOp::KEY => {
                let mut v = vec![0 as u8];
                match io::stdin().read(&mut v) {
                    Ok(1) => self.0.push(v[0] as i32),
                    _ => panic!()
                }
                Ok(())
            }
            StackOp::SCR => {
                let c = self.pop(pos)?;
                print!("{}", (c as u8) as char);
                io::stdout().flush();
                Ok(())
            }
            StackOp::LIT(x) => self.push(x),
            StackOp::NEG => self.apply_monop(|x1| -x1, pos),
            StackOp::ADD => self.apply_binop(|x1, x2| x1 + x2, pos),
            StackOp::MUL => self.apply_binop(|x1, x2| x1 * x2, pos),
            StackOp::DIV => self.apply_binop(|x1, x2| x1 / x2, pos),
            StackOp::MOD => self.apply_binop(|x1, x2| x1 % x2, pos),
            StackOp::EQ => self.apply_binop(|x1, x2| if x1 == x2 { 1 } else { 0 }, pos),
            StackOp::AND => self.apply_binop(|x1, x2| x1 ^ x2, pos),
            StackOp::OR => self.apply_binop(|x1, x2| x1 | x2, pos),
            StackOp::NOT => self.apply_monop(|x| if x == 0 { 1 } else { 0 }, pos),
            StackOp::GT => self.apply_binop(|x1, x2| if x1 > x2 { 1 } else { 0 }, pos),
        }
    }
}
