use std::fmt::Debug;

pub mod string;

use types::*;
use errors::ProgramError;

pub type Result<T> = ::std::result::Result<T, ProgramError>;

pub trait Program<'a>: Debug {

    fn get_pos(&self) -> usize;

    fn read_next(&mut self) -> Result<Op>;

    fn goto(&mut self, pos: ProgPos);

    fn child(&self) -> Box<Program<'a> + 'a>;

    fn child_at(&self, pos: ProgPos) -> Box<Program<'a> + 'a> {
        let mut c = self.child();
        c.goto(pos);
        c
    }
}

#[allow(dead_code)]
#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub enum StackOp {
    NOP,
    SWAP,
    DUP,
    ADD,
    MUL,
    DIV,
    MOD,
    NEG,
    EQ,
    AND,
    OR,
    NOT,
    GT,
    LIT(StackVal),
    KEY, SCR
}

#[allow(dead_code)]
#[derive(Debug, Copy, Clone)]
pub enum MemOp {
    INC,
    DEC,
    LDW,
    STW,
    LOCAL(u8),
    FP
}

#[allow(dead_code)]
#[derive(Debug, Copy, Clone)]
pub enum ProcOp {
    NewFrame,
    DropFrame,
    // Declare an array
    NewArr,
    // Declare a channel
    NewChan,
    // Declare a channel array
    NewChanArr,
    // Channel reading and writing
    ChanRead,
    ChanWrite,
    // Alt constructs
    StartAlts,
    AltBranch(u8),
    TimeBranch(u8),
    EndAlts,
    // Par constructs
    StartPars,
    ParBranch,
    EndPars,
    // Indexed Par
    IndexPar,
    // Process done
    EndProc,
    Stop
}

#[allow(dead_code)]
#[derive(Debug, Copy, Clone)]
pub enum TapeOp {
    Jump, // Jump a given distance
    CJump, // conditionally jump a given distance
}

#[allow(dead_code)]
#[derive(Debug, Copy, Clone)]
pub enum Op {
    Tape(TapeOp),
    Stack(StackOp),
    Mem(MemOp),
    Proc(ProcOp),
}
