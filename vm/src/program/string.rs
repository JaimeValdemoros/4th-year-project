extern crate byteorder;

use std::io::Cursor;
use self::byteorder::{ReadBytesExt, BigEndian};

use types::*;
use errors::ProgramError;
use program::{Result, Op, StackOp, MemOp, TapeOp, ProcOp, Program};

#[derive(Debug)]
pub struct BinaryProgram(pub Vec<Op>);

impl From<Vec<u8>> for BinaryProgram {
    fn from(contents: Vec<u8>) -> BinaryProgram {
        BinaryProgram(read_binary(&contents).unwrap())
    }
}

#[derive(Debug)]
pub struct BinaryProgramViewer<'a> {
    index: ProgPos,
    data: &'a BinaryProgram,
}

impl<'a> From<&'a BinaryProgram> for BinaryProgramViewer<'a> {
    fn from(data: &'a BinaryProgram) -> BinaryProgramViewer {
        BinaryProgramViewer {
            data: data,
            index: 0,
        }
    }
}


impl<'a> Program<'a> for BinaryProgramViewer<'a> {

    fn get_pos(&self) -> usize {
        self.index
    }

    fn read_next(&mut self) -> Result<Op> {
        self.index += 1;
        let res = self.data.0.get(self.index - 1).cloned().ok_or(ProgramError::EndOfFile);
        res
    }

    fn goto(&mut self, pos: ProgPos) {
        self.index = pos
    }

    fn child(&self) -> Box<Program<'a> + 'a> {
        Box::new(BinaryProgramViewer {
            data: self.data,
            index: self.index,
        })
    }
}

fn read_binary(binary: &Vec<u8>) -> Result<Vec<Op>> {
    let mut res = Vec::new();
    let mut input = binary.iter();
    while let Some(&next) = input.next() {
        match read_ops(next) {
            ReadResult::Op(op) => res.push(op),
            ReadResult::Fail(code) => return Err(ProgramError::InvalidOpCode(code)),
            ReadResult::Lit => {
                let vs = (0..4)
                    .map(|i| input.next().cloned())
                    .collect::<Option<Vec<u8>>>()
                    .ok_or(ProgramError::LiteralReadError)?;
                let val = Cursor::new(vs)
                    .read_i32::<BigEndian>()
                    .map(|x| Op::Stack(StackOp::LIT(x)))
                    .map_err(|_| ProgramError::LiteralReadError)?;
                res.push(val);
            }
        }
    }
    Ok(res)
}


enum ReadResult {
    Fail(u8),
    Op(Op),
    Lit,
}

fn read_ops(v: u8) -> ReadResult {

    use self::ReadResult::*;
    use program::Op::*;

    match v {
        0 => Op(Stack(StackOp::NOP)),
        1 => Op(Stack(StackOp::SWAP)),
        2 => Op(Stack(StackOp::DUP)),
        3 => Op(Mem(MemOp::INC)),
        4 => Op(Mem(MemOp::DEC)),
        5 => Op(Stack(StackOp::ADD)),
        6 => Op(Stack(StackOp::MUL)),
        7 => Op(Stack(StackOp::DIV)),
        8 => Op(Stack(StackOp::MOD)),
        9 => Op(Stack(StackOp::NEG)),
        10 => Op(Stack(StackOp::EQ)),
        11 => Op(Stack(StackOp::AND)),
        12 => Op(Stack(StackOp::OR)),
        13 => Op(Stack(StackOp::NOT)),
        14 => Op(Stack(StackOp::GT)),

        15 => Op(Mem(MemOp::LDW)),
        16 => Op(Mem(MemOp::STW)),
        17 => Op(Mem(MemOp::FP)),

        18 => Op(Proc(ProcOp::NewArr)),
        19 => Op(Proc(ProcOp::NewChan)),
        20 => Op(Proc(ProcOp::NewChanArr)),

        21 => Op(Proc(ProcOp::NewFrame)),
        22 => Op(Proc(ProcOp::DropFrame)),

        23 => Op(Proc(ProcOp::ChanRead)),
        24 => Op(Proc(ProcOp::ChanWrite)),
        25 => Op(Proc(ProcOp::StartAlts)),
        26 => Op(Proc(ProcOp::EndAlts)),
        27 => Op(Proc(ProcOp::StartPars)),
        28 => Op(Proc(ProcOp::ParBranch)),
        29 => Op(Proc(ProcOp::EndPars)),
        30 => Op(Proc(ProcOp::IndexPar)),
        31 => Op(Proc(ProcOp::EndProc)),
        x if x >= 32 && x < 64 => Op(Proc(ProcOp::AltBranch(x-32))),
        x if x >= 64 && x < 96 => Op(Proc(ProcOp::TimeBranch(x-64))),

        97 => Op(Tape(TapeOp::Jump)),
        98 => Op(Tape(TapeOp::CJump)),

        99 => Op(Stack(StackOp::KEY)),
        100 => Op(Stack(StackOp::SCR)),
        101 => Op(Proc(ProcOp::Stop)),
        102 => Lit,

        x if x >= 128 => Op(Mem(MemOp::LOCAL(x-128))),

        _ => Fail(v),
    }
}