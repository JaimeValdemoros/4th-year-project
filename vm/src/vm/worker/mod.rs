use uuid::Uuid;

mod ready_worker;
mod par_worker;
mod alt_worker;
mod other_workers;

pub use self::ready_worker::*;
pub use self::par_worker::*;
pub use self::alt_worker::*;
pub use self::other_workers::*;

use types::*;
use errors::WorkerError;
use vm::memory::Memory;
use vm::frame::{Frame, Stack};
use vm::channel::ChannelPos;
use program::Program;
use program::{Op, StackOp, ProcOp, TapeOp, MemOp};

pub type Result<T> = ::std::result::Result<T, WorkerError>;

// Possible states for the worker
pub trait WorkerState {}

#[derive(Debug)]
pub enum Allocated {
    Chan(ChannelPos), // single label
    ChannArr(usize, Vec<ChannelPos>), // list of channels
    Arr(usize, usize), // array with size
}

#[derive(Debug)]
pub struct Worker<'a, S: WorkerState> {
    pub id: Uuid,
    pub parent_id: Option<Uuid>,
    pub state: S,
    program: Box<Program<'a> + 'a>,
    stack: Stack,
    frame_pointer: usize,
    frames: Vec<Frame>,
    allocated: Vec<Allocated>,
}

pub enum WorkerWrapper<'a> {
    Ready(ReadyWorker<'a>),
    Done(DoneWorker<'a>),
    Par(ParWorker<'a>, Vec<ReadyWorker<'a>>),
    Read(ReadingWorker<'a>),
    Alt(AltWorker<'a>),
    Write(WritingWorker<'a>),
}

impl<'a, S: WorkerState> Worker<'a, S> {
    fn new(mem: &mut Memory,
           mut prog: Box<Program<'a> + 'a>,
           parent: Option<Uuid>)
           -> Result<ReadyWorker<'a>> {
        let res = Ok(Worker {
               id: Uuid::new_v4(),
               parent_id: parent,
               state: ReadyState(vec![]),
               program: prog,
               stack: Stack::new(),
               frame_pointer: 0,
               frames: Vec::new(),
               allocated: Vec::new(),
           });
//        println!("New worker: {:?}", res.as_ref().unwrap().id);
        res
    }

    pub fn root(mem: &mut Memory, prog: Box<Program<'a> + 'a>) -> Result<ReadyWorker<'a>> {
        ReadyWorker::<'a>::new(mem, prog, None)
    }

    pub fn child(mem: &mut Memory,
                 prog: Box<Program<'a> + 'a>,
                 parent: Uuid)
                 -> Result<ReadyWorker<'a>> {
        ReadyWorker::<'a>::new(mem, prog, Some(parent))
    }

    pub fn id(&self) -> Uuid {
        self.id
    }

    pub fn parent_id(&self) -> Option<Uuid> {
        self.parent_id
    }

    fn change_state<T: WorkerState>(self, s: T) -> Worker<'a, T> {
        Worker {
            id: self.id,
            parent_id: self.parent_id,
            state: s,
            program: self.program,
            stack: self.stack,
            frame_pointer: self.frame_pointer,
            frames: self.frames,
            allocated: self.allocated,
        }
    }

    fn tape_op(&mut self, mem: &mut Memory, op: TapeOp) -> Result<()> {
        match op {
            TapeOp::Jump => {
                let pos = self.stack.pop(self.program.get_pos())? as ProgPos;
                self.program.goto(pos);
            }
            TapeOp::CJump => {
                let pos = self.stack.pop(self.program.get_pos())? as ProgPos;
                let b = self.stack.pop(self.program.get_pos())?;
                if b != 0 {
                    self.program.goto(pos)
                }
            }
        }
        Ok(())
    }

    fn mem_op(&mut self, mem: &mut Memory, op: MemOp) -> Result<()> {
        match op {
            MemOp::INC => {
                let pos = self.stack.pop(self.program.get_pos())?;
                let v= mem.get(pos as usize)?;
                mem.put(pos as usize, v+1)?;
                Ok(())
            }
            MemOp::DEC => {
                let pos = self.stack.pop(self.program.get_pos())?;
                let v= mem.get(pos as usize)?;
                mem.put(pos as usize, v-1)?;
                Ok(())
            }
            MemOp::LDW => {
                let pos = self.stack.pop(self.program.get_pos())?;
                let v = mem.get(pos as usize)?;
                self.stack.push(v);
                Ok(())
            }
            MemOp::STW => {
                let pos = self.stack.pop(self.program.get_pos())?;
                let v = self.stack.pop(self.program.get_pos())?;
                mem.put(pos as usize, v)?;
                Ok(())
            }
            MemOp::FP => {
                self.stack.push(self.frame_pointer as i32);
                Ok(())
            }
            MemOp::LOCAL(n) => {
                self.stack.push(self.frame_pointer as i32 + n as i32);
                Ok(())
            }
        }
    }

    fn run_until_proc(&mut self, mem: &mut Memory) -> Result<ProcOp> {
        loop {
//            match {let v = self.program.read_next()?; println!("Id: {:?}, Op: {:?}", self.id, v); v}
            match self.program.read_next()? {
                Op::Tape(op) => self.tape_op(mem, op)?,
                Op::Stack(op) => self.stack.stack_op(op, self.program.get_pos())?,
                Op::Mem(op) => self.mem_op(mem, op)?,
                Op::Proc(op) => return Ok(op),
            }
        }
    }
}
