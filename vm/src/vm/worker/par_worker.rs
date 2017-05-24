use itertools::Either::{self, Left, Right};

use types::*;
use vm::worker::{Result, Worker, WorkerState, ReadyState, ReadyWorker, DoneWorker};
use vm::memory::Memory;

#[derive(Debug)]
pub struct ParState {
    children: Either<Vec<(ProgPos, Option<Index>)>, u32>,
}

impl ParState {
    pub fn new() -> ParState {
        ParState { children: Left(Vec::new()) }
    }

    pub fn child(&mut self, pos: ProgPos, index: Option<Index>) {
        match self.children {
            Left(ref mut vs) => vs.push((pos, index)),
            Right(_) => unreachable!(),
        }
    }
}

pub type Index = StackVal;

impl WorkerState for ParState {}

pub type ParWorker<'a> = Worker<'a, ParState>;

impl<'a> ParWorker<'a> {
    pub fn from(w: ReadyWorker<'a>,
                mut state: ParState,
                mem: &mut Memory)
                -> Result<(Self, Vec<ReadyWorker<'a>>)> {
        let cs = match ::std::mem::replace(&mut state.children, Right(0)) {
            Left(vs) => vs,
            Right(_) => unreachable!(),
        };
        let mut p_worker = w.change_state(state);
        let r_workers: Result<Vec<_>> = cs.into_iter()
            .map(|(pos, index)| p_worker.make_child(mem, pos, index))
            .collect();
        Ok((p_worker, r_workers?))
    }

    fn make_child(&mut self,
                  mem: &mut Memory,
                  pos: ProgPos,
                  v: Option<Index>)
                  -> Result<ReadyWorker<'a>> {

        assert!(self.state.children.is_right());
        self.state.children.as_mut().map_right(|mut x| *x += 1);

        let mut my_prog = self.program.child();
        my_prog.goto(pos);

        let mut w = ReadyWorker::child(mem, my_prog, self.id)?;
        w.frame_pointer = self.frame_pointer;
        w.state = ReadyState(v.map_or(Vec::new(), |v| vec![v]));

        Ok(w)
    }

    pub fn child_done(mut self, c: DoneWorker<'a>) -> Either<ParWorker<'a>, ReadyWorker<'a>> {
        assert_eq!(c.parent_id, Some(self.id));

        assert!(self.state.children.is_right());
        self.state.children.as_mut().map_right(|mut x| *x -= 1);

        match self.state.children.as_ref() {
            Right(&n) => {
                if n == 0 {
                    Right(ReadyWorker::from(self, Vec::new()))
                } else {
                    Left(self)
                }
            }
            Left(_) => unreachable!(),
        }
    }
}
