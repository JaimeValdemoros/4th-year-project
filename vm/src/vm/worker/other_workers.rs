use types::*;
use vm::worker::{Worker, WorkerState, ReadyWorker, Allocated, Result};
use vm::memory::Memory;
use vm::channel::Channels;

#[derive(Debug)]
pub struct ReadingState {
    pub channel: ChanLabel,
}

impl WorkerState for ReadingState {}

pub type ReadingWorker<'a> = Worker<'a, ReadingState>;

impl<'a> ReadingWorker<'a> {
    pub fn from(w: ReadyWorker<'a>, chan: ChanLabel) -> Self {
        w.change_state(ReadingState { channel: chan })
    }

    pub fn reader_wake(self, v: StackVal) -> ReadyWorker<'a> {
        ReadyWorker::from(self, vec![v])
    }
}

#[derive(Debug)]
pub struct WritingState {
    pub channel: ChanLabel,
    pub val: StackVal,
}

impl WorkerState for WritingState {}

pub type WritingWorker<'a> = Worker<'a, WritingState>;

impl<'a> WritingWorker<'a> {
    pub fn from(w: ReadyWorker<'a>, chan: ChanLabel, val: StackVal) -> Self {
        w.change_state(WritingState {
                           channel: chan,
                           val: val,
                       })
    }

    pub fn writer_wake(self) -> (StackVal, ReadyWorker<'a>) {
        (self.state.val, ReadyWorker::from(self, Vec::new()))
    }
}

#[derive(Debug)]
pub struct DoneState;

impl WorkerState for DoneState {}

pub type DoneWorker<'a> = Worker<'a, DoneState>;

impl<'a> DoneWorker<'a> {
    pub fn drop_memory(&mut self, mem: &mut Memory, chans: &mut Channels) -> Result<()> {
//        println!("Dropped memory: {:?}", self.id);
        for a in ::std::mem::replace(&mut self.allocated, Vec::new()) {
            match a {
                Allocated::Chan(c) => chans.free_channels(Some(c))?,
                Allocated::Arr(pos, size) => mem.free(pos, size),
                Allocated::ChannArr(pos, cs) => {
                    mem.free(pos as usize, cs.len());
                    chans.free_channels(cs)?
                }
            }
        }
        Ok(())
    }
}
