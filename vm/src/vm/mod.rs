use std::collections::HashMap;
use std::collections::VecDeque;

use uuid::Uuid;
use itertools::Either::{Left, Right};

pub mod worker;
pub mod memory;
pub mod frame;
pub mod channel;

use self::memory::Memory;
use errors::VMError;
use vm::worker::{ReadyWorker, ParWorker, DoneWorker, WorkerWrapper};
use vm::channel::Channels;
use program::Program;
use time::Time;

pub type Result<T> = ::std::result::Result<T, VMError>;

#[derive(Debug)]
struct ReadyWorkers<'a>(VecDeque<ReadyWorker<'a>>);

impl<'a> ReadyWorkers<'a> {
    fn new() -> ReadyWorkers<'a> {
        ReadyWorkers(VecDeque::new())
    }

    fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    fn enqueue(&mut self, w: ReadyWorker<'a>) {
        self.0.push_back(w)
    }

    fn dequeue(&mut self) -> Option<ReadyWorker<'a>> {
        self.0.pop_front()
    }

    fn append<I>(&mut self, vals: I)
        where I: IntoIterator<Item = ReadyWorker<'a>>
    {
        for w in vals {
            self.enqueue(w)
        }
    }
}

#[derive(Debug)]
struct ParWorkers<'a>(HashMap<Uuid, ParWorker<'a>>);

impl<'a> ParWorkers<'a> {
    fn new() -> ParWorkers<'a> {
        ParWorkers(HashMap::new())
    }

    fn add(&mut self, w: ParWorker<'a>) {
        let res = self.0.insert(w.id(), w);
        if res.is_some() {
            panic!()
        }
    }

    fn one_less(&mut self, c: DoneWorker<'a>) -> Option<ReadyWorker<'a>> {
        let p_id = match c.parent_id() {
            Some(p) => p,
            None => panic!(),
        };
        let parent = match self.0.remove(&p_id) {
            Some(w) => w,
            None => panic!(),
        };

        match parent.child_done(c) {
            Left(par_parent) => {
                self.0.insert(par_parent.id(), par_parent);
                None
            }
            Right(ready_parent) => Some(ready_parent),
        }
    }

    fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

#[derive(Debug)]
pub struct VM<'a> {
    memory: Memory,
    par: ParWorkers<'a>,
    ready: ReadyWorkers<'a>,
    channels: Channels<'a>,
    time: Time,
}

impl<'a> VM<'a> {
    pub fn new(size: usize, program: &Program<'a>) -> Result<VM<'a>> {
        let mut mem = Memory::new(size, program)?;
        let worker = ReadyWorker::root(&mut mem, program.child())?;
        let mut worker_queue = ReadyWorkers::new();
        worker_queue.enqueue(worker);
        Ok(VM {
               memory: mem,
               ready: worker_queue,
               par: ParWorkers::new(),
               channels: Channels::new(),
               time: Time::new(),
           })
    }

    pub fn run(mut self) -> Result<()> {
        while let Some(worker) = self.ready.dequeue() {
            self.time.step();
            let wakeup_timed = self.channels.wake_timer(self.time)?;
            self.ready.append(wakeup_timed);
            match worker.run(&mut self.memory, &mut self.channels)? {
                // If the worker is ready to run again we simply push it
                // back on to the stack of ready workers
                WorkerWrapper::Ready(ready_worker) => self.ready.enqueue(ready_worker),
                // If the worker is done and has a parent we pass it to
                // one_less() to decrement the child index of the parent.
                // If one_less() returns the parent we push it on to the
                // stack of ready workers.
                WorkerWrapper::Done(mut done_worker) => {
                    done_worker.drop_memory(&mut self.memory, &mut self.channels);
                    if done_worker.parent_id().is_none() {
                        // this is the root so should be the last one to
                        // run. If the 'ready' queue isn't empty then we
                        // need to detect this so we break out of the loop
                        break;
                    } else {
                        // 'par'
                        let res = self.par.one_less(done_worker);
                        if let Some(parent_worker) = res {
                            self.ready.enqueue(parent_worker)
                        }
                    }
                }

                // If we are given a par-par process and its children we
                // push them on to the relevent structures
                WorkerWrapper::Par(par_worker, children) => {
                    self.par.add(par_worker);
                    for child in children {
                        self.ready.enqueue(child);
                    }
                }

                WorkerWrapper::Read(w) => {
                    if let Some((w1, w2)) = self.channels.read(w)? {
                        self.ready.append(vec![w1, w2])
                    }
                }

                WorkerWrapper::Alt(w) => {
                    if let Some((w1, w2)) = self.channels.alt(w)? {
                        self.ready.append(vec![w1, w2])
                    }
                }

                WorkerWrapper::Write(w) => {
                    if let Some((w1, w2)) = self.channels.write(w)? {
                        self.ready.append(vec![w1, w2])
                    }
                }
            }
        }

        if self.par.is_empty() && self.ready.is_empty() && self.channels.all_done() {
            Ok(())
        } else {
//            println!("Par: {:?}", self.par);
//            println!("Ready: {:?}", self.ready);
//            println!("Channels: {:?}", self.channels);
            Err(VMError::ImproperEndState)
        }
    }
}
