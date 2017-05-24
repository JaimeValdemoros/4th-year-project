use types::*;
use program::ProcOp;
use vm::memory::Memory;
use vm::channel::Channels;
use errors::WorkerError;
use time::Time;
use vm::frame::Frame;

use vm::worker::*;

#[derive(Debug)]
// 'Ready' takes an optional parameter of a value to push
// onto its stack as it gets run
pub struct ReadyState(pub Vec<StackVal>);

impl WorkerState for ReadyState {}

pub type ReadyWorker<'a> = Worker<'a, ReadyState>;

impl<'a> ReadyWorker<'a> {
    pub fn from<T: WorkerState>(w: Worker<'a, T>, vals: Vec<StackVal>) -> Self {
        w.change_state(ReadyState(vals))
    }

    fn new_array(&mut self, mem: &mut Memory) -> Result<()> {
        let size = self.stack.pop(self.program.get_pos())? as usize;
        let pointer = mem.alloc(size as usize)?;
        self.stack.push(pointer as StackVal)?;
        self.allocated.push(Allocated::Arr(pointer, size));
        Ok(())
    }

    fn new_chan(&mut self, mem: &mut Memory, chans: &mut Channels) -> Result<()> {
        let pointer = chans.new_channel();
        self.stack.push(pointer.0 as StackVal)?;
        self.allocated.push(Allocated::Chan(pointer));
        Ok(())
    }

    fn new_chan_array(&mut self, mem: &mut Memory, chans: &mut Channels) -> Result<()> {
        let size = self.stack.pop(self.program.get_pos())? as usize;
        let arr_pointer = mem.alloc(size)?;
        let mut channels = Vec::with_capacity(size);
        for i in 0..size {
            let c_pointer = chans.new_channel();
            mem.put((arr_pointer + i as usize), c_pointer.0 as i32)?;
            channels.push(c_pointer)
        }
        self.stack.push(arr_pointer as StackVal)?;
        self.allocated
            .push(Allocated::ChannArr(arr_pointer, channels));
        println!("Worker allocated: {:?}", self.id);
        Ok(())
    }

    fn chan_read(mut self, mem: &mut Memory) -> Result<ReadingWorker<'a>> {
        let chan = self.stack.pop(self.program.get_pos())? as ChanLabel;
        Ok(ReadingWorker::from(self, chan))
    }

    fn chan_write(mut self, mem: &mut Memory) -> Result<WritingWorker<'a>> {
        let chan = self.stack.pop(self.program.get_pos())? as ChanLabel;
        let val = self.stack.pop(self.program.get_pos())? as StackVal;
        Ok(WritingWorker::from(self, chan, val))
    }

    fn alt(mut self, mem: &mut Memory, chans: &mut Channels) -> Result<AltWorker<'a>> {
        let mut a_state = AltState::new();

        loop {
            let alt_op = self.run_until_proc(mem)?;
            println!("Id: {:?} Op: {:?}, Stack: {:?}", self.id, alt_op, self.stack);
            match alt_op {

                ProcOp::AltBranch(n) => {
                    let dist = self.stack.pop(self.program.get_pos())? as ProgPos;
                    let indexes =
                        (0..n).map(|_| self.stack.pop(self.program.get_pos()).map_err(WorkerError::FrameError))
                              .collect::<Result<Vec<StackVal>>>()?;
                    let chan = self.stack.pop(self.program.get_pos())? as ChanLabel;
                    a_state.chan_branch(chan, dist, indexes)
                }

                ProcOp::TimeBranch(n) => {
                    let dist = self.stack.pop(self.program.get_pos())? as ProgPos;
                    let indexes =
                        (0..n).map(|_| self.stack.pop(self.program.get_pos()).map_err(WorkerError::FrameError))
                            .collect::<Result<Vec<StackVal>>>()?;
                    let time = self.stack.pop(self.program.get_pos())? as StackVal;
                    a_state.time_branch(Time::from(time), dist, indexes)
                }

                ProcOp::NewArr => {self.new_array(mem);}
                ProcOp::NewChan => {self.new_chan(mem, chans);}
                ProcOp::NewChanArr => {self.new_chan_array(mem, chans);}

                ProcOp::NewFrame => {
                    let size = self.stack.pop(self.program.get_pos())?;
                    let frame = Frame::new(mem, size as u32)?;
                    mem.put(frame.mem_location -1, self.frame_pointer as i32);
                    self.frame_pointer = frame.mem_location;
                    self.frames.push(frame);
                },
                ProcOp::DropFrame => {
                    let frame = self.frames.pop().unwrap();
                    self.frame_pointer = mem.get(self.frame_pointer as usize - 1)? as usize;
                    frame.destroy(mem);
                }

                ProcOp::EndAlts => break,
                ProcOp::Stop => panic!("Program called STOP"),
                _ => return Err(WorkerError::DisallowedOp),
            }
        }

        Ok(self.change_state(a_state))
    }

    fn par_indexed(mut self, mem: &mut Memory) -> Result<WorkerWrapper<'a>> {
        let pos = self.stack.pop(self.program.get_pos())? as ProgPos;
        let end_index = self.stack.pop(self.program.get_pos())?;
        let start_index = self.stack.pop(self.program.get_pos())?;

        let mut par_state = ParState::new();

        for i in start_index..end_index {
            par_state.child(pos, Some(i));
        }

        let (par_worker, children) = ParWorker::from(self, par_state, mem)?;
        Ok(WorkerWrapper::Par(par_worker, children))
    }

    fn par(mut self, mem: &mut Memory, chans: &mut Channels) -> Result<WorkerWrapper<'a>> {
        let mut par_state = ParState::new();
        loop {
            let par_op = self.run_until_proc(mem)?;
            println!("Id: {:?} Op: {:?}, Stack: {:?}", self.id, par_op, self.stack);
            match par_op {
                ProcOp::ParBranch => {
                    let pos = self.stack.pop(self.program.get_pos())? as ProgPos;
                    par_state.child(pos, None)
                }
                ProcOp::EndPars => break,
                ProcOp::Stop => panic!("Program called STOP"),

                ProcOp::NewArr => {self.new_array(mem);}
                ProcOp::NewChan => {self.new_chan(mem, chans);}
                ProcOp::NewChanArr => {self.new_chan_array(mem, chans);}

                ProcOp::NewFrame => {
                    let size = self.stack.pop(self.program.get_pos())?;
                    let frame = Frame::new(mem, size as u32)?;
                    mem.put(frame.mem_location -1, self.frame_pointer as i32);
                    self.frame_pointer = frame.mem_location;
                    self.frames.push(frame);
                },
                ProcOp::DropFrame => {
                    let frame = self.frames.pop().unwrap();
                    self.frame_pointer = mem.get(self.frame_pointer as usize - 1)? as usize;
                    frame.destroy(mem);
                }

                _ => return Err(WorkerError::DisallowedOp),
            }
        }

        let (par_worker, children) = ParWorker::from(self, par_state, mem)?;
        Ok(WorkerWrapper::Par(par_worker, children))
    }

    pub fn run(mut self, mem: &mut Memory, chans: &mut Channels) -> Result<WorkerWrapper<'a>> {
        for v in ::std::mem::replace(&mut self.state.0, Vec::new()) {
            self.stack.push(v)?
        }
        let proc_op = self.run_until_proc(mem)?; // run until we get a procOp
        println!("Id: {:?} Op: {:?}, Stack: {:?}", self.id, proc_op, self.stack);
        match proc_op {
            ProcOp::Stop => panic!("Program called STOP"),
            ProcOp::NewArr => self.new_array(mem).map(|()| WorkerWrapper::Ready(self)),
            ProcOp::NewChan => self.new_chan(mem, chans).map(|()| WorkerWrapper::Ready(self)),
            ProcOp::NewChanArr => self.new_chan_array(mem, chans).map(|()| WorkerWrapper::Ready(self)),
            ProcOp::ChanRead => self.chan_read(mem).map(WorkerWrapper::Read),
            ProcOp::ChanWrite => self.chan_write(mem).map(WorkerWrapper::Write),
            ProcOp::StartAlts => self.alt(mem, chans).map(WorkerWrapper::Alt),
            ProcOp::StartPars => self.par(mem, chans),
            ProcOp::IndexPar => self.par_indexed(mem),
            ProcOp::EndProc => Ok(WorkerWrapper::Done(self.change_state(DoneState))),
            ProcOp::NewFrame => {
                let size = self.stack.pop(self.program.get_pos())?;
                let frame = Frame::new(mem, size as u32)?;
                mem.put(frame.mem_location -1, self.frame_pointer as i32);
                self.frame_pointer = frame.mem_location;
                self.frames.push(frame);
                Ok(WorkerWrapper::Ready(self))
            },
            ProcOp::DropFrame => {
                let frame = self.frames.pop().unwrap();
                self.frame_pointer = mem.get(self.frame_pointer as usize - 1)? as usize;
                frame.destroy(mem);
                Ok(WorkerWrapper::Ready(self))
            }
            _ => Err(WorkerError::DisallowedOp)
        }
    }
}
