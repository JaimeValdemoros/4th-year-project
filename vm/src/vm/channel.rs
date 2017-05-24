extern crate uuid;

use std::mem;

use types::*;

use vm::worker::{ReadyWorker, ReadingWorker, AltWorker, WritingWorker};
use errors::ChannelError;
use time::{Time, TimeWaiting, TimedAlt};

pub type Result<T> = ::std::result::Result<T, ChannelError>;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct AltToken(usize);

#[derive(Debug)]
enum ChannelState<'a> {
    Empty,
    ReadWaiting(WritingWorker<'a>),
    AltWaiting(AltToken),
    WriteWaiting(ReadingWorker<'a>),
}

impl<'a> ChannelState<'a> {
    fn take(&mut self) -> Self {
        mem::replace(self, ChannelState::Empty)
    }
}

#[derive(Debug)]
pub struct Channel<'a> {
    ch_id: uuid::Uuid,
    state: ChannelState<'a>,
}

impl<'a> Channel<'a> {
    fn new() -> Channel<'a> {
        Channel {
            ch_id: uuid::Uuid::new_v4(),
            state: ChannelState::Empty,
        }
    }

    fn is_empty(&self) -> bool {
        match self.state {
            ChannelState::Empty => true,
            _ => false,
        }
    }

    fn read(&mut self,
            r_worker: ReadingWorker<'a>)
            -> Result<Option<(ReadyWorker<'a>, ReadyWorker<'a>)>> {
        // Take the contents of the state field so we can use it
        // WARNING: this sets the state to Empty
        match self.state.take() {
            ChannelState::Empty => {
                self.state = ChannelState::WriteWaiting(r_worker);
                Ok(None)
            }
            ChannelState::ReadWaiting(w_worker) => {
                let (v, w1) = w_worker.writer_wake();
                let w2 = r_worker.reader_wake(v);
                self.state = ChannelState::Empty;
                Ok(Some((w1, w2)))
            }
            _ => Err(ChannelError::InvalidState),
        }
    }

    fn read_alt(&mut self,
                ch: ChanLabel,
                a_worker: AltWorker<'a>)
                -> Result<(ReadyWorker<'a>, ReadyWorker<'a>)> {
        match self.state.take() {
            ChannelState::ReadWaiting(w_worker) => {
                let (v, w1) = w_worker.writer_wake();
                let w2 = a_worker.chan_wake(ch, v);
                self.state = ChannelState::Empty;
                Ok((w1, w2))
            }
            _ => panic!(),
        }
    }

    fn alt_token(&mut self, tok: AltToken) -> Result<()> {
        if !self.is_empty() {
            Err(ChannelError::InvalidState)
        } else {
            self.state = ChannelState::AltWaiting(tok);
            Ok(())
        }
    }

    fn un_alt(&mut self) -> Result<()> {
        match self.state {
            ChannelState::AltWaiting(_) => Ok(self.state = ChannelState::Empty),
            _ => Err(ChannelError::InvalidState),
        }
    }
}

#[derive(Debug)]
struct AltWorkers<'a>(Vec<Option<AltWorker<'a>>>);

impl<'a> AltWorkers<'a> {
    fn new() -> AltWorkers<'a> {
        AltWorkers(Vec::new())
    }

    fn insert(&mut self, w: AltWorker<'a>) -> AltToken {
        let pos = self.0.len();
        self.0.push(Some(w));
        AltToken(pos)
    }

    fn get(&mut self, tok: AltToken) -> Result<AltWorker<'a>> {
        self.0
            .get_mut(tok.0) // Option<&mut Option<AltWorker>>
            // take() swaps out the value in the location for None
            // and_then(_) to flatten the Option<Option<_>>
            .and_then(|m_w| m_w.take()) // Option<AltWorker>
            .ok_or(ChannelError::AltNotFound) // Result<AltWorker>
    }
}

#[derive(Debug)]
pub struct ChannelPos(pub usize);

#[derive(Debug)]
pub struct Channels<'a> {
    free: Vec<ChannelPos>,
    channels: Vec<Channel<'a>>,
    alt_workers: AltWorkers<'a>,
    time_channel: TimeWaiting,
}


impl<'a> Channels<'a> {
    pub fn new() -> Channels<'a> {
        Channels {
            free: vec![],
            channels: vec![],
            alt_workers: AltWorkers::new(),
            time_channel: TimeWaiting::new(),
        }
    }

    pub fn all_done(&self) -> bool {
        for n in 0..self.channels.len() {
            // check if this channel has been free'd.
            // We do this by checking that each position in
            // the vector has a corresponding token in the
            // 'free' collection.
            if self.free.iter().position(|tok| tok.0 == n).is_none() {
                return false;
            }
        }
        true
    }

    pub fn new_channel(&mut self) -> ChannelPos {
        match self.free.pop() {
            Some(pos) => pos,
            None => {
                let pos = self.channels.len();
                self.channels.push(Channel::new());
                ChannelPos(pos)
            }
        }
    }

    pub fn free_channels<I>(&mut self, chs: I) -> Result<()>
        where I: IntoIterator<Item = ChannelPos>
    {
        for ch in chs {
            if !self.channels[ch.0].is_empty() {
                return Err(ChannelError::InvalidState);
            }
            self.free.push(ch)
        }
        Ok(())
    }


    pub fn read(&mut self,
                r_worker: ReadingWorker<'a>)
                -> Result<Option<(ReadyWorker<'a>, ReadyWorker<'a>)>> {
        let channel_pos = r_worker.state.channel;
        self.channels[channel_pos].read(r_worker)
    }

    pub fn alt(&mut self,
               a_worker: AltWorker<'a>)
               -> Result<Option<(ReadyWorker<'a>, ReadyWorker<'a>)>> {
        let chan_search = a_worker
            .channels()
            .into_iter()
            .find(|&ch| !self.channels[ch].is_empty());
        println!("ALT list; {:?}", a_worker.channels());
        println!("ALT search; {:?}", chan_search);
        if let Some(ch) = chan_search {
            self.channels[ch].read_alt(ch, a_worker).map(Some)
        } else {

            let maybe_time = a_worker.time();
            let channels = a_worker.channels();
            let token = self.alt_workers.insert(a_worker);
            for ch in channels {
                self.channels[ch].alt_token(token)?
            }
            if let Some(time) = maybe_time {
                self.time_channel.push(TimedAlt::from((time, token)));
            }

            Ok(None)

        }
    }

    pub fn write(&mut self,
                 w_worker: WritingWorker<'a>)
                 -> Result<Option<(ReadyWorker<'a>, ReadyWorker<'a>)>> {
        let channel_pos = w_worker.state.channel;
        println!("Writing to channel {:?}", channel_pos);
        let channel_state = self.channels[channel_pos].state.take();
        match channel_state {
            ChannelState::Empty => {
                self.channels[channel_pos].state = ChannelState::ReadWaiting(w_worker);
                Ok(None)
            }
            ChannelState::WriteWaiting(r_worker) => {
                let (v, w1) = w_worker.writer_wake();
                let w2 = r_worker.reader_wake(v);
                Ok(Some((w1, w2)))
            }
            ChannelState::AltWaiting(tok) => {
                let (v, w1) = w_worker.writer_wake();
                let w2 = self.alt_workers.get(tok)?;
                for channel in w2.channels() {
                    if channel != channel_pos {
                        self.channels[channel].un_alt()?
                    }
                }
                Ok(Some((w1, w2.chan_wake(channel_pos, v))))
            }
            ChannelState::ReadWaiting(_) => {
                self.channels[channel_pos].state = channel_state;
                Err(ChannelError::InvalidState)
            }
        }
    }

    pub fn wake_timer(&mut self, time: Time) -> Result<Vec<ReadyWorker<'a>>> {
        let tokens = self.time_channel.pop_ready(time);
        let mut a_workers = Vec::new();
        for TimedAlt(_, tok) in tokens {
            let a_worker = self.alt_workers.get(tok)?;
            for channel in a_worker.channels() {
                self.channels[channel].un_alt()?;
            }
            a_workers.push(a_worker.time_wake(time))
        }
        Ok(a_workers)
    }
}
