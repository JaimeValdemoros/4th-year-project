use types::*;
use time::Time;

use vm::worker::{Worker, WorkerState, ReadyWorker};

type Index = i32;

#[derive(Debug)]
pub struct AltState {
    channels: Vec<(ChanLabel, ProgPos, Vec<Index>)>,
    timer: Option<(Time, ProgPos, Vec<Index>)>,
}

impl AltState {
    pub fn new() -> AltState {
        AltState {
            channels: Vec::new(),
            timer: None,
        }
    }

    pub fn chan_branch(&mut self, chan: ChanLabel, pos: ProgPos, index: Vec<Index>) {
        self.channels.push((chan, pos, index))
    }

    pub fn time_branch(&mut self, time: Time, pos: ProgPos, index: Vec<Index>) {
        // only update if the current timer variable is empty or has
        // a greater time value
        if self.timer.as_ref().map_or(true, |&(t, _, _)| t > time) {
            self.timer = Some((time, pos, index))
        }
    }
}

impl WorkerState for AltState {}

pub type AltWorker<'a> = Worker<'a, AltState>;

impl<'a> AltWorker<'a> {
    pub fn from(w: ReadyWorker<'a>, s: AltState) -> Self {
        w.change_state(s)
    }

    pub fn time(&self) -> Option<Time> {
        self.state.timer.as_ref().map(|&(t, _, _)| t)
    }

    pub fn channels(&self) -> Vec<ChanLabel> {
        self.state
            .channels
            .iter()
            .map(|&(c, _, _)| c)
            .collect()
    }

    pub fn chan_wake(mut self, ch: ChanLabel, v: StackVal) -> ReadyWorker<'a> {

        let goto = self.state
            .channels
            .iter()
            .find(|&&(c, _, _)| c == ch)
            .cloned();

        match goto {
            Some((_, j, mut vs)) => {
                self.program.goto(j);
                let mut stack = vec![v];
                vs.reverse();
                stack.append(&mut vs);
                ReadyWorker::from(self, stack)
            },
            None => panic!()
        }
    }

    pub fn time_wake(mut self, t: Time) -> ReadyWorker<'a> {

        if let Some((t2, pos, vs)) = self.state.timer.take() {
             if t >= t2 {
                self.program.goto(pos);
                ReadyWorker::from(self, vs)
            } else {
                panic!()
            }
        } else {
            panic!()
        }
    }
}
