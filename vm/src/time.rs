use std::cmp::Ordering;

use std::collections::BinaryHeap;

use vm::channel::AltToken;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Copy, Clone)]
pub struct Time(i32);

impl Time {
    pub fn new() -> Time {
        Time::from(0)
    }

    pub fn step(&mut self) {
        self.0 += 1
    }
}

impl From<i32> for Time {
    fn from(x: i32) -> Time {
        Time(x)
    }
}

#[derive(PartialEq, Eq, Debug)]
pub struct TimedAlt(pub Time, pub AltToken);

impl From<(Time, AltToken)> for TimedAlt {
    fn from((t, tok): (Time, AltToken)) -> TimedAlt {
        TimedAlt(t, tok)
    }
}

// We want a decreased time to have a higher priority
// so we reverse the ordering on the first element.
impl Ord for TimedAlt {
    fn cmp(&self, other: &TimedAlt) -> Ordering {
        match self.0.cmp(&other.0) {
            Ordering::Greater => Ordering::Less,
            Ordering::Less => Ordering::Greater,
            Ordering::Equal => self.1.cmp(&other.1),
        }
    }
}

impl PartialOrd for TimedAlt {
    fn partial_cmp(&self, other: &TimedAlt) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

#[derive(Debug)]
pub struct TimeWaiting(BinaryHeap<TimedAlt>);

impl TimeWaiting {
    pub fn new() -> TimeWaiting {
        TimeWaiting(BinaryHeap::new())
    }

    pub fn push(&mut self, alt: TimedAlt) {
        self.0.push(alt)
    }

    pub fn pop_ready(&mut self, current_time: Time) -> Vec<TimedAlt> {
        let mut ready_alts = Vec::new();
        loop {
            // If the heap is non-empty and the top (least time) value
            // is less than or equal to the current time then we take
            // the value and push it onto our vector. Otherwise we break
            // the loop
            let is_next_ready = self.0
                .peek()
                .map_or(false, |top_worker| top_worker.0 <= current_time);

            if is_next_ready {
                let timed_alt = self.0.pop().unwrap();
                ready_alts.push(timed_alt)
            } else {
                break;
            }
        }
        ready_alts
    }
}
