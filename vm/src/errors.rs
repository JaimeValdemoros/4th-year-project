
#[derive(Debug)]
pub enum MemoryError {
    FreeError,
    OutOfMemory,
    OutOfBoundsAccess,
}

#[derive(Debug)]
pub enum ProgramError {
    InvalidOpCode(u8),
    LiteralReadError,
    EndOfFile
}

#[derive(Debug)]
pub enum ChannelError {
    InvalidState,
    AltNotFound,
}

#[derive(Debug)]
pub enum FrameError {
    MemoryError(MemoryError),
    OutOfBoundsLocal,
    StackUnderflow(usize),
    StackOverflow,
}

#[derive(Debug)]
pub enum WorkerError {
    StackNotEmpty,
    DisallowedOp,
    ChannelError(ChannelError),
    ProgramError(ProgramError),
    FrameError(FrameError),
    MemoryError(MemoryError),
}


#[derive(Debug)]
pub enum VMError {
    MemoryError(MemoryError),
    ChannelError(ChannelError),
    WorkerError(WorkerError),
    ImproperEndState,
}

pub enum MainError {
    ParseArgError(::std::num::ParseIntError),
    FileError(::std::io::Error),
    VMError(VMError),
}


// Derive a from implementation two types.
// f is a function that converts from A to B -
// this is mainly useful if f is simple an
// enum constructor.
macro_rules! derive_from {
    ($A:ty => $B:ty ; $f:expr) => (
        impl From<$A> for $B {
            fn from(e: $A) -> Self {
                $f(e)
            }
        }
    );
}

derive_from!(MemoryError => FrameError ; FrameError::MemoryError);

derive_from!(ChannelError => WorkerError ; WorkerError::ChannelError);

derive_from!(ProgramError => WorkerError ; WorkerError::ProgramError);

derive_from!(FrameError => WorkerError ; WorkerError::FrameError);

derive_from!(MemoryError => WorkerError ; WorkerError::MemoryError);

derive_from!(MemoryError => VMError ; VMError::MemoryError);

derive_from!(ChannelError => VMError ; VMError::ChannelError);

derive_from!(WorkerError => VMError ; VMError::WorkerError);

derive_from!(VMError => MainError ; MainError::VMError);
