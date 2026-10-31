use std::fmt;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ErrorKind {
    // There is no MIR to read: rustc never borrow checks the body, or the crate is a
    // prebuilt sysroot library. A caller falls back to what it knows without the MIR.
    Unavailable,
    // There is MIR to read, but the driver did not record it or the MIR file is unreadable.
    // A caller treats this as a bug in the build.
    Internal,
}

// Why the recorded MIR of a body cannot be read.
#[derive(Clone, Debug)]
pub struct Error {
    pub kind: ErrorKind,
    pub reason: String,
}

impl Error {
    pub fn new(reason: impl Into<String>) -> Self {
        Self { kind: ErrorKind::Internal, reason: reason.into() }
    }

    pub fn unavailable(reason: impl Into<String>) -> Self {
        Self { kind: ErrorKind::Unavailable, reason: reason.into() }
    }

    pub fn is_unavailable(&self) -> bool {
        self.kind == ErrorKind::Unavailable
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.reason)
    }
}

impl std::error::Error for Error {}
