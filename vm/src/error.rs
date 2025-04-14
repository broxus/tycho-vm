use everscale_types::error::Error;

use crate::stack::StackValueType;

/// Result of VM-related stuff.
pub type VmResult<T> = Result<T, Box<VmError>>;

/// VM execution error.
#[derive(Debug, thiserror::Error)]
pub enum VmError {
    #[error("stack underflow at depth {0}")]
    StackUnderflow(usize),
    #[error("too many arguments copied into a closure continuation: {0}")]
    TooManyArguments(usize),
    #[error("expected integer in range {min}..={max}, found {actual}")]
    IntegerOutOfRange {
        min: isize,
        max: isize,
        actual: String,
    },
    #[error("control register index out of range: {0}")]
    ControlRegisterOutOfRange(usize),
    #[error("control register redefined")]
    ControlRegisterRedefined,
    #[error("integer overflow")]
    IntegerOverflow,
    #[error("invalid opcode")]
    InvalidOpcode,
    #[error("expected type {expected:?}, found {actual:?}")]
    InvalidType {
        expected: StackValueType,
        actual: StackValueType,
    },
    #[error("out of gas")]
    OutOfGas,
    #[error(transparent)]
    CellError(#[from] Error),
    #[error("dict error")]
    DictError,
    #[error("unknown error. {0}")]
    Unknown(String),
}

impl VmError {
    pub fn is_out_of_gas(&self) -> bool {
        matches!(self, Self::OutOfGas | Self::CellError(Error::Cancelled))
    }

    pub fn as_exception(&self) -> VmException {
        match self {
            Self::StackUnderflow(_) => VmException::StackUnderflow,
            Self::TooManyArguments(_) => VmException::StackOverflow,
            Self::IntegerOutOfRange { .. } => VmException::RangeCheck,
            Self::ControlRegisterOutOfRange(_) => VmException::RangeCheck,
            Self::ControlRegisterRedefined => VmException::TypeCheck,
            Self::IntegerOverflow => VmException::IntOverflow,
            Self::InvalidOpcode => VmException::InvalidOpcode,
            Self::InvalidType { .. } => VmException::TypeCheck,
            Self::OutOfGas => VmException::OutOfGas,
            Self::Unknown(_) => VmException::Unknown,
            Self::CellError(e) => match e {
                Error::CellUnderflow => VmException::CellUnderflow,
                Error::CellOverflow => VmException::CellOverflow,
                Error::UnexpectedExoticCell | Error::UnexpectedOrdinaryCell => {
                    VmException::VirtError
                }
                Error::Cancelled => VmException::OutOfGas, // ?
                Error::IntOverflow => VmException::IntOverflow,
                _ => VmException::Fatal, // ?
            },
            Self::DictError => VmException::DictError,
        }
    }
}

impl From<Error> for Box<VmError> {
    #[inline]
    fn from(e: Error) -> Self {
        Box::new(VmError::CellError(e))
    }
}

/// Opcode dump result.
#[cfg(feature = "dump")]
pub type DumpResult = Result<(), DumpError>;

/// Opcode dump error.
#[cfg(feature = "dump")]
#[derive(thiserror::Error, Debug)]
pub enum DumpError {
    #[error(transparent)]
    InvalidCode(#[from] everscale_types::error::Error),
    #[error("invalid opcode")]
    InvalidOpcode,
    #[error("unexpected cell")]
    CellMismatch,
    #[error(transparent)]
    WriterError(#[from] std::fmt::Error),
}

/// A code for an execution error.
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
#[repr(u8)]
pub enum VmException {
    Ok = 0,
    Alternative = 1,
    StackUnderflow = 2,
    StackOverflow = 3,
    IntOverflow = 4,
    RangeCheck = 5,
    InvalidOpcode = 6,
    TypeCheck = 7,
    CellOverflow = 8,
    CellUnderflow = 9,
    DictError = 10,
    Unknown = 11,
    Fatal = 12,
    OutOfGas = 13,
    VirtError = 14,
}

impl VmException {
    pub const fn as_exit_code(&self) -> i32 {
        !(*self as i32)
    }
}

impl std::fmt::Display for VmException {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::Ok => "normal termination",
            Self::Alternative => "alternative termination",
            Self::StackUnderflow => "stack underflow",
            Self::StackOverflow => "stack overflow",
            Self::IntOverflow => "integer overflow",
            Self::RangeCheck => "integer out of range",
            Self::InvalidOpcode => "invalid opcode",
            Self::TypeCheck => "type check error",
            Self::CellOverflow => "cell overflow",
            Self::CellUnderflow => "cell underflow",
            Self::DictError => "dictionary error",
            Self::Unknown => "unknown error",
            Self::Fatal => "fatal error",
            Self::OutOfGas => "out of gas",
            Self::VirtError => "virtualization error",
        })
    }
}
