use std::{error, fmt::Display};
use thiserror;

use super::{Location, LocationRange, TokenLocation};

#[derive(PartialEq, Debug, Clone, thiserror::Error)]
pub enum Error {
    #[error("IO error: {0}")]
    Io(String),
    #[error("Tokenize error: {0}")]
    Tokenize(String),
    #[error("Parse error: {0}")]
    Parse(String),
    #[error("Evaluation error: {0}")]
    Eval(String),
    #[error("Type error: {0}")]
    Type(String),

    #[error("Undefind variable: {0}")]
    UndefindVariable(String),

    #[error("Bug: {message:?} at {file:?}:{line:?}")]
    Bug {
        message: String,
        file: &'static str,
        line: u32,
    },

    // For non-local exists
    #[error("")]
    DoNothing,
}

impl Error {
    pub fn with_location(self, location: TokenLocation) -> ErrorWithLocation {
        ErrorWithLocation {
            err: self,
            location,
        }
    }

    pub fn with_single_location(self, loc: Location) -> ErrorWithLocation {
        let end = Location {
            line: loc.line,
            column: loc.column + 1,
        };
        self.with_location(TokenLocation::Range(LocationRange::new(loc, end)))
    }

    pub fn with_null_location(self) -> ErrorWithLocation {
        ErrorWithLocation {
            err: self,
            location: TokenLocation::Null,
        }
    }
}

#[derive(PartialEq, Debug, Clone)]
pub struct ErrorWithLocation {
    pub err: Error,
    pub location: TokenLocation,
}

impl Display for ErrorWithLocation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.err)
    }
}

impl error::Error for ErrorWithLocation {}
