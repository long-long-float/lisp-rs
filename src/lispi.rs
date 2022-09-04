pub mod error;
pub mod evaluator;
pub mod parser;
pub mod tokenizer;

#[derive(Clone, Debug)]
pub struct SymbolValue {
    pub value: String,
    pub id: u32,
}

impl PartialEq for SymbolValue {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value
    }
}

impl SymbolValue {
    pub fn empty() -> SymbolValue {
        SymbolValue {
            value: "".to_string(),
            id: 0,
        }
    }

    pub fn without_id(value: String) -> SymbolValue {
        SymbolValue { value, id: 0 }
    }
}

/// A location in file
#[derive(Clone, Copy, PartialEq, Debug)]
pub struct Location {
    /// zero-based line no
    pub line: usize,
    /// zero-based column no
    pub column: usize,
}

impl Location {
    fn head() -> Location {
        Location { line: 0, column: 0 }
    }

    fn newline(self: &mut Self) {
        self.line += 1;
        self.column = 0;
    }

    pub fn humanize(self) -> Location {
        Location {
            line: self.line + 1,
            column: self.column + 1,
        }
    }
}

impl std::fmt::Display for Location {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}:{}", self.line + 1, self.column + 1)
    }
}

#[derive(Clone, Copy, PartialEq, Debug)]
pub enum TokenLocation {
    Range(LocationRange),
    EOF,
    Null,
}

impl std::fmt::Display for TokenLocation {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            TokenLocation::Range(range) => write!(f, "{}", range),
            TokenLocation::Null => write!(f, "NULL"),
            TokenLocation::EOF => write!(f, "EOF"),
        }
    }
}

/// A range in file, `[begin, end)`.
#[derive(Clone, Copy, PartialEq, Debug)]
pub struct LocationRange {
    pub begin: Location,
    pub end: Location,
}

impl LocationRange {
    fn new(begin: Location, end: Location) -> LocationRange {
        LocationRange { begin, end }
    }
}

impl std::fmt::Display for LocationRange {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{} - {}", self.begin, self.end)
    }
}
