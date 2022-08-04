#[derive(PartialEq, Debug)]
pub enum Error {
    Io(String),
    Tokenize(String),
    Parse(String),
    Eval(String),
    Type(String),

    Bug {
        message: String,
        file: &'static str,
        line: u32,
    },

    // For non-local exists
    DoNothing,
}
