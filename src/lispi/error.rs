#[derive(Debug)]
pub enum Error {
    Io(String),
    Tokenize(String),
    Parse(String),
    Eval(String),
}
