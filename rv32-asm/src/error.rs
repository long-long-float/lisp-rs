use thiserror;

#[derive(PartialEq, Debug, Clone, thiserror::Error)]
pub enum Error {
    #[error("A label {0} is not defined.")]
    LabelNotDefined(String),

    #[error("Undefined variable: `{0}` at {1}")]
    UndefinedVariable(String, &'static str),

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
