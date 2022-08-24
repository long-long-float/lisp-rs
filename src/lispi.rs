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
