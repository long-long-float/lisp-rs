#[derive(Clone, PartialEq, Debug, Default)]
pub struct UniqueGenerator {
    prefix: String,
    count: u32,
}

impl UniqueGenerator {
    pub fn new(prefix: String) -> Self {
        Self { prefix, count: 0 }
    }

    pub fn gen(&mut self) -> u32 {
        let id = self.count;
        self.count += 1;
        id
    }

    pub fn gen_string(&mut self) -> String {
        format!("{}{}", self.prefix.clone(), self.gen())
    }
}
