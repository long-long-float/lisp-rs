#[derive(Clone, PartialEq, Debug)]
pub struct UniqueGenerator(u32);

impl UniqueGenerator {
    pub fn new() -> Self {
        Self(0)
    }

    pub fn gen(&mut self) -> u32 {
        let id = self.0;
        self.0 += 1;
        id
    }

    pub fn gen_string(&mut self) -> String {
        format!("{}", self.gen())
    }
}
