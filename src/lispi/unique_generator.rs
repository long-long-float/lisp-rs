#[derive(Clone, PartialEq, Debug, Default)]
pub struct UniqueGenerator(u32);

impl UniqueGenerator {
    pub fn gen(&mut self) -> u32 {
        let id = self.0;
        self.0 += 1;
        id
    }

    pub fn gen_string(&mut self) -> String {
        format!("{}", self.gen())
    }
}
