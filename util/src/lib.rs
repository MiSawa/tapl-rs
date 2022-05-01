pub mod repl;

use anyhow::anyhow;
pub trait ResultExt<T> {
    fn staticalize(self) -> anyhow::Result<T>;
}
impl<T, E: std::fmt::Debug> ResultExt<T> for std::result::Result<T, E> {
    fn staticalize(self) -> anyhow::Result<T> {
        self.map_err(|e| anyhow!("{e:?}"))
    }
}
