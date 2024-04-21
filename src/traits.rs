use std::fmt::{Error, Formatter};

pub trait PrettyPrint {
    fn pretty_print(&self, f: &mut Formatter<'_>, spaces: i32) -> Result<(), Error>;
}
