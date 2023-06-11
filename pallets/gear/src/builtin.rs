
use core_processor::common::JournalNote;
use gear_core::message::StoredDispatch;

pub enum BuiltinExecution {
    Handled(Vec<JournalNote>),
    NoMatch(StoredDispatch),
}

pub trait BuiltinHandler {
    fn handle(dispatch: StoredDispatch) -> BuiltinExecution;
}

impl BuiltinHandler for () {
    fn handle(dispatch: StoredDispatch) -> BuiltinExecution {
        BuiltinExecution::NoMatch(dispatch)
    }
}
