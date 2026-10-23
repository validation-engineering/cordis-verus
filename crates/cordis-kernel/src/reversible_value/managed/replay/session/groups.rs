//! Bootstrap services are grouped by the actual source setup ticket. Multiple
//! names exported by one source episode share one real target cleanup owner.
use crate::action_ledger::ActionTicket;
use crate::reversible_value::managed::replay::{self, batch::ProviderOwner, services::Preload};
use vstd::prelude::*;

verus! {
pub(crate) struct Plan<T:?Sized> {pub source_origin:ActionTicket,pub entries:Vec<Preload<T>>}
pub struct Group<E,T:?Sized> {
    pub plan:usize,
    pub id:usize,pub source_origin:ActionTicket,pub services:Vec<Preload<T>>,pub owner:ProviderOwner<T>,
    pub report:Result<replay::RegisteredReport<E,T>,replay::AdmissionError>,
}
}
