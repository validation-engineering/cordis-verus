//! Executable allocation names, certified by the actual Journal allocation.
//! Equal local keys in different Journals are never treated as aliases.
use super::super::service_composition::Address;
use crate::identity_issuer::{Named, ValueIssuer};
use std::sync::Arc;
use vstd::prelude::*;
use vstd::resource::map::{GhostMapAuth, GhostPersistentPointsTo};

verus! {
exec static ALLOCATIONS:ValueIssuer<Option<Address>>=ValueIssuer::new();
pub(super) fn issuer()->(out:&'static ValueIssuer<Option<Address>>) {&ALLOCATIONS}
#[allow(dead_code)]
pub struct AllocationIdentity {
    name:Option<Named<Option<Address>>>,address:Ghost<Address>,
    allocation:Tracked<GhostPersistentPointsTo<nat,Option<u64>>>,
}
impl AllocationIdentity {
    pub closed spec fn address(&self)->Address {self.address@}
    pub closed spec fn number_spec(&self)->Option<u64> {match self.name {Some(n)=>Some(n.value()),None=>None}}
    pub open spec fn namespace(&self)->vstd::resource::Loc {self.address().journal.identity_namespace()}
    pub closed spec fn wf(&self)->bool {
        self.allocation@.id()==self.address().journal.inner.pred().names
            && self.allocation@.key()==self.address().key && self.allocation@.value()==self.number_spec()
            && (self.name.is_some() ==> self.name.unwrap().wf()
                && self.name.unwrap().source()==self.namespace() && self.name.unwrap().meaning()==Some(self.address()))
    }
    /// Exhaustion is explicit. No pointer casts, counter wrapping or guessed
    /// names enter the proof. Ordinary operations remain available on None.
    #[allow(clippy::manual_map)] // Explicit branches retain the erased receipt relation.
    pub fn number(&self)->(out:Option<u64>)
        requires self.wf(),ensures out==self.number_spec(),
    {match &self.name {Some(n)=>Some(n.get()),None=>None}}
    pub fn same(&self,other:&Self)->(out:Option<bool>)
        requires self.wf(),other.wf(),self.namespace()==other.namespace(),
        ensures out.is_some()==(self.number_spec().is_some() && other.number_spec().is_some()),
            out.is_some() ==> out.unwrap()==(self.address()==other.address()),
    {
        match (&self.name,&other.name) {
            (Some(a),Some(b))=>{
                proof {
                    if self.address()==other.address() {
                        let tracked mut point=self.allocation.borrow().duplicate();
                        point.intersection_agrees(other.allocation.borrow());
                    }
                    if a.value()==b.value() {a.agrees(b);}
                }
                Some(a.get()==b.get())
            },
            _=>None,
        }
    }
}
pub(super) fn allocate(issuer:&ValueIssuer<Option<Address>>,Ghost(address):Ghost<Address>,Tracked(names):Tracked<&mut GhostMapAuth<nat,Option<u64>>>)->(out:Arc<AllocationIdentity>)
    requires issuer.source()==address.journal.inner.pred().issuer,old(names).id()==address.journal.inner.pred().names,!old(names)@.contains_key(address.key),
    ensures out.wf(),out.address()==address,final(names).id()==old(names).id(),
        final(names)@==old(names)@.insert(address.key,out.number_spec()),
{
    let name=issuer.name(Ghost(Some(address))).ok();
    let ghost number=match &name {Some(n)=>Some(n.value()),None=>None};
    let tracked allocation=names.insert(address.key,number).persist();
    Arc::new(AllocationIdentity {name,address:Ghost(address),allocation:Tracked(allocation)})
}
}
