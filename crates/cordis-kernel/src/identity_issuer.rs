//! Concurrent identity issuance used by the native host. The runtime stores
//! one atomic counter; allocation permissions and progress witnesses erase.
//! Namespaces are independent: equal integers from different issuers need not
//! name the same object. Allocation identity is not Arc/Weak pointer identity.
use vstd::atomic_ghost::{AtomicInvariantPredicate, AtomicU64};
use vstd::prelude::*;
use vstd::resource::map::{GhostMapAuth, GhostPersistentPointsTo, GhostPointsTo};
use vstd::resource::Loc;

verus! {
#[allow(dead_code)] // Authority and progress state erase from the executable.
tracked struct State {
    issued:GhostMapAuth<u64,()>,
    progress:GhostMapAuth<u64,()>,
    frontier:GhostPersistentPointsTo<u64,()>,
}
struct Predicate;
impl AtomicInvariantPredicate<(Loc,Loc),u64,State> for Predicate {
    closed spec fn atomic_inv(source:(Loc,Loc),next:u64,state:State)->bool {
        &&& next>0
        &&& state.issued.id()==source.0 && state.progress.id()==source.1
        &&& forall|id:u64| #[trigger] state.issued@.contains_key(id) ==> 0<id<next
        &&& forall|id:u64| #[trigger] state.progress@.contains_key(id) ==> 0<id<=next
        &&& state.frontier.id()==source.1 && state.frontier.key()==next
    }
}

pub struct IdentityIssuer {next:AtomicU64<(Loc,Loc),State,Predicate>}
/// A non-cloneable permission for one successful allocation. Copying its u64
/// does not allocate another identity and gives no new allocation permission.
#[allow(dead_code)]
pub struct Identity {value:u64,point:Tracked<GhostPointsTo<u64,()>>}
#[allow(dead_code)]
pub struct Exhausted {witness:Tracked<GhostPersistentPointsTo<u64,()>>}
impl Identity {
    pub closed spec fn value(&self)->u64 {self.value}
    pub closed spec fn source(&self)->Loc {self.point@.id()}
    pub closed spec fn wf(&self)->bool {0<self.value<u64::MAX && self.point@.key()==self.value}
    pub fn get(&self)->(out:u64) ensures out==self.value(), {self.value}
    /// Two live allocation permissions in one namespace cannot alias. No
    /// assumption about a global host counter or pointer address is required.
    pub fn distinct_from(&mut self,other:&Self)->(out:bool)
        requires old(self).wf(),other.wf(),old(self).source()==other.source(),
        ensures out,final(self).value()!=other.value(),final(self).wf(),final(self).value()==old(self).value(),final(self).source()==old(self).source(),
    {proof {self.point.borrow_mut().disjoint(other.point.borrow());} self.value!=other.value}
}
impl Exhausted {
    pub closed spec fn source(&self)->Loc {self.witness@.id()}
    pub closed spec fn wf(&self)->bool {self.witness@.key()==u64::MAX}
}
impl IdentityIssuer {
    pub closed spec fn source(&self)->Loc {self.next.constant().0}
    pub closed spec fn progress_source(&self)->Loc {self.next.constant().1}
    #[verifier::type_invariant]
    closed spec fn wf(&self)->bool {self.next.well_formed()}

    /// Start a fresh independent namespace. MAX is the exhausted sentinel and
    /// is never issued; zero is reserved by the host.
    pub const fn new()->(out:Self) {Self::from_nonzero(1)}
    /// A bounded tail is useful for embeddings and exhaustion acceptance. This
    /// creates a separate namespace; it does not resume an existing issuer.
    pub const fn starting_at(first:u64)->(out:Option<Self>)
        ensures out.is_some()==(first>0),
    {if first==0 {None} else {Some(Self::from_nonzero(first))}}
    const fn from_nonzero(first:u64)->(out:Self)
        requires first>0,
    {
        let tracked (issued,_)=GhostMapAuth::new(Map::<u64,()>::empty());
        let tracked (mut progress,_)=GhostMapAuth::new(Map::<u64,()>::empty());
        let tracked frontier=progress.insert(first,()).persist();
        let ghost source=(issued.id(),progress.id());
        proof {
            assert forall|id:u64| #[trigger] progress@.contains_key(id) implies 0<id<=first by {
                assert(id==first);
            }
        }
        Self {next:AtomicU64::new(Ghost(source),first,Tracked(State {issued,progress,frontier}))}
    }
    /// Strong CAS retries consume a strictly increasing observation, so the
    /// loop has a finite numeric variant. This does not prove scheduler fairness.
    pub fn issue(&self)->(out:Result<Identity,Exhausted>)
        ensures out.is_ok() ==> out->Ok_0.wf() && out->Ok_0.source()==self.source(),
            out.is_err() ==> out->Err_0.wf() && out->Err_0.source()==self.progress_source(),
    {
        proof {use_type_invariant(self);}
        let tracked mut observed:Option<GhostPersistentPointsTo<u64,()>>=None;
        let mut next=vstd::atomic_with_ghost!(&self.next => load(); returning value; ghost state => {
            observed=Some(state.frontier.duplicate());
        });
        loop
            invariant self.wf(),next>0,observed.is_some(),
                observed.unwrap().id()==self.progress_source(),observed.unwrap().key()==next,
            decreases u64::MAX-next,
        {
            if next==u64::MAX {return Err(Exhausted {witness:Tracked(observed.tracked_unwrap())});}
            let tracked mut issued:Option<GhostPointsTo<u64,()>>=None;
            let result=vstd::atomic_with_ghost!(&self.next => compare_exchange(next,next+1);
                update before -> after; returning result; ghost state => {
                observed.tracked_borrow().agree(&state.progress);
                assert(before>=next);
                if result.is_ok() {
                    issued=Some(state.issued.insert(next,()));
                    state.frontier=state.progress.insert((next+1) as u64,()).persist();
                }
                observed=Some(state.frontier.duplicate());
            });
            match result {
                Ok(_)=>return Ok(Identity {value:next,point:Tracked(issued.tracked_unwrap())}),
                Err(current)=>{next=current;},
            }
        }
    }
    /// A real later load confirms that exhaustion is permanent in this issuer.
    pub fn remains_exhausted(&self,_earlier:&Exhausted)->(out:bool)
        requires _earlier.wf(),_earlier.source()==self.progress_source(),
        ensures out,
    {
        proof {use_type_invariant(self);}
        let value=vstd::atomic_with_ghost!(&self.next => load(); ghost state => {
            _earlier.witness.borrow().agree(&state.progress);
        });
        value==u64::MAX
    }
}
impl Default for IdentityIssuer {fn default()->Self {Self::new()}}
} // verus!
