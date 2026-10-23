//! Complete Journal transport derived from a certified native episode window.
//! A source-selected effect mask is admitted by read continuity and causal
//! closure, never by assuming that a target primitive or callback succeeds.
use super::super::Snapshot;
use super::trace::{Issue as NativeIssue, Window};
use crate::reversible_value::joint::Frame;
#[cfg(verus_keep_ghost)]
use crate::reversible_value::joint::{
    self as j,
    erasure::{reads, Plan},
    Change, Record,
};
use vstd::prelude::*;
verus! {
broadcast use vstd::seq_lib::group_seq_properties;
pub ghost struct Selection<V> {pub source:Snapshot<V>,pub window:Window,pub effects:Seq<bool>}
pub ghost enum Issue {Window {issue:NativeIssue},MaskLength,Local {at:nat},Read {at:nat},Reference {at:nat},Cause {at:nat}}
impl<V> Selection<V> {
    pub open spec fn frames(self)->Seq<Frame> {self.source.joint_spec().events()}
    pub open spec fn kept(self,i:int)->bool {
        let e=self.frames()[i].event;
        if e.key!=self.source.key() {self.effects[i]}
        else if e.change==Change::Allocate {true}
        else {let k=e.after->Native_state.revision as int-1;self.window.keep(k,self.source.history().labels[k])}
    }
    pub open spec fn image(self,i:int)->Record {
        let e=self.frames()[i].event;
        if e.key!=self.source.key() {e.after} else {
            let k=e.after->Native_state.revision;
            Record::Native {state:self.window.at(self.source.history(),k as int).project(self.window.positions(self.source.history(),k).len())}
        }
    }
    pub open spec fn plan(self)->Plan {Plan {
        mask:Seq::new(self.frames().len(),|i:int|self.kept(i)),images:Seq::new(self.frames().len(),|i:int|self.image(i))}}
    pub open spec fn local(self,i:nat)->bool {
        let e=self.frames()[i as int].event;
        e.key==self.source.key() || !self.kept(i as int) || e.change==Change::Allocate
            || reads::get(self.plan().records(self.frames(),i),e.key)==reads::get(j::state_at(self.frames(),i),e.key)
    }
    pub open spec fn read(self,i:nat)->bool {
        let e=self.frames()[i as int].event;let before=j::state_at(self.frames(),i);
        e.key==self.source.key() || !self.kept(i as int) || e.change==Change::Allocate
            || reads::same(before,self.plan().records(self.frames(),i),before[e.key],e.change)
    }
    pub open spec fn reference(self,i:nat)->bool {
        let e=self.frames()[i as int].event;
        !self.kept(i as int) || !(e.after is Slot) || e.after->Slot_object.domain!=self.source.joint_spec().domain()
            || reads::get(j::state_at(self.frames(),i),e.after->Slot_object.key)
                ==reads::get(self.plan().records(self.frames(),i),e.after->Slot_object.key)
    }
    pub open spec fn cause(self,i:nat)->bool {
        let e=self.frames()[i as int].event;
        &&& self.kept(i as int) ==> self.plan().scalar_origin(self.frames(),i)
        &&& self.kept(i as int) && e.change is RegisterInverse ==> self.kept(e.change->RegisterInverse_write as int)
        &&& e.settled.is_some() ==> self.kept(i as int)==self.kept(e.settled.unwrap() as int)
    }
    pub open spec fn admissible(self)->bool {
        &&& self.effects.len()==self.frames().len()
        &&& self.window.admissible(self.source.history())
        &&& forall|i:nat|i<self.frames().len() ==> self.local(i) && self.read(i) && self.reference(i) && self.cause(i)
    }
    pub open spec fn diagnosed(self,issue:Issue)->bool {
        match issue {
            Issue::Window {issue}=>self.window.diagnosed(self.source.history(),issue),
            Issue::MaskLength=>self.effects.len()!=self.frames().len(),
            Issue::Local {at}=>at<self.frames().len() && !self.local(at),
            Issue::Read {at}=>at<self.frames().len() && !self.read(at),
            Issue::Reference {at}=>at<self.frames().len() && !self.reference(at),
            Issue::Cause {at}=>at<self.frames().len() && !self.cause(at),
        }
    }
    pub proof fn check(self)->(out:Option<Issue>)
        requires self.source.certified(),
        ensures out.is_none()==self.admissible(),out.is_some() ==> self.diagnosed(out.unwrap()),
    {
        self.source.valid_history();
        if let Some(issue)=self.window.check(self.source.history()) {return Some(Issue::Window {issue});}
        if self.effects.len()!=self.frames().len() {return Some(Issue::MaskLength);}
        if exists|i:nat|i<self.frames().len() && !self.local(i) {
            let at=choose|i:nat|i<self.frames().len() && !self.local(i);return Some(Issue::Local {at});
        }
        if exists|i:nat|i<self.frames().len() && !self.read(i) {
            let at=choose|i:nat|i<self.frames().len() && !self.read(i);return Some(Issue::Read {at});
        }
        if exists|i:nat|i<self.frames().len() && !self.reference(i) {
            let at=choose|i:nat|i<self.frames().len() && !self.reference(i);return Some(Issue::Reference {at});
        }
        if exists|i:nat|i<self.frames().len() && !self.cause(i) {
            let at=choose|i:nat|i<self.frames().len() && !self.cause(i);return Some(Issue::Cause {at});
        }
        assert(self.admissible());None
    }
    /// The native image is fixed by the actual source revision. It is not an
    /// arbitrary replacement supplied by the caller of this query.
    pub open spec fn native_at(self,n:nat)->Option<Record> {
        let a=j::state_at(self.frames(),n);let key=self.source.key();
        if a.contains_key(key) {let k=a[key]->Native_state.revision;
            Some(Record::Native {state:self.window.at(self.source.history(),k as int).project(self.window.positions(self.source.history(),k).len())})
        } else {None}
    }
    #[verifier::spinoff_prover]
    pub proof fn native_edge(self,i:nat)
        requires self.source.certified(),self.window.admissible(self.source.history()),i<self.frames().len(),
        ensures !self.kept(i as int) || self.frames()[i as int].event.key!=self.source.key() ==>
                self.native_at(i+1)==self.native_at(i),
            self.frames()[i as int].event.key==self.source.key() && self.kept(i as int) ==>
                self.native_at(i+1)==Some(self.image(i as int)) &&
                (self.frames()[i as int].event.change==Change::Allocate ==> self.native_at(i).is_none()) &&
                (self.frames()[i as int].event.change!=Change::Allocate ==> self.native_at(i).is_some()
                    && j::changes(self.native_at(i).unwrap(),self.image(i as int),self.frames()[i as int].event.change)),
    {
        hide(j::valid);hide(j::references::history);
        self.source.valid_history();self.source.joint_spec().valid_history();
        let s=self.frames();let e=s[i as int].event;let key=self.source.key();let h=self.source.history();
        assert(j::step(j::state_at(s,i),s[i as int].state,e)) by {reveal(j::valid);}
        if e.key==key {
            let k=self.source.complete_at(i);
            assert(e.after==(Record::Native {state:h.states[k].project(k as nat)}));
            if k>0 {
                assert(j::native::recorded(s,i,key)) by {reveal(j::changes);}
                j::native::edge(s,i,key);let before=self.source.recovery_index(i);
                reveal(j::native::step);assert(before==k-1);
                self.window.edge(h,k-1);
                if self.kept(i as int) {
                    super::super::project_step(self.window.at(h,k-1),self.window.at(h,k),h.labels[k-1].0,h.labels[k-1].1,self.window.positions(h,(k-1) as nat).len());
                    assert(self.window.positions(h,k as nat).len()==self.window.positions(h,(k-1) as nat).len()+1);
                    assert(j::changes(self.native_at(i).unwrap(),self.image(i as int),e.change)) by {reveal(j::changes);}
                }
            }
        }
    }
    #[verifier::spinoff_prover]
    pub proof fn native_prefix(self,n:nat)
        requires self.source.certified(),self.window.admissible(self.source.history()),n<=self.frames().len(),
        ensures reads::get(self.plan().records(self.frames(),n),self.source.key())==self.native_at(n),
        decreases n,
    {
        if n>0 {let i=(n-1) as nat;self.native_prefix(i);self.native_edge(i);}
    }
    /// Allocations are unique in the source, so retaining a subsequence cannot
    /// turn an allocation into a write over an existing retained record.
    pub proof fn record_source(self,n:nat,key:nat)
        requires self.source.certified(),n<=self.frames().len(),self.plan().records(self.frames(),n).contains_key(key),
        ensures j::state_at(self.frames(),n).contains_key(key),
        decreases n,
    {
        self.source.joint_spec().valid_history();assert(n>0);let i=(n-1) as nat;
        assert(j::step(j::state_at(self.frames(),i),self.frames()[i as int].state,self.frames()[i as int].event));
        if !self.kept(i as int) || self.frames()[i as int].event.key!=key {self.record_source(i,key);}
    }
    #[verifier::spinoff_prover]
    pub proof fn edge(self,i:nat)
        requires self.source.certified(),self.admissible(),i<self.frames().len(),self.kept(i as int),
        ensures j::step(self.plan().records(self.frames(),i),self.plan().records(self.frames(),i+1),self.plan().event(self.frames(),i)),
            j::references::linked(self.plan().records(self.frames(),i),self.image(i as int),self.source.joint_spec().domain()),
    {
        hide(j::valid);hide(j::references::history);
        self.source.valid_history();self.source.joint_spec().valid_history();
        let s=self.frames();let p=self.plan();let a=j::state_at(s,i);let b=p.records(s,i);let e=s[i as int].event;
        assert(j::step(a,s[i as int].state,e)) by {reveal(j::valid);}
        assert(j::references::linked(a,e.after,self.source.joint_spec().domain())) by {reveal(j::references::history);}
        assert(self.local(i));assert(self.read(i));assert(self.reference(i));
        if e.change==Change::Allocate {
            if b.contains_key(e.key) {self.record_source(i,e.key);}
        } else if e.key==self.source.key() {
            self.native_prefix(i);self.native_edge(i);
            reveal(j::groups::guard);
            assert(e.change is Native) by {let k=self.source.complete_at(i);}
        } else {
            assert(b.contains_pair(e.key,a[e.key]));
            reads::transport(a,b,a[e.key],e.change);
            if let Change::Value {event:crate::reversible_value::Event::Restore {inverse,before,after,origin}}=e.change {
                reads::scalar_restore(a[e.key],e.after,inverse,before,after,origin,p.rank(origin));reveal(j::groups::guard);
            }
            if let Change::RegisterInverse {write}=e.change {
                reads::registration(a[e.key],e.after,write,p.rank(write));reveal(j::groups::guard);
            }
        }
        assert(j::step(b,p.records(s,i+1),p.event(s,i)));
        assert(j::references::linked(b,self.image(i as int),self.source.joint_spec().domain()));
    }
    pub proof fn cause_closure(self)
        requires self.source.certified(),self.admissible(),ensures self.plan().causes(self.frames()),
    {
        self.source.joint_spec().valid_history();let p=self.plan();let s=self.frames();
        assert forall|i:int|0<=i<s.len() implies {
            &&& p.mask[i] && s[i].event.change is RegisterInverse ==> p.mask[s[i].event.change->RegisterInverse_write as int]
            &&& s[i].event.settled.is_some() ==> p.mask[i]==p.mask[s[i].event.settled.unwrap() as int]
        } by {
            assert(self.cause(i as nat));
            assert(j::step(j::state_at(s,i as nat),s[i].state,s[i].event));
            assert(j::caused(s.take(i),s[i].event));
            if s[i].event.settled.is_some() {j::pending_recovery::settlement_source(s,s[i].event.settled.unwrap(),i as nat);}
        }
    }
    #[verifier::spinoff_prover]
    pub proof fn construct(self)->(out:Seq<Frame>)
        requires self.source.certified(),self.admissible(),
        ensures out==self.plan().prefix(self.frames(),self.frames().len()),j::valid(out),
            j::references::history(out,self.source.joint_spec().domain()),j::erasure::scalar_sources(out),j::classification::history(out),
            j::state_at(out,out.len())==self.plan().records(self.frames(),self.frames().len()),
            j::pending_at(out,out.len())==self.plan().pending(self.frames(),self.frames().len()),
            out.len()==self.plan().rank(self.frames().len()),
            forall|k:int|0<=k<out.len() ==> out[k].event==self.plan().event(self.frames(),self.plan().positions(self.frames().len())[k]),
    {
        hide(j::valid);hide(j::step);hide(j::references::history);
        self.source.joint_spec().valid_history();let s=self.frames();let p=self.plan();
        self.cause_closure();
        assert(p.transported(s)) by {assert forall|i:nat|i<s.len() && p.mask[i as int] implies
            j::step(p.records(s,i),p.records(s,i+1),p.event(s,i)) by {self.edge(i);}}
        p.construct(s,s.len());let out=p.prefix(s,s.len());
        self.reference_prefix(s.len());
        assert forall|i:nat|i<s.len() && p.mask[i as int] implies p.scalar_origin(s,i) by {assert(self.cause(i));}
        p.restoration_sources(s);j::classification::classify_history(out);out
    }
    /// Counterfactual native revisions count retained native commits. The exact
    /// final control, owner and publication observation is the source endpoint.
    pub proof fn endpoint(self)
        requires self.source.certified(),self.admissible(),
        ensures self.plan().records(self.frames(),self.frames().len()).contains_pair(self.source.key(),
            Record::Native {state:self.source.history().states.last().project(self.window.positions(self.source.history(),self.source.history().labels.len()).len())}),
    {
        self.source.valid_history();let h=self.source.history();self.native_prefix(self.frames().len());
        if self.window.end==h.labels.len() {super::boundary_identity(h.states.last(),self.window.region);}
    }
    pub proof fn reference_prefix(self,n:nat)
        requires self.source.certified(),self.admissible(),n<=self.frames().len(),self.plan().transported(self.frames()),self.plan().causes(self.frames()),
        ensures j::references::history(self.plan().prefix(self.frames(),n),self.source.joint_spec().domain()),
        decreases n,
    {
        hide(j::valid);hide(j::step);hide(j::references::history);reveal(Plan::prefix);
        if n>0 {
            let i=(n-1) as nat;self.reference_prefix(i);
            if self.kept(i as int) {
                self.edge(i);let p=self.plan();let s=self.frames();
                self.source.joint_spec().valid_history();p.construct(s,i);
                j::references::append(p.prefix(s,i),Frame {event:p.event(s,i),state:p.records(s,n),pending:p.pending(s,n)},self.source.joint_spec().domain());
            }
        } else {reveal(j::references::history);}
    }
}
/// The only runtime field is the actual read-only snapshot. Historical effects,
/// masks and the constructed counterfactual remain erased.
pub struct Capture<V> {pub cut:Snapshot<V>,pub window:Ghost<Window>,pub effects:Ghost<Seq<bool>>,pub result:Ghost<Result<Seq<Frame>,Issue>>}
impl<V> Capture<V> {
    pub open spec fn selection(&self)->Selection<V> {Selection {source:self.cut,window:self.window@,effects:self.effects@}}
    pub open spec fn certified(&self)->bool {
        self.cut.certified() && self.result@.is_ok()==self.selection().admissible()
            && (self.result@.is_ok() ==> self.result@->Ok_0==self.selection().plan().prefix(self.selection().frames(),self.selection().frames().len())
                && j::valid(self.result@->Ok_0) && j::erasure::scalar_sources(self.result@->Ok_0) && j::classification::history(self.result@->Ok_0) && j::references::history(self.result@->Ok_0,self.cut.joint_spec().domain()))
            && (self.result@.is_err() ==> self.selection().diagnosed(self.result@->Err_0))
    }
}
impl<V> Snapshot<V> {
    /// Consume the same captured cut; no second read or runtime history buffer.
    pub fn with_effect_deletion(self,Ghost(window):Ghost<Window>,Ghost(effects):Ghost<Seq<bool>>)->(out:Capture<V>)
        requires self.certified(),
        ensures out.certified(),out.cut==self,out.window@==window,out.effects@==effects,
    {
        let ghost result=self.delete_effect_window(window,effects);
        Capture {cut:self,window:Ghost(window),effects:Ghost(effects),result:Ghost(result)}
    }

    pub proof fn delete_effect_window(&self,window:Window,effects:Seq<bool>)->(out:Result<Seq<Frame>,Issue>)
        requires self.certified(),
        ensures {
            let selection=Selection {source:*self,window,effects};
            &&& out.is_ok()==selection.admissible()
            &&& out.is_ok() ==> out->Ok_0==selection.plan().prefix(selection.frames(),selection.frames().len())
                && j::valid(out->Ok_0) && j::erasure::scalar_sources(out->Ok_0) && j::classification::history(out->Ok_0) && j::references::history(out->Ok_0,self.joint_spec().domain())
            &&& out.is_err() ==> selection.diagnosed(out->Err_0)
        },
    {
        let selection=Selection {source:*self,window,effects};
        match selection.check() {Some(issue)=>Err(issue),None=>Ok(selection.construct())}
    }
}
}
