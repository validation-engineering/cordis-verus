//! Construct a complete surviving Journal, including registration obligations.
//! This module is a transport combinator. The native adapter derives its edited
//! steps from the certified episode window; ordinary steps preserve source reads.
#[path = "joint_erasure_client.rs"]
pub mod client;
#[path = "joint_erasure_reads.rs"]
pub mod reads;
use super::Record;
#[cfg(verus_keep_ghost)]
use super::{Change, Frame, Step};
use vstd::prelude::*;
verus! {
broadcast use vstd::seq_lib::group_seq_properties;
pub open spec fn scalar_sources(source:Seq<Frame>)->bool {
    forall|i:int|0<=i<source.len() ==> match (#[trigger] source[i]).event.change {
        Change::Value {event:super::super::Event::Restore {inverse,origin,..}}=>
            origin<i && source[origin as int].event.key==source[i].event.key
                && super::forward(source[origin as int].event) && source[origin as int].event.change is Value
                && source[origin as int].event.change->Value_event.before()==inverse.before
                && source[origin as int].event.change->Value_event.after()==inverse.after
                && forall|k:int|0<=k<i ==> match (#[trigger] source[k]).event.change {
                    Change::Value {event:super::super::Event::Restore {origin:old,..}}=>old!=origin,_=>true,
                },
        _=>true,
    }
}
pub ghost struct Plan {pub mask:Seq<bool>,pub images:Seq<Record>}
impl Plan {
    pub open spec fn wf(self,source:Seq<Frame>)->bool {self.mask.len()==source.len() && self.images.len()==source.len()}
    pub open spec fn positions(self,n:nat)->Seq<nat> decreases n, {
        if n==0 {Seq::empty()} else {let before=self.positions((n-1) as nat);if self.mask[n-1] {before.push((n-1) as nat)} else {before}}
    }
    pub open spec fn rank(self,n:nat)->nat {self.positions(n).len()}
    pub open spec fn event(self,source:Seq<Frame>,i:nat)->Step {
        let e=source[i as int].event;
        Step {after:self.images[i as int],change:match e.change {Change::RegisterInverse {write}=>Change::RegisterInverse {write:self.rank(write)},
            Change::Value {event:super::super::Event::Restore {inverse,before,after,origin}}=>Change::Value {event:super::super::Event::Restore {inverse,before,after,origin:self.rank(origin)}},_=>e.change},
            settled:match e.settled {Some(write)=>Some(self.rank(write)),None=>None},..e}
    }
    pub open spec fn records(self,source:Seq<Frame>,n:nat)->Map<nat,Record> decreases n, {
        if n==0 {Map::empty()} else {let before=self.records(source,(n-1) as nat);
            if self.mask[n-1] {before.insert(source[n-1].event.key,self.images[n-1])} else {before}}
    }
    /// Keys are compressed event positions. The source map determines both
    /// presence and object identity, including still-unregistered forwards.
    pub open spec fn pending(self,source:Seq<Frame>,n:nat)->Map<nat,nat> {
        let pos=self.positions(n);let p=super::pending_at(source,n);
        Map::new(Seq::new(pos.len(),|k:int|k as nat).to_set().filter(|k:nat|p.contains_key(pos[k as int])),|k:nat|p[pos[k as int]])
    }
    #[verifier::opaque]
    pub open spec fn prefix(self,source:Seq<Frame>,n:nat)->Seq<Frame> decreases n, {
        if n==0 {Seq::empty()} else {let before=self.prefix(source,(n-1) as nat);if self.mask[n-1] {
            before.push(Frame {event:self.event(source,(n-1) as nat),state:self.records(source,n),pending:self.pending(source,n)})
        } else {before}}
    }
    pub open spec fn causes(self,source:Seq<Frame>)->bool {
        forall|i:int|0<=i<source.len() ==> {
            &&& self.mask[i] && source[i].event.change is RegisterInverse ==> self.mask[source[i].event.change->RegisterInverse_write as int]
            &&& source[i].event.settled.is_some() ==> self.mask[i]==self.mask[source[i].event.settled.unwrap() as int]
        }
    }
    pub open spec fn scalar_origin(self,source:Seq<Frame>,i:nat)->bool {
        let e=source[i as int].event;
        if let Change::Value {event:super::super::Event::Restore {inverse,origin,..}}=e.change {
            &&& origin<i && self.mask[origin as int]
            &&& source[origin as int].event.key==e.key && super::forward(source[origin as int].event)
            &&& source[origin as int].event.change is Value
            &&& source[origin as int].event.change->Value_event.before()==inverse.before
            &&& source[origin as int].event.change->Value_event.after()==inverse.after
            &&& forall|k:nat|k<i && self.mask[k as int] ==> match source[k as int].event.change {
                Change::Value {event:super::super::Event::Restore {origin:old,..}}=>old!=origin,
                _=>true,
            }
        } else {true}
    }
    pub proof fn positions_law(self,n:nat)
        requires n<=self.mask.len(),
        ensures forall|k:int|0<=k<self.positions(n).len() ==> self.positions(n)[k]<n && self.mask[self.positions(n)[k] as int]
                && self.rank(self.positions(n)[k])==k,
            forall|i:nat|i<n && self.mask[i as int] ==> self.rank(i)<self.rank(n) && self.positions(n)[self.rank(i) as int]==i,
        decreases n,
    {
        if n>0 {
            self.positions_law((n-1) as nat);let before=self.positions((n-1) as nat);let out=self.positions(n);
            assert forall|k:int|0<=k<out.len() implies out[k]<n && self.mask[out[k] as int] && self.rank(out[k])==k by {
                if k<before.len() {assert(out[k]==before[k]);} else {assert(k==before.len());}
            }
            assert forall|i:nat|i<n && self.mask[i as int] implies self.rank(i)<self.rank(n) && out[self.rank(i) as int]==i by {
                if i<n-1 {assert(out[self.rank(i) as int]==before[self.rank(i) as int]);}
            }
        }
    }
    pub proof fn pending_domain(self,source:Seq<Frame>,n:nat,k:nat)
        requires self.wf(source),n<=source.len(),
        ensures self.pending(source,n).contains_key(k)==(k<self.rank(n) && super::pending_at(source,n).contains_key(self.positions(n)[k as int])),
            self.pending(source,n).contains_key(k) ==> self.pending(source,n)[k]==super::pending_at(source,n)[self.positions(n)[k as int]],
    {
        let seq=Seq::new(self.rank(n),|i:int|i as nat);
        if k<seq.len() {assert(seq[k as int]==k);assert(seq.to_set().contains(k));}
        if seq.to_set().contains(k) {let i=choose|i:int|0<=i<seq.len() && seq[i]==k;assert(i==k);}
    }
    #[verifier::spinoff_prover]
    pub proof fn pending_edge(self,source:Seq<Frame>,i:nat)
        requires super::valid(source),self.wf(source),self.causes(source),i<source.len(),
        ensures self.mask[i as int] ==> super::pending_step(self.pending(source,i),self.pending(source,i+1),self.event(source,i),self.rank(i)),
            !self.mask[i as int] ==> self.pending(source,i+1)==self.pending(source,i),
    {
        let e=source[i as int].event;let a=super::pending_at(source,i);let b=super::pending_at(source,i+1);
        let x=self.pending(source,i);let y=self.pending(source,i+1);let p=self.positions(i);let q=self.positions(i+1);
        self.positions_law(i);self.positions_law(i+1);
        assert(super::step(super::state_at(source,i),source[i as int].state,e));
        assert(super::pending_step(a,b,e,i));
        if e.settled.is_some() {super::pending_recovery::settlement_source(source,e.settled.unwrap(),i);}
        assert forall|k:nat|#[trigger] y.contains_key(k) || x.contains_key(k) || k==self.rank(i) implies {
            &&& y.contains_key(k)==if e.pending && self.mask[i as int] {x.contains_key(k) || k==self.rank(i)}
                else if e.settled.is_some() && self.mask[i as int] {x.contains_key(k) && k!=self.rank(e.settled.unwrap())} else {x.contains_key(k)}
            &&& y.contains_key(k) ==> y[k]==if e.pending && self.mask[i as int] && k==self.rank(i) {e.key} else {x[k]}
        } by {
            self.pending_domain(source,i,k);self.pending_domain(source,i+1,k);
            if k<p.len() {
                assert(q[k as int]==p[k as int]);
                if e.settled.is_some() {
                    let w=e.settled.unwrap();
                    if self.mask[w as int] {assert(p[self.rank(w) as int]==w);}
                    if p[k as int]==w {assert(self.rank(w)==k);}
                    if self.mask[i as int] && self.rank(w)==k {assert(p[k as int]==w);}
                }
            } else if k<q.len() {assert(k==p.len());assert(q[k as int]==i);}
        }
        if self.mask[i as int] {
            self.pending_domain(source,i,self.rank(i));
            if e.pending {assert(y =~= x.insert(self.rank(i),e.key));}
            else if e.settled.is_some() {
                let w=e.settled.unwrap();self.pending_domain(source,i,self.rank(w));
                assert(y =~= x.remove(self.rank(w)));
            } else {assert(y =~= x);}
            assert(super::pending_step(x,y,self.event(source,i),self.rank(i)));
        } else {assert(y =~= x);}
    }
    /// A compressed registration must identify the same selected source write,
    /// which precedes the registration in the surviving prefix.
    pub proof fn registration_position(self,source:Seq<Frame>,i:nat)
        requires self.wf(source),i<source.len(),source[i as int].event.change is RegisterInverse,
            source[i as int].event.change->RegisterInverse_write<i,
            self.mask[source[i as int].event.change->RegisterInverse_write as int],
        ensures self.event(source,i).change is RegisterInverse,
            self.event(source,i).change->RegisterInverse_write<self.rank(i),
            self.positions(i)[self.event(source,i).change->RegisterInverse_write as int]==source[i as int].event.change->RegisterInverse_write,
    {
        self.positions_law(i);
        assert(self.event(source,i).change->RegisterInverse_write<self.rank(i)
            && self.positions(i)[self.event(source,i).change->RegisterInverse_write as int]==source[i as int].event.change->RegisterInverse_write);
    }
    /// Supplied only by the typed native-window transport. The public snapshot
    /// query does not accept this obligation or a successful target as input.
    pub open spec fn transported(self,source:Seq<Frame>)->bool {
        forall|i:nat|i<source.len() && self.mask[i as int] ==>
            super::step(self.records(source,i),self.records(source,i+1),self.event(source,i))
    }
    #[verifier::spinoff_prover]
    #[verifier::rlimit(30)]
    pub proof fn construct(self,source:Seq<Frame>,n:nat)
        requires super::valid(source),self.wf(source),self.causes(source),self.transported(source),n<=source.len(),
        ensures super::valid(self.prefix(source,n)),self.prefix(source,n).len()==self.rank(n),
            super::state_at(self.prefix(source,n),self.rank(n))==self.records(source,n),
            super::pending_at(self.prefix(source,n),self.rank(n))==self.pending(source,n),
            forall|k:int|0<=k<self.rank(n) ==> #[trigger] self.prefix(source,n)[k].event==self.event(source,self.positions(n)[k]),
        decreases n,
    {
        hide(super::valid);hide(super::step);hide(super::guard);
        reveal(Plan::prefix);
        if n==0 {assert(self.pending(source,n) =~= Map::empty());reveal(super::valid);}
        else {
            let i=(n-1) as nat;self.construct(source,i);self.pending_edge(source,i);self.positions_law(n);
            let before=self.prefix(source,i);let event=self.event(source,i);
            if self.mask[i as int] {
                assert(super::step(self.records(source,i),self.records(source,n),event));
                if event.change is RegisterInverse {
                    let w=source[i as int].event.change->RegisterInverse_write;
                    assert(super::caused(source.take(i as int),source[i as int].event)) by {reveal(super::valid);assert(super::step(super::state_at(source,i),source[i as int].state,source[i as int].event));}
                    self.positions_law(i);self.registration_position(source,i);
                    assert(before[self.rank(w) as int].event==self.event(source,w));
                    assert(super::forward(self.event(source,w)));
                }
                assert(super::caused(before,event));
                super::append(before,event,self.records(source,n),self.pending(source,n));
            }
            assert forall|k:int|0<=k<self.rank(n) implies #[trigger] self.prefix(source,n)[k].event==self.event(source,self.positions(n)[k]) by {
                if k<self.rank(i) {assert(self.positions(n)[k]==self.positions(i)[k]);}
                else {assert(k==self.rank(i));}
            }
        }
    }
    pub proof fn ordered(self,n:nat)
        requires n<=self.mask.len(),
        ensures forall|a:int,b:int|0<=a<b<self.rank(n) ==> self.positions(n)[a]<self.positions(n)[b],
        decreases n,
    {
        if n>0 {
            let i=(n-1) as nat;self.ordered(i);self.positions_law(i);
            assert forall|a:int,b:int|0<=a<b<self.rank(n) implies self.positions(n)[a]<self.positions(n)[b] by {
                if b<self.rank(i) {assert(self.positions(n)[a]==self.positions(i)[a]);assert(self.positions(n)[b]==self.positions(i)[b]);}
                else {assert(b==self.rank(i));assert(self.positions(n)[a]==self.positions(i)[a]);}
            }
        }
    }
    /// Scalar inverse origins are Journal positions too. Transport them with
    /// registration pointers, and preserve unique consumption of each origin.
    #[verifier::spinoff_prover]
    pub proof fn restoration_sources(self,source:Seq<Frame>)
        requires super::valid(source),self.wf(source),self.causes(source),self.transported(source),
            forall|i:nat|i<source.len() && self.mask[i as int] ==> self.scalar_origin(source,i),
        ensures scalar_sources(self.prefix(source,source.len())),
    {
        hide(super::valid);hide(super::step);self.construct(source,source.len());self.positions_law(source.len());self.ordered(source.len());
        let out=self.prefix(source,source.len());let pos=self.positions(source.len());
        assert forall|k:int|0<=k<out.len() implies match (#[trigger] out[k]).event.change {
            Change::Value {event:super::super::Event::Restore {inverse,origin,..}}=>
                origin<k && out[origin as int].event.key==out[k].event.key
                    && super::forward(out[origin as int].event) && out[origin as int].event.change is Value
                    && out[origin as int].event.change->Value_event.before()==inverse.before
                    && out[origin as int].event.change->Value_event.after()==inverse.after
                    && forall|t:int|0<=t<k ==> match (#[trigger] out[t]).event.change {
                        Change::Value {event:super::super::Event::Restore {origin:old,..}}=>old!=origin,_=>true,
                    },
            _=>true,
        } by {
            let i=pos[k];assert(self.scalar_origin(source,i));
            if let Change::Value {event:super::super::Event::Restore {origin:w,..}}=source[i as int].event.change {
                self.positions_law(i);assert(pos[self.rank(w) as int]==w);
                assert(out[self.rank(w) as int].event==self.event(source,w));
                assert forall|t:int|0<=t<k implies match (#[trigger] out[t]).event.change {
                    Change::Value {event:super::super::Event::Restore {origin:old,..}}=>old!=self.rank(w),_=>true,
                } by {
                    let j=pos[t];assert(j<i);assert(self.scalar_origin(source,j));
                    if let Change::Value {event:super::super::Event::Restore {origin:old,..}}=source[j as int].event.change {
                        assert(old!=w);assert(pos[self.rank(old) as int]==old);
                    }
                }
            }
        }
    }

}
}
