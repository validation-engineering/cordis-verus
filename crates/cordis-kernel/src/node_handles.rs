//! The actual Node handle-delivery queue. Retirement and filtering are checked
//! in the same owner as the real publication payloads. JS deletion stays external.
use super::*;
#[cfg(verus_keep_ghost)]
use vstd::seq_lib::*;

verus! {
pub open spec fn held(store:PublicationStore<u64>,value:u64)->bool {
    exists|i:int|0<=i<store.values().len() && store.values()[i]==Some(value)
}
pub open spec fn unheld(store:PublicationStore<u64>)->spec_fn(u64)->bool {|value:u64|!held(store,value)}
pub open spec fn values(items:Seq<ReleasedValue<u64>>)->Seq<u64> {items.map(|i:int,item:ReleasedValue<u64>|item.value)}
pub open spec fn added(event:Event)->Seq<u64> {
    match event {
        Event::Replace {value,out:Ok(previous),..}=>if previous!=value {seq![previous]} else {Seq::empty()},
        Event::Reclaim {out:Ok(value),..}=>seq![value],
        Event::Release {out:Ok(items),..}|Event::ReleaseReservation {out:Ok(items),..}=>values(items@),
        _=>Seq::empty(),
    }
}
pub open spec fn step(a:Observation,b:Observation,event:Event)->bool {
    match event {
        Event::DrainReleased {out}=>b.released.len()==0 && out==a.released.filter(unheld(a.store)),
        _=>b.released==a.released+added(event),
    }
}
impl NodeRuntime {
    pub(super) fn queue_released(&mut self,items:&[ReleasedValue<u64>])
        ensures final(self).observation()==(Observation {released:old(self).released@+values(items@),..old(self).observation()}),
            final(self).history()==old(self).history(),
    {
        let ghost before=self.observation();let mut i=0;
        while i<items.len()
            invariant i<=items.len(),self.observation()==(Observation {released:before.released+values(items@.take(i as int)),..before}),
                self.history()==old(self).history(),
            decreases items.len()-i,
        {
            self.released.push(items[i].value);
            proof {assert(values(items@.take(i as int+1))==values(items@.take(i as int)).push(items[i as int].value));}
            i+=1;
        }
        proof {assert(items@.take(i as int)==items@);}
    }
    /// Take one completed native delivery batch. All candidates are consumed;
    /// any value still retained by another slot is excluded. Later retirement of
    /// that slot will enqueue its own candidate. Order and multiplicity persist.
    pub fn drain_released(&mut self)->(out:Vec<u64>)
        requires old(self).wf(),
        ensures final(self).wf(),
            out@==old(self).observation().released.filter(unheld(old(self).observation().store)),
            final(self).observation()==(Observation {released:Seq::empty(),..old(self).observation()}),
            final(self).history()==old(self).history().append(final(self).observation(),Event::DrainReleased {out:out@}),
            forall|value:u64|out@.contains(value) ==> !held(old(self).observation().store,value),
    {
        let ghost before=self.observation();let mut pending=Vec::new();
        core::mem::swap(&mut pending,&mut self.released);
        let mut out:Vec<u64>=Vec::new();let mut i=0;
        while i<pending.len()
            invariant i<=pending.len(),pending@==before.released,
                self.observation()==(Observation {released:Seq::empty(),..before}),
                self.history()==old(self).history(),before==old(self).observation(),old(self).wf(),
                out@==pending@.take(i as int).filter(unheld(before.store)),
            decreases pending.len()-i,
        {
            let value=pending[i];
            if !self.store.contains_handle(value) {out.push(value);}
            proof {
                assert(pending@.take(i as int+1)==pending@.take(i as int).push(value));
                pending@.take(i as int).lemma_filter_push(value,unheld(before.store));
            }
            i+=1;
        }
        proof {
            assert(pending@.take(i as int)==pending@);
            assert forall|value:u64|out@.contains(value) implies !held(before.store,value) by {
                pending@.lemma_filter_contains_rev(unheld(before.store),value);
            }
            self.scopes.unchanged_reflexive();reveal(history::operation);
            self.record(before,Event::DrainReleased {out:out@});
        }
        out
    }
}
/// Every newly queued value was the actual payload of a slot consumed or
/// replaced by this very operation. A second slot may still retain the value.
pub proof fn added_has_source(a:Observation,b:Observation,event:Event,value:u64)
    requires history::step(a,b,event),added(event).contains(value),
    ensures exists|slot:int|0<=slot<a.store.values().len() && slot<b.store.values().len()
        && a.store.values()[slot]==Some(value) && b.store.values()[slot]!=Some(value),
{
    reveal(history::operation);
    match event {
        Event::Replace {id,..}|Event::Reclaim {id,..}=>{
            assert(a.store.values()[id.0 as int]==Some(value));
            assert(b.store.values()[id.0 as int]!=Some(value));
        },
        Event::Release {publications,out:Ok(items),..}|Event::ReleaseReservation {publications,out:Ok(items),..}=>{
            let j=choose|j:int|0<=j<values(items@).len() && values(items@)[j]==value;
            let slot=publications[j].0 as int;
            assert(items[j].value==value);assert(publications.contains(publications[j]));
            assert(a.store.values()[slot]==Some(value));assert(b.store.values()[slot].is_none());
        },
        _=>{},
    }
}
/// No successful last-reference removal is omitted from the real queue.
pub proof fn removed_is_queued(a:Observation,b:Observation,event:Event,slot:int,value:u64)
    requires history::step(a,b,event),0<=slot<a.store.values().len(),slot<b.store.values().len(),
        a.store.values()[slot]==Some(value),b.store.values()[slot]!=Some(value),
    ensures b.released.contains(value),
{
    reveal(history::operation);a.store.slot_count();
    if b.store.same(&a.store) {b.store.same_observations(&a.store);}
    match event {
        Event::Replace {id,value:replacement,out,..}=>{
            assert(out.is_ok());assert(id.0==slot);assert(out->Ok_0==value);assert(replacement!=value);
            assert(added(event).len()==1);assert(added(event)[0]==value);assert(added(event).contains(value));
        },
        Event::Reclaim {id,out}=>{
            assert(out.is_ok());assert(id.0==slot);assert(out->Ok_0==value);assert(added(event).len()==1);assert(added(event)[0]==value);assert(added(event).contains(value));
        },
        Event::Release {publications,out:Ok(items),..}|Event::ReleaseReservation {publications,out:Ok(items),..}=>{
            let id=PublicationId(slot as usize);assert(publications.contains(id));
            let j=choose|j:int|0<=j<publications.len() && publications[j]==id;
            assert(items[j].value==value);assert(values(items@)[j]==value);assert(values(items@).contains(value));assert(added(event).contains(value));
        },
        _=>{assert(false);},
    }
    assert(added(event).contains(value));
    let j=choose|j:int|0<=j<added(event).len() && added(event)[j]==value;
    assert(b.released[a.released.len()+j]==value);
}
impl History {
    pub open spec fn payload_written_at(&self,index:int,slot:int,value:u64)->bool {
        0<=index<self.events.len() && match self.events[index] {
            Event::Publish {value:v,out:Ok(id),..}=>id.0==slot && v==value,
            Event::Replace {id,value:v,out:Ok(_),..}=>id.0==slot && v==value,
            _=>false,
        }
    }
    pub open spec fn handle_retired_at(&self,index:int,value:u64)->bool {
        0<=index<self.events.len() && added(self.events[index]).contains(value)
            && exists|slot:int|0<=slot<self.states[index].store.values().len() && slot<self.states[index+1].store.values().len()
                && self.states[index].store.values()[slot]==Some(value) && self.states[index+1].store.values()[slot]!=Some(value)
    }
    /// Opaque handle numbers enter a slot only through actual successful publish
    /// or replacement. This says nothing about the interior of the JS object.
    pub proof fn payload_origin(&self,end:int,slot:int,value:u64)
        requires self.valid(),0<=end<self.states.len(),0<=slot<self.states[end].store.values().len(),self.states[end].store.values()[slot]==Some(value),
        ensures exists|index:int|0<=index<end && self.payload_written_at(index,slot,value),
        decreases end,
    {
        if end==0 {assert(false);} else {
            let index=end-1;assert(history::step(self.states[index],self.states[index+1],self.events[index]));
            reveal(history::operation);
            if self.states[end].store.same(&self.states[index].store) {self.states[end].store.same_observations(&self.states[index].store);}
            if self.payload_written_at(index,slot,value) {} else {
                assert(slot<self.states[index].store.values().len());
                assert(self.states[index].store.values()[slot]==Some(value));
                self.payload_origin(index,slot,value);
            }
        }
    }
    /// Pending candidates have a real retiring operation, even if later calls
    /// publish the same number again. Delivery rechecks current retention.
    pub proof fn queued_handle_origin(&self,end:int,value:u64)
        requires self.valid(),0<=end<self.states.len(),self.states[end].released.contains(value),
        ensures exists|index:int|0<=index<end && self.handle_retired_at(index,value),
        decreases end,
    {
        if end==0 {assert(false);} else {
            let index=end-1;assert(history::step(self.states[index],self.states[index+1],self.events[index]));
            reveal(history::operation);
            if added(self.events[index]).contains(value) {
                added_has_source(self.states[index],self.states[index+1],self.events[index],value);
                assert(self.handle_retired_at(index,value));
            } else {
                let j=choose|j:int|0<=j<self.states[end].released.len() && self.states[end].released[j]==value;
                assert(self.events[index] !is DrainReleased);
                if j>=self.states[index].released.len() {
                    assert(added(self.events[index])[j-self.states[index].released.len()]==value);
                    assert(added(self.events[index]).contains(value));
                }
                assert(self.states[index].released[j]==value);
                self.queued_handle_origin(index,value);
            }
        }
    }
    /// Failed cleanup, stale replies, retry and unrelated operations cannot drop
    /// a pending candidate. Only an explicit delivery batch consumes the queue.
    pub proof fn queued_until_drain(&self,start:int,end:int,value:u64)
        requires self.valid(),0<=start<=end<self.states.len(),self.states[start].released.contains(value),
            forall|i:int|start<=i<end ==> self.events[i] !is DrainReleased,
        ensures self.states[end].released.contains(value),
        decreases end-start,
    {
        if start<end {
            let index=end-1;self.queued_until_drain(start,index,value);
            assert(history::step(self.states[index],self.states[index+1],self.events[index]));reveal(history::operation);
            let j=choose|j:int|0<=j<self.states[index].released.len() && self.states[index].released[j]==value;
            assert(self.states[end].released[j]==value);
        }
    }
    /// The actual batch returned to the driver is safe against every retained
    /// slot (including withdrawn versions) and has both write and retirement
    /// origins in the same continuous execution.
    pub proof fn delivered_handle_origin(&self,index:int,value:u64)
        requires self.valid(),0<=index<self.events.len(),self.events[index] is DrainReleased,
            self.events[index]->DrainReleased_out.contains(value),
        ensures !held(self.states[index].store,value),
            exists|written:int,retired:int,slot:int|0<=written<retired<index
                && self.payload_written_at(written,slot,value) && self.handle_retired_at(retired,value)
                && 0<=slot<self.states[retired].store.values().len() && slot<self.states[retired+1].store.values().len()
                && self.states[retired].store.values()[slot]==Some(value) && self.states[retired+1].store.values()[slot]!=Some(value),
    {
        assert(history::step(self.states[index],self.states[index+1],self.events[index]));reveal(history::operation);
        self.states[index].released.lemma_filter_contains_rev(unheld(self.states[index].store),value);
        self.queued_handle_origin(index,value);
        let retired=choose|i:int|0<=i<index && self.handle_retired_at(i,value);
        let slot=choose|slot:int|0<=slot<self.states[retired].store.values().len() && slot<self.states[retired+1].store.values().len()
            && self.states[retired].store.values()[slot]==Some(value) && self.states[retired+1].store.values()[slot]!=Some(value);
        self.payload_origin(retired,slot,value);
        let written=choose|i:int|0<=i<retired && self.payload_written_at(i,slot,value);
        assert(0<=written<retired<index);
    }
}
}
