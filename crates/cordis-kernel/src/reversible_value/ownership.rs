//! Erased inverse custody maintained inside the real scalar value lock.
//! Every successful forward mints one linear lease. Registration moves the
//! actual inverse; blocked restoration retains it; successful restoration
//! consumes the lease and names its creating Journal position.
use super::{Event, InverseState};
use vstd::prelude::*;
use vstd::resource::map::{GhostMapAuth, GhostPointsTo};
#[cfg(verus_keep_ghost)]
use vstd::resource::Loc;

verus! {
pub open spec fn creates(event:Event)->bool {event is Forward || event is Computed}
pub open spec fn inverse(event:Event)->InverseState {InverseState {before:event.before(),after:event.after()}}
pub ghost struct Frame {pub event:Event,pub at:nat,pub live:Map<nat,InverseState>}
pub open spec fn live_at(frames:Seq<Frame>,n:nat)->Map<nat,InverseState> {if n==0 {Map::empty()} else {frames[n-1].live}}
pub open spec fn step(before:Map<nat,InverseState>,after:Map<nat,InverseState>,event:Event,at:nat)->bool {
    if creates(event) {!before.contains_key(at) && after==before.insert(at,inverse(event))}
    else if event is Restore {before.contains_pair(event->Restore_origin,event->Restore_inverse) && after==before.remove(event->Restore_origin)}
    else {after==before}
}
#[verifier::opaque]
pub open spec fn valid(frames:Seq<Frame>)->bool {
    &&& forall|i:int|0<=i<frames.len() ==> #[trigger] step(live_at(frames,i as nat),frames[i].live,frames[i].event,frames[i].at)
    &&& forall|i:int,j:int|0<=i<j<frames.len() ==> #[trigger] frames[i].at<#[trigger] frames[j].at
    &&& forall|i:int,k:nat|0<=i<frames.len() && #[trigger] frames[i].live.contains_key(k) ==> k<=frames[i].at
}
pub open spec fn matches(frames:Seq<Frame>,events:Seq<Event>,positions:Seq<nat>)->bool {
    frames.len()==events.len() && frames.len()==positions.len()
        && forall|i:int|0<=i<frames.len() ==> (#[trigger] frames[i]).event==events[i] && frames[i].at==positions[i]
}
pub proof fn append(frames:Seq<Frame>,next:Frame)
    requires valid(frames),frames.len()>0 ==> frames.last().at<next.at,
        step(live_at(frames,frames.len()),next.live,next.event,next.at),
    ensures valid(frames.push(next)),
{
    reveal(valid);let updated=frames.push(next);
    assert forall|i:int|0<=i<updated.len() implies #[trigger] step(live_at(updated,i as nat),updated[i].live,updated[i].event,updated[i].at) by {
        if i<frames.len() {assert(live_at(updated,i as nat)==live_at(frames,i as nat));assert(step(live_at(frames,i as nat),frames[i].live,frames[i].event,frames[i].at));}
        else {assert(live_at(updated,i as nat)==live_at(frames,frames.len()));}
    }
    assert forall|i:int,k:nat|0<=i<updated.len() && #[trigger] updated[i].live.contains_key(k) implies k<=updated[i].at by {
        if i==frames.len() && k!=next.at {assert(frames.len()>0);assert(frames.last().live.contains_key(k));}
    }
    assert forall|i:int,j:int|0<=i<j<updated.len() implies #[trigger] updated[i].at<#[trigger] updated[j].at by {
        if j==frames.len() && i<frames.len()-1 {assert(frames[i].at<frames.last().at);}
    }
}
#[allow(dead_code)]
pub tracked struct Lease {point:GhostPointsTo<nat,InverseState>}
impl Lease {
    pub closed spec fn source(&self)->Loc {self.point.id()}
    pub closed spec fn origin(&self)->nat {self.point.key()}
    pub closed spec fn inverse(&self)->InverseState {self.point.value()}
}
pub open spec fn issued(lease:Option<Lease>,source:Loc,event:Event,at:nat)->bool {
    lease.is_some()==creates(event) && (lease.is_some() ==> lease.unwrap().source()==source
        && lease.unwrap().origin()==at && lease.unwrap().inverse()==inverse(event))
}
#[allow(dead_code)]
pub tracked struct Protocol {auth:GhostMapAuth<nat,InverseState>,ghost frames:Seq<Frame>}
impl Protocol {
    pub closed spec fn source(&self)->Loc {self.auth.id()}
    pub closed spec fn frames(&self)->Seq<Frame> {self.frames}
    pub closed spec fn wf(&self)->bool {valid(self.frames()) && self.auth@==live_at(self.frames(),self.frames().len())}
    pub proof fn facts(&self) requires self.wf(),ensures valid(self.frames()), {}
    pub proof fn new()->(tracked out:Self)
        ensures out.wf(),out.frames()==Seq::<Frame>::empty(),
    {reveal(valid);let tracked (auth,_)=GhostMapAuth::new(Map::empty());Self {auth,frames:Seq::empty()}}
    pub proof fn record(tracked &mut self,event:Event,at:nat,tracked restore:Option<Lease>)->(tracked out:Option<Lease>)
        requires old(self).wf(),old(self).frames().len()>0 ==> old(self).frames().last().at<at,
            restore.is_some()==(event is Restore),
            restore.is_some() ==> restore.unwrap().source()==old(self).source() && restore.unwrap().origin()==event->Restore_origin
                && restore.unwrap().inverse()==event->Restore_inverse,
        ensures final(self).wf(),final(self).source()==old(self).source(),
            final(self).frames().len()==old(self).frames().len()+1,
            final(self).frames().drop_last()==old(self).frames(),final(self).frames().last().event==event,final(self).frames().last().at==at,
            issued(out,final(self).source(),event,at),
    {
        let prior=self.frames;let before=self.auth@;
        let tracked out=if creates(event) {
            reveal(valid);
            assert(!self.auth@.contains_key(at)) by {if self.auth@.contains_key(at) {assert(prior.len()>0);assert(prior.last().live.contains_key(at));}}
            Some(Lease {point:self.auth.insert(at,inverse(event))})
        } else {if let Some(lease)=restore {lease.point.agree(&self.auth);self.auth.delete_points_to(lease.point);} None};
        let frame=Frame {event,at,live:self.auth@};
        assert(step(before,self.auth@,event,at));append(prior,frame);self.frames=prior.push(frame);out
    }
}
/// Every available lease has one real creating event. This is derived from
/// the producer's protocol, rather than supplied as an initial membership axiom.
pub proof fn origin(frames:Seq<Frame>,n:nat,key:nat)->(i:int)
    requires valid(frames),n<=frames.len(),live_at(frames,n).contains_key(key),
    ensures 0<=i<n,frames[i].at==key,creates(frames[i].event),inverse(frames[i].event)==live_at(frames,n)[key],
    decreases n,
{
    reveal(valid);assert(n>0);let j=(n-1) as nat;let frame=frames[j as int];
    assert(step(live_at(frames,j),frame.live,frame.event,frame.at));
    if creates(frame.event) && frame.at==key {j as int} else {origin(frames,j,key)}
}
pub proof fn consumed_stays_absent(frames:Seq<Frame>,at:int,n:nat)
    requires valid(frames),0<=at<n<=frames.len(),frames[at].event is Restore,
    ensures !live_at(frames,n).contains_key(frames[at].event->Restore_origin),
    decreases n-at,
{
    reveal(valid);let key=frames[at].event->Restore_origin;
    assert(step(live_at(frames,at as nat),frames[at].live,frames[at].event,frames[at].at));
    origin(frames,at as nat,key);
    if n>at+1 {
        consumed_stays_absent(frames,at,(n-1) as nat);
        assert(step(live_at(frames,(n-1) as nat),frames[n-1].live,frames[n-1].event,frames[n-1].at));
        assert(frames[at].at<frames[n-1].at);
    }
}
pub proof fn restore_source(frames:Seq<Frame>,at:int)->(created:int)
    requires valid(frames),0<=at<frames.len(),frames[at].event is Restore,
    ensures 0<=created<at,creates(frames[created].event),frames[created].at==frames[at].event->Restore_origin,
        inverse(frames[created].event)==frames[at].event->Restore_inverse,
        forall|i:int|0<=i<frames.len() && (#[trigger] frames[i]).event is Restore
            && frames[i].event->Restore_origin==frames[at].event->Restore_origin ==> i==at,
{
    reveal(valid);let key=frames[at].event->Restore_origin;
    assert(step(live_at(frames,at as nat),frames[at].live,frames[at].event,frames[at].at));
    let created=origin(frames,at as nat,key);
    assert forall|i:int|0<=i<frames.len() && (#[trigger] frames[i]).event is Restore
        && frames[i].event->Restore_origin==key implies i==at by {
        assert(step(live_at(frames,i as nat),frames[i].live,frames[i].event,frames[i].at));
        if i<at {consumed_stays_absent(frames,i,at as nat);}
        if at<i {consumed_stays_absent(frames,at,i as nat);}
    }
    created
}
impl super::Snapshot {
    /// Every same-allocation frame is the birth or an actual producer entry,
    /// including raw callers, computed effects, rejections and blocked retries.
    pub proof fn source_at(&self,at:nat)->(i:int)
        requires self.certified(),at<self.joint_spec().events().len(),
            self.joint_spec().events()[at as int].event.key==self.object().key,at!=self.birth(),
        ensures 0<=i<self.history().len(),self.positions()[i]==at,
            self.joint_spec().events()[at as int].event.change==(super::joint::Change::Value {event:self.history()[i]}),
    {
        let all=seq![self.birth()]+self.positions();assert(all.contains(at));
        let j=choose|j:int|0<=j<all.len() && all[j]==at;assert(j>0);j-1
    }
    pub proof fn restore_origin(&self,i:int)->(created:int)
        requires self.certified(),0<=i<self.history().len(),self.history()[i] is Restore,
        ensures 0<=created<i,creates(self.history()[created]),
            self.positions()[created]==self.history()[i]->Restore_origin,
            inverse(self.history()[created])==self.history()[i]->Restore_inverse,
            forall|j:int|0<=j<self.history().len() && (#[trigger] self.history()[j]) is Restore
                && self.history()[j]->Restore_origin==self.history()[i]->Restore_origin ==> j==i,
    {
        assert(self.custody()[i].event==self.history()[i]);let created=restore_source(self.custody(),i);
        assert forall|j:int|0<=j<self.history().len() && (#[trigger] self.history()[j]) is Restore
            && self.history()[j]->Restore_origin==self.history()[i]->Restore_origin implies j==i by {assert(self.custody()[j].event==self.history()[j]);}
        created
    }
}

}
