//! The identity and version of an actual shared typed payload. Its interior
//! meaning is supplied by the typed owner, not guessed by the common carrier.
#[cfg(verus_keep_ghost)]
use super::{Frame, Record};
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::resource::Loc;
verus! {
broadcast use vstd::seq_lib::group_seq_properties;
pub open spec fn mutation(change:super::Change)->bool {change is PayloadReplace || change is PayloadApply || change is PayloadRestore}
pub open spec fn present(record:Record)->bool {record is Payload || record is RetiredPayload}
pub open spec fn source(record:Record)->Loc {match record {Record::Payload {source,..}|Record::RetiredPayload {source,..}=>source,_=>arbitrary()}}
pub open spec fn version(record:Record)->u64 {match record {Record::Payload {revision,..}|Record::RetiredPayload {revision,..}=>revision,_=>0}}
pub open spec fn recorded(frames:Seq<Frame>,n:nat,key:nat)->bool {
    super::state_at(frames,n).contains_key(key) && present(super::state_at(frames,n)[key])
}
pub open spec fn revision(frames:Seq<Frame>,n:nat,key:nat)->u64 {version(super::state_at(frames,n)[key])}
pub proof fn edge(frames:Seq<Frame>,n:nat,key:nat)
    requires super::valid(frames),n<frames.len(),recorded(frames,n,key),
    ensures recorded(frames,n+1,key),
        source(super::state_at(frames,n+1)[key])==source(super::state_at(frames,n)[key]),
        frames[n as int].event.key==key ==> super::state_at(frames,n)[key] is Payload
            && (mutation(frames[n as int].event.change) && super::state_at(frames,n+1)[key] is Payload
                && revision(frames,n+1,key)==revision(frames,n,key)+1
                || frames[n as int].event.change==super::Change::PayloadRetire && super::state_at(frames,n+1)[key] is RetiredPayload
                && revision(frames,n+1,key)==revision(frames,n,key)),
        frames[n as int].event.key!=key ==> super::state_at(frames,n+1)[key]==super::state_at(frames,n)[key],
{
    assert(super::step(super::state_at(frames,n),frames[n as int].state,frames[n as int].event));
    reveal(super::changes);
}
pub proof fn retained(frames:Seq<Frame>,start:nat,end:nat,key:nat)
    requires super::valid(frames),start<=end<=frames.len(),recorded(frames,start,key),
    ensures recorded(frames,end,key),revision(frames,start,key)<=revision(frames,end,key),
        source(super::state_at(frames,start)[key])==source(super::state_at(frames,end)[key]),
        super::state_at(frames,start)[key] is RetiredPayload ==> super::state_at(frames,end)[key]==super::state_at(frames,start)[key],
    decreases end-start,
{if start<end {retained(frames,start,(end-1) as nat,key);edge(frames,(end-1) as nat,key);}}
pub proof fn unique_revision(frames:Seq<Frame>,a:nat,b:nat,key:nat)
    requires super::valid(frames),a<frames.len(),b<frames.len(),
        frames[a as int].event.key==key,frames[b as int].event.key==key,
        frames[a as int].event.after is Payload,frames[b as int].event.after is Payload,
        frames[a as int].event.after->Payload_revision==frames[b as int].event.after->Payload_revision,
    ensures a==b,
{
    assert(super::step(super::state_at(frames,a),frames[a as int].state,frames[a as int].event));
    assert(super::step(super::state_at(frames,b),frames[b as int].state,frames[b as int].event));
    if a<b {retained(frames,a+1,b,key);edge(frames,b,key);}
    if b<a {retained(frames,b+1,a,key);edge(frames,a,key);}
}
pub open spec fn indexed(count:nat,positions:Seq<nat>,frames:Seq<Frame>,key:nat,source:Loc)->bool {
    &&& positions.len()==count
    &&& forall|i:int|0<=i<count ==> #[trigger] positions[i]<frames.len()
        && frames[positions[i] as int].event.key==key
        && frames[positions[i] as int].event.after==(Record::Payload {source,revision:i as u64}) && i<=u64::MAX
        && if i==0 {frames[positions[i] as int].event.change==super::Change::Allocate} else {mutation(frames[positions[i] as int].event.change)}
    &&& forall|i:int,j:int|0<=i<j<count ==> #[trigger] positions[i]<#[trigger] positions[j]
}
pub proof fn extend_indexed(count:nat,positions:Seq<nat>,before:Seq<Frame>,after:Seq<Frame>,key:nat,source:Loc)
    requires indexed(count,positions,before,key,source),before.len()<=after.len(),after.take(before.len() as int)==before,
    ensures indexed(count,positions,after,key,source),
{
    assert forall|i:int|0<=i<count implies #[trigger] positions[i]<after.len()
        && after[positions[i] as int].event.key==key
        && after[positions[i] as int].event.after==(Record::Payload {source,revision:i as u64}) && i<=u64::MAX
        && if i==0 {after[positions[i] as int].event.change==super::Change::Allocate} else {mutation(after[positions[i] as int].event.change)} by {
        assert(after[positions[i] as int]==before[positions[i] as int]);
    }
}
pub proof fn append_indexed(count:nat,positions:Seq<nat>,before:Seq<Frame>,after:Seq<Frame>,key:nat,source:Loc)
    requires indexed(count,positions,before,key,source),0<count<=u64::MAX,
        before.len()<after.len(),after.take(before.len() as int)==before,
        after.last().event.key==key,mutation(after.last().event.change),
        after.last().event.after==(Record::Payload {source,revision:count as u64}),
    ensures indexed(count+1,positions.push((after.len()-1) as nat),after,key,source),
{
    extend_indexed(count,positions,before,after,key,source);let updated=positions.push((after.len()-1) as nat);
    assert forall|i:int,j:int|0<=i<j<count+1 implies #[trigger] updated[i]<#[trigger] updated[j] by {
        if j==count {assert(positions[i]<before.len());}
    }
}
pub proof fn complete_at(frames:Seq<Frame>,positions:Seq<nat>,key:nat,source:Loc,count:nat,n:nat)->(index:int)
    requires super::valid(frames),indexed(count,positions,frames,key,source),0<count,
        super::state_at(frames,frames.len()).contains_pair(key,Record::Payload {source,revision:(count-1) as u64}),count-1<=u64::MAX,
        n<frames.len(),frames[n as int].event.key==key,
    ensures 0<=index<count,positions[index]==n,
{
    let start=positions[0];
    assert(super::step(super::state_at(frames,start),frames[start as int].state,frames[start as int].event));
    if n<start {
        assert(super::step(super::state_at(frames,n),frames[n as int].state,frames[n as int].event));
        super::key_persists(frames,n+1,start,key);assert(false);
    }
    if n==start {0} else {
        retained(frames,start+1,n,key);edge(frames,n,key);retained(frames,n+1,frames.len(),key);
        assert(frames[n as int].event.after is Payload);
        let i=frames[n as int].event.after->Payload_revision as int;
        assert(0<=i<count);assert(positions[i]<frames.len());
        unique_revision(frames,n,positions[i],key);i
    }
}
pub proof fn complete_projection(frames:Seq<Frame>,positions:Seq<nat>,key:nat,source:Loc,count:nat)
    requires super::valid(frames),indexed(count,positions,frames,key,source),0<count,
        super::state_at(frames,frames.len()).contains_pair(key,Record::Payload {source,revision:(count-1) as u64}),count-1<=u64::MAX,
    ensures forall|n:int|0<=n<frames.len() && #[trigger] frames[n].event.key==key ==> exists|i:int|0<=i<count && positions[i]==n,
{
    assert forall|n:int|0<=n<frames.len() && #[trigger] frames[n].event.key==key implies exists|i:int|0<=i<count && positions[i]==n by {
        let i=complete_at(frames,positions,key,source,count,n as nat);assert(positions[i]==n);
    }
}

}
