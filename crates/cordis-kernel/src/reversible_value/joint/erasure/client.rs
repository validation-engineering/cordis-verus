//! A nonempty full-record transport client: interleaved managed forwards,
//! registration, failed cleanup/retry, exact restoration and a live pending debt.
#[cfg(verus_keep_ghost)]
use super::{
    super::{self as j, Change, Frame, Record, Step},
    Plan,
};
#[cfg(verus_keep_ghost)]
use crate::{
    cleanup_journal::{RestoreOutcome, RestoreTicket},
    reversible_value::{Branch, Event, InverseState, Operation, Outcome, ValueState},
};
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::resource::Loc;
verus! {
broadcast use vstd::seq_lib::group_seq_properties;
pub open spec fn value(after:bool)->ValueState {ValueState {value:if after {1} else {0},depth:if after {1} else {0}}}
pub open spec fn queue(domain:u64)->j::episode::CleanupState {j::episode::CleanupState {domain,next:0,selected:None,failed:false,committed:Seq::empty(),waiting:Seq::empty(),pending:false,settled:true,cancelled:false,occupied:Seq::empty(),issued:false}}
pub open spec fn q(at:nat)->j::episode::CleanupState {
    let a=queue(2);let ticket=RestoreTicket {domain:2,attempt:if at<11 {0} else {1},token:0};
    if at<7 {a} else if at<9 {j::episode::CleanupState {occupied:seq![true],waiting:seq![0usize],..a}}
    else if at<14 {j::episode::CleanupState {next:if at<11 {1} else {2},occupied:seq![at==10 || at==11],selected:Some(ticket),failed:at==10,issued:at==9 || at==12 || at==13,..a}}
    else {j::episode::CleanupState {next:2,occupied:seq![false],..a}}
}
pub open spec fn records(object:Loc,slot:Loc,domain:Loc,n:nat)->Map<nat,Record> {
    let base=Map::empty();
    let base=if n>0 {base.insert(0nat,Record::Object {source:object,state:value(5<=n<13)})} else {base};
    let base=if n>1 {base.insert(1nat,Record::Object {source:object,state:value((6<=n<15) || n>=16)})} else {base};
    let base=if n>2 {base.insert(2nat,Record::Cleanup {state:q(n)})} else {base};
    let base=if n>3 {base.insert(3nat,Record::Cleanup {state:if n<8 {queue(3)} else {j::episode::CleanupState {occupied:seq![true],waiting:seq![0usize],..queue(3)}}})} else {base};
    if n>16 {base.insert(4nat,Record::Slot {source:slot,revision:0,object:j::Object {domain,key:1}})} else {base}
}
pub open spec fn pending(n:nat)->Map<nat,nat> {
    let p=Map::empty();let p=if 5<=n<7 {p.insert(4nat,0nat)} else {p};
    let p=if 6<=n<8 {p.insert(5nat,1nat)} else {p};
    if n>=16 {p.insert(15nat,1nat)} else {p}
}
pub open spec fn forward()->Event {Event::Forward {operation:Operation::Add(1),branch:Branch {matched:None,unmatched:None},before:value(false),after:value(true),outcome:Outcome {before:0,after:1,matched:true},next:None}}
pub open spec fn restore(origin:nat)->Event {Event::Restore {inverse:InverseState {before:value(false),after:value(true)},before:value(true),after:value(false),origin}}
pub open spec fn key(i:nat)->nat {if i<4 {i} else if i==4 || i==12 {0} else if i==5 || i==14 || i==15 {1} else if i==7 {3} else if i==16 {4} else {2}}
pub open spec fn change(i:nat)->Change {
    if i<4 || i==16 {Change::Allocate}
    else if i==4 || i==5 || i==15 {Change::Value {event:forward()}}
    else if i==12 || i==14 {Change::Value {event:restore(if i==12 {4} else {5})}}
    else if i==6 || i==7 {Change::RegisterInverse {write:if i==6 {4} else {5}}}
    else {Change::Cleanup {event:if i==8 || i==11 {j::episode::CleanupChange::Pop {ticket:RestoreTicket {domain:2,attempt:if i==8 {0} else {1},token:0}}}
        else if i==10 {j::episode::CleanupChange::Retry {ticket:RestoreTicket {domain:2,attempt:1,token:0}}}
        else {j::episode::CleanupChange::Complete {ticket:RestoreTicket {domain:2,attempt:if i==9 {0} else {1},token:0},outcome:if i==9 {RestoreOutcome::Failed} else {RestoreOutcome::Succeeded},retained:i==9}}}}
}
pub open spec fn source(object:Loc,slot:Loc,domain:Loc)->Seq<Frame> {Seq::new(17,|i:int|Frame {
    event:Step {key:key(i as nat),change:change(i as nat),after:records(object,slot,domain,(i+1) as nat)[key(i as nat)],pending:i==4 || i==5 || i==15,settled:if i==6 {Some(4nat)} else if i==7 {Some(5nat)} else {None}},
    state:records(object,slot,domain,(i+1) as nat),pending:pending((i+1) as nat)})}
pub open spec fn plan(object:Loc,slot:Loc,domain:Loc)->Plan {
    let s=source(object,slot,domain);Plan {mask:Seq::new(17,|i:int|key(i as nat)!=0 && key(i as nat)!=2),images:s.map(|_:int,f:Frame|f.event.after)}
}
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn source_step(object:Loc,slot:Loc,domain:Loc,i:int)
    requires 0<=i<17,
    ensures {
        let s=source(object,slot,domain);
        &&& j::step(j::state_at(s,i as nat),s[i].state,s[i].event)
        &&& j::caused(s.take(i),s[i].event)
        &&& j::pending_step(j::pending_at(s,i as nat),s[i].pending,s[i].event,i as nat)
    },
{
    let s=source(object,slot,domain);
    assert(seq![true].update(0,false) =~= seq![false]);
    assert(seq![false].update(0,true) =~= seq![true]);
    assert(seq![false].update(0,false) =~= seq![false]);
    assert(seq![0usize].drop_last() =~= Seq::<usize>::empty());
        reveal(j::changes);reveal(j::groups::guard);
        assert(j::state_at(s,i as nat)==records(object,slot,domain,i as nat));
        assert(j::pending_at(s,i as nat)==pending(i as nat));
        assert(s[i].state =~= records(object,slot,domain,i as nat).insert(s[i].event.key,s[i].event.after));
        if s[i].event.pending {assert(s[i].pending =~= pending(i as nat).insert(i as nat,s[i].event.key));}
        else if s[i].event.settled.is_some() {assert(s[i].pending =~= pending(i as nat).remove(s[i].event.settled.unwrap()));}
        else {assert(s[i].pending =~= pending(i as nat));}
        if i==0 { assert(j::step(j::state_at(s,i as nat),s[i].state,s[i].event));assert(j::caused(s.take(i),s[i].event));assert(j::pending_step(j::pending_at(s,i as nat),s[i].pending,s[i].event,i as nat)); }
        else if i==1 { assert(j::step(j::state_at(s,i as nat),s[i].state,s[i].event));assert(j::caused(s.take(i),s[i].event));assert(j::pending_step(j::pending_at(s,i as nat),s[i].pending,s[i].event,i as nat)); }
        else if i==2 { assert(j::step(j::state_at(s,i as nat),s[i].state,s[i].event));assert(j::caused(s.take(i),s[i].event));assert(j::pending_step(j::pending_at(s,i as nat),s[i].pending,s[i].event,i as nat)); }
        else if i==3 { assert(j::step(j::state_at(s,i as nat),s[i].state,s[i].event));assert(j::caused(s.take(i),s[i].event));assert(j::pending_step(j::pending_at(s,i as nat),s[i].pending,s[i].event,i as nat)); }
        else if i==4 { assert(j::step(j::state_at(s,i as nat),s[i].state,s[i].event));assert(j::caused(s.take(i),s[i].event));assert(j::pending_step(j::pending_at(s,i as nat),s[i].pending,s[i].event,i as nat)); }
        else if i==5 { assert(j::step(j::state_at(s,i as nat),s[i].state,s[i].event));assert(j::caused(s.take(i),s[i].event));assert(j::pending_step(j::pending_at(s,i as nat),s[i].pending,s[i].event,i as nat)); }
        else if i==6 { assert(j::step(j::state_at(s,i as nat),s[i].state,s[i].event));assert(j::caused(s.take(i),s[i].event));assert(j::pending_step(j::pending_at(s,i as nat),s[i].pending,s[i].event,i as nat)); }
        else if i==7 { assert(j::step(j::state_at(s,i as nat),s[i].state,s[i].event));assert(j::caused(s.take(i),s[i].event));assert(j::pending_step(j::pending_at(s,i as nat),s[i].pending,s[i].event,i as nat)); }
        else if i==8 { assert(j::step(j::state_at(s,i as nat),s[i].state,s[i].event));assert(j::caused(s.take(i),s[i].event));assert(j::pending_step(j::pending_at(s,i as nat),s[i].pending,s[i].event,i as nat)); }
        else if i==9 { assert(j::step(j::state_at(s,i as nat),s[i].state,s[i].event));assert(j::caused(s.take(i),s[i].event));assert(j::pending_step(j::pending_at(s,i as nat),s[i].pending,s[i].event,i as nat)); }
        else if i==10 { assert(j::step(j::state_at(s,i as nat),s[i].state,s[i].event));assert(j::caused(s.take(i),s[i].event));assert(j::pending_step(j::pending_at(s,i as nat),s[i].pending,s[i].event,i as nat)); }
        else if i==11 { assert(j::step(j::state_at(s,i as nat),s[i].state,s[i].event));assert(j::caused(s.take(i),s[i].event));assert(j::pending_step(j::pending_at(s,i as nat),s[i].pending,s[i].event,i as nat)); }
        else if i==12 { assert(j::step(j::state_at(s,i as nat),s[i].state,s[i].event));assert(j::caused(s.take(i),s[i].event));assert(j::pending_step(j::pending_at(s,i as nat),s[i].pending,s[i].event,i as nat)); }
        else if i==13 { assert(j::step(j::state_at(s,i as nat),s[i].state,s[i].event));assert(j::caused(s.take(i),s[i].event));assert(j::pending_step(j::pending_at(s,i as nat),s[i].pending,s[i].event,i as nat)); }
        else if i==14 { assert(j::step(j::state_at(s,i as nat),s[i].state,s[i].event));assert(j::caused(s.take(i),s[i].event));assert(j::pending_step(j::pending_at(s,i as nat),s[i].pending,s[i].event,i as nat)); }
        else if i==15 { assert(j::step(j::state_at(s,i as nat),s[i].state,s[i].event));assert(j::caused(s.take(i),s[i].event));assert(j::pending_step(j::pending_at(s,i as nat),s[i].pending,s[i].event,i as nat)); }
        else if i==16 { assert(j::step(j::state_at(s,i as nat),s[i].state,s[i].event));assert(j::caused(s.take(i),s[i].event));assert(j::pending_step(j::pending_at(s,i as nat),s[i].pending,s[i].event,i as nat)); } else {assert(false);}
}
pub proof fn source_valid(object:Loc,slot:Loc,domain:Loc)
    ensures j::valid(source(object,slot,domain)),j::references::history(source(object,slot,domain),domain),
{
    hide(j::step);hide(j::caused);hide(j::pending_step);
    let s=source(object,slot,domain);
    assert forall|i:int|0<=i<s.len() implies j::step(j::state_at(s,i as nat),#[trigger] s[i].state,s[i].event)
        && j::caused(s.take(i),s[i].event) && j::pending_step(j::pending_at(s,i as nat),s[i].pending,s[i].event,i as nat) by {source_step(object,slot,domain,i);}
    assert forall|i:int,k:nat|0<=i<s.len() && #[trigger] s[i].pending.contains_key(k) implies k<=i by {}
    assert(j::valid(s));
}
pub open spec fn scalar_sources_for_client(object:Loc,slot:Loc,domain:Loc)->bool {
    super::scalar_sources(plan(object,slot,domain).prefix(source(object,slot,domain),17))
}
#[verifier::spinoff_prover]
pub proof fn projected_records(object:Loc,slot:Loc,domain:Loc,n:nat)
    requires n<=17,
    ensures plan(object,slot,domain).records(source(object,slot,domain),n)==records(object,slot,domain,n).remove(0nat).remove(2nat),
    decreases n,
{
    let p=plan(object,slot,domain);let s=source(object,slot,domain);
    if n==0 {assert(p.records(s,n) =~= records(object,slot,domain,n).remove(0nat).remove(2nat));}
    else {
        let i=(n-1) as nat;projected_records(object,slot,domain,i);source_step(object,slot,domain,i as int);
        assert(j::state_at(s,i)==records(object,slot,domain,i));
        assert(j::step(records(object,slot,domain,i),records(object,slot,domain,n),s[i as int].event));
        assert(p.records(s,n) =~= records(object,slot,domain,n).remove(0nat).remove(2nat));
    }
}
#[verifier::spinoff_prover]
pub proof fn ready(object:Loc,slot:Loc,domain:Loc)
    ensures plan(object,slot,domain).causes(source(object,slot,domain)),plan(object,slot,domain).transported(source(object,slot,domain)),
        forall|i:nat|i<17 && plan(object,slot,domain).mask[i as int] ==> plan(object,slot,domain).scalar_origin(source(object,slot,domain),i),
{
    let s=source(object,slot,domain);let p=plan(object,slot,domain);
    assert(p.causes(s));
    assert(p.transported(s)) by {
        assert forall|i:nat|i<17 && p.mask[i as int] implies j::step(p.records(s,i),p.records(s,i+1),p.event(s,i)) by {
            projected_records(object,slot,domain,i);projected_records(object,slot,domain,i+1);source_step(object,slot,domain,i as int);
            reveal(j::changes);reveal(j::groups::guard);
            assert(p.records(s,i+1) =~= p.records(s,i).insert(s[i as int].event.key,s[i as int].event.after));
        }
    }
    assert forall|i:nat|i<s.len() && p.mask[i as int] implies p.scalar_origin(s,i) by {
        if let Change::Value {event:Event::Restore {..}}=s[i as int].event.change {assert(i==14);}
    }
}
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn nonempty(object:Loc,slot:Loc,domain:Loc)
    ensures j::valid(plan(object,slot,domain).prefix(source(object,slot,domain),17)),
        scalar_sources_for_client(object,slot,domain),
        plan(object,slot,domain).rank(17)==7,
        plan(object,slot,domain).prefix(source(object,slot,domain),17)[3].event.change==(Change::RegisterInverse {write:2}),
        j::pending_at(plan(object,slot,domain).prefix(source(object,slot,domain),17),7)==Map::empty().insert(5nat,1nat),
{
    hide(j::valid);hide(j::step);hide(Plan::records);
    let s=source(object,slot,domain);let p=plan(object,slot,domain);source_valid(object,slot,domain);ready(object,slot,domain);
    p.construct(s,17);p.positions_law(17);
    reveal_with_fuel(Plan::positions,18);
    p.restoration_sources(s);
    assert(p.positions(17)==seq![1nat,3nat,5nat,7nat,14nat,15nat,16nat]);
    assert(j::pending_at(s,17)==Map::empty().insert(15nat,1nat));
    assert forall|k:nat|#[trigger] p.pending(s,17).contains_key(k)==(k==5) by {p.pending_domain(s,17,k);}
    p.pending_domain(s,17,5);
    assert(p.pending(s,17)[5]==1);
    assert(p.pending(s,17) =~= Map::empty().insert(5nat,1nat));
}
}
