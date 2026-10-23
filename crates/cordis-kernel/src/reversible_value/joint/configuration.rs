//! Configuration protocol projection in the real native execution Journal.
//! Typed candidates, recovery payloads and plans stay in the associated ledger.
//! These are explicit configuration transitions, not assumed paper stutters.
use crate::configuration_transaction::Structure;
#[cfg(verus_keep_ghost)]
use std::task::Poll;
use vstd::prelude::*;
verus! {
#[derive(Copy,Clone,PartialEq,Eq,Structural)]
pub enum Outcome {Pending,Failed,More,Done}
pub open spec fn outcome<E>(result:Poll<Result<bool,E>>)->Outcome {
    match result {Poll::Pending=>Outcome::Pending,Poll::Ready(Err(_))=>Outcome::Failed,
        Poll::Ready(Ok(true))=>Outcome::Done,Poll::Ready(Ok(false))=>Outcome::More}
}
#[derive(Copy,Clone,PartialEq,Eq,Structural)]
pub enum Event {Begin {structural:bool},Update {result:Outcome},Rollback {result:Outcome},Structure {result:Outcome},Commit,Recover,Refresh}
pub struct State {
    pub index:nat,pub version:u64,pub pending:bool,pub phase:Option<Structure>,
    pub length:nat,pub applied:nat,pub attempted:nat,pub restoring:bool,
}
#[verifier::opaque]
pub open spec fn step(a:State,b:State,event:Event)->bool {
    &&& b.index==a.index+1
    &&& (event==Event::Commit ==> a.version<u64::MAX && b.version==a.version+1)
    &&& (event!=Event::Commit ==> b.version==a.version)
    &&& match event {
        Event::Begin {structural}=>!a.pending && a.version<u64::MAX && b.pending
            && b.phase==if structural {Some(Structure::Remove)} else {None},
        Event::Update {result}=>b.pending==a.pending && b.length==a.length
            && (result==Outcome::Done ==> b.applied==b.length && !b.restoring),
        Event::Rollback {result}=>b.pending==a.pending && b.restoring
            && (result==Outcome::Done ==> b.length==0)
            && (result==Outcome::Pending || result==Outcome::Failed ==> b.length>0),
        Event::Structure {result}=>b.length==a.length && b.applied==a.applied && b.attempted==a.attempted && b.restoring==a.restoring
            && (result==Outcome::Pending || result==Outcome::Failed ==> b.phase==a.phase)
            && (b.phase!=a.phase ==> a.phase.is_some() && a.phase.unwrap().successor()==b.phase)
            && (result==Outcome::Done ==> matches!(b.phase,Some(Structure::Updates|Structure::Ready|Structure::Recovered))),
        Event::Commit=>a.pending && !a.restoring && a.applied==a.length && (a.phase.is_none() || a.phase==Some(Structure::Ready))
            && !b.pending && b.length==0 && b.phase.is_none(),
        Event::Recover=>a.pending && a.length==0 && (a.phase.is_none() || a.phase==Some(Structure::Recovered))
            && !b.pending && b.length==0 && b.phase.is_none(),
        Event::Refresh=>!a.pending && b==(State {index:a.index+1,..a}),
    }
}
pub open spec fn recorded(frames:Seq<super::Frame>,n:nat,key:nat)->bool {
    super::state_at(frames,n).contains_key(key) && super::state_at(frames,n)[key] is Configuration
}
pub open spec fn at(frames:Seq<super::Frame>,n:nat,key:nat)->State {super::state_at(frames,n)[key]->Configuration_state}
pub proof fn edge(frames:Seq<super::Frame>,n:nat,key:nat)
    requires super::valid(frames),n<frames.len(),recorded(frames,n,key),
    ensures recorded(frames,n+1,key),
        frames[n as int].event.key==key ==> frames[n as int].event.change is Configuration
            && step(at(frames,n,key),at(frames,n+1,key),frames[n as int].event.change->Configuration_event)
            && at(frames,n+1,key).index==at(frames,n,key).index+1,
        frames[n as int].event.key!=key ==> at(frames,n+1,key)==at(frames,n,key),
{
    assert(super::step(super::state_at(frames,n),frames[n as int].state,frames[n as int].event));
    reveal(super::changes);reveal(step);
}
pub proof fn monotone(frames:Seq<super::Frame>,start:nat,end:nat,key:nat)
    requires super::valid(frames),start<=end<=frames.len(),recorded(frames,start,key),
    ensures recorded(frames,end,key),at(frames,start,key).index<=at(frames,end,key).index,
    decreases end-start,
{if start<end {monotone(frames,start,(end-1) as nat,key);edge(frames,(end-1) as nat,key);}}
pub proof fn unique_index(frames:Seq<super::Frame>,a:nat,b:nat,key:nat)
    requires super::valid(frames),a<frames.len(),b<frames.len(),
        frames[a as int].event.key==key,frames[b as int].event.key==key,
        frames[a as int].event.after is Configuration,frames[b as int].event.after is Configuration,
        frames[a as int].event.after->Configuration_state.index==frames[b as int].event.after->Configuration_state.index,
    ensures a==b,
{
    assert(super::step(super::state_at(frames,a),frames[a as int].state,frames[a as int].event));
    assert(super::step(super::state_at(frames,b),frames[b as int].state,frames[b as int].event));
    if a<b {monotone(frames,a+1,b,key);edge(frames,b,key);}
    if b<a {monotone(frames,b+1,a,key);edge(frames,a,key);}
}
}
