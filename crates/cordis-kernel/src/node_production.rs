//! Complete protocol observations and their continuous control interpretation.
//! A control stutter does not erase publication versions, leases, callback scopes,
//! action tickets, policies, interfaces, errors or retained restoration inputs.
#[cfg(verus_keep_ghost)]
use super::history::{self, Observation};
use super::{history::History, Snapshot};
#[cfg(verus_keep_ghost)]
use crate::lifecycle_state::history as control;
use crate::refinement as r;
use vstd::prelude::*;
verus! {
pub enum Kind {Paper {actor:usize,rule:r::Rule},Restart {actor:usize},Interface,Protocol,Internal}
pub open spec fn label(a:Observation,b:Observation)->control::Label {
    if a.control.control().paper()==b.control.control().paper() {control::Label::Internal}
    else {b.control.control_history().labels.last()}
}
pub open spec fn kind(a:Observation,b:Observation)->Kind {
    if b.same(a) {Kind::Internal} else {match label(a,b) {
        control::Label::Paper {actor,rule}=>Kind::Paper {actor,rule},
        control::Label::Restart {actor}=>Kind::Restart {actor},
        control::Label::Internal=>Kind::Protocol,
        _=>Kind::Interface,
    }}
}
pub open spec fn projection(h:History)->control::History {
    control::History {states:h.states.map(|_:int,s:Observation|s.control.control().paper()),
        labels:Seq::new(h.events.len(),|i:int|label(h.states[i],h.states[i+1]))}
}
#[verifier::opaque]
pub open spec fn classified(h:History,index:int)->bool {
    let a=h.states[index];let b=h.states[index+1];
    &&& history::step(a,b,h.events[index])
    &&& control::step(a.control.control().paper(),b.control.control().paper(),label(a,b))
    &&& (kind(a,b) is Internal)==b.same(a)
    &&& match kind(a,b) {
        Kind::Paper {actor,rule}=>rule!=r::Rule::Restart && rule!=r::Rule::Stutter
            && r::step(a.control.control().paper(),b.control.control().paper(),actor,rule),
        Kind::Restart {actor}=>r::step(a.control.control().paper(),b.control.control().paper(),actor,r::Rule::Restart),
        Kind::Interface=>label(a,b) is Declare || label(a,b) is Release || label(a,b) is Dependencies,
        Kind::Protocol=>a.control.control().paper()==b.control.control().paper() && !b.same(a),
        Kind::Internal=>b.same(a),
    }
}
#[verifier::opaque]
pub open spec fn interpreted(h:History)->bool {
    h.valid() && projection(h).valid()
        && forall|i:int|0<=i<h.events.len() ==> #[trigger] classified(h,i)
}
impl History {
    pub proof fn production_step(&self,index:int)
        requires self.valid(),0<=index<self.events.len(),ensures classified(*self,index),
    {
        self.control_classified(index);reveal(classified);
        if self.states[index+1].same(self.states[index]) {
            self.states[index+1].control.same_observations(&self.states[index].control);
        }
    }
    pub proof fn production_trace(&self)
        requires self.valid(),ensures interpreted(*self),
            projection(*self).base_only() ==> r::execution(projection(*self).states,projection(*self).paper_labels(),false),
    {
        assert forall|i:int|0<=i<self.events.len() implies #[trigger] classified(*self,i) by {self.production_step(i);}
        assert forall|i:int|0<=i<self.events.len() implies control::step(projection(*self).states[i],projection(*self).states[i+1],projection(*self).labels[i]) by {
            assert(classified(*self,i));reveal(classified);
        }
        assert(projection(*self).valid());
        if projection(*self).base_only() {projection(*self).strict_paper_trace();}
        reveal(interpreted);
    }
}
impl Snapshot {
    pub proof fn production_trace(&self)
        requires self.certified(),ensures interpreted(self.history()),
    {self.history().production_trace();}
}
}
