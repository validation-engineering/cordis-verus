//! Values and original Child obligations at the same actual production cut.
//! Value interference remains explicit; native activity need not be quiet.
pub mod foreign;
pub mod pending;
#[cfg(verus_keep_ghost)]
use super::RecordedExecution;
use crate::reversible_value::{effect::ScalarEffect, managed::root::RegisteredReport};
#[cfg(verus_keep_ghost)]
use crate::{
    lifecycle_state::native::runtime::{child_history::Ledger, episode::Unload, history::Snapshot},
    reversible_value::{
        joint,
        managed::{
            self,
            episode::endpoint as function_endpoint,
            interleaving::{self as trajectory, endpoint, Event},
            recovery,
            semantics::Value,
            Step,
        },
        service_composition::Address,
    },
};
use vstd::prelude::*;

verus! {
pub open spec fn output_at_cut<A,R,T:?Sized,M,X>(steps:Seq<Step<T>>,events:Seq<Event<A,R,T,M,X>>,cut:&joint::Snapshot,key:Address)->Option<Value<T>> {
    match endpoint::latest(events,key,events.len()) {
        Some(i)=>events[i as int].value_at(cut.events(),cut.events().len()),
        None=>function_endpoint::value_at(steps[function_endpoint::basis(steps,key,true)],cut.events(),cut.events().len()),
    }
}
pub open spec fn observe_at_cut<A,R,T:?Sized,M,X>(steps:Seq<Step<T>>,events:Seq<Event<A,R,T,M,X>>,cut:&joint::Snapshot)->Map<Address,Value<T>> {
    Map::new(function_endpoint::keys(steps).filter(|key:Address|key.journal==cut.journal_spec() && output_at_cut(steps,events,cut,key).is_some()),
        |key:Address|output_at_cut(steps,events,cut,key).unwrap())
}
pub open spec fn quiet_after<T:?Sized>(steps:Seq<Step<T>>,end:&joint::Receipt,cut:&joint::Snapshot)->bool {
    cut.covers(end) && forall|key:Address|function_endpoint::keys(steps).contains(key) ==>
        recovery::quiet(cut.events(),end.events().len(),cut.events().len(),key.key)
}
/// Decode the same actual per-allocation source at a later real read cut.
/// Neither a target value nor an observation-preserving suffix is assumed.
pub proof fn observe_later<A,R,T:?Sized,M,X>(steps:Seq<Step<T>>,events:Seq<Event<A,R,T,M,X>>,end:&joint::Receipt,cut:&joint::Snapshot)
    requires end.wf(),cut.certified(),quiet_after(steps,end,cut),
    ensures observe_at_cut(steps,events,cut)==endpoint::observe(steps,events,*end),
{
    hide(joint::valid);hide(joint::step);cut.valid_history();
    assert(joint::state_at(cut.events(),end.events().len())==joint::state_at(end.events(),end.events().len()));
    assert forall|key:Address|function_endpoint::keys(steps).contains(key) implies
        output_at_cut(steps,events,cut,key)==endpoint::output(steps,events,*end,key) by {
        function_endpoint::quiet_domain(cut.events(),end.events().len(),cut.events().len(),key.key);
        endpoint::latest_bound(events,key,events.len());
        match endpoint::latest(events,key,events.len()) {
            Some(i)=>{assert(events[i as int].inverse().address==key);},
            None=>{function_endpoint::basis_exists(steps,key,true);},
        }
    }
    assert(observe_at_cut(steps,events,cut) =~= endpoint::observe(steps,events,*end));
}

impl<E:ScalarEffect,T:?Sized> RegisteredReport<E,T> {
    pub open spec fn recovered_values_at_cut<A,R,M,X,V>(&self,events:Seq<Event<A,R,T,M,X>>,cut:&Snapshot<V>)->Map<Address,Value<T>> {
        observe_at_cut(self.result->Ok_0.steps@,events,&cut.joint_spec())
    }
    /// Combine real managed restoration, the episode's own Unload and all
    /// recorded native Child completions. Completeness/foreign closure are
    /// source conditions; value equality and terminal state share this cut.
    pub proof fn unload_recovers_with_children<C,G,A,R,M,X,V>(&self,tracked owner:&RecordedExecution<C,G,A,R,T,M,X>,
        id:usize,offset:nat,tracked end:&Unload,ledger:&Ledger,cut:&Snapshot<V>)
        requires owner.wf(),owner.baseline().cleanup_state().live(id),owner.histories().contains_key(id),owner.terminal().contains_key(id),
            self.start().owner().owns(&owner.baseline()),
            self.completed(),self.effects_before_return(),self.episode_interval(),self.endpoint_source(),
            self.result->Ok_0.witnessed(),self.result->Ok_0.recovery_history(),
            self.retained_recovery(owner.baseline(),id,offset),managed::retained(self.result->Ok_0.steps@,owner.baseline(),id,offset),
            trajectory::linked(owner.histories()[id].events(),self.completion(),self.return_values(),self.obligations(owner.baseline(),id,offset)),
            self.unload_source(owner.histories()[id].events(),end),
            self.result->Ok_0.registered(owner.baseline().cleanup_state().link(),id),end.cleanup_link()==owner.baseline().cleanup_state().link(),
            self.result->Ok_0.queued_sources(owner.baseline().cleanup_state().queues()[id].link()),
            end.cleanup_checkpoint().is_some(),end.cleanup_checkpoint().unwrap().journal()==end.checkpoint().journal(),
            trajectory::completion::foreign_settled(owner.histories()[id].events(),self.return_values().dom()),
            owner.native_children_resolved(ledger),ledger.cut_source(cut),cut.key()==end.native(),
            quiet_after(self.result->Ok_0.steps@,&end.checkpoint(),&cut.joint_spec()),
        ensures self.recovered_values_at_cut(owner.histories()[id].events(),cut)==self.begin_values(),
            owner.native_children_terminal(ledger,cut),self.writes_registered_at_cut(&cut.joint_spec()),
            self.start().recorded(cut.joint_spec().events()),end.recorded(cut.joint_spec().events()),
    {
        hide(joint::valid);hide(joint::step);
        self.unload_recovers_from_owner(owner,id,offset,end);
        owner.native_children_at_cut(ledger,cut);
        cut.valid_history();end.facts();observe_later(self.result->Ok_0.steps@,owner.histories()[id].events(),&end.checkpoint(),&cut.joint_spec());
        self.source_bounds();self.start().facts();
        assert(cut.joint_spec().events().take(self.completion().events().len() as int) =~= end.checkpoint().events().take(self.completion().events().len() as int));
        self.registered_pending_at_cut(end.cleanup_link(),id,&cut.joint_spec());
        assert(self.start().at()<end.checkpoint().events().len());
        assert(cut.joint_spec().events()[self.start().at() as int]==end.checkpoint().events()[self.start().at() as int]);
        assert(cut.joint_spec().events()[end.at() as int]==end.checkpoint().events()[end.at() as int]);
        assert(joint::state_at(cut.joint_spec().events(),end.at())==joint::state_at(end.checkpoint().events(),end.at()));
    }
    /// Actual terminal foreign owners discharge their registered forwards.
    /// Complete observation coverage replaces a supplied success/closure premise.
    pub proof fn unload_recovers_from_observed_owners<C,G,C2,G2,A,R,M,X,V>(&self,tracked owner:&RecordedExecution<C,G,A,R,T,M,X>,
        id:usize,offset:nat,tracked end:&Unload,ledger:&Ledger,cut:&Snapshot<V>,foreign_owners:Map<usize,RecordedExecution<C2,G2,A,R,T,M,X>>)
        requires owner.wf(),owner.baseline().cleanup_state().live(id),owner.histories().contains_key(id),owner.terminal().contains_key(id),
            self.start().owner().owns(&owner.baseline()),
            self.completed(),self.effects_before_return(),self.episode_interval(),self.endpoint_source(),
            self.result->Ok_0.witnessed(),self.result->Ok_0.recovery_history(),
            self.retained_recovery(owner.baseline(),id,offset),managed::retained(self.result->Ok_0.steps@,owner.baseline(),id,offset),
            trajectory::linked(owner.histories()[id].events(),self.completion(),self.return_values(),self.obligations(owner.baseline(),id,offset)),
            self.unload_source(owner.histories()[id].events(),end),
            self.result->Ok_0.registered(owner.baseline().cleanup_state().link(),id),end.cleanup_link()==owner.baseline().cleanup_state().link(),
            self.result->Ok_0.queued_sources(owner.baseline().cleanup_state().queues()[id].link()),
            end.cleanup_checkpoint().is_some(),end.cleanup_checkpoint().unwrap().journal()==end.checkpoint().journal(),
            foreign::covered(owner.histories()[id].events(),self.return_values().dom(),foreign_owners),
            owner.native_children_resolved(ledger),ledger.cut_source(cut),cut.key()==end.native(),
            quiet_after(self.result->Ok_0.steps@,&end.checkpoint(),&cut.joint_spec()),
        ensures self.recovered_values_at_cut(owner.histories()[id].events(),cut)==self.begin_values(),
            owner.native_children_terminal(ledger,cut),self.writes_registered_at_cut(&cut.joint_spec()),
            self.start().recorded(cut.joint_spec().events()),end.recorded(cut.joint_spec().events()),
    {
        foreign::closed_from_owners(owner.histories()[id].events(),self.return_values().dom(),foreign_owners);
        self.unload_recovers_with_children(owner,id,offset,end,ledger,cut);
    }
    /// Production source evidence derives value continuity at the same common
    /// cut. No caller-provided observation equality or foreign success list.
    pub proof fn unload_recovers_from_source_history<C,G,C2,G2,A,R,M,X,V>(&self,tracked owner:&RecordedExecution<C,G,A,R,T,M,X>,
        id:usize,offset:nat,tracked end:&Unload,ledger:&Ledger,cut:&Snapshot<V>,foreign_owners:Map<usize,RecordedExecution<C2,G2,A,R,T,M,X>>)
        requires owner.wf(),owner.baseline().cleanup_state().live(id),owner.histories().contains_key(id),owner.terminal().contains_key(id),
            self.start().owner().owns(&owner.baseline()),
            self.completed(),self.effects_before_return(),self.episode_interval(),self.endpoint_source(),
            self.result->Ok_0.witnessed(),self.result->Ok_0.recovery_history(),
            self.retained_recovery(owner.baseline(),id,offset),managed::retained(self.result->Ok_0.steps@,owner.baseline(),id,offset),
            self.recorded_source(*owner,id,offset),
            self.unload_source(owner.histories()[id].events(),end),
            self.result->Ok_0.registered(owner.baseline().cleanup_state().link(),id),end.cleanup_link()==owner.baseline().cleanup_state().link(),
            self.result->Ok_0.queued_sources(owner.baseline().cleanup_state().queues()[id].link()),
            end.cleanup_checkpoint().is_some(),end.cleanup_checkpoint().unwrap().journal()==end.checkpoint().journal(),
            foreign::covered(owner.histories()[id].events(),self.return_values().dom(),foreign_owners),
            owner.native_children_resolved(ledger),ledger.cut_source(cut),cut.key()==end.native(),
            quiet_after(self.result->Ok_0.steps@,&end.checkpoint(),&cut.joint_spec()),
        ensures self.recovered_values_at_cut(owner.histories()[id].events(),cut)==self.begin_values(),
            owner.native_children_terminal(ledger,cut),self.writes_registered_at_cut(&cut.joint_spec()),
            self.start().recorded(cut.joint_spec().events()),end.recorded(cut.joint_spec().events()),
    {
        self.link_recorded_source(owner,id,offset);
        self.unload_recovers_from_observed_owners(owner,id,offset,end,ledger,cut,foreign_owners);
    }
}
}
