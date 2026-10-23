//! A continuous control history maintained by the production lifecycle owner.
//! Values, inverse functions and callback effects are separate observations;
//! this projection never presents their erasure as whole-context refinement.
use super::LifecycleState;
#[cfg(verus_keep_ghost)]
use crate::Phase;
use crate::{refinement as r, Kernel, Port};
use vstd::prelude::*;

verus! {
pub enum Label {
    Paper {actor:usize,rule:r::Rule},
    Restart {actor:usize},
    Declare {actor:usize,port:Port},
    Release {actor:usize,port:Port},
    Dependencies {actor:usize,ports:ISet<Port>},
    Internal,
}
pub open spec fn same_control(a:r::Fiber,z:r::Fiber)->bool {
    a.parent==z.parent && a.retired==z.retired && a.phase==z.phase && a.committed==z.committed
}
/// The dynamic-interface extensions have exact frames; an arbitrary interface
/// rewrite cannot be classified as an extension or as an internal step.
pub open spec fn step(a:r::State,z:r::State,label:Label)->bool {
    match label {
        Label::Paper {actor,rule}=>rule!=r::Rule::Restart && rule!=r::Rule::Stutter && r::step(a,z,actor,rule),
        Label::Restart {actor}=>r::step(a,z,actor,r::Rule::Restart),
        Label::Declare {actor,port}=>r::registered(a,actor) && r::registered(z,actor) && r::frame(a,z,actor)
            && same_control(a.fibers[actor],z.fibers[actor]) && !a.fibers[actor].retired
            && a.fibers[actor].phase!=Phase::Unloading
            && z.fibers[actor].dependencies==a.fibers[actor].dependencies
            && z.fibers[actor].provisions==a.fibers[actor].provisions.insert(port),
        Label::Release {actor,port}=>r::registered(a,actor) && r::registered(z,actor) && r::frame(a,z,actor)
            && same_control(a.fibers[actor],z.fibers[actor])
            && z.fibers[actor].dependencies==a.fibers[actor].dependencies
            && z.fibers[actor].provisions==a.fibers[actor].provisions.remove(port)
            && forall|n:usize,b:crate::Binding| r::registered(a,n) && #[trigger] a.fibers[n].committed.contains(b)
                ==> b.provider!=actor || b.key!=port.key || b.realm!=port.realm,
        Label::Dependencies {actor,ports}=>r::registered(a,actor) && r::registered(z,actor) && r::frame(a,z,actor)
            && same_control(a.fibers[actor],z.fibers[actor]) && !a.fibers[actor].retired
            && a.fibers[actor].phase==Phase::Inactive
            && z.fibers[actor].provisions==a.fibers[actor].provisions && z.fibers[actor].dependencies==ports,
        Label::Internal=>a==z,
    }
}
/// Ordinary incoherence uses L-Divert/L-Leave; a forced coherent withdrawal
/// keeps its explicit Restart classification.
pub open spec fn withdrawal(a:r::State,actor:usize)->Label {
    if !r::coherent(a,actor) && a.fibers[actor].phase==Phase::Loading {Label::Paper {actor,rule:r::Rule::Divert}}
    else if !r::coherent(a,actor) && a.fibers[actor].phase==Phase::Active {Label::Paper {actor,rule:r::Rule::Leave}}
    else {Label::Restart {actor}}
}
pub proof fn withdrawal_classified(a:r::State,z:r::State,actor:usize)
    requires r::step(a,z,actor,r::Rule::Restart),
    ensures step(a,z,withdrawal(a,actor)),
{}
pub struct History {pub states:Seq<r::State>,pub labels:Seq<Label>}
impl History {
    pub open spec fn valid(&self)->bool {
        &&& self.states.len()==self.labels.len()+1
        &&& self.states.first().fibers.dom().is_empty()
        &&& forall|i:int| 0<=i<self.labels.len() ==> #[trigger] step(self.states[i],self.states[i+1],self.labels[i])
    }
    pub open spec fn append(&self,state:r::State,label:Label)->Self {Self {states:self.states.push(state),labels:self.labels.push(label)}}
    pub open spec fn extends(&self,prior:Self)->bool {
        self.labels.len()==prior.labels.len()+1 && self.states.drop_last()==prior.states && self.labels.drop_last()==prior.labels
    }
    pub proof fn extended(&self,state:r::State,label:Label)
        requires self.valid(),step(self.states.last(),state,label),
        ensures self.append(state,label).valid(),self.append(state,label).extends(*self),
    {
        let next=self.append(state,label);
        assert(next.states.drop_last() =~= self.states);assert(next.labels.drop_last() =~= self.labels);
        assert forall|i:int| 0<=i<next.labels.len() implies #[trigger] step(next.states[i],next.states[i+1],next.labels[i]) by {
            if i<self.labels.len() {assert(step(self.states[i],self.states[i+1],self.labels[i]));}
        }
    }
    pub open spec fn base_only(&self)->bool {
        forall|i:int| 0<=i<self.labels.len() ==> match #[trigger] self.labels[i] {Label::Paper {..}|Label::Internal=>true,_=>false}
    }
    pub open spec fn paper_labels(&self)->Seq<(usize,r::Rule)> {
        self.labels.map(|_:int,label:Label| match label {Label::Paper {actor,rule}=>(actor,rule),_=>(0,r::Rule::Stutter)})
    }
    /// Only histories without explicit extensions enter the strict paper
    /// closure. An extension can never be hidden by labelling it Stutter.
    pub proof fn strict_paper_trace(&self)
        requires self.valid(),self.base_only(),
        ensures r::execution(self.states,self.paper_labels(),false),r::reaches(self.states.first(),self.states.last(),self.labels.len(),false),
    {
        assert forall|i:int| 0<=i<self.labels.len() implies r::labelled_step(self.states[i],self.states[i+1],self.paper_labels()[i],false) by {
            assert(step(self.states[i],self.states[i+1],self.labels[i]));
        }
        r::finite_execution_refines(self.states,self.paper_labels(),false);
    }
}
impl LifecycleState {
    pub open spec fn control_history_valid(&self)->bool {
        self.control_history().valid() && self.control_history().states.last()==self.control().paper()
    }
    pub proof fn control_history_correspondence(&self)
        requires self.wf(),
        ensures self.control_history_valid(),
            self.control_history().base_only() ==> r::execution(self.control_history().states,self.control_history().paper_labels(),false)
                && r::reaches(self.control_history().states.first(),self.control().paper(),self.control_history().labels.len(),false),
    {if self.control_history().base_only() {self.control_history().strict_paper_trace();}}
    pub(super) proof fn record_control(tracked &mut self,before:r::State,label:Label)
        requires old(self).control().wf(),old(self).protocol().wf(),old(self).history@.valid(),
            old(self).history@.states.last()==before,step(before,old(self).control().paper(),label),
        ensures final(self).wf(),final(self).control()==old(self).control(),final(self).protocol()==old(self).protocol(),
            final(self).control_history()==old(self).control_history().append(old(self).control().paper(),label),
            final(self).control_history().extends(old(self).control_history()),
    {
        self.history@.extended(self.control().paper(),label);
        self.history=Ghost(self.history@.append(self.control().paper(),label));
    }
}

impl Kernel {
    pub proof fn interface_history(&self,prior:&Self,label:Label)
        requires self.same_control(prior),self.same_bindings(prior),
            match label {
                Label::Declare {actor,port}=>prior.registered(actor) && !prior.is_retired(actor)
                    && prior.phase_of(actor)!=Some(Phase::Unloading) && self.declares_provision(actor,port)
                    && self.other_interfaces_preserved(prior,actor,port),
                Label::Release {actor,port}=>prior.registered(actor) && !self.declares_provision(actor,port)
                    && self.other_interfaces_preserved(prior,actor,port)
                    && forall|n:usize,b:crate::Binding| #[trigger] prior.binding_recorded(n,b)
                        ==> b.provider!=actor || b.key!=port.key || b.realm!=port.realm,
                _=>false,
            },
        ensures step(prior.paper(),self.paper(),label),
    {
        reveal(Kernel::same_control);reveal(Kernel::same_bindings);reveal(Kernel::paper);reveal(Kernel::paper_fiber);reveal(Kernel::binding_recorded);reveal(Kernel::other_interfaces_preserved);
        reveal(Kernel::registered);reveal(Kernel::is_retired);reveal(Kernel::phase_of);reveal(Kernel::declares_provision);
        let actor=match label {Label::Declare {actor,..}|Label::Release {actor,..}|Label::Dependencies {actor,..}=>actor,_=>0};
        assert(r::frame(prior.paper(),self.paper(),actor)) by {
            assert forall|n:usize| n!=actor implies r::registered(prior.paper(),n)==r::registered(self.paper(),n)
                && (r::registered(prior.paper(),n) ==> prior.paper().fibers[n]==self.paper().fibers[n]) by {
                if r::registered(prior.paper(),n) {
                assert(prior.paper().fibers[n].dependencies =~= self.paper().fibers[n].dependencies);
                assert(prior.paper().fibers[n].provisions =~= self.paper().fibers[n].provisions);
                assert(prior.paper().fibers[n].committed =~= self.paper().fibers[n].committed);
                }
            }
        }
        assert(prior.paper().fibers[actor].committed =~= self.paper().fibers[actor].committed);
        assert(prior.paper().fibers[actor].dependencies =~= self.paper().fibers[actor].dependencies);
        match label {
            Label::Declare {port,..}=>{assert(self.paper().fibers[actor].provisions =~= prior.paper().fibers[actor].provisions.insert(port));},
            Label::Release {port,..}=>{assert(self.paper().fibers[actor].provisions =~= prior.paper().fibers[actor].provisions.remove(port));},
            _=>{},
        }
    }
    pub proof fn dependencies_history(&self,prior:&Self,actor:usize,ports:Seq<Port>)
        requires prior.registered(actor),!prior.is_retired(actor),prior.phase_of(actor)==Some(Phase::Inactive),
            self.pending_dependencies_configured(prior,actor,ports),
        ensures step(prior.paper(),self.paper(),Label::Dependencies {actor,ports:ports.to_set().to_iset()}),
    {
        reveal(Kernel::pending_dependencies_configured);reveal(Kernel::paper);reveal(Kernel::paper_fiber);reveal(Kernel::binding_recorded);reveal(Kernel::registered);
        reveal(Kernel::is_retired);reveal(Kernel::phase_of);
        assert(r::frame(prior.paper(),self.paper(),actor)) by {
            assert forall|n:usize| n!=actor implies r::registered(prior.paper(),n)==r::registered(self.paper(),n)
                && (r::registered(prior.paper(),n) ==> prior.paper().fibers[n]==self.paper().fibers[n]) by {
                if r::registered(prior.paper(),n) {
                assert(prior.paper().fibers[n].dependencies =~= self.paper().fibers[n].dependencies);
                assert(prior.paper().fibers[n].provisions =~= self.paper().fibers[n].provisions);
                assert(prior.paper().fibers[n].committed =~= self.paper().fibers[n].committed);
                }
            }
        }
        assert(prior.paper().fibers[actor].committed =~= self.paper().fibers[actor].committed);
        assert(prior.paper().fibers[actor].provisions =~= self.paper().fibers[actor].provisions);
        assert(self.paper().fibers[actor].dependencies =~= ports.to_set().to_iset());
    }
}
}
