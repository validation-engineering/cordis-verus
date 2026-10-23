//! Paper guards imply concrete administrative admission at a represented cut.
//! The all-row inverse scan is discharged by the real quiescent-journal invariant.
use super::FreshDriver;
#[cfg(verus_keep_ghost)]
use crate::{
    child_history as ch, fresh_semantics as fs, mixed_driver as core,
    mixed_driver::fresh::{programs, Command},
    mixed_grammar as mx, refinement as r, semantics as s, Phase,
};
use vstd::prelude::*;
verus! {
pub open spec fn remove_enabled(a:mx::Configuration<u64,core::Index>,actor:usize)->bool {
    &&& r::removal_domain(a.state.control,actor)
    &&& a.state.tables[actor].is_empty() && ch::remove_unreferenced(mx::kind(a.history),a.state,actor)
}
/// The independent source rule, actual installed shape and finite-machine
/// side conditions used by command completeness. No executable success or
/// proposed replay result is an input to this predicate.
pub open spec fn call(machine:&FreshDriver,bank:Seq<core::Blueprint>,a:mx::Configuration<u64,core::Index>,z:mx::Configuration<u64,core::Index>,t:core::Transition)->bool {
    let label=crate::mixed_driver::fresh::label(t);
    &&& machine.wf() && machine.quiescent_journals() && machine.represents(bank,a)
    &&& fs::well_formed(core::library(),programs(bank),a)
    &&& fs::step(core::library(),programs(bank),a,z,label.0,label.1,label.2)
    &&& crate::mixed_driver::fresh::allocation::payload(t,z) && super::shape::configuration(bank,z)
    &&& match crate::mixed_driver::fresh::allocation::birth_spec(t) {Some(n)=>n==machine.next_id() && machine.next_id()<usize::MAX,None=>true}
    &&& match t {core::Transition::Begin {actor}=>machine.generation_available(actor),core::Transition::Unload {actor}=>machine.cleanup_idle(actor),_=>true}
}
impl FreshDriver {
    /// Combined with `apply`'s exact success domain, this proves one real
    /// command cannot reject when the corresponding source call is admitted.
    pub proof fn source_command_admission(&self,bank:Seq<core::Blueprint>,a:mx::Configuration<u64,core::Index>,z:mx::Configuration<u64,core::Index>,t:core::Transition)
        requires call(self,bank,a,z,t),
        ensures self.command_enabled(t.command()),
    {
        let label=crate::mixed_driver::fresh::label(t);
        match t {
            core::Transition::Insert {actor,parent,blueprint}=>self.source_insert_admission(bank,a,z,actor,parent,blueprint),
            core::Transition::Begin {actor}=>self.source_begin_admission(bank,a,z,actor),
            core::Transition::Step {actor,..}=>self.source_step_admission(bank,a,z,actor,label.1,label.2),
            core::Transition::Unload {actor}=>self.source_unload_admission(bank,a,z,actor),
            _=>self.source_administrative_admission(bank,a,z,label.0,label.1,label.2),
        }
    }
    #[verifier::spinoff_prover]
    pub proof fn source_remove_domain(&self,bank:Seq<core::Blueprint>,a:mx::Configuration<u64,core::Index>,actor:usize)
        requires self.wf(),self.quiescent_journals(),self.represents(bank,a),fs::well_formed(core::library(),programs(bank),a),
        ensures self.remove_enabled(actor)==remove_enabled(a,actor),
    {
        reveal(crate::Kernel::removal_enabled);
        self.inner.kernel.paper_observations(actor);
        assert(self.inner.kernel.paper()==a.state.control);
        assert(self.inner.kernel.registered(actor)==s::registered(a.state,actor));
        assert(self.inner.kernel.is_retired(actor)==(s::registered(a.state,actor) && a.state.control.fibers[actor].retired));
        assert(self.inner.kernel.phase_of(actor)==if s::registered(a.state,actor) {Some(a.state.control.fibers[actor].phase)} else {None});
        assert(self.inner.kernel.removal_enabled(actor)==r::removal_domain(a.state.control,actor));
        assert(self.remove_enabled(actor)==(self.inner.kernel.removal_enabled(actor) && self.inner.table(actor).is_empty() && self.inner.unreferenced(actor)));
        if s::registered(a.state,actor) {
            assert(self.inner.table(actor)==a.state.tables[actor]);
            assert(self.inner.unreferenced(actor)==ch::remove_unreferenced(mx::kind(a.history),a.state,actor)) by {
                if self.inner.unreferenced(actor) {
                    assert forall|n:usize,token:nat|s::registered(a.state,n) && a.state.accumulators[n].contains(token)
                        implies mx::kind(a.history)(token)!=Some(actor) by {
                        let i=choose|i:int|0<=i<a.state.accumulators[n].len() && a.state.accumulators[n][i]==token;
                        assert(self.inner.rows[n as int].journal[i].inverse!=(core::Inverse::Child {child:actor}));
                        assert(a.history[token as int].landed.receipt==self.journal(n)[i].model());
                        match self.journal(n)[i].inverse {core::Inverse::Child {..}=>{},_=>{}}
                    }
                }
                if ch::remove_unreferenced(mx::kind(a.history),a.state,actor) {
                    assert forall|n:int,i:int|0<=n<self.inner.rows.len() && 0<=i<self.inner.rows[n].journal.len()
                        implies self.inner.rows[n].journal[i].inverse!=(core::Inverse::Child {child:actor}) by {
                        assert(s::registered(a.state,n as usize));
                        let token=a.state.accumulators[n as usize][i];
                        assert(a.state.accumulators[n as usize].contains(token));
                        assert(a.history[token as int].landed.receipt==self.journal(n as usize)[i].model());
                        assert(mx::kind(a.history)(token)!=Some(actor));
                    }
                }
            }
        }
    }
    /// A real source rule discharges the corresponding input check. This also
    /// covers Divert admission; the synchronous dispatcher performs its plain
    /// departure branch, not the separate admitted-landing API.
    pub proof fn source_administrative_admission(&self,bank:Seq<core::Blueprint>,a:mx::Configuration<u64,core::Index>,z:mx::Configuration<u64,core::Index>,actor:usize,rule:r::Rule,choice:Option<usize>)
        requires self.wf(),self.quiescent_journals(),self.represents(bank,a),fs::well_formed(core::library(),programs(bank),a),
            fs::step(core::library(),programs(bank),a,z,actor,rule,choice),
            rule==r::Rule::Retire || rule==r::Rule::Remove || rule==r::Rule::Divert || rule==r::Rule::Leave,
        ensures self.command_enabled(match rule {r::Rule::Retire=>Command::Retire {actor},r::Rule::Remove=>Command::Remove {actor},_=>Command::Depart {actor}}),
    {
        match rule {
            r::Rule::Remove=>self.source_remove_domain(bank,a,actor),
            r::Rule::Divert | r::Rule::Leave=>{
                self.inner.paper_total(a.state);s::total_targets_agree(a.state,actor,a.state.control.fibers[actor].committed);
            },_=>{},
        }
    }
    #[verifier::spinoff_prover]
    pub proof fn source_begin_admission(&self,bank:Seq<core::Blueprint>,a:mx::Configuration<u64,core::Index>,z:mx::Configuration<u64,core::Index>,actor:usize)
        requires self.wf(),self.represents(bank,a),fs::well_formed(core::library(),programs(bank),a),
            fs::step(core::library(),programs(bank),a,z,actor,r::Rule::Begin,None),self.generation_available(actor),
        ensures self.begin_enabled(actor),
    {
        reveal(crate::Kernel::begin_enabled);reveal(crate::Kernel::unavailable);
        self.inner.kernel.paper_observations(actor);self.inner.paper_total(a.state);
        let view=z.state.control.fibers[actor].committed;s::total_targets_agree(a.state,actor,view);
        assert(r::target(self.control(),actor,view));
        assert(!self.inner.kernel.unavailable(actor)) by {
            if self.inner.kernel.unavailable(actor) {
                let k=self.inner.kernel;
                let i=choose|i:int|0<=i<k.declarations.len() && !k.declarations[i].provides && k.declarations[i].owner==actor && !k.has_provider(k.declarations[i].port);
                let port=k.declarations[i].port;
                assert(a.state.control.fibers[actor].dependencies.contains(port));
                let b=choose|b:crate::Binding|view.contains(b) && b.key==port.key && b.realm==port.realm;
                assert(r::publishes(k.paper(),port,b.provider));
                assert(crate::Kernel::node_ok(k.nodes@,b.provider as int));
                assert(k.active_provider(b.provider));
                let j=choose|j:int|0<=j<k.declarations.len() && k.declarations[j].provides && k.declarations[j].owner==b.provider && k.declarations[j].port==port;
                assert(k.has_provider(port));
            }
        }
        assert(self.inner.rows[actor as int].journal.len()==0);
    }
    #[verifier::spinoff_prover]
    pub proof fn source_unload_admission(&self,bank:Seq<core::Blueprint>,a:mx::Configuration<u64,core::Index>,z:mx::Configuration<u64,core::Index>,actor:usize)
        requires self.wf(),self.represents(bank,a),fs::well_formed(core::library(),programs(bank),a),
            fs::step(core::library(),programs(bank),a,z,actor,r::Rule::Unload,None),self.cleanup_idle(actor),
        ensures self.unload_enabled(actor),
    {
        reveal(crate::Kernel::cleanup_enabled);
        let k=self.inner.kernel;k.refines_paper();k.paper_observations(actor);
        assert forall|j:int|0<=j<k.links.len() implies !(k.links[j].live && k.links[j].binding.provider==actor) by {
            if k.links[j].live && k.links[j].binding.provider==actor {
                let link=k.links[j];let owner=link.consumer;
                assert(crate::Kernel::link_ok(k.nodes@,link));k.paper_observations(owner);
                assert(k.binding_recorded(owner,link.binding));
                assert(a.state.control.fibers[owner].committed.contains(link.binding));
                assert(owner!=actor);
                assert(r::relied(a.state.control,actor));
            }
        }
        assert(self.inner.kernel.cleanup_enabled(actor));
        let tokens=a.state.accumulators[actor];let receipts=self.journal(actor);
        assert forall|i:int|0<=i<tokens.len() implies tokens[i]<a.history.len()
            && a.history[tokens[i] as int].landed.receipt==receipts[i].model() && receipts[i].actor==actor by {
            assert(self.inner.rows[actor as int].journal[i].actor==actor);
        }
        core::restore_journal(a.history,tokens,receipts,a.state,actor);
        core::restore_payload(receipts,self.inner.primitive_state(),a.state);
    }

}
}
