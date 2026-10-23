//! Protected execution over real Bank allocations. All entry failures retain
//! the original owner; every successful lock acquisition is explicitly released.
use super::super::interleaving::history::lifecycle::RecordedExecution;
pub use super::super::protected_typed::Error as TypedError;
use super::super::{
    protected::{Binding, Context},
    Owner, Slot,
};
use super::{
    bank::Bank, batch::Provider, Destination, ManagedRuntime, Source, StartError, TargetRun,
};
use super::{inputs, keys, same_ports};
#[cfg(verus_keep_ghost)]
use super::{transport, Function};
use crate::lifecycle_state::registration::PluginDefinition;
use crate::lifecycle_state::services::NativeEpisode;
use crate::reversible_value::function::Body;
use crate::reversible_value::{effect::ScalarEffect, slot, ReversibleValue};
use crate::Port;
use vstd::prelude::*;

verus! {
broadcast use vstd::seq_lib::group_seq_properties;
pub ghost struct Interval<T:?Sized> {
    pub before:Seq<crate::reversible_value::ValueState>,pub after:Seq<crate::reversible_value::ValueState>,
    pub routes:Seq<usize>,pub steps:Seq<super::super::Step<T>>,
}
impl<T:?Sized> Interval<T> {
    pub(crate) proof fn establish(&self)
        requires super::super::protected::execution(self.before,self.routes,self.steps),self.after==super::super::protected::after(self.before,self.routes,self.steps),
        ensures self.wf(),
    {}

    pub closed spec fn wf(&self)->bool {
        super::super::protected::execution(self.before,self.routes,self.steps)
            && self.after==super::super::protected::after(self.before,self.routes,self.steps)
    }
}
pub open spec fn result_steps<T:?Sized>(result:Result<super::super::Report<T>,super::super::AdmissionError>)->Seq<super::super::Step<T>> {
    match result {Ok(report)=>report.steps@,Err(_)=>Seq::empty()}
}
pub(crate) struct Storage {pub values:Vec<ReversibleValue>,pub slots:Vec<slot::Slot>}
pub(crate) open spec fn mapped<T:?Sized>(bank:&Bank<T>,routes:Seq<usize>,steps:Seq<super::super::Step<T>>)->bool {
    forall|i:int|0<=i<steps.len() ==> {
        let s=#[trigger] steps[i];
        &&& s.pc<routes.len() && routes[s.pc as int]<bank.len_spec()
        &&& bank.mapping().contains_pair(s.address(),bank.target_address(routes[s.pc as int] as int))
    }
}
pub(crate) proof fn mapped_append<T:?Sized>(bank:&Bank<T>,routes:Seq<usize>,steps:Seq<super::super::Step<T>>,s:super::super::Step<T>)
    requires mapped(bank,routes,steps),s.pc<routes.len(),routes[s.pc as int]<bank.len_spec(),
        bank.mapping().contains_pair(s.address(),bank.target_address(routes[s.pc as int] as int)),
    ensures mapped(bank,routes,steps.push(s)),
{
    assert forall|i:int|0<=i<steps.push(s).len() implies {
        let x=#[trigger] steps.push(s)[i];
        &&& x.pc<routes.len() && routes[x.pc as int]<bank.len_spec()
        &&& bank.mapping().contains_pair(x.address(),bank.target_address(routes[x.pc as int] as int))
    } by {if i<steps.len() {} else {}}
}
impl Storage {
    pub(crate) proof fn acquire_ready<T:?Sized>(&self,bank:&Bank<T>)
        requires self.matches(bank),
        ensures self.values.len()==self.slots.len(),
            forall|i:int|0<=i<self.slots.len() ==> *self.slots@[i].initial()==self.values@[i],
            forall|i:int,j:int|0<=i<j<self.values.len() ==> self.values@[i]!=self.values@[j],
    {
        assert forall|i:int|0<=i<self.slots.len() implies *self.slots@[i].initial()==self.values@[i] by {assert(bank.target(i) is Scalar);}
    }

    pub(crate) open spec fn matches<T:?Sized>(&self,bank:&Bank<T>)->bool {
        self.values.len()==bank.len_spec() && self.slots.len()==self.values.len()
            && (forall|i:int|0<=i<self.values.len() ==> (#[trigger] bank.target(i)) is Scalar && self.values@[i]==bank.target(i)->Scalar_0
                && bank.service(i).managed()==Some(self.slots@[i]) && *self.slots@[i].initial()==self.values@[i])
            && (forall|i:int,j:int|0<=i<j<self.values.len() ==> self.values@[i]!=self.values@[j])
    }
}
#[derive(Debug)]
pub enum Error {NotScalar,NotControlled,Mixed(super::mixed::Error),Typed(super::super::protected_typed::Error),Binding {pc:usize},
    ChangedSlot {index:usize},SourceState {step:usize}}
impl<'a> Context<'a> {
    pub(crate) open spec fn bank<T:?Sized>(&self,bank:&Bank<T>)->bool {
        self.targets().len()==bank.len_spec() && self.slot_names().len()==bank.len_spec()
            && (forall|i:int|0<=i<bank.len_spec() ==> {
                &&& (#[trigger] bank.target(i)) is Scalar
                &&& self.targets()[i]==bank.target(i)->Scalar_0
                &&& bank.service(i).managed()==Some(self.slot_names()[i])
            })
    }
    pub(crate) proof fn bank_entry<T:?Sized>(&self,bank:&Bank<T>,i:int)
        requires self.bank(bank),0<=i<bank.len_spec(),
        ensures bank.target(i) is Scalar,self.targets()[i]==bank.target(i)->Scalar_0,bank.service(i).managed()==Some(self.slot_names()[i]),
    {}
    pub(crate) proof fn bank_frame<T:?Sized>(&self,prior:&Self,bank:&Bank<T>)
        requires prior.bank(bank),self.targets()==prior.targets(),self.slot_names()==prior.slot_names(),
        ensures self.bank(bank),
    {
        assert forall|i:int|0<=i<bank.len_spec() implies bank.target(i) is Scalar && self.targets()[i]==bank.target(i)->Scalar_0
            && bank.service(i).managed()==Some(self.slot_names()[i]) by {
            prior.bank_entry(bank,i);
        }
    }
    /// Check the retained source operands against the held heap before the
    /// first target write. The checker invokes no effect and mutates no cell.
    #[verifier::rlimit(12)]
    pub(crate) fn check_source<E:ScalarEffect+Copy,T:?Sized>(&self,source:&Source<E,T>,bank:&Bank<T>)->(out:Result<(),Error>)
        requires self.wf(),self.bank(bank),bank.wf(),source.wf(),source.original().succeeded(),
            forall|i:int|0<=i<source.input_spec().len() ==> source.input_spec()[i].identity_spec().namespace()==bank.namespace(),
            super::super::protected::kernel_only(source.program().code()),
        ensures out.is_ok() ==> mapped(bank,self.routes(),source.original().result->Ok_0.steps@)
            && super::super::protected::plan(source.program().code(),source.original().result->Ok_0.steps@)
            && super::super::protected::execution(self.states(),self.routes(),source.original().result->Ok_0.steps@),
    {
        hide(crate::reversible_value::joint::valid);hide(crate::reversible_value::joint::step);hide(Source::wf);
        proof {source.closed_plan();}
        let inputs=source.inputs();
        let mut values=self.values();let mut i=0;
        proof {assert(source.original().result->Ok_0.steps@.take(0) =~= Seq::empty());super::super::protected::empty::<T>(self.states(),self.routes());}
        while i<inputs.len()
            invariant inputs@==source.input_spec(),inputs::captured(inputs@,source.original().result),
                super::super::protected::plan(source.program().code(),source.original().result->Ok_0.steps@),self.wf(),self.bank(bank),bank.wf(),source.wf(),source.original().succeeded(),
                forall|j:int|0<=j<inputs.len() ==> inputs@[j].identity_spec().namespace()==bank.namespace(),super::super::protected::kernel_only(source.program().code()),
                i<=inputs.len(),values.len()==self.states().len(),
                mapped(bank,self.routes(),source.original().result->Ok_0.steps@.take(i as int)),
                values@==super::super::protected::after(self.states(),self.routes(),source.original().result->Ok_0.steps@.take(i as int)),
                super::super::protected::execution(self.states(),self.routes(),source.original().result->Ok_0.steps@.take(i as int)),
            decreases inputs.len()-i,
        {
            let input=&inputs[i];let pc=input.pc();
            let index=match self.route(pc) {Some(index)=>index,None=>return Err(Error::SourceState {step:i})};
            let mapped=match bank.find(input) {Some(mapped)=>mapped,None=>return Err(Error::SourceState {step:i})};
            if mapped!=index {return Err(Error::SourceState {step:i});}
            proof {assert(mapped==index);bank.mapping_entry(mapped as int);assert(bank.mapping().contains_pair(input.source().address(),bank.target_address(index as int)));}
            let expected=match input.operand() {inputs::Operand::Scalar(v)=>v,_=>return Err(Error::SourceState {step:i})};
            if values[index].value!=expected.value || values[index].depth!=expected.depth {return Err(Error::SourceState {step:i});}
            proof {assert(values@[index as int]==*expected);}
            let after=match input.scalar_output() {Some(value)=>value,None=>return Err(Error::SourceState {step:i})};
            proof {
                let steps=source.original().result->Ok_0.steps@;
                super::super::protected::append(self.states(),self.routes(),steps.take(i as int),steps[i as int]);
                mapped_append(bank,self.routes(),steps.take(i as int),steps[i as int]);
                assert(steps.take(i as int).push(steps[i as int]) =~= steps.take(i as int+1));
            }
            values.set(index,after);i+=1;
        }
        proof {
            let steps=source.original().result->Ok_0.steps@;assert(steps.take(i as int) =~= steps);
        }

        Ok(())
    }
    /// Resolve actual episode-committed imports against the bank publications.
    /// This does not recapture a slot lock already held by this context.
    #[verifier::rlimit(12)]
    pub(crate) fn bind_episode<E,T:?Sized>(&mut self,episode:&NativeEpisode<Slot<T,()>>,ports:&[Port],_bank:&Bank<T>,providers:&[Provider<E,T>])->(out:Result<(),Error>)
        requires old(self).wf(),old(self).bank(_bank),_bank.wf(),episode.wf(),
            super::selection::providers_match(_bank,providers@,episode.capture().sources),
        ensures final(self).wf(),final(self).targets()==old(self).targets(),final(self).states()==old(self).states(),
            final(self).slot_names()==old(self).slot_names(),final(self).chosen()==old(self).chosen(),final(self).bank(_bank),
            out.is_ok() ==> final(self).supports(*episode,ports@),
    {
        let mut bindings:Vec<Binding>=Vec::new();let mut i=0;
        while i<ports.len()
            invariant *self==*old(self),self.wf(),self.bank(_bank),_bank.wf(),episode.wf(),i<=ports.len(),bindings.len()==i,
                super::selection::providers_match(_bank,providers@,episode.capture().sources),
                forall|j:int|0<=j<bindings.len() ==> (#[trigger] bindings@[j]).slot<self.slot_names().len()
                    && bindings@[j].port==ports@[j] && !episode.closed()
                    && episode.selects_slot(bindings@[j].provider,bindings@[j].port,self.slot_names()[bindings@[j].slot as int]),
            decreases ports.len()-i,
        {
            let port=ports[i];
            if episode.declares(port) {return Err(Error::Binding {pc:i});}
            let (id,_selected)=match episode.read(port) {Ok(pair)=>pair,Err(_)=>return Err(Error::Binding {pc:i})};
            let mut p=0;let mut found:Option<usize>=None;
            while p<providers.len()
                invariant p<=providers.len(),found.is_some() ==> found.unwrap()<providers.len() && providers@[found.unwrap() as int].id==id && providers@[found.unwrap() as int].port==port,
                decreases providers.len()-p,
            {
                if providers[p].id==id && providers[p].port==port {found=Some(p);break;}p+=1;
            }
            let n=match found {Some(n)=>n,None=>return Err(Error::Binding {pc:i})};
            let provider=&providers[n];
            proof {
                assert(provider.id==id && provider.port==port);
                assert(episode.capture().sources[id].values.contains_pair((port.key,port.realm),_bank.service(provider.index as int)));
                assert(episode.capture().imports[(id,port.key,port.realm)]==_bank.service(provider.index as int));
                self.bank_entry(_bank,provider.index as int);
                assert(_bank.target(provider.index as int) is Scalar);
                assert(_bank.service(provider.index as int).managed()==Some(self.slot_names()[provider.index as int]));
                assert(episode.selects_slot(id,port,self.slot_names()[provider.index as int]));
            }
            bindings.push(Binding {provider:id,port,slot:provider.index});i+=1;
        }
        // Empty programs still require an open native episode.
        if episode.is_closed() {return Err(Error::Binding {pc:0});}
        self.bind(bindings);proof {self.bank_frame(old(self),_bank);}Ok(())
    }
}
pub enum Start<T:?Sized,C=()> {
    Before(StartError<()>),
    After {id:usize,owner:Box<RecordedExecution<C,(),(),(),T,(),()>>,error:Error},
}
impl<E:ScalarEffect+Copy,T:?Sized> Source<E,T> {
    pub(crate) proof fn closed_plan(&self)
        requires self.wf(),self.original().succeeded(),super::super::protected::kernel_only(self.program().code()),
        ensures super::super::protected::plan(self.program().code(),self.original().result->Ok_0.steps@),
    {
        hide(crate::reversible_value::joint::valid);hide(crate::reversible_value::joint::step);reveal(super::super::protected::plan);
        let code=self.program().code();let steps=self.original().result->Ok_0.steps@;
        assert forall|i:int|0<=i<steps.len() implies {
            let s=#[trigger] steps[i];
            &&& s.result is Scalar && Some(s.pc)==super::super::next(code.len(),steps.take(i))
            &&& super::transport::step(code,s)
        } by {assert(super::transport::step(code,steps[i]));assert(code[steps[i].pc as int].effect is Kernel);}
    }

    pub fn typed_only(&self)->(out:bool) requires self.wf(),ensures out==super::super::protected_typed::typed_only(self.program().code()),
    {self.function.is_typed_only()}
    pub fn kernel_only(&self)->(out:bool) requires self.wf(),ensures out==super::super::protected::kernel_only(self.program().code()),
    {self.function.is_kernel_only()}
    #[verifier::rlimit(12)]
    pub(crate) fn instantiate_protected<P>(&self,runtime:&mut ManagedRuntime<P,(),E,T,()>,destination:Destination<()>,bank:&Bank<T>,providers:&[Provider<E,T>],mode:&mut Option<Context<'_>>)
        ->(out:Result<super::batch::Run<E,T>,Start<T>>)
        requires self.wf(),old(runtime).wf(),bank.wf(),old(mode).is_some(),old(mode)->Some_0.wf(),old(mode)->Some_0.bank(bank),
            super::selection::providers_match(bank,providers@,crate::lifecycle_state::services::capture::sources(old(runtime).publications().entries())),
            super::super::protected::kernel_only(self.program().code()),self.original().succeeded(),
            forall|i:int|0<=i<self.input_spec().len() ==> self.input_spec()[i].identity_spec().namespace()==bank.namespace(),
        ensures out.is_ok() && out->Ok_0.report->Ok_0.result.is_ok() ==> out->Ok_0.scalar_replay_matches(self,bank),
            out.is_ok() && out->Ok_0.report->Ok_0.result.is_ok() ==>
                out->Ok_0.report->Ok_0.result->Ok_0.failure.is_none()
                && super::super::protected::same(out->Ok_0.report->Ok_0.result->Ok_0.steps@,self.original().result->Ok_0.steps@),
            out.is_ok() && out->Ok_0.report->Ok_0.result.is_ok() ==>
                super::super::protected::execution(old(mode)->Some_0.states(),final(mode)->Some_0.routes(),out->Ok_0.report->Ok_0.result->Ok_0.steps@)
                && final(mode)->Some_0.states()==super::super::protected::after(old(mode)->Some_0.states(),final(mode)->Some_0.routes(),out->Ok_0.report->Ok_0.result->Ok_0.steps@),
            out.is_ok() && out->Ok_0.report->Ok_0.result.is_err() ==> final(mode)->Some_0.states()==old(mode)->Some_0.states(),
            final(mode).is_some(),final(mode)->Some_0.wf(),final(mode)->Some_0.bank(bank),final(mode)->Some_0.targets()==old(mode)->Some_0.targets(),
            final(mode)->Some_0.slot_names()==old(mode)->Some_0.slot_names(),final(mode)->Some_0.chosen()==old(mode)->Some_0.chosen(),
            out.is_err() ==> final(mode)->Some_0.states()==old(mode)->Some_0.states(),
            final(runtime).publications()==old(runtime).publications(),
            out.is_ok() ==> out->Ok_0.owner.baseline().value_state().is_some()
                && out->Ok_0.owner.baseline().value_state().unwrap().capture().sources==crate::lifecycle_state::services::capture::sources(old(runtime).publications().entries())
                && out->Ok_0.owner.baseline().value_state().unwrap().provisions()==self.provision_ports(),
            final(runtime).wf(),final(runtime).journal_spec()==old(runtime).journal_spec(),
            out.is_ok() ==> out->Ok_0.report.is_ok(),
            out.is_ok() ==> out->Ok_0.from_source(self),
            out.is_ok() ==> out->Ok_0.report->Ok_0.completion().journal()==old(runtime).journal_spec(),
            out.is_ok() ==> out->Ok_0.report->Ok_0.work.domain_id()==destination.work_domain,
            out.is_ok() ==> out->Ok_0.report->Ok_0.work!=self.original().work,
            out.is_ok() ==> out->Ok_0.report->Ok_0.origin!=self.original().origin,
    {
        let mut typed=None;
        self.instantiate_guarded(runtime,destination,bank,providers,mode,&mut typed)
    }
    #[verifier::rlimit(12)]
    pub(crate) fn instantiate_guarded<P>(&self,runtime:&mut ManagedRuntime<P,(),E,T,()>,destination:Destination<()>,bank:&Bank<T>,providers:&[Provider<E,T>],mode:&mut Option<Context<'_>>,typed:&mut Option<super::super::protected_typed::Context<'_,T,()>>)
        ->(out:Result<super::batch::Run<E,T>,Start<T>>)
        requires self.wf(),old(runtime).wf(),bank.wf(),old(mode).is_some() || old(typed).is_some(),
            old(mode).is_some() ==> old(mode)->Some_0.wf() && old(mode)->Some_0.bank(bank),
            old(typed).is_some() ==> old(mode).is_none() && old(typed)->Some_0.wf() && old(typed)->Some_0.bank(bank)
                && super::super::protected_typed::typed_only(self.program().code()),
            super::selection::providers_match(bank,providers@,crate::lifecycle_state::services::capture::sources(old(runtime).publications().entries())),
            old(mode).is_some() ==> super::super::protected::kernel_only(self.program().code()),self.original().succeeded(),
            forall|i:int|0<=i<self.input_spec().len() ==> self.input_spec()[i].identity_spec().namespace()==bank.namespace(),
        ensures final(typed).is_some()==old(typed).is_some(),
            final(typed).is_some() ==> final(typed)->Some_0.wf() && final(typed)->Some_0.bank(bank)
                && final(typed)->Some_0.targets()==old(typed)->Some_0.targets() && final(typed)->Some_0.slots()==old(typed)->Some_0.slots()
                && (out.is_err() || out->Ok_0.report->Ok_0.result.is_err() ==> final(typed)->Some_0.states()==old(typed)->Some_0.states() && final(typed)->Some_0.revisions()==old(typed)->Some_0.revisions())
                && (out.is_ok() && out->Ok_0.report->Ok_0.result.is_ok() ==> out->Ok_0.report->Ok_0.result->Ok_0.failure.is_none()
                    && mapped(bank,final(typed)->Some_0.routes(),self.original().result->Ok_0.steps@)
                    && super::super::protected_typed::addressed(old(typed)->Some_0.targets(),final(typed)->Some_0.routes(),out->Ok_0.report->Ok_0.result->Ok_0.steps@)
                    && super::super::protected_typed::execution(old(typed)->Some_0.states(),old(typed)->Some_0.revisions(),final(typed)->Some_0.routes(),out->Ok_0.report->Ok_0.result->Ok_0.steps@)
                    && final(typed)->Some_0.states()==super::super::protected_typed::after(old(typed)->Some_0.states(),final(typed)->Some_0.routes(),out->Ok_0.report->Ok_0.result->Ok_0.steps@)
                    && final(typed)->Some_0.revisions()==super::super::protected_typed::clocks(old(typed)->Some_0.revisions(),final(typed)->Some_0.routes(),out->Ok_0.report->Ok_0.result->Ok_0.steps@)),
            old(mode).is_some() && out.is_ok() && out->Ok_0.report->Ok_0.result.is_ok() ==> out->Ok_0.scalar_replay_matches(self,bank),
            old(mode).is_some() && out.is_ok() && out->Ok_0.report->Ok_0.result.is_ok() ==>
                out->Ok_0.report->Ok_0.result->Ok_0.failure.is_none()
                && super::super::protected::same(out->Ok_0.report->Ok_0.result->Ok_0.steps@,self.original().result->Ok_0.steps@),
            old(mode).is_some() && out.is_ok() && out->Ok_0.report->Ok_0.result.is_ok() ==>
                super::super::protected::execution(old(mode)->Some_0.states(),final(mode)->Some_0.routes(),out->Ok_0.report->Ok_0.result->Ok_0.steps@)
                && final(mode)->Some_0.states()==super::super::protected::after(old(mode)->Some_0.states(),final(mode)->Some_0.routes(),out->Ok_0.report->Ok_0.result->Ok_0.steps@),
            old(mode).is_some() && out.is_ok() && out->Ok_0.report->Ok_0.result.is_err() ==> final(mode)->Some_0.states()==old(mode)->Some_0.states(),
            final(mode).is_some()==old(mode).is_some(),
            final(mode).is_some() ==> final(mode)->Some_0.wf() && final(mode)->Some_0.bank(bank) && final(mode)->Some_0.targets()==old(mode)->Some_0.targets()
                && final(mode)->Some_0.slot_names()==old(mode)->Some_0.slot_names() && final(mode)->Some_0.chosen()==old(mode)->Some_0.chosen()
                && (out.is_err() ==> final(mode)->Some_0.states()==old(mode)->Some_0.states()),
            final(runtime).publications()==old(runtime).publications(),
            out.is_ok() ==> out->Ok_0.owner.baseline().value_state().is_some()
                && out->Ok_0.owner.baseline().value_state().unwrap().capture().sources==crate::lifecycle_state::services::capture::sources(old(runtime).publications().entries())
                && out->Ok_0.owner.baseline().value_state().unwrap().provisions()==self.provision_ports(),
            final(runtime).wf(),final(runtime).journal_spec()==old(runtime).journal_spec(),
            out.is_ok() ==> out->Ok_0.report.is_ok(),
            out.is_ok() ==> out->Ok_0.from_source(self),
            out.is_ok() ==> out->Ok_0.report->Ok_0.completion().journal()==old(runtime).journal_spec(),
            out.is_ok() ==> out->Ok_0.report->Ok_0.work.domain_id()==destination.work_domain,
            out.is_ok() ==> out->Ok_0.report->Ok_0.work!=self.original().work,
            out.is_ok() ==> out->Ok_0.report->Ok_0.origin!=self.original().origin,
    {
        let mut mixed=None;
        self.instantiate_all(runtime,destination,bank,providers,mode,typed,&mut mixed,None,None,None,None)
    }
    #[verifier::rlimit(20)]
    #[verifier::spinoff_prover]
    // The real owners, storage catalogs and erased proof inputs are distinct. The type records the native owner and each cleanup payload category.
    #[allow(clippy::too_many_arguments,clippy::type_complexity)]
    pub(crate) fn instantiate_all<P,C>(&self,runtime:&mut ManagedRuntime<P,(),E,T,()>,destination:Destination<()>,bank:&Bank<T>,providers:&[Provider<E,T>],mode:&mut Option<Context<'_>>,typed:&mut Option<super::super::protected_typed::Context<'_,T,()>>,mixed:&mut Option<super::super::protected_mixed::Context<'_,T,()>>,storage:Option<&super::mixed::Storage<T>>,catalog:Option<(&super::slots::Slots<T>,&super::slots::storage::Storage,&[super::services::Service<T>],&[super::services::Preload<T>])>,child:Option<&crate::lifecycle_state::registration::shared_child::SharedChild>,existing:Option<usize>)
        ->(out:Result<TargetRun<C,(),(),(),T,(),(),E>,Start<T,C>>)
        requires self.wf(),old(runtime).wf(),bank.wf(),child.is_some() ==> child.unwrap().wf(),old(mode).is_some() || old(typed).is_some() || old(mixed).is_some(),
            old(mixed).is_some() ==> old(mode).is_none() && old(typed).is_none() && old(mixed)->Some_0.wf()
                && storage.is_some() && storage.unwrap().matches(bank) && storage.unwrap().held(&old(mixed)->Some_0) && self.program().controlled()
                && (catalog.is_none() ==> storage.unwrap().original_slots(&old(mixed)->Some_0)),
            old(mode).is_some() ==> old(mode)->Some_0.wf() && old(mode)->Some_0.bank(bank),
            old(typed).is_some() ==> old(mode).is_none() && old(typed)->Some_0.wf() && old(typed)->Some_0.bank(bank)
                && super::super::protected_typed::typed_only(self.program().code()),
            catalog.is_none() ==> super::selection::providers_match(bank,providers@,crate::lifecycle_state::services::capture::sources(old(runtime).publications().entries())),
            catalog.is_some() ==> old(mixed).is_some() && catalog.unwrap().0.wf(bank)
                && catalog.unwrap().1.matches(storage.unwrap(),bank,catalog.unwrap().0) && catalog.unwrap().1.held(&old(mixed)->Some_0)
                && super::services::published(bank,catalog.unwrap().0,catalog.unwrap().2@,crate::lifecycle_state::services::capture::sources(old(runtime).publications().entries()))
                && forall|i:int|0<=i<catalog.unwrap().3.len() ==> (#[trigger] catalog.unwrap().3@[i]).wf(bank,catalog.unwrap().0),
            old(mode).is_some() ==> super::super::protected::kernel_only(self.program().code()),self.original().succeeded(),
            forall|i:int|0<=i<self.input_spec().len() ==> self.input_spec()[i].identity_spec().namespace()==bank.namespace(),
        ensures out.is_ok() && catalog.is_some() ==> super::services::preloaded(catalog.unwrap().3@,out->Ok_0.owner.baseline().value_state().unwrap())
                && out->Ok_0.owner.core().value_state().is_some() && super::services::preloaded(catalog.unwrap().3@,out->Ok_0.owner.core().value_state().unwrap()),
            final(mixed).is_some()==old(mixed).is_some(),
            final(mixed).is_some() ==> final(mixed)->Some_0.wf() && storage.unwrap().held(&final(mixed)->Some_0)
                && final(mixed)->Some_0.scalar->Some_0.slot_names()==old(mixed)->Some_0.scalar->Some_0.slot_names()
                && final(mixed)->Some_0.scalar->Some_0.chosen()==old(mixed)->Some_0.scalar->Some_0.chosen()
                && (catalog.is_some() ==> catalog.unwrap().1.held(&final(mixed)->Some_0))
                && (catalog.is_none() ==> storage.unwrap().original_slots(&final(mixed)->Some_0))
                && (out.is_err() || out->Ok_0.report->Ok_0.result.is_err() ==>
                    final(mixed)->Some_0.scalar->Some_0.states()==old(mixed)->Some_0.scalar->Some_0.states()
                    && final(mixed)->Some_0.payload->Some_0.states()==old(mixed)->Some_0.payload->Some_0.states()
                    && final(mixed)->Some_0.payload->Some_0.revisions()==old(mixed)->Some_0.payload->Some_0.revisions())
                && (out.is_ok() && out->Ok_0.report->Ok_0.result.is_ok() ==>
                    out->Ok_0.report->Ok_0.result->Ok_0.failure.is_none()
                    && super::super::protected_mixed::same(out->Ok_0.report->Ok_0.result->Ok_0.steps@,self.original().result->Ok_0.steps@)
                    && super::mixed::mapped(storage.unwrap(),bank,final(mixed)->Some_0.scalar->Some_0.routes(),final(mixed)->Some_0.payload->Some_0.routes(),self.original().result->Ok_0.steps@)
                    && super::mixed::advanced(&old(mixed)->Some_0,&final(mixed)->Some_0,out->Ok_0.report->Ok_0.result->Ok_0.steps@)),
            final(typed).is_some()==old(typed).is_some(),
            final(typed).is_some() ==> final(typed)->Some_0.wf() && final(typed)->Some_0.bank(bank)
                && final(typed)->Some_0.targets()==old(typed)->Some_0.targets() && final(typed)->Some_0.slots()==old(typed)->Some_0.slots()
                && (out.is_err() || out->Ok_0.report->Ok_0.result.is_err() ==> final(typed)->Some_0.states()==old(typed)->Some_0.states() && final(typed)->Some_0.revisions()==old(typed)->Some_0.revisions())
                && (out.is_ok() && out->Ok_0.report->Ok_0.result.is_ok() ==> out->Ok_0.report->Ok_0.result->Ok_0.failure.is_none()
                    && mapped(bank,final(typed)->Some_0.routes(),self.original().result->Ok_0.steps@)
                    && super::super::protected_typed::addressed(old(typed)->Some_0.targets(),final(typed)->Some_0.routes(),out->Ok_0.report->Ok_0.result->Ok_0.steps@)
                    && super::super::protected_typed::execution(old(typed)->Some_0.states(),old(typed)->Some_0.revisions(),final(typed)->Some_0.routes(),out->Ok_0.report->Ok_0.result->Ok_0.steps@)
                    && final(typed)->Some_0.states()==super::super::protected_typed::after(old(typed)->Some_0.states(),final(typed)->Some_0.routes(),out->Ok_0.report->Ok_0.result->Ok_0.steps@)
                    && final(typed)->Some_0.revisions()==super::super::protected_typed::clocks(old(typed)->Some_0.revisions(),final(typed)->Some_0.routes(),out->Ok_0.report->Ok_0.result->Ok_0.steps@)),
            old(mode).is_some() && out.is_ok() && out->Ok_0.report->Ok_0.result.is_ok() ==> out->Ok_0.scalar_replay_matches(self,bank),
            old(mode).is_some() && out.is_ok() && out->Ok_0.report->Ok_0.result.is_ok() ==>
                out->Ok_0.report->Ok_0.result->Ok_0.failure.is_none()
                && super::super::protected::same(out->Ok_0.report->Ok_0.result->Ok_0.steps@,self.original().result->Ok_0.steps@),
            old(mode).is_some() && out.is_ok() && out->Ok_0.report->Ok_0.result.is_ok() ==>
                super::super::protected::execution(old(mode)->Some_0.states(),final(mode)->Some_0.routes(),out->Ok_0.report->Ok_0.result->Ok_0.steps@)
                && final(mode)->Some_0.states()==super::super::protected::after(old(mode)->Some_0.states(),final(mode)->Some_0.routes(),out->Ok_0.report->Ok_0.result->Ok_0.steps@),
            old(mode).is_some() && out.is_ok() && out->Ok_0.report->Ok_0.result.is_err() ==> final(mode)->Some_0.states()==old(mode)->Some_0.states(),
            final(mode).is_some()==old(mode).is_some(),
            final(mode).is_some() ==> final(mode)->Some_0.wf() && final(mode)->Some_0.bank(bank) && final(mode)->Some_0.targets()==old(mode)->Some_0.targets()
                && final(mode)->Some_0.slot_names()==old(mode)->Some_0.slot_names() && final(mode)->Some_0.chosen()==old(mode)->Some_0.chosen()
                && (out.is_err() ==> final(mode)->Some_0.states()==old(mode)->Some_0.states()),
            final(runtime).publications()==old(runtime).publications(),
            out.is_ok() ==> out->Ok_0.owner.baseline().value_state().is_some()
                && out->Ok_0.owner.baseline().value_state().unwrap().capture().sources==crate::lifecycle_state::services::capture::sources(old(runtime).publications().entries())
                && out->Ok_0.owner.baseline().value_state().unwrap().provisions()==self.provision_ports(),
            final(runtime).wf(),final(runtime).journal_spec()==old(runtime).journal_spec(),
            out.is_ok() ==> out->Ok_0.report.is_ok(),
            out.is_ok() ==> out->Ok_0.from_source(self),
            out.is_ok() ==> out->Ok_0.report->Ok_0.completion().event().after is Recipes
                && out->Ok_0.report->Ok_0.completion().event().after->Recipes_state.entries[out->Ok_0.id].parent==
                    if child.is_some() {Some(child.unwrap().owner())} else {destination.parent},
            out.is_ok() ==> out->Ok_0.report->Ok_0.completion().journal()==old(runtime).journal_spec(),
            out.is_ok() ==> out->Ok_0.report->Ok_0.work.domain_id()==destination.work_domain,
            out.is_ok() ==> out->Ok_0.report->Ok_0.work!=self.original().work,
            out.is_ok() ==> out->Ok_0.report->Ok_0.origin!=self.original().origin,
    {
        hide(crate::reversible_value::joint::valid);hide(crate::reversible_value::joint::step);
        if runtime.lifecycle().domain()==self.origin.domain || destination.work_domain==self.work_domain {
            return Err(Start::Before(StartError::ReusedDomain {host:destination.host}));
        }
        let id=if let Some(id)=existing {
            if runtime.kernel().phase(id)!=Some(crate::Phase::Inactive) {return Err(Start::Before(StartError::Begin {id,error:crate::Error::InvalidState}));}
            let recipe=match runtime.registration(id) {Some(r)=>r,None=>return Err(Start::Before(StartError::Binding {id}))};
            let parent=match child {Some(c)=>Some(c.parent_id()),None=>destination.parent};
            if recipe.parent()!=parent || !same_ports(recipe.dependencies(),self.dependencies.as_slice())
                || !same_ports(recipe.provisions(),self.provisions.as_slice()) {return Err(Start::Before(StartError::Binding {id}));}
            if let Some(child)=child {
                let snapshot=child.snapshot();
                let identity=match snapshot.identity() {Some(i)=>i,None=>return Err(Start::Before(StartError::Binding {id}))};
                if identity.id()!=id {return Err(Start::Before(StartError::Binding {id}));}
            }
            match runtime.replace(id,Body::Managed(self.function.duplicate())) {
                Ok(_)=>{},Err((error,_))=>return Err(Start::Before(StartError::Begin {id,error})),
            }
            id
        } else {
        let definition=PluginDefinition::new(keys(self.dependencies.as_slice()),keys(self.provisions.as_slice()),Body::Managed(self.function.duplicate()));
        let registration=match child {Some(child)=>runtime.register_shared_child(child,self.realms.as_map(),destination.anchor,definition,()).result,None=>runtime.register(destination.parent,self.realms.as_map(),destination.anchor,definition,())};
        match registration {
            Ok(id)=>id,Err((error,_,host))=>return Err(Start::Before(StartError::Registration {error,host})),
        }
        };
        let recipe=match runtime.registration(id) {Some(recipe)=>recipe,None=>{assert(false);panic!("certified managed registration")}};
        let ports=match self.function.bind(recipe) {Ok(p)=>p,Err(_)=>return Err(Start::Before(StartError::Binding {id}))};
        // Matching the complete resolved dependency list also rejects an
        // inherited/aliased environment that cannot be reproduced here.
        if !same_ports(recipe.dependencies(),self.dependencies.as_slice())
            || !same_ports(recipe.provisions(),self.provisions.as_slice())
            || !same_ports(ports.as_slice(),self.original_ports()) {
            return Err(Start::Before(StartError::Binding {id}));
        }
        proof {
            reveal(Function::valid);
            assert(ports@==self.original().ports@);
            assert(recipe.payload() is Managed);
            assert(recipe.payload()->Managed_0.code()==self.program().code());
            assert(recipe.payload()->Managed_0.valid());
            self.function.equal_binding(recipe.payload()->Managed_0,*recipe,ports@);
            assert(recipe.payload()->Managed_0.bound(ports@,*recipe));
        }
        let mut execution:Owner<C,(),(),(),T,(),()>=match runtime.begin_managed_execution(id,destination.work_domain) {
            Ok(owner)=>owner,Err(error)=>return Err(Start::Before(StartError::Begin {id,error})),
        };
        proof {assert(runtime.managed_invocation_ready(id,&execution));}
        if let Some((_,_,_,preloads))=catalog {
            if let Some(pc)=super::services::install(&mut execution,preloads) {
                return Err(Start::After {id,owner:Box::new(RecordedExecution::new(execution)),error:Error::Binding {pc}});
            }
        }
        let episode=execution.native().unwrap();
        if mixed.is_some() {
            let storage=storage.unwrap();
            let binding=match catalog {
                Some((catalog,selected,routes,preloads))=>{
                    let owned=super::services::routes(preloads,id);
                    proof {super::services::routes_owned(bank,catalog,preloads@,owned@,*episode);}
                    selected.bind(mixed.as_mut().unwrap(),episode,ports.as_slice(),self,storage,bank,catalog,routes,owned.as_slice())
                },
                None=>mixed.as_mut().unwrap().bind_mixed(episode,ports.as_slice(),self,bank,storage,providers),
            };
            if let Err(error)=binding {
                return Err(Start::After {id,owner:Box::new(RecordedExecution::new(execution)),error:Error::Mixed(error)});
            }
            if let Err(error)=mixed.as_ref().unwrap().check_mixed(self,bank,storage) {
                return Err(Start::After {id,owner:Box::new(RecordedExecution::new(execution)),error:Error::Mixed(error)});
            }
            if let Err(error)=mixed.as_ref().unwrap().payload.as_ref().unwrap().reserve(self.function.code.len()) {
                return Err(Start::After {id,owner:Box::new(RecordedExecution::new(execution)),error:Error::Typed(error)});
            }
            proof {
                let recipe=runtime.registry().entries()[id].recipe();
                assert forall|other:Seq<Port>|recipe.payload()->Managed_0.bound(other,recipe)
                    implies mixed->Some_0.supports(execution.value_state().unwrap(),other,self.program().code(),self.original().result->Ok_0.steps@) by {
                    recipe.payload()->Managed_0.equal_binding(self.function,recipe,other);
                    self.function.binding_unique(recipe,ports@,other);
                }
                assert(runtime.mixed_protection_ready(id,&execution,&mixed->Some_0,self.original().result->Ok_0.steps@));
            }
        } else if mode.is_some() {
        if let Err(error)=mode.as_mut().unwrap().bind_episode(episode,ports.as_slice(),bank,providers) {
            return Err(Start::After {id,owner:Box::new(RecordedExecution::new(execution)),error});
        }
        if let Err(error)=mode.as_ref().unwrap().check_source(self,bank) {
            return Err(Start::After {id,owner:Box::new(RecordedExecution::new(execution)),error});
        }
        proof {
            let recipe=runtime.registry().entries()[id].recipe();
            assert forall|other:Seq<Port>|recipe.payload()->Managed_0.bound(other,recipe)
                implies mode->Some_0.supports(execution.value_state().unwrap(),other) by {
                recipe.payload()->Managed_0.equal_binding(self.function,recipe,other);
                    self.function.binding_unique(recipe,ports@,other);
            }
            assert(runtime.protection_ready(id,&execution,&mode->Some_0));
        }
        } else {
            if let Err(error)=typed.as_mut().unwrap().bind_episode(episode,ports.as_slice(),bank,providers) {
                return Err(Start::After {id,owner:Box::new(RecordedExecution::new(execution)),error:Error::Typed(error)});
            }
            if let Err(error)=typed.as_ref().unwrap().check_routes(self,bank) {
                return Err(Start::After {id,owner:Box::new(RecordedExecution::new(execution)),error:Error::Typed(error)});
            }
            if let Err(error)=typed.as_ref().unwrap().reserve(self.function.code.len()) {
                return Err(Start::After {id,owner:Box::new(RecordedExecution::new(execution)),error:Error::Typed(error)});
            }
            proof {
                let recipe=runtime.registry().entries()[id].recipe();
                assert forall|other:Seq<Port>|recipe.payload()->Managed_0.bound(other,recipe)
                    implies typed->Some_0.supports(execution.value_state().unwrap(),other) by {
                    recipe.payload()->Managed_0.equal_binding(self.function,recipe,other);
                    self.function.binding_unique(recipe,ports@,other);
                }
                assert(runtime.typed_protection_ready(id,&execution,&typed->Some_0));
            }
        }
        let ghost offset=execution.cleanup_state().queues()[0].slots().len();
        let ghost expected=if mode.is_some() {Some(self.original().result->Ok_0.steps@)} else {None};
        let ghost mixed_expected=if mixed.is_some() {Some(self.original().result->Ok_0.steps@)} else {None};
        let ghost before_mixed=*mixed;
        let (owner,report)=runtime.run_recorded_root_guarded(id,execution,mode,Ghost(expected),typed,mixed,Ghost(mixed_expected));
        proof {if catalog.is_some() {catalog.unwrap().1.held_frame(&before_mixed->Some_0,&mixed->Some_0);}}
        assert(report.is_ok());
        proof {
            if report.is_ok() {
                if report->Ok_0.result.is_ok() {transport::derive(report->Ok_0.function@.code(),report->Ok_0.result->Ok_0,report->Ok_0.ports@,owner.baseline().value_state().unwrap());}
                let actual=report->Ok_0.ports@;
                assert forall|i:int|0<=i<ports.len() implies actual[i]==ports@[i] by {
                    let recipe=runtime.registry().entries()[id].recipe();
                    let a=choose|j:int|0<=j<recipe.dependencies_spec().len() && recipe.dependencies_spec()[j]==actual[i]
                        && forall|k:int|0<=k<j ==> recipe.dependencies_spec()[k].key!=actual[i].key;
                    let b=choose|j:int|0<=j<recipe.dependencies_spec().len() && recipe.dependencies_spec()[j]==ports@[i]
                        && forall|k:int|0<=k<j ==> recipe.dependencies_spec()[k].key!=ports@[i].key;
                    if a<b {assert(recipe.dependencies_spec()[a].key!=ports@[i].key);} else if b<a {assert(recipe.dependencies_spec()[b].key!=actual[i].key);}
                }
                assert(actual =~= ports@);
            }
        }
        proof {
            let r=report->Ok_0;let core=owner.baseline();
            assert(r.completed() && r.episode_interval() && r.effects_before_return());
            assert(r.function@.code()==self.program().code() && r.ports@==self.original().ports@);
            assert(r.origin.id==id && r.work.domain_id()==core.work_state().domain_id());
            assert(r.start().owner().owns(&core) && core.execution_journal()==Some(r.completion().journal()));
            assert(owner.recovery_boundary().is_some() && owner.recovery_boundary().unwrap().same(&r.completion()));
            if r.result.is_ok() {
                r.result->Ok_0.cover_return(r.completion());
                assert(core.value_state().is_some() && r.result->Ok_0.certified(self.program().code(),r.ports@,core.value_state().unwrap()));
                assert(r.result->Ok_0.interpreted(self.program().code()) && r.result->Ok_0.witnessed() && transport::steps(self.program().code(),r.result->Ok_0));
                assert(r.result->Ok_0.registered(core.cleanup_state().link(),0));
                assert(super::super::retained(r.result->Ok_0.steps@,core,0,offset));
            }
        }
        proof {if report->Ok_0.result.is_ok() {reveal(super::super::Report::recovery_history);}}
        proof {if mode.is_some() {mode->Some_0.bank_frame(&old(mode)->Some_0,bank);}if typed.is_some() {typed->Some_0.bank_frame(&old(typed)->Some_0,bank);}}
        proof {if report->Ok_0.result.is_ok() {inputs::selection_facts(self.program().code(),report->Ok_0.result->Ok_0,report->Ok_0.ports@,owner.baseline().value_state().unwrap());}}
        let inputs=inputs::capture(owner.execution(),0,&report.as_ref().unwrap().result,Ghost(offset));
        let run=TargetRun {id,owner,report,offset:Ghost(offset),inputs};
        proof {if mode.is_some() && run.report->Ok_0.result.is_ok() {
            let actual=run.report->Ok_0.result->Ok_0.steps@;let expected=self.original().result->Ok_0.steps@;
            assert forall|i:int|0<=i<expected.len() implies super::observation::same_scalar(#[trigger] expected[i],actual[i]) by {}
            assert forall|i:int|0<=i<expected.len() implies super::selection::mapped(bank,#[trigger] expected[i],actual[i]) by {
                let index=mode->Some_0.routes()[expected[i].pc as int];
                assert(bank.mapping().contains_pair(expected[i].address(),bank.target_address(index as int)));
                assert(bank.target(index as int) is Scalar);
                assert(mode->Some_0.targets()[index as int]==bank.target(index as int)->Scalar_0);
                assert(actual[i].address()==bank.target_address(index as int));
            }
        }}
        proof {if mixed.is_some() && run.report->Ok_0.result.is_ok() {
            let steps=run.report->Ok_0.result->Ok_0.steps@;
            assert forall|i:int|0<=i<steps.len() && (#[trigger] steps[i]).result is Payload implies steps[i].result->Payload_0.inverse().wf() by {assert(steps[i].recorded_values());}
            mixed->Some_0.typed_inputs(&before_mixed->Some_0,steps);
            reveal(super::super::protected_mixed::Context::trace);
            assert(super::mixed::advanced(&old(mixed)->Some_0,&mixed->Some_0,steps));
        }}
        Ok(run)
    }
}

}
