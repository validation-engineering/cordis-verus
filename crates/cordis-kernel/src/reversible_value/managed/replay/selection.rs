//! Tie actual scalar selections to the bank through real published providers.
//! A zero slot revision certifies its original allocation. Changed slots are
//! rejected even when their replacement has the same scalar value and depth.
use super::super::Step;
use super::{bank::Bank, batch::Provider, observation, Source, TargetRun};
#[cfg(verus_keep_ghost)]
use crate::lifecycle_state::services::capture;
use crate::reversible_value::{effect::ScalarEffect, managed::ResultStep};
use vstd::prelude::*;

verus! {
#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
#[allow(inconsistent_fields)]
pub enum Error {
    Observation(observation::Error),MissingSource {step:usize},
    MissingProvider {step:usize},Provider {step:usize,expected:usize,observed:usize},
    ReplacedSlot {step:usize,revision:u64},
}
pub open spec fn actual_providers_match<E,T:?Sized>(bank:&Bank<T>,providers:Seq<Provider<E,T>>,sources:Map<usize,capture::Source<super::super::Slot<T,()>>>)->bool {
    forall|i:int|0<=i<providers.len() ==> {
        let p=#[trigger] providers[i];
        &&& p.index<bank.len_spec() && super::bank::seed_slot(bank.target(p.index as int),*p.service) && sources.contains_key(p.id)
        &&& sources[p.id].values.contains_pair((p.port.key,p.port.realm),p.service)
    }
}
pub open spec fn providers_match<E,T:?Sized>(bank:&Bank<T>,providers:Seq<Provider<E,T>>,sources:Map<usize,capture::Source<super::super::Slot<T,()>>>)->bool {
    forall|i:int|0<=i<providers.len() ==> {
        let p=#[trigger] providers[i];
        &&& p.index<bank.len_spec() && p.service==bank.service(p.index as int) && sources.contains_key(p.id)
        &&& sources[p.id].values.contains_pair((p.port.key,p.port.realm),bank.service(p.index as int))
    }
}
pub proof fn preserve_providers<E,T:?Sized>(bank:&Bank<T>,providers:Seq<Provider<E,T>>,
    before:Map<usize,crate::lifecycle_state::services::NativePublication<super::super::Slot<T,()>>>,
    after:Map<usize,crate::lifecycle_state::services::NativePublication<super::super::Slot<T,()>>>)
    requires providers_match(bank,providers,capture::sources(before)),before.submap_of(after),
    ensures providers_match(bank,providers,capture::sources(after)),
{
    reveal(Map::submap_of);
    assert forall|i:int|0<=i<providers.len() implies {
        let p=#[trigger] providers[i];
        &&& p.index<bank.len_spec() && capture::sources(after).contains_key(p.id)
        &&& capture::sources(after)[p.id].values.contains_pair((p.port.key,p.port.realm),bank.service(p.index as int))
    } by {
        let p=providers[i];
        assert(capture::sources(before).contains_key(p.id));
        assert(before.dom().contains(p.id));
        assert(before[p.id]==after[p.id]);
    }
}
pub(crate) proof fn remove_unrelated<E,T:?Sized>(bank:&Bank<T>,providers:Seq<Provider<E,T>>,
    before:Map<usize,crate::lifecycle_state::services::NativePublication<super::super::Slot<T,()>>>,
    after:Map<usize,crate::lifecycle_state::services::NativePublication<super::super::Slot<T,()>>>,id:usize)
    requires providers_match(bank,providers,capture::sources(before)),after==before || after==before.remove(id),
        forall|i:int|0<=i<providers.len() ==> (#[trigger] providers[i]).id!=id,
    ensures providers_match(bank,providers,capture::sources(after)),
{
    assert forall|i:int|0<=i<providers.len() implies {
        let p=#[trigger] providers[i];
        &&& p.index<bank.len_spec() && capture::sources(after).contains_key(p.id)
        &&& capture::sources(after)[p.id].values.contains_pair((p.port.key,p.port.realm),bank.service(p.index as int))
    } by {let p=providers[i];assert(before.contains_key(p.id));assert(before[p.id]==after[p.id]);}
}
pub open spec fn mapped<T:?Sized>(bank:&Bank<T>,source:Step<T>,target:Step<T>)->bool {
    bank.mapping().contains_pair(source.address(),target.address())
}
pub(super) fn find_provider<E,T:?Sized>(providers:&[Provider<E,T>],port:crate::Port,index:usize)->(out:Option<usize>)
    ensures out.is_some() ==> out.unwrap()<providers.len() && providers@[out.unwrap() as int].port==port && providers@[out.unwrap() as int].index==index,
{
    let mut p=0;
    while p<providers.len()
        invariant p<=providers.len(),
        decreases providers.len()-p,
    {
        if providers[p].port==port && providers[p].index==index {return Some(p);}
        p+=1;
    }
    None
}
#[allow(clippy::too_many_arguments)] // Two arguments carry erased interpretation evidence.
#[verifier::rlimit(8)]
fn check_step<E:ScalarEffect,T:?Sized>(input:&super::inputs::Input<T>,target:&Step<T>,bank:&Bank<T>,providers:&[Provider<E,T>],port:crate::Port,position:usize,
    Ghost(call):Ghost<super::super::Call<E,T>>,Ghost(episode):Ghost<crate::lifecycle_state::services::NativeEpisode<super::super::Slot<T,()>>>)->(out:Result<(),Error>)
    requires input.wf(),bank.wf(),input.identity_spec().namespace()==bank.namespace(),
        target.result is Scalar,target.corresponds(call,port,episode),!episode.provisions().contains(port),
        providers_match(bank,providers@,episode.capture().sources),
    ensures out.is_ok() ==> mapped(bank,input.source(),*target),
{
    hide(crate::reversible_value::joint::valid);hide(crate::reversible_value::joint::step);
    let index=match bank.find(input) {Some(index)=>index,None=>return Err(Error::MissingSource {step:position})};
    let p=match find_provider(providers,port,index) {Some(p)=>p,None=>return Err(Error::MissingProvider {step:position})};
    let provider=&providers[p];
    let write=match &target.result {ResultStep::Scalar {write,..}=>write,_=>{assert(false);panic!("checked scalar kind")}};
    let observed=write.binding.provider();
    if observed!=provider.id {return Err(Error::Provider {step:position,expected:provider.id,observed});}
    let revision=write.binding.capture().revision();
    if revision!=0 {return Err(Error::ReplacedSlot {step:position,revision});}
    proof {
        let step=*target;
        reveal(super::super::Step::corresponds);
        assert(step.corresponds(call,port,episode));
        assert(episode.capture().imports.contains_key((provider.id,port.key,port.realm)));
        assert(provider.port==port && provider.index==index);
        assert(episode.wf());assert(episode.capture().wf());
        assert(episode.capture().sources.contains_key(provider.id));
        assert(episode.capture().sources[provider.id].values.contains_pair((port.key,port.realm),bank.service(index as int)));
        assert(episode.capture().imports[(provider.id,port.key,port.realm)]==episode.capture().sources[provider.id].values[(port.key,port.realm)]);
        assert(episode.capture().imports[(provider.id,port.key,port.realm)]==bank.service(index as int));
        assert(write.binding.capture_spec().slot()==bank.service(index as int).managed().unwrap());
        write.binding.capture_spec().initial_selection();
        bank.seed_facts(index as int);
        bank.service(index as int).payload_partition();
        assert(bank.target(index as int) is Scalar);
        assert(*write.binding.capture_spec().value_spec()==bank.target(index as int)->Scalar_0);
        bank.mapping_entry(index as int);
        assert(step.address()==bank.target_address(index as int));
    }
    Ok(())
}
fn check_steps<E:ScalarEffect,T:?Sized>(inputs:&[super::inputs::Input<T>],steps:&[Step<T>],ports:&[crate::Port],bank:&Bank<T>,providers:&[Provider<E,T>],
    Ghost(code):Ghost<Seq<super::super::Call<E,T>>>,Ghost(episode):Ghost<crate::lifecycle_state::services::NativeEpisode<super::super::Slot<T,()>>>)->(out:Result<(),Error>)
    requires bank.wf(),inputs.len()==steps.len(),episode.provisions().len()==0,providers_match(bank,providers@,episode.capture().sources),
        forall|i:int|0<=i<inputs.len() ==> {
            let input=#[trigger] inputs@[i];let target=steps@[i];
            &&& input.wf() && input.identity_spec().namespace()==bank.namespace()
            &&& target.result is Scalar && target.pc==input.source().pc && target.pc<ports.len()
            &&& target.corresponds(code[target.pc as int],ports@[target.pc as int],episode)
        },
    ensures out.is_ok() ==> forall|i:int|0<=i<inputs.len() ==> mapped(bank,(#[trigger] inputs@[i]).source(),steps@[i]),
{
    hide(crate::reversible_value::joint::valid);hide(crate::reversible_value::joint::step);
    let mut i=0;
    while i<inputs.len()
        invariant i<=inputs.len(),bank.wf(),inputs.len()==steps.len(),episode.provisions().len()==0,providers_match(bank,providers@,episode.capture().sources),
            forall|j:int|0<=j<inputs.len() ==> {
                let input=#[trigger] inputs@[j];let target=steps@[j];
                &&& input.wf() && input.identity_spec().namespace()==bank.namespace()
                &&& target.result is Scalar && target.pc==input.source().pc && target.pc<ports.len()
                &&& target.corresponds(code[target.pc as int],ports@[target.pc as int],episode)
            },
            forall|j:int|0<=j<i ==> mapped(bank,(#[trigger] inputs@[j]).source(),steps@[j]),
        decreases inputs.len()-i,
    {
        let pc=inputs[i].pc();
        check_step(&inputs[i],&steps[i],bank,providers,ports[pc],i,Ghost(code[pc as int]),Ghost(episode))?;
        i+=1;
    }
    Ok(())
}
/// Check the real typed selection before landing a write. Typed service
/// slots retain an immutable owner; payload versions are checked separately.
pub fn check_payload_capture<E,T:?Sized>(_bank:&Bank<T>,providers:&[Provider<E,T>],index:usize,capture:&crate::reversible_value::native_payload::Capture<T,()>)->(out:Result<(),Error>)
    requires _bank.wf(),index<_bank.len_spec(),capture.wf(),!capture.episode().provisions().contains(capture.port_spec()),
        providers_match(_bank,providers@,capture.episode().capture().sources),
    ensures out.is_ok() ==> _bank.target(index as int) is Payload
        && capture.payload().owner()==_bank.target(index as int)->Payload_0,
{
    proof {capture.provenance();}
    let port=capture.port();
    let p=match find_provider(providers,port,index) {Some(p)=>p,None=>return Err(Error::MissingProvider {step:index})};
    let observed=capture.provider();let expected=providers[p].id;
    if observed!=expected {return Err(Error::Provider {step:index,expected,observed});}
    proof {
        let episode=capture.episode();
        assert(episode.wf());assert(episode.capture().wf());
        assert(episode.capture().sources.contains_key(expected));
        assert(episode.capture().sources[expected].values.contains_pair((port.key,port.realm),_bank.service(index as int)));
        assert(episode.imports()[(expected,port.key,port.realm)]==_bank.service(index as int));
        assert(capture.retained()==_bank.service(index as int));
        _bank.seed_facts(index as int);_bank.service(index as int).payload_partition();
    }
    Ok(())
}
impl<C,G,A,R,T:?Sized,X,E:ScalarEffect> TargetRun<C,G,A,R,T,(),X,E> {
    pub open spec fn captured_providers(&self,bank:&Bank<T>,providers:Seq<Provider<E,T>>)->bool {
        self.owner.baseline().value_state().is_some()
            && providers_match(bank,providers,self.owner.baseline().value_state().unwrap().capture().sources)
    }
    pub open spec fn scalar_replay_matches(&self,source:&Source<E,T>,bank:&Bank<T>)->bool {
        self.scalar_observations_match(source)
            && forall|i:int|0<=i<source.original().result->Ok_0.steps.len() ==>
                mapped(bank,#[trigger] source.original().result->Ok_0.steps@[i],self.report->Ok_0.result->Ok_0.steps@[i])
    }
    /// Selection evidence comes from Begin's actual publication capture and the
    /// actual interpreter binding, not a mutable lookup after the invocation.
    #[verifier::rlimit(12)]
    pub fn check_scalar_replay(&self,source:&Source<E,T>,bank:&Bank<T>,providers:&[Provider<E,T>])->(out:Result<(),Error>)
        requires source.wf(),self.from_source(source),bank.wf(),self.captured_providers(bank,providers@),
            source.provision_ports().len()==0,self.owner.baseline().value_state().unwrap().provisions()==source.provision_ports(),
            forall|i:int|0<=i<source.input_spec().len() ==> (#[trigger] source.input_spec()[i]).identity_spec().namespace()==bank.namespace(),
        ensures out.is_ok() ==> self.scalar_replay_matches(source,bank),
    {
        hide(crate::reversible_value::joint::valid);hide(crate::reversible_value::joint::step);
        reveal(Source::input_spec);reveal(Source::provision_ports);
        if let Err(error)=self.check_scalar_observations(source) {return Err(Error::Observation(error));}
        let target=match &self.report {Ok(r)=>match &r.result {Ok(t)=>t,Err(_)=>{assert(false);panic!("checked target")}},Err(_)=>{assert(false);panic!("checked admission")}};
        proof {
            source.facts();
            assert forall|i:int|0<=i<source.inputs.len() implies {
                let input=#[trigger] source.inputs@[i];let step=target.steps@[i];
                &&& input.wf() && input.identity_spec().namespace()==bank.namespace()
                &&& step.result is Scalar && step.pc==input.source().pc && step.pc<source.ports.len()
                &&& step.corresponds(source.program().code()[step.pc as int],source.ports@[step.pc as int],self.owner.baseline().value_state().unwrap())
            } by {
                assert(source.input_spec()[i]==source.inputs@[i]);
                assert(observation::same_scalar(source.inputs@[i].source(),target.steps@[i]));
            }
        }
        check_steps(source.inputs.as_slice(),target.steps.as_slice(),source.ports.as_slice(),bank,providers,
            Ghost(source.program().code()),Ghost(self.owner.baseline().value_state().unwrap()))?;
        proof {
            assert forall|i:int|0<=i<source.original().result->Ok_0.steps.len() implies
                mapped(bank,#[trigger] source.original().result->Ok_0.steps@[i],self.report->Ok_0.result->Ok_0.steps@[i]) by {
                assert(source.inputs@[i].source()==source.original().result->Ok_0.steps@[i]);
            }
        }
        Ok(())
    }
    /// The actual selected allocation and strict inverse are transported by
    /// the same map. This still describes a checked completed invocation.
    pub proof fn mapped_inverse(&self,source:&Source<E,T>,bank:&Bank<T>,i:int)
        requires source.wf(),self.from_source(source),bank.wf(),self.scalar_replay_matches(source,bank),
            0<=i<source.original().result->Ok_0.steps.len(),
        ensures bank.mapping().contains_pair(source.original().result->Ok_0.steps@[i].address(),self.report->Ok_0.result->Ok_0.steps@[i].address()),
            source.original().result->Ok_0.steps@[i].result is Scalar,self.report->Ok_0.result->Ok_0.steps@[i].result is Scalar,
            source.original().result->Ok_0.steps@[i].result->Scalar_inverse@.state()==self.report->Ok_0.result->Ok_0.steps@[i].result->Scalar_inverse@.state(),
    {self.scalar_inverse(source,i);}
}
}
