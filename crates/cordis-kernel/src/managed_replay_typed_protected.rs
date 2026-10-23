//! Actual typed Bank storage and episode selection for the managed interpreter.
use super::super::{
    protected_typed::{Binding, Context, Error},
    Slot,
};
use super::{bank::Bank, batch::Provider};
use crate::lifecycle_state::services::NativeEpisode;
use crate::reversible_value::payload::SharedPayload;
use crate::Port;
use std::sync::Arc;
use vstd::prelude::*;

verus! {
pub ghost struct Interval<T:?Sized> {
    pub correspondence:Option<super::typed_correspondence::Certificate<T>>,
    pub before:Seq<crate::reversible_value::payload::State<T>>,pub after:Seq<crate::reversible_value::payload::State<T>>,
    pub before_revisions:Seq<u64>,pub after_revisions:Seq<u64>,pub routes:Seq<usize>,pub steps:Seq<super::super::Step<T>>,
}
impl<T:?Sized> Interval<T> {
    pub closed spec fn wf(&self)->bool {
        (self.correspondence.is_some() ==> self.correspondence.unwrap().wf() && self.correspondence.unwrap().target==self.steps
            && self.correspondence.unwrap().routes==self.routes && self.correspondence.unwrap().before_target==self.before && self.correspondence.unwrap().after_target==self.after)
            && super::super::protected_typed::execution(self.before,self.before_revisions,self.routes,self.steps)
            && self.after==super::super::protected_typed::after(self.before,self.routes,self.steps)
            && self.after_revisions==super::super::protected_typed::clocks(self.before_revisions,self.routes,self.steps)
    }
    pub(crate) proof fn establish(&self)
        requires (self.correspondence.is_some() ==> self.correspondence.unwrap().wf() && self.correspondence.unwrap().target==self.steps
            && self.correspondence.unwrap().routes==self.routes && self.correspondence.unwrap().before_target==self.before && self.correspondence.unwrap().after_target==self.after),
            super::super::protected_typed::execution(self.before,self.before_revisions,self.routes,self.steps),
            self.after==super::super::protected_typed::after(self.before,self.routes,self.steps),
            self.after_revisions==super::super::protected_typed::clocks(self.before_revisions,self.routes,self.steps),
        ensures self.wf(),
    {}
}

pub(crate) struct Storage<T:?Sized> {pub values:Vec<SharedPayload<T>>,pub slots:Vec<Arc<Slot<T,()>>>}
impl<T:?Sized> Storage<T> {
    pub(crate) proof fn acquire_ready(&self,bank:&Bank<T>)
        requires self.matches(bank),
        ensures self.values.len()==self.slots.len(),
            forall|i:int|0<=i<self.slots.len() ==> (#[trigger] self.slots@[i]).opaque_spec()==Some(self.values@[i]),
            forall|i:int,j:int|0<=i<j<self.values.len() ==> self.values@[i]!=self.values@[j],
    {assert forall|i:int|0<=i<self.slots.len() implies (#[trigger] self.slots@[i]).opaque_spec()==Some(self.values@[i]) by {assert(bank.target(i) is Payload);}}

    pub(crate) open spec fn matches(&self,bank:&Bank<T>)->bool {
        self.values.len()==bank.len_spec() && self.slots.len()==self.values.len()
            && (forall|i:int|0<=i<self.values.len() ==> (#[trigger] bank.target(i)) is Payload
                && self.values@[i]==bank.target(i)->Payload_0 && self.slots@[i]==bank.service(i)
                && self.slots@[i].opaque_spec()==Some(self.values@[i]))
            && (forall|i:int,j:int|0<=i<j<self.values.len() ==> self.values@[i]!=self.values@[j])
    }
}
impl<'a,T:?Sized> Context<'a,T,()> {
    pub(crate) proof fn mapped_steps(&self,bank:&Bank<T>,source:Seq<super::super::Step<T>>,actual:Seq<super::super::Step<T>>)
        requires self.wf(),self.bank(bank),bank.wf(),super::protected::mapped(bank,self.routes(),source),
            super::super::protected_typed::addressed(self.targets(),self.routes(),actual),
            super::typed_correspondence::aligned(source,actual),
        ensures super::typed_correspondence::allocations(bank,source,actual),
    {
        reveal(super::super::protected_typed::addressed);reveal(super::typed_correspondence::allocations);
        assert forall|i:int|0<=i<source.len() implies super::selection::mapped(bank,#[trigger] source[i],actual[i]) by {
            let index=self.routes()[source[i].pc as int] as int;self.bank_entry(bank,index);
            assert(actual[i].address()==bank.target_address(index));
        }
    }

    #[verifier::opaque]
    pub(crate) open spec fn initial_entry(&self,bank:&Bank<T>,i:int)->bool {
        0<=i<bank.len_spec() && i<self.states().len() && i<self.revisions().len() && bank.first(i).source().before() is Payload
            && self.states()[i].value==bank.first(i).source().before()->Payload_0.value
            && self.states()[i].depth==bank.first(i).source().before()->Payload_0.depth
            && self.states()[i].head==0 && self.revisions()[i]==0 && self.states()[i].depth==0
    }
    /// Derive one initial correspondence from real seed provenance and a held
    /// zero-clock capture, then compose entries without unfolding their Journal.
    #[verifier::rlimit(12)]
    fn check_initial_entry(&self,bank:&Bank<T>,i:usize)->(out:Result<(),Error>)
        requires self.wf(),self.bank(bank),bank.wf(),i<bank.len_spec(),
        ensures out.is_ok() ==> self.initial_entry(bank,i as int),
    {
        hide(crate::reversible_value::joint::valid);hide(crate::reversible_value::joint::step);reveal(Context::initial_entry);
        proof {self.bank_entry(bank,i as int);self.storage_facts();}
        let first=bank.first_input(i).unwrap();
        match first.operand() {super::inputs::Operand::Payload {depth,..}=>{if *depth!=0 {return Err(Error::OutstandingHistory {entry:i});}},_=>return Err(Error::NotTyped)}
        let current=self.capture(i);
        if current.revision()!=0 {return Err(Error::ChangedVersion {entry:i});}
        proof {
            assert(current.revision_spec()==0);
            current.initial_state();first.provenance();
            assert(first.source().before() is Payload);
            assert(first.source().before()->Payload_0.depth==0);
            assert(super::transport::values(first.source().before(),bank.target(i as int).initial()));
            assert(self.states()[i as int].value==first.source().before()->Payload_0.value);
            assert(self.states()[i as int].depth==0 && self.states()[i as int].head==0 && self.revisions()[i as int]==0);
            assert(first.source()==bank.first(i as int).source());
        }Ok(())
    }
    pub(crate) fn check_initial(&self,bank:&Bank<T>)->(out:Result<(),Error>)
        requires self.wf(),self.bank(bank),bank.wf(),
        ensures out.is_ok() ==> forall|i:int|0<=i<bank.len_spec() ==> #[trigger] self.initial_entry(bank,i),
    {
        let mut i=0;
        while i<bank.len()
            invariant self.wf(),self.bank(bank),bank.wf(),i<=bank.len_spec(),
                forall|j:int|0<=j<i ==> #[trigger] self.initial_entry(bank,j),
            decreases bank.len_spec()-i,
        {self.check_initial_entry(bank,i)?;i+=1;}Ok(())
    }
    /// Check actual captured allocation selection before the first effect.
    pub(crate) fn check_routes<E:crate::reversible_value::effect::ScalarEffect>(&self,source:&super::Source<E,T>,bank:&Bank<T>)->(out:Result<(),Error>)
        requires self.wf(),self.bank(bank),bank.wf(),source.wf(),source.original().succeeded(),
            forall|i:int|0<=i<source.input_spec().len() ==> source.input_spec()[i].identity_spec().namespace()==bank.namespace(),
        ensures out.is_ok() ==> super::protected::mapped(bank,self.routes(),source.original().result->Ok_0.steps@),
    {
        hide(super::Source::wf);proof {source.facts();}let inputs=source.inputs();let mut i=0;
        proof {assert(source.original().result.is_err() ==> inputs.len()==0);}
        while i<inputs.len()
            invariant self.wf(),self.bank(bank),bank.wf(),source.wf(),source.original().succeeded(),inputs@==source.input_spec(),i<=inputs.len(),
                super::inputs::captured(inputs@,source.original().result),
                forall|j:int|0<=j<inputs.len() ==> (#[trigger] inputs@[j]).identity_spec().namespace()==bank.namespace(),
                super::protected::mapped(bank,self.routes(),source.original().result->Ok_0.steps@.take(i as int)),
            decreases inputs.len()-i,
        {
            let input=&inputs[i];
            let selected=match self.route(input.pc()) {Some(index)=>index,None=>return Err(Error::SourceAllocation {step:i})};
            let mapped=match bank.find(input) {Some(index)=>index,None=>return Err(Error::SourceAllocation {step:i})};
            if selected!=mapped {return Err(Error::SourceAllocation {step:i});}
            proof {
                bank.mapping_entry(mapped as int);
                super::protected::mapped_append(bank,self.routes(),source.original().result->Ok_0.steps@.take(i as int),input.source());
                assert(source.original().result->Ok_0.steps@.take(i as int+1) =~= source.original().result->Ok_0.steps@.take(i as int).push(input.source()));
            }i+=1;
        }
        proof {assert(source.original().result->Ok_0.steps@.take(i as int) =~= source.original().result->Ok_0.steps@);}
        Ok(())
    }

    pub(crate) open spec fn bank(&self,bank:&Bank<T>)->bool {
        self.targets().len()==bank.len_spec() && self.slots().len()==bank.len_spec()
            && forall|i:int|0<=i<bank.len_spec() ==> {
                &&& (#[trigger] bank.target(i)) is Payload
                &&& self.targets()[i]==bank.target(i)->Payload_0 && self.slots()[i]==bank.service(i)
            }
    }
    pub(crate) proof fn bank_entry(&self,bank:&Bank<T>,i:int)
        requires self.bank(bank),0<=i<bank.len_spec(),
        ensures bank.target(i) is Payload,self.targets()[i]==bank.target(i)->Payload_0,self.slots()[i]==bank.service(i),
    {}
    pub(crate) proof fn bank_frame(&self,prior:&Self,bank:&Bank<T>)
        requires prior.bank(bank),self.targets()==prior.targets(),self.slots()==prior.slots(),ensures self.bank(bank),
    {assert forall|i:int|0<=i<bank.len_spec() implies (#[trigger] bank.target(i)) is Payload
        && self.targets()[i]==bank.target(i)->Payload_0 && self.slots()[i]==bank.service(i) by {prior.bank_entry(bank,i);}}
    pub(crate) fn bind_episode<E>(&mut self,episode:&NativeEpisode<Slot<T,()>>,ports:&[Port],_bank:&Bank<T>,providers:&[Provider<E,T>])->(out:Result<(),Error>)
        requires old(self).wf(),old(self).bank(_bank),_bank.wf(),episode.wf(),
            super::selection::providers_match(_bank,providers@,episode.capture().sources),
        ensures final(self).wf(),final(self).targets()==old(self).targets(),final(self).states()==old(self).states(),final(self).revisions()==old(self).revisions(),
            final(self).slots()==old(self).slots(),final(self).bank(_bank),
            out.is_ok() ==> final(self).supports(*episode,ports@),
    {
        reveal(Context::supports);
        let mut bindings:Vec<Binding>=Vec::new();let mut i=0;
        while i<ports.len()
            invariant *self==*old(self),self.wf(),self.bank(_bank),_bank.wf(),episode.wf(),i<=ports.len(),bindings.len()==i,
                super::selection::providers_match(_bank,providers@,episode.capture().sources),
                forall|j:int|0<=j<bindings.len() ==> (#[trigger] bindings@[j]).entry<self.slots().len()
                    && bindings@[j].port@==ports@[j] && !episode.closed()
                    && episode.selects_value(bindings@[j].provider@,bindings@[j].port@,self.slots()[bindings@[j].entry as int]),
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
                assert(_bank.target(provider.index as int) is Payload);
                assert(_bank.service(provider.index as int)==self.slots()[provider.index as int]);
                assert(episode.selects_value(id,port,self.slots()[provider.index as int]));
            }
            bindings.push(Binding {provider:Ghost(id),port:Ghost(port),entry:provider.index});i+=1;
        }
        // Empty programs still require an open native episode.
        if episode.is_closed() {return Err(Error::Binding {pc:0});}
        self.bind(bindings);proof {self.bank_frame(old(self),_bank);}Ok(())
    }
}
}
