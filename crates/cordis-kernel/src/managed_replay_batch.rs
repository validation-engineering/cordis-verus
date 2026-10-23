//! Actual finite multi-call target execution with shared target services.
//! This preserves reports and cleanup owners on every partial-failure path;
//! it does not synthesize a desired Journal or claim arbitrary interference.
use super::super::interleaving::history::lifecycle::RecordedExecution;
use super::super::{Function, Owner};
use super::{
    bank, continuity, observation, order, selection, Destination, ManagedRuntime, Source,
    StartError, TargetRun,
};
use crate::lifecycle_state::registration::PluginDefinition;
use crate::reversible_value::{effect::ScalarEffect, function::Body, joint};
use crate::{Error, Port};
use std::collections::BTreeMap;
use vstd::prelude::*;

verus! {
broadcast use vstd::seq_lib::group_seq_properties;
pub type Run<E,T> = TargetRun<(),(),(),(),T,(),(),E>;
pub type ProviderOwner<T> = RecordedExecution<(),(),(),(),T,(),()>;
pub struct Provider<E,T:?Sized> {
    pub id:usize,pub port:Port,pub index:usize,pub slot:Option<usize>,pub source_origin:Option<crate::action_ledger::ActionTicket>,pub service:std::sync::Arc<super::super::Slot<T,()>>,pub owner:ProviderOwner<T>,
    pub report:Result<super::RegisteredReport<E,T>,super::AdmissionError>,
}
#[derive(Debug)]
#[allow(inconsistent_fields)]
pub enum Failure {
    Ordering(order::Error),Capacity,Slot {call:usize,error:super::slots::Error},SourceProvisions {call:usize},MissingInput {call:usize,port:Port},
    Binding {call:usize,error:bank::Error},ReboundPort {port:Port},
    ProviderRegistration(Error),ProviderBegin {id:usize,error:Error},ProviderAdmission {id:usize},
    ProviderPublication {id:usize},ProviderFinish {id:usize,error:Error},
    Start {call:usize,error:StartError<()>},Invocation {call:usize},Finish {call:usize,error:Error},
    Observation {call:usize,error:observation::Error},
    Selection {call:usize,error:selection::Error},
    Protection {call:Option<usize>,error:super::protected::Error},
}
struct Binding {port:Port,index:usize,slot:Option<usize>,source_origin:Option<crate::action_ledger::ActionTicket>}
impl Binding {
    spec fn valid<T:?Sized>(&self,bank:&bank::Bank<T>,slots:&super::slots::Slots<T>)->bool {
        self.index<bank.len_spec() && (self.slot.is_some() ==> self.slot.unwrap()<slots.len_spec() && self.index==slots.initial(self.slot.unwrap() as int))
    }
}
/// Anchor/work names are consumed monotonically, with checked exhaustion.
/// Host registration still decides whether a proposed anchor can be admitted.
pub struct Names {pub anchor:u64,pub work:u64}
impl Names {
    pub(crate) fn take(&mut self)->(out:Option<(Port,u64)>) {
        if self.anchor==u64::MAX || self.work==u64::MAX {return None;}
        let out=(Port {key:self.anchor,realm:0},self.work);self.anchor+=1;self.work+=1;Some(out)
    }
}
pub struct Batch<E,T:?Sized> {
    pub slots:super::slots::Slots<T>,
    pub mixed_protection:Ghost<Seq<super::mixed::Interval<T>>>,
    pub typed_protection:Ghost<Seq<super::typed_protected::Interval<T>>>,
    pub blocked:Option<(usize,ProviderOwner<T>)>,pub protection:Ghost<Seq<super::protected::Interval<T>>>,
    pub order:Vec<usize>,pub bank:bank::Bank<T>,pub providers:Vec<Provider<E,T>>,pub calls:Vec<Run<E,T>>,pub failure:Option<Failure>,
}
impl<E:ScalarEffect,T:?Sized> Batch<E,T> {
    pub open spec fn typed_replay_matches(&self,sources:Seq<Source<E,T>>)->bool {
        forall|i:int|0<=i<self.calls.len() ==> {
            let run=#[trigger] self.calls@[i];
            &&& i<self.order.len() && self.order@[i]<sources.len() && i<self.typed_protection@.len() && run.report.is_ok()
            &&& run.report->Ok_0.result.is_ok() ==> {
                let c=self.typed_protection@[i].correspondence;
                &&& c.is_some() && c.unwrap().wf()
                &&& c.unwrap().source==sources[self.order@[i] as int].original().result->Ok_0.steps@
                &&& c.unwrap().target==run.report->Ok_0.result->Ok_0.steps@
                &&& super::typed_correspondence::allocations(&self.bank,c.unwrap().source,c.unwrap().target)
                &&& i>0 ==> self.typed_protection@[i-1].correspondence.is_some()
                    && c.unwrap().before_source==self.typed_protection@[i-1].correspondence.unwrap().after_source
                    && c.unwrap().before_names==self.typed_protection@[i-1].correspondence.unwrap().after_names
            }
        }
    }
    /// The actual target storage preserves aliases in both directions,
    /// including between different completed typed root calls.
    pub proof fn typed_aliases(&self,sources:Seq<Source<E,T>>,left:int,a:int,right:int,b:int)
        requires self.bank.wf(),self.typed_replay_matches(sources),
            0<=left<self.calls.len(),0<=right<self.calls.len(),
            self.calls@[left].report->Ok_0.result.is_ok(),self.calls@[right].report->Ok_0.result.is_ok(),
            0<=a<sources[self.order@[left] as int].original().result->Ok_0.steps.len(),
            0<=b<sources[self.order@[right] as int].original().result->Ok_0.steps.len(),
        ensures (sources[self.order@[left] as int].original().result->Ok_0.steps@[a].address()
                    ==sources[self.order@[right] as int].original().result->Ok_0.steps@[b].address())
                ==(self.calls@[left].report->Ok_0.result->Ok_0.steps@[a].address()
                    ==self.calls@[right].report->Ok_0.result->Ok_0.steps@[b].address()),
    {reveal(super::typed_correspondence::allocations);self.bank.mapping_injective();}
    pub open spec fn typed_exclusive_prefix(&self)->bool {
        self.typed_protection@.len()==self.calls.len() && forall|i:int|0<=i<self.calls.len() ==> {
            let interval=#[trigger] self.typed_protection@[i];
            &&& interval.wf() && self.calls@[i].report.is_ok()
            &&& interval.steps==super::protected::result_steps(self.calls@[i].report->Ok_0.result)
            &&& i>0 ==> interval.before==self.typed_protection@[i-1].after && interval.before_revisions==self.typed_protection@[i-1].after_revisions
        }
    }

    /// Every interval is extracted from the held real cells and actual
    /// returned root report. Adjacent calls share the same protected heap.
    pub open spec fn exclusive_prefix(&self)->bool {
        self.protection@.len()==self.calls.len() && forall|i:int|0<=i<self.calls.len() ==> {
            let interval=#[trigger] self.protection@[i];
            &&& interval.wf() && self.calls@[i].report.is_ok()
            &&& interval.steps==super::protected::result_steps(self.calls@[i].report->Ok_0.result)
            &&& i>0 ==> interval.before==self.protection@[i-1].after
        }
    }
    pub open spec fn actual_prefix(&self,sources:Seq<Source<E,T>>)->bool {
        self.calls.len()<=self.order.len() && forall|i:int|0<=i<self.calls.len() ==>
            self.order@[i]<sources.len() && (#[trigger] self.calls@[i]).report.is_ok() && self.calls@[i].from_source(&sources[self.order@[i] as int])
            && self.calls@[i].report->Ok_0.completion().journal()==self.bank.journal()
    }
    pub open spec fn scalar_observations_match(&self,sources:Seq<Source<E,T>>)->bool {
        forall|i:int|0<=i<self.calls.len() ==> self.order@[i]<sources.len()
            && (#[trigger] self.calls@[i]).scalar_observations_match(&sources[self.order@[i] as int])
    }
    pub open spec fn scalar_replay_matches(&self,sources:Seq<Source<E,T>>)->bool {
        forall|i:int|0<=i<self.calls.len() ==> self.order@[i]<sources.len()
            && (#[trigger] self.calls@[i]).scalar_replay_matches(&sources[self.order@[i] as int],&self.bank)
    }
    /// Aliases are preserved across actual calls, not just across bank seeds.
    pub proof fn scalar_aliases(&self,sources:Seq<Source<E,T>>,left:int,a:int,right:int,b:int)
        requires self.bank.wf(),self.scalar_replay_matches(sources),
            0<=left<self.calls.len(),0<=right<self.calls.len(),
            0<=a<sources[self.order@[left] as int].original().result->Ok_0.steps.len(),
            0<=b<sources[self.order@[right] as int].original().result->Ok_0.steps.len(),
        ensures (sources[self.order@[left] as int].original().result->Ok_0.steps@[a].address()
                    ==sources[self.order@[right] as int].original().result->Ok_0.steps@[b].address())
                ==(self.calls@[left].report->Ok_0.result->Ok_0.steps@[a].address()
                    ==self.calls@[right].report->Ok_0.result->Ok_0.steps@[b].address()),
    {self.bank.mapping_injective();}
    pub open spec fn succeeded(&self)->bool {
        forall|i:int|0<=i<self.calls.len() ==> (#[trigger] self.calls@[i]).report.is_ok()
            && self.calls@[i].report->Ok_0.result.is_ok() && self.calls@[i].report->Ok_0.result->Ok_0.failure.is_none()
    }
}
pub closed spec fn supported_namespace<E:ScalarEffect,T:?Sized>(sources:Seq<Source<E,T>>,source:joint::Journal)->bool {
    forall|i:int|0<=i<sources.len() ==> (#[trigger] sources[i]).wf() && sources[i].stream_identity().namespace()==source.identity_namespace()
        && (sources[i].environment().is_some() ==> sources[i].environment().unwrap().namespace(source.identity_namespace()))
        && (sources[i].owned_environment().is_some() ==> sources[i].owned_environment().unwrap().namespace(source.identity_namespace()))
        && (sources[i].publication_environment().is_some() ==> sources[i].publication_environment().unwrap().namespace(source.identity_namespace()))
        && forall|j:int|0<=j<sources[i].inputs.len() ==> sources[i].inputs@[j].namespace(source.identity_namespace())
}
pub(crate) proof fn supported_at<E:ScalarEffect,T:?Sized>(sources:Seq<Source<E,T>>,source:joint::Journal,i:int)
    requires supported_namespace(sources,source),0<=i<sources.len(),
    ensures sources[i].wf(),sources[i].publication_environment().is_some() ==> sources[i].publication_environment().unwrap().namespace(source.identity_namespace()),sources[i].owned_environment().is_some() ==> sources[i].owned_environment().unwrap().namespace(source.identity_namespace()),sources[i].environment().is_some() ==> sources[i].environment().unwrap().namespace(source.identity_namespace()),forall|j:int|0<=j<sources[i].input_spec().len() ==> sources[i].input_spec()[j].namespace(source.identity_namespace()),
{reveal(Source::input_spec);}
/// Build all aliases from authentic operands, publish real providers and run
/// every preserved function in its actual source Call order using the real root
/// path. Complete lifecycle scheduling and target-state simulation are separate
/// obligations; the caller supplies neither a permutation nor call positions.
pub fn run<P,E:ScalarEffect+Copy,T:?Sized>(runtime:&mut ManagedRuntime<P,(),E,T,()>,source_journal:&joint::Journal,sources:&[Source<E,T>],names:Names)
    ->(out:Batch<E,T>)
    requires old(runtime).wf(),supported_namespace(sources@,*source_journal),
    ensures final(runtime).wf(),out.bank.wf(),out.actual_prefix(sources@),
        out.failure.is_none() ==> out.calls.len()==sources.len() && out.succeeded()
            && order::prefix(sources@,out.order@,sources@.len()) && order::chronological(sources@,out.order@),
{
    let indices=match order::plan(sources) {
        Ok(indices)=>indices,Err(error)=>{
            let target=runtime.execution_journal();
            return Batch {slots:super::slots::Slots::new(),mixed_protection:Ghost(Seq::empty()),typed_protection:Ghost(Seq::empty()),blocked:None,protection:Ghost(Seq::empty()),order:Vec::new(),bank:bank::Bank::new(source_journal,&target),providers:Vec::new(),calls:Vec::new(),failure:Some(Failure::Ordering(error))};
        },
    };
    run_ordered(runtime,source_journal,sources,names,indices,Mode::Plain)
}
#[derive(Copy,Clone,PartialEq,Eq,Structural)]
enum Mode {Plain,CheckedScalar,ExclusiveScalar,ExclusiveTyped,ExclusiveMixed,Prepare,PrepareObjects}
#[verifier::rlimit(16)]
#[verifier::spinoff_prover]
fn run_ordered<P,E:ScalarEffect+Copy,T:?Sized>(runtime:&mut ManagedRuntime<P,(),E,T,()>,source_journal:&joint::Journal,sources:&[Source<E,T>],mut names:Names,indices:Vec<usize>,mode:Mode)
    ->(out:Batch<E,T>)
    requires old(runtime).wf(),supported_namespace(sources@,*source_journal),
        order::prefix(sources@,indices@,sources@.len()),order::chronological(sources@,indices@),
    ensures (mode==Mode::Prepare || mode==Mode::PrepareObjects) ==> out.calls.len()==0,
        (mode==Mode::Prepare || mode==Mode::PrepareObjects) && out.failure.is_none() ==> (forall|i:int|0<=i<out.providers.len() ==> (#[trigger] out.providers@[i]).owner.wf()) && out.bank.namespace()==source_journal.identity_namespace() && final(runtime).journal_spec()==out.bank.journal()
            && out.slots.wf(&out.bank) && super::slots::published(&out.bank,&out.slots,out.providers@,crate::lifecycle_state::services::capture::sources(final(runtime).publications().entries())),
        mode==Mode::ExclusiveMixed ==> out.mixed_prefix(sources@),mode==Mode::ExclusiveScalar ==> out.exclusive_prefix(),mode==Mode::ExclusiveTyped ==> out.typed_exclusive_prefix() && out.typed_replay_matches(sources@),
        final(runtime).wf(),out.bank.wf(),out.actual_prefix(sources@),out.order@==indices@,
        out.failure.is_none() ==> ((mode!=Mode::Prepare && mode!=Mode::PrepareObjects) ==> out.calls.len()==sources.len()) && out.succeeded()
            && ((mode==Mode::CheckedScalar || mode==Mode::ExclusiveScalar) ==> out.scalar_observations_match(sources@) && out.scalar_replay_matches(sources@)),
{
    hide(joint::valid);hide(joint::step);
    let validate=matches!(mode,Mode::CheckedScalar|Mode::ExclusiveScalar);
    let protect=mode==Mode::ExclusiveScalar;let typed_protect=mode==Mode::ExclusiveTyped;
    reveal(Source::input_spec);reveal(Source::provision_ports);
    let target=runtime.execution_journal();
    let mut out=Batch {slots:super::slots::Slots::new(),mixed_protection:Ghost(Seq::empty()),typed_protection:Ghost(Seq::empty()),blocked:None,protection:Ghost(Seq::empty()),order:Vec::new(),bank:bank::Bank::new(source_journal,&target),providers:Vec::new(),calls:Vec::new(),failure:None};
    out.order=indices;
    let ghost chosen=out.order@;
    let mut bindings:Vec<Binding>=Vec::new();let mut i=0;
    while i<out.order.len()
        invariant out.order@==chosen,chosen==indices@,order::prefix(sources@,chosen,sources@.len()),order::chronological(sources@,chosen),i<=out.order.len(),runtime.wf(),runtime.journal_spec()==out.bank.journal(),out.bank.wf(),out.slots.wf(&out.bank),out.bank.namespace()==source_journal.identity_namespace(),
            out.calls.len()==0,out.protection@.len()==0,out.typed_protection@.len()==0,out.mixed_protection@.len()==0,supported_namespace(sources@,*source_journal),
            (mode!=Mode::Prepare && mode!=Mode::PrepareObjects) ==> forall|k:int|0<=k<i ==> sources[chosen[k] as int].provision_ports().len()==0,
            forall|k:int|0<=k<bindings.len() ==> (#[trigger] bindings@[k]).valid(&out.bank,&out.slots) && ((mode!=Mode::Prepare && mode!=Mode::PrepareObjects) ==> bindings@[k].slot.is_none()),
        decreases out.order.len()-i,
    {
        let call=out.order[i];let source=&sources[call];
        if !source.provisions.is_empty() && (mode!=Mode::Prepare && mode!=Mode::PrepareObjects) {out.failure=Some(Failure::SourceProvisions {call});return out;}
        let mut j=0;
        while j<source.inputs.len()
            invariant out.order@==chosen,chosen==indices@,order::prefix(sources@,chosen,sources@.len()),order::chronological(sources@,chosen),j<=source.inputs.len(),source.wf(),supported_namespace(sources@,*source_journal),runtime.wf(),runtime.journal_spec()==out.bank.journal(),out.bank.wf(),out.slots.wf(&out.bank),
                out.bank.namespace()==source_journal.identity_namespace(),out.calls.len()==0,out.protection@.len()==0,out.typed_protection@.len()==0,out.mixed_protection@.len()==0,
                forall|k:int|0<=k<source.inputs.len() ==> source.inputs@[k].wf() && source.inputs@[k].namespace(out.bank.namespace()),
                forall|k:int|0<=k<bindings.len() ==> (#[trigger] bindings@[k]).valid(&out.bank,&out.slots) && ((mode!=Mode::Prepare && mode!=Mode::PrepareObjects) ==> bindings@[k].slot.is_none()),
            decreases source.inputs.len()-j,
        {
            let input=&source.inputs[j];
            let ghost previous_bank=out.bank;
            let result=out.bank.bind(input);
            proof {out.slots.extend_bank(&previous_bank,&out.bank);}
            let index=match result {Ok(n)=>n,Err(error)=>{out.failure=Some(Failure::Binding {call,error});return out;}};
            let pc=input.pc();
            if pc>=source.ports.len() {out.failure=Some(Failure::Capacity);return out;}
            let port=source.ports[pc];
            let catalog_slot=if (mode==Mode::Prepare || mode==Mode::PrepareObjects) && matches!(input.operand(),super::inputs::Operand::Scalar(_)) {
                let slot=match out.slots.bind(&out.bank,input,index) {Ok(n)=>n,Err(error)=>{out.failure=Some(Failure::Slot {call,error});return out;}};
                Some(slot)
            } else {None};
            proof {assert forall|n:int|0<=n<sources.len() implies (#[trigger] sources@[n]).wf() by {supported_at(sources@,*source_journal,n);}}
            if (mode==Mode::Prepare || mode==Mode::PrepareObjects) && provided_for_source(sources,source,port) {j+=1;continue;}
            let mut k=0;let mut found=false;
            while k<bindings.len()
                invariant out.order@==chosen,chosen==indices@,order::prefix(sources@,chosen,sources@.len()),order::chronological(sources@,chosen),runtime.wf(),runtime.journal_spec()==out.bank.journal(),out.bank.wf(),out.slots.wf(&out.bank),out.calls.len()==0,out.protection@.len()==0,out.typed_protection@.len()==0,out.mixed_protection@.len()==0,k<=bindings.len(),forall|a:int|0<=a<bindings.len() ==> (#[trigger] bindings@[a]).valid(&out.bank,&out.slots) && ((mode!=Mode::Prepare && mode!=Mode::PrepareObjects) ==> bindings@[a].slot.is_none()),
                decreases bindings.len()-k,
            {
                if bindings[k].port==port {
                    if bindings[k].index!=index && (mode!=Mode::Prepare && mode!=Mode::PrepareObjects) {out.failure=Some(Failure::ReboundPort {port});return out;}
                    found=true;
                }k+=1;
            }
            if !found {
                let (slot,index)=match catalog_slot {
                    Some(slot)=>{let index=out.slots.original_entry(slot).unwrap();proof {out.slots.entry_facts(&out.bank,slot as int);}(Some(slot),index)},
                    None=>(None,index),
                };
                bindings.push(Binding {port,index,slot,source_origin:source.binding_origin(port)});
            }j+=1;
        }
        let mut j=0;
        while j<source.dependencies.len()
            invariant out.order@==chosen,chosen==indices@,order::prefix(sources@,chosen,sources@.len()),order::chronological(sources@,chosen),runtime.wf(),runtime.journal_spec()==out.bank.journal(),out.bank.wf(),out.slots.wf(&out.bank),out.calls.len()==0,out.protection@.len()==0,out.typed_protection@.len()==0,out.mixed_protection@.len()==0,j<=source.dependencies.len(),
            decreases source.dependencies.len()-j,
        {
            let port=source.dependencies[j];let mut k=0;let mut found=false;
            while k<bindings.len() invariant out.order@==chosen,chosen==indices@,order::prefix(sources@,chosen,sources@.len()),order::chronological(sources@,chosen),runtime.wf(),runtime.journal_spec()==out.bank.journal(),out.bank.wf(),out.slots.wf(&out.bank),out.calls.len()==0,out.protection@.len()==0,out.typed_protection@.len()==0,out.mixed_protection@.len()==0,k<=bindings.len(),decreases bindings.len()-k,
            {if bindings[k].port==port {found=true;}k+=1;}
            if !found && (mode!=Mode::Prepare && mode!=Mode::PrepareObjects) {out.failure=Some(Failure::MissingInput {call,port});return out;}j+=1;
        }
        i+=1;
    }
    if mode==Mode::PrepareObjects {return out;}
    let mut i=0;
    while i<bindings.len()
        invariant out.order@==chosen,chosen==indices@,order::prefix(sources@,chosen,sources@.len()),order::chronological(sources@,chosen),i<=bindings.len(),runtime.wf(),runtime.journal_spec()==out.bank.journal(),out.bank.wf(),out.slots.wf(&out.bank),out.bank.namespace()==source_journal.identity_namespace(),out.calls.len()==0,out.protection@.len()==0,out.typed_protection@.len()==0,out.mixed_protection@.len()==0,
            (mode!=Mode::Prepare && mode!=Mode::PrepareObjects) ==> forall|k:int|0<=k<chosen.len() ==> sources[chosen[k] as int].provision_ports().len()==0,
            super::slots::published(&out.bank,&out.slots,out.providers@,crate::lifecycle_state::services::capture::sources(runtime.publications().entries())),
            (mode!=Mode::Prepare && mode!=Mode::PrepareObjects) ==> selection::providers_match(&out.bank,out.providers@,crate::lifecycle_state::services::capture::sources(runtime.publications().entries())),
            forall|k:int|0<=k<out.providers.len() ==> (#[trigger] out.providers@[k]).owner.wf(),
            forall|k:int|0<=k<bindings.len() ==> (#[trigger] bindings@[k]).valid(&out.bank,&out.slots) && ((mode!=Mode::Prepare && mode!=Mode::PrepareObjects) ==> bindings@[k].slot.is_none()),
        decreases bindings.len()-i,
    {
        let (anchor,work)=match names.take() {Some(n)=>n,None=>{out.failure=Some(Failure::Capacity);return out;}};
        let port=bindings[i].port;let mut realms=BTreeMap::new();realms.insert(port.key,port.realm);
        let provisions=vec![port.key];
        let definition=PluginDefinition::new(Vec::new(),provisions,Body::Managed(Function {code:Vec::new()}));
        let id=match runtime.register(None,&realms,anchor,definition,()) {
            Ok(id)=>id,Err((error,_,_))=>{out.failure=Some(Failure::ProviderRegistration(error));return out;},
        };
        let execution:Owner<(),(),(),(),T,(),()>=match runtime.begin_managed_execution(id,work) {
            Ok(owner)=>owner,Err(error)=>{out.failure=Some(Failure::ProviderBegin {id,error});return out;},
        };
        let (mut owner,report)=runtime.run_recorded_root(id,execution);
        let slot=match bindings[i].slot {
            Some(n)=>{proof {out.slots.entry_facts(&out.bank,n as int);}out.slots.published(n).unwrap()},
            None=>out.bank.slot(bindings[i].index).unwrap(),
        };
        if report.is_err() {out.providers.push(Provider {id,port,index:bindings[i].index,slot:bindings[i].slot,source_origin:bindings[i].source_origin,service:slot,owner,report});out.failure=Some(Failure::ProviderAdmission {id});return out;}
        if owner.provide(port,slot.clone()).is_err() {out.providers.push(Provider {id,port,index:bindings[i].index,slot:bindings[i].slot,source_origin:bindings[i].source_origin,service:slot,owner,report});out.failure=Some(Failure::ProviderPublication {id});return out;}
        let ghost previous_providers=out.providers@;
        let ghost previous_entries=runtime.publications().entries();
        let finished=owner.finish(runtime,id);out.providers.push(Provider {id,port,index:bindings[i].index,slot:bindings[i].slot,source_origin:bindings[i].source_origin,service:slot,owner,report});
        if let Err(error)=finished {out.failure=Some(Failure::ProviderFinish {id,error});return out;}
        proof {
            super::slots::preserve(&out.bank,&out.slots,previous_providers,previous_entries,runtime.publications().entries());
            if (mode!=Mode::Prepare && mode!=Mode::PrepareObjects) {selection::preserve_providers(&out.bank,previous_providers,previous_entries,runtime.publications().entries());}
            assert forall|k:int|0<=k<out.providers.len() implies {
                let p=#[trigger] out.providers@[k];
                &&& super::slots::provider(&out.bank,&out.slots,p,crate::lifecycle_state::services::capture::sources(runtime.publications().entries()))
                &&& (mode!=Mode::Prepare && mode!=Mode::PrepareObjects) ==> p.service==out.bank.service(p.index as int)
            } by {
                if k<previous_providers.len() {assert(out.providers@[k]==previous_providers[k]);}
                else {assert(out.providers@[k].id==id && out.providers@[k].port==port && out.providers@[k].index==bindings@[i as int].index);}
            }
        }
        i+=1;
    }
    if mode==Mode::Prepare || mode==Mode::PrepareObjects {return out;}
    if mode==Mode::ExclusiveMixed {
        let storage=super::mixed::Storage::new(&out.bank);let view=storage.payload_bank(&out.bank);
        let context=match storage.acquire(&out.bank) {Ok(context)=>context,Err(error)=>{out.failure=Some(Failure::Protection {call:None,error:super::protected::Error::Mixed(error)});return out;}};
        proof {storage.held_payload_bank(&out.bank,&view,&context);}
        if let Err(error)=context.payload.as_ref().unwrap().check_initial(&view) {context.release();out.failure=Some(Failure::Protection {call:None,error:super::protected::Error::Typed(error)});return out;}
        let mut context=Some(context);
        let out=super::mixed::run_calls(runtime,source_journal,sources,names,out,&mut context,&storage,&view);
        context.unwrap().release();return out;
    }
    if typed_protect {
        let storage=match out.bank.typed_storage() {Some(storage)=>storage,None=>{out.failure=Some(Failure::Protection {call:None,error:super::protected::Error::Typed(super::super::protected_typed::Error::NotTyped)});return out;}};
        proof {storage.acquire_ready(&out.bank);}
        let context=match super::super::protected_typed::Context::acquire(storage.values.as_slice(),storage.slots) {
            Ok(context)=>context,Err(error)=>{out.failure=Some(Failure::Protection {call:None,error:super::protected::Error::Typed(error)});return out;},
        };
        proof {assert(context.bank(&out.bank));}
        if let Err(error)=context.check_initial(&out.bank) {
            context.release();out.failure=Some(Failure::Protection {call:None,error:super::protected::Error::Typed(error)});return out;
        }
        let mut typed=Some(context);
        let out=run_typed_calls(runtime,source_journal,sources,names,out,&mut typed);
        typed.unwrap().release();return out;
    }
    if !protect {let mut mode=None;return run_calls(runtime,source_journal,sources,names,out,validate,&mut mode);}
    let storage=match out.bank.scalar_storage() {Some(storage)=>storage,None=>{out.failure=Some(Failure::Protection {call:None,error:super::protected::Error::NotScalar});return out;}};
    proof {storage.acquire_ready(&out.bank);}
    let context=match super::super::protected::Context::acquire(storage.values.as_slice(),storage.slots.as_slice()) {
        Ok(context)=>context,Err(super::super::protected::Error::ChangedSlot {index})=>{out.failure=Some(Failure::Protection {call:None,error:super::protected::Error::ChangedSlot {index}});return out;},
    };
    proof {
        assert forall|i:int|0<=i<out.bank.len_spec() implies out.bank.target(i) is Scalar && context.targets()[i]==out.bank.target(i)->Scalar_0
            && out.bank.service(i).managed()==Some(context.slot_names()[i]) by {assert(storage.values@[i]==out.bank.target(i)->Scalar_0);}
        assert(context.bank(&out.bank));
    }
    let mut mode=Some(context);
    let out=run_calls(runtime,source_journal,sources,names,out,validate,&mut mode);
    mode.unwrap().release();out
}
#[verifier::rlimit(24)]
fn run_calls<P,E:ScalarEffect+Copy,T:?Sized>(runtime:&mut ManagedRuntime<P,(),E,T,()>,_source_journal:&joint::Journal,sources:&[Source<E,T>],mut names:Names,mut out:Batch<E,T>,validate:bool,mode:&mut Option<super::super::protected::Context<'_>>)->(result:Batch<E,T>)
    requires old(runtime).wf(),out.bank.wf(),old(runtime).journal_spec()==out.bank.journal(),out.bank.namespace()==_source_journal.identity_namespace(),
        supported_namespace(sources@,*_source_journal),out.calls.len()==0,out.protection@.len()==0,
        order::prefix(sources@,out.order@,sources@.len()),order::chronological(sources@,out.order@),
        forall|k:int|0<=k<out.order.len() ==> sources[out.order@[k] as int].provision_ports().len()==0,
        selection::providers_match(&out.bank,out.providers@,crate::lifecycle_state::services::capture::sources(old(runtime).publications().entries())),
        old(mode).is_some() ==> old(mode)->Some_0.wf() && old(mode)->Some_0.bank(&out.bank),
    ensures old(mode).is_some() ==> result.exclusive_prefix(),
        final(runtime).wf(),result.bank.wf(),result.actual_prefix(sources@),result.order@==out.order@,
        result.failure.is_none() ==> result.calls.len()==sources.len() && result.succeeded()
            && (validate ==> result.scalar_observations_match(sources@) && result.scalar_replay_matches(sources@)),
        final(mode).is_some()==old(mode).is_some(),final(mode).is_some() ==> final(mode)->Some_0.wf()
            && final(mode)->Some_0.targets()==old(mode)->Some_0.targets() && final(mode)->Some_0.slot_names()==old(mode)->Some_0.slot_names(),
{
    hide(joint::valid);hide(joint::step);hide(Source::wf);
    hide(TargetRun::from_source);hide(TargetRun::scalar_replay_matches);hide(TargetRun::scalar_observations_match);
    reveal(Source::input_spec);reveal(Source::provision_ports);
    let ghost chosen=out.order@;
    let mut i=0;
    while i<out.order.len()
        invariant mode.is_some() ==> out.exclusive_prefix()
                && (out.protection@.len()>0 ==> out.protection@.last().after==mode->Some_0.states()),
            mode.is_some()==old(mode).is_some(),
            mode.is_some() ==> mode->Some_0.wf() && mode->Some_0.bank(&out.bank)
                && mode->Some_0.targets()==old(mode)->Some_0.targets() && mode->Some_0.slot_names()==old(mode)->Some_0.slot_names(),
            out.order@==chosen,order::prefix(sources@,chosen,sources@.len()),order::chronological(sources@,chosen),i<=out.order.len(),runtime.wf(),runtime.journal_spec()==out.bank.journal(),out.bank.wf(),out.bank.namespace()==_source_journal.identity_namespace(),out.calls.len()==i,out.actual_prefix(sources@),out.succeeded(),
            validate ==> out.scalar_observations_match(sources@) && out.scalar_replay_matches(sources@),
            forall|k:int|0<=k<chosen.len() ==> sources[chosen[k] as int].provision_ports().len()==0,
            selection::providers_match(&out.bank,out.providers@,crate::lifecycle_state::services::capture::sources(runtime.publications().entries())),
            supported_namespace(sources@,*_source_journal),
        decreases out.order.len()-i,
    {
        let (anchor,work_domain)=match names.take() {Some(n)=>n,None=>{out.failure=Some(Failure::Capacity);return out;}};
        let call=out.order[i];
        let ghost before=if mode.is_some() {mode->Some_0.states()} else {Seq::empty()};
        let mut run:Run<E,T>=if mode.is_some() {
            if !sources[call].kernel_only() {out.failure=Some(Failure::Protection {call:Some(call),error:super::protected::Error::NotControlled});return out;}
            if !sources[call].succeeded() {out.failure=Some(Failure::Invocation {call});return out;}
            match sources[call].instantiate_protected(runtime,Destination {parent:None,anchor,host:(),work_domain},&out.bank,out.providers.as_slice(),mode) {
                Ok(run)=>run,
                Err(super::protected::Start::Before(error))=>{out.failure=Some(Failure::Start {call,error});return out;},
                Err(super::protected::Start::After {id,owner,error})=>{out.blocked=Some((id,*owner));out.failure=Some(Failure::Protection {call:Some(call),error});return out;},
            }
        } else {match sources[call].instantiate(runtime,Destination {parent:None,anchor,host:(),work_domain}) {
            Ok(run)=>run,Err(error)=>{out.failure=Some(Failure::Start {call,error});return out;},
        }};
        if mode.is_some() {
            let ghost steps=super::protected::result_steps(run.report->Ok_0.result);
            let ghost interval=super::protected::Interval {before,after:mode->Some_0.states(),routes:mode->Some_0.routes(),steps};
            proof {if run.report->Ok_0.result.is_err() {super::super::protected::empty::<T>(before,mode->Some_0.routes());}interval.establish();}
            out.protection=Ghost(out.protection@.push(interval));
        }
        let succeeded=match &run.report {
            Ok(r)=>match &r.result {Ok(report)=>report.succeeded(),Err(_)=>false},Err(_)=>false,
        };
        if !succeeded {out.calls.push(run);out.failure=Some(Failure::Invocation {call});return out;}
        if validate && mode.is_none() {
            proof {
                reveal(Source::input_spec);reveal(Source::provision_ports);
                assert(run.captured_providers(&out.bank,out.providers@));
                assert(sources[call as int].provision_ports().len()==0);
                assert forall|j:int|0<=j<sources[call as int].input_spec().len() implies (#[trigger] sources[call as int].input_spec()[j]).identity_spec().namespace()==out.bank.namespace() by {
                    assert(sources[call as int].inputs@[j].identity_spec().namespace()==_source_journal.identity_namespace());
                }
            }
            if let Err(error)=run.check_scalar_replay(&sources[call],&out.bank,out.providers.as_slice()) {
                out.calls.push(run);out.failure=Some(match error {
                    selection::Error::Observation(error)=>Failure::Observation {call,error},
                    error=>Failure::Selection {call,error},
                });return out;
            }
        }
        proof {
            assert(run.owner.wf()) by {reveal(TargetRun::from_source);}
            if validate {assert(run.scalar_observations_match(&sources[call as int])) by {reveal(TargetRun::scalar_replay_matches);}}
        }
        let ghost before_finish=runtime.publications().entries();let ghost before_run=run;
        let finished=run.owner.finish(runtime,run.id);
        proof {
            assert(run.report==before_run.report && run.inputs==before_run.inputs && run.id==before_run.id);
            assert(run.owner.baseline()==before_run.owner.baseline() && run.owner.recovery_boundary()==before_run.owner.recovery_boundary());
            assert(run.from_source(&sources[call as int])) by {reveal(TargetRun::from_source);}
            if validate {
                assert(run.scalar_replay_matches(&sources[call as int],&out.bank)) by {reveal(TargetRun::scalar_replay_matches);reveal(TargetRun::scalar_observations_match);}
                assert(run.scalar_observations_match(&sources[call as int])) by {reveal(TargetRun::scalar_observations_match);}
            }
            selection::preserve_providers(&out.bank,out.providers@,before_finish,runtime.publications().entries());
        }
        out.calls.push(run);
        if let Err(error)=finished {out.failure=Some(Failure::Finish {call,error});return out;}
        i+=1;
    }
    out
}

#[verifier::rlimit(24)]
#[verifier::spinoff_prover]
fn run_typed_calls<P,E:ScalarEffect+Copy,T:?Sized>(runtime:&mut ManagedRuntime<P,(),E,T,()>,_source_journal:&joint::Journal,sources:&[Source<E,T>],mut names:Names,mut out:Batch<E,T>,typed:&mut Option<super::super::protected_typed::Context<'_,T,()>>)->(result:Batch<E,T>)
    requires old(runtime).wf(),out.bank.wf(),old(runtime).journal_spec()==out.bank.journal(),out.bank.namespace()==_source_journal.identity_namespace(),
        supported_namespace(sources@,*_source_journal),out.calls.len()==0,out.typed_protection@.len()==0,out.mixed_protection@.len()==0,
        order::prefix(sources@,out.order@,sources@.len()),order::chronological(sources@,out.order@),
        forall|k:int|0<=k<out.order.len() ==> sources[out.order@[k] as int].provision_ports().len()==0,
        selection::providers_match(&out.bank,out.providers@,crate::lifecycle_state::services::capture::sources(old(runtime).publications().entries())),
        old(typed).is_some(),old(typed)->Some_0.wf(),old(typed)->Some_0.bank(&out.bank),
        forall|i:int|0<=i<out.bank.len_spec() ==> #[trigger] old(typed)->Some_0.initial_entry(&out.bank,i),
    ensures result.typed_exclusive_prefix(),result.typed_replay_matches(sources@),final(runtime).wf(),result.bank.wf(),result.actual_prefix(sources@),result.order@==out.order@,
        result.failure.is_none() ==> result.calls.len()==sources.len() && result.succeeded(),
        final(typed).is_some(),final(typed)->Some_0.wf(),final(typed)->Some_0.targets()==old(typed)->Some_0.targets(),final(typed)->Some_0.slots()==old(typed)->Some_0.slots(),
{
    hide(joint::valid);hide(joint::step);hide(Source::wf);hide(TargetRun::from_source);hide(super::typed_correspondence::heaps);hide(super::typed_correspondence::paired);hide(super::typed_correspondence::aligned);
    reveal(Source::input_spec);reveal(Source::provision_ports);
    let mut tracker=super::typed_tracker::Tracker::start(&out.bank,typed.as_ref().unwrap());
    let ghost chosen=out.order@;let mut i=0;
    while i<out.order.len()
        invariant typed.is_some(),typed->Some_0.wf(),typed->Some_0.bank(&out.bank),
            tracker.wf(&out.bank),super::typed_correspondence::heaps(tracker.names(),tracker.states(),typed->Some_0.states()),
            out.typed_replay_matches(sources@),
            out.typed_protection@.len()>0 ==> out.typed_protection@.last().correspondence.is_some()
                && out.typed_protection@.last().correspondence.unwrap().after_source==tracker.states()
                && out.typed_protection@.last().correspondence.unwrap().after_names==tracker.names(),
            typed->Some_0.targets()==old(typed)->Some_0.targets(),typed->Some_0.slots()==old(typed)->Some_0.slots(),
            out.typed_exclusive_prefix(),out.typed_protection@.len()>0 ==> out.typed_protection@.last().after==typed->Some_0.states() && out.typed_protection@.last().after_revisions==typed->Some_0.revisions(),
            out.order@==chosen,order::prefix(sources@,chosen,sources@.len()),order::chronological(sources@,chosen),i<=out.order.len(),runtime.wf(),runtime.journal_spec()==out.bank.journal(),out.bank.wf(),out.bank.namespace()==_source_journal.identity_namespace(),out.calls.len()==i,out.actual_prefix(sources@),out.succeeded(),
            forall|k:int|0<=k<chosen.len() ==> sources[chosen[k] as int].provision_ports().len()==0,
            selection::providers_match(&out.bank,out.providers@,crate::lifecycle_state::services::capture::sources(runtime.publications().entries())),supported_namespace(sources@,*_source_journal),
        decreases out.order.len()-i,
    {
        let (anchor,work_domain)=match names.take() {Some(n)=>n,None=>{out.failure=Some(Failure::Capacity);return out;}};
        let call=out.order[i];
        if !sources[call].typed_only() {out.failure=Some(Failure::Protection {call:Some(call),error:super::protected::Error::Typed(super::super::protected_typed::Error::NotTyped)});return out;}
        if !sources[call].succeeded() {out.failure=Some(Failure::Invocation {call});return out;}
        let plan=match tracker.prepare(&sources[call],&out.bank) {
            Ok(plan)=>plan,Err(error)=>{out.failure=Some(Failure::Protection {call:Some(call),error:super::protected::Error::Typed(error)});return out;},
        };
        let ghost before=typed->Some_0.states();let ghost before_revisions=typed->Some_0.revisions();let mut mode=None;
        let mut run=match sources[call].instantiate_guarded(runtime,Destination {parent:None,anchor,host:(),work_domain},&out.bank,out.providers.as_slice(),&mut mode,typed) {
            Ok(run)=>run,
            Err(super::protected::Start::Before(error))=>{out.failure=Some(Failure::Start {call,error});return out;},
            Err(super::protected::Start::After {id,owner,error})=>{out.blocked=Some((id,*owner));out.failure=Some(Failure::Protection {call:Some(call),error});return out;},
        };
        let ghost steps=super::protected::result_steps(run.report->Ok_0.result);
        let ghost correspondence=if run.report->Ok_0.result.is_ok() {
            Some(super::typed_correspondence::certify(&sources[call as int],&run,&plan,&out.bank,before,before_revisions,typed->Some_0.routes()))
        } else {None};
        proof {if correspondence.is_some() {
            correspondence.unwrap().facts();
            typed->Some_0.mapped_steps(&out.bank,sources[call as int].original().result->Ok_0.steps@,steps);
        }}
        let ghost interval=super::typed_protected::Interval {correspondence,before,after:typed->Some_0.states(),before_revisions,after_revisions:typed->Some_0.revisions(),routes:typed->Some_0.routes(),steps};
        proof {if run.report->Ok_0.result.is_err() {super::super::protected_typed::empty::<T>(before,before_revisions,typed->Some_0.routes());}interval.establish();}
        out.typed_protection=Ghost(out.typed_protection@.push(interval));
        let succeeded=match &run.report {Ok(r)=>match &r.result {Ok(report)=>report.succeeded(),Err(_)=>false},Err(_)=>false};
        if !succeeded {out.calls.push(run);out.failure=Some(Failure::Invocation {call});return out;}
        proof {correspondence.unwrap().facts();}
        tracker=plan.finish(Ghost(correspondence.unwrap().after_names));
        proof {assert(run.owner.wf()) by {reveal(TargetRun::from_source);}}
        let ghost before_finish=runtime.publications().entries();let ghost before_run=run;
        let finished=run.owner.finish(runtime,run.id);
        proof {
            assert(run.report==before_run.report && run.inputs==before_run.inputs && run.id==before_run.id);
            assert(run.owner.baseline()==before_run.owner.baseline() && run.owner.recovery_boundary()==before_run.owner.recovery_boundary());
            assert(run.from_source(&sources[call as int])) by {reveal(TargetRun::from_source);}
            selection::preserve_providers(&out.bank,out.providers@,before_finish,runtime.publications().entries());
        }
        out.calls.push(run);
        if let Err(error)=finished {out.failure=Some(Failure::Finish {call,error});return out;}i+=1;
    }out
}

#[derive(Debug)]
pub enum PreflightError {NotControlled {call:usize},NotTyped {call:usize},NotScalar {call:usize},SourceIncomplete {call:usize},Ordering(order::Error),Continuity(continuity::Error)}
/// Source continuity is a checked fact about actual retained observations.
/// The batch still reports target admission, execution and observation failures.
#[allow(dead_code)]
pub struct CheckedScalarBatch<E,T:?Sized> {pub batch:Batch<E,T>,pub history:Ghost<continuity::Checked<T>>}
impl<E:ScalarEffect,T:?Sized> CheckedScalarBatch<E,T> {
    pub closed spec fn history(&self)->continuity::Checked<T> {self.history@}
    pub open spec fn certified_source(&self,sources:Seq<Source<E,T>>)->bool {
        self.history().wf() && self.history().steps()==continuity::trace(sources,self.batch.order@)
    }
}
/// Opt-in scalar replay with automatic source continuity and actual target
/// observation checks. Preflight has no target effects. A later mismatch is
/// detected after that invocation, before Finish or the next call; all owners
/// and already registered inverses are returned through the ordinary Batch.
pub fn run_checked_scalar<P,E:ScalarEffect+Copy,T:?Sized>(runtime:&mut ManagedRuntime<P,(),E,T,()>,source_journal:&joint::Journal,sources:&[Source<E,T>],names:Names)
    ->(out:Result<CheckedScalarBatch<E,T>,PreflightError>)
    requires old(runtime).wf(),supported_namespace(sources@,*source_journal),
    ensures final(runtime).wf(),out.is_err() ==> *final(runtime)==*old(runtime),
        out.is_ok() ==> out->Ok_0.certified_source(sources@) && out->Ok_0.batch.bank.wf()
            && out->Ok_0.batch.actual_prefix(sources@)
            && order::prefix(sources@,out->Ok_0.batch.order@,sources@.len()) && order::chronological(sources@,out->Ok_0.batch.order@)
            && (out->Ok_0.batch.failure.is_none() ==> out->Ok_0.batch.calls.len()==sources.len()
                && out->Ok_0.batch.succeeded() && out->Ok_0.batch.scalar_observations_match(sources@)
                && out->Ok_0.batch.scalar_replay_matches(sources@)),
{
    let mut i=0;
    while i<sources.len()
        invariant i<=sources.len(),runtime.wf(),*runtime==*old(runtime),supported_namespace(sources@,*source_journal),
        decreases sources.len()-i,
    {
        if !sources[i].is_scalar_program() {return Err(PreflightError::NotScalar {call:i});}
        if !sources[i].succeeded() {return Err(PreflightError::SourceIncomplete {call:i});}
        i+=1;
    }
    let indices=match order::plan(sources) {Ok(indices)=>indices,Err(error)=>return Err(PreflightError::Ordering(error))};
    let _history=match continuity::check(sources,indices.as_slice()) {Ok(history)=>history,Err(error)=>return Err(PreflightError::Continuity(error))};
    let batch=run_ordered(runtime,source_journal,sources,names,indices,Mode::CheckedScalar);
    Ok(CheckedScalarBatch {batch,history:Ghost(_history)})
}

/// Validate the complete source set before allocating target providers. This
/// gate is executable; the replay then shares `run` and its original interpreter.
/// Controlled execution excludes callback interference, not lifecycle/admission
/// failure or unrelated writes by other owners.
pub fn run_controlled<P,E:ScalarEffect+Copy,T:?Sized>(runtime:&mut ManagedRuntime<P,(),E,T,()>,source_journal:&joint::Journal,sources:&[Source<E,T>],names:Names)
    ->(out:Result<Batch<E,T>,usize>)
    requires old(runtime).wf(),supported_namespace(sources@,*source_journal),
    ensures final(runtime).wf(),
        out.is_err() ==> out->Err_0<sources.len() && !sources[out->Err_0 as int].program().controlled() && *final(runtime)==*old(runtime),
        out.is_ok() ==> out->Ok_0.bank.wf() && out->Ok_0.actual_prefix(sources@)
            && (forall|i:int|0<=i<sources.len() ==> (#[trigger] sources[i]).program().controlled())
            && (forall|i:int|0<=i<out->Ok_0.calls.len() ==> (#[trigger] out->Ok_0.calls@[i]).report->Ok_0.result.is_ok()
                ==> out->Ok_0.calls@[i].report->Ok_0.result->Ok_0.no_scalar_interference()),
        out.is_ok() && out->Ok_0.failure.is_none() ==> out->Ok_0.calls.len()==sources.len() && out->Ok_0.succeeded()
            && order::prefix(sources@,out->Ok_0.order@,sources@.len()) && order::chronological(sources@,out->Ok_0.order@),
{
    let mut i=0;
    while i<sources.len()
        invariant i<=sources.len(),supported_namespace(sources@,*source_journal),runtime.wf(),*runtime==*old(runtime),
            forall|j:int|0<=j<i ==> (#[trigger] sources[j]).program().controlled(),
        decreases sources.len()-i,
    {if !sources[i].is_controlled() {return Err(i);}i+=1;}
    let out=run(runtime,source_journal,sources,names);
    proof {
        assert forall|i:int|0<=i<out.calls.len() && (#[trigger] out.calls@[i]).report->Ok_0.result.is_ok()
            implies out.calls@[i].report->Ok_0.result->Ok_0.no_scalar_interference() by {
            let target=out.calls@[i];let report=target.report->Ok_0;let source=sources[out.order@[i] as int];
            report.result->Ok_0.controlled_execution(source.program(),report.ports@,target.owner.baseline().value_state().unwrap());
        }
    }
    Ok(out)
}

/// Hold every actual bank cell and slot across the complete target call batch.
/// The public input contains no lock guards, provider certificates or expected
/// target states. All owners survive partial failures; no callbacks run locked.
pub fn run_exclusive<P,E:ScalarEffect+Copy,T:?Sized>(runtime:&mut ManagedRuntime<P,(),E,T,()>,source_journal:&joint::Journal,sources:&[Source<E,T>],names:Names)
    ->(out:Result<Batch<E,T>,PreflightError>)
    requires old(runtime).wf(),supported_namespace(sources@,*source_journal),
    ensures final(runtime).wf(),out.is_err() ==> *final(runtime)==*old(runtime),
        out.is_ok() ==> out->Ok_0.exclusive_prefix() && out->Ok_0.bank.wf() && out->Ok_0.actual_prefix(sources@)
            && (out->Ok_0.failure.is_none() ==> out->Ok_0.calls.len()==sources.len() && out->Ok_0.succeeded()
                && out->Ok_0.scalar_observations_match(sources@) && out->Ok_0.scalar_replay_matches(sources@)),
{
    let mut i=0;
    while i<sources.len()
        invariant i<=sources.len(),runtime.wf(),*runtime==*old(runtime),supported_namespace(sources@,*source_journal),
        decreases sources.len()-i,
    {
        if !sources[i].kernel_only() {return Err(PreflightError::NotScalar {call:i});}
        if !sources[i].succeeded() {return Err(PreflightError::SourceIncomplete {call:i});}i+=1;
    }
    let indices=match order::plan(sources) {Ok(indices)=>indices,Err(error)=>return Err(PreflightError::Ordering(error))};
    let _history=match continuity::check(sources,indices.as_slice()) {Ok(history)=>history,Err(error)=>return Err(PreflightError::Continuity(error))};
    Ok(run_ordered(runtime,source_journal,sources,names,indices,Mode::ExclusiveScalar))
}

/// Typed functions use actual held payloads and original cleanup registration.
/// Source continuity is checked before publishing target providers. Opaque
/// payload interiors and general dynamic lifecycle transport remain separate.
pub fn run_exclusive_typed<P,E:ScalarEffect+Copy,T:?Sized>(runtime:&mut ManagedRuntime<P,(),E,T,()>,source_journal:&joint::Journal,sources:&[Source<E,T>],names:Names)
    ->(out:Result<Batch<E,T>,PreflightError>)
    requires old(runtime).wf(),supported_namespace(sources@,*source_journal),
    ensures final(runtime).wf(),out.is_err() ==> *final(runtime)==*old(runtime),
        out.is_ok() ==> out->Ok_0.typed_exclusive_prefix() && out->Ok_0.typed_replay_matches(sources@) && out->Ok_0.bank.wf() && out->Ok_0.actual_prefix(sources@)
            && (out->Ok_0.failure.is_none() ==> out->Ok_0.calls.len()==sources.len() && out->Ok_0.succeeded()),
{
    let mut i=0;
    while i<sources.len()
        invariant i<=sources.len(),runtime.wf(),*runtime==*old(runtime),supported_namespace(sources@,*source_journal),
        decreases sources.len()-i,
    {
        if !sources[i].typed_only() {return Err(PreflightError::NotTyped {call:i});}
        if !sources[i].succeeded() {return Err(PreflightError::SourceIncomplete {call:i});}i+=1;
    }
    let indices=match order::plan(sources) {Ok(indices)=>indices,Err(error)=>return Err(PreflightError::Ordering(error))};
    let _history=match continuity::check(sources,indices.as_slice()) {Ok(history)=>history,Err(error)=>return Err(PreflightError::Continuity(error))};
    Ok(run_ordered(runtime,source_journal,sources,names,indices,Mode::ExclusiveTyped))
}

}

verus! {
/// Execute heterogeneous controlled functions with the original interpreter,
/// holding both scalar and typed allocations across the complete batch.
/// Generic payload interiors remain opaque; closed values provide their own
/// explicit reference-transport contract.
pub fn run_exclusive_mixed<P,E:ScalarEffect+Copy,T:?Sized>(runtime:&mut ManagedRuntime<P,(),E,T,()>,source_journal:&joint::Journal,sources:&[Source<E,T>],names:Names)
    ->(out:Result<Batch<E,T>,PreflightError>)
    requires old(runtime).wf(),supported_namespace(sources@,*source_journal),
    ensures final(runtime).wf(),out.is_err() ==> *final(runtime)==*old(runtime),
        out.is_ok() ==> out->Ok_0.mixed_prefix(sources@) && out->Ok_0.bank.wf() && out->Ok_0.actual_prefix(sources@)
            && (out->Ok_0.failure.is_none() ==> out->Ok_0.calls.len()==sources.len() && out->Ok_0.succeeded()),
{
    let mut i=0;
    while i<sources.len()
        invariant i<=sources.len(),runtime.wf(),*runtime==*old(runtime),supported_namespace(sources@,*source_journal),
        decreases sources.len()-i,
    {
        if !sources[i].is_controlled() {return Err(PreflightError::NotControlled {call:i});}
        if !sources[i].succeeded() {return Err(PreflightError::SourceIncomplete {call:i});}i+=1;
    }
    let indices=match order::plan(sources) {Ok(indices)=>indices,Err(error)=>return Err(PreflightError::Ordering(error))};
    let _history=match continuity::check(sources,indices.as_slice()) {Ok(history)=>history,Err(error)=>return Err(PreflightError::Continuity(error))};
    Ok(run_ordered(runtime,source_journal,sources,names,indices,Mode::ExclusiveMixed))
}
}

verus! {
/// Prepare shared allocations and real providers without invoking any source
/// function. The resumable session owns the subsequent protected invocations.
pub(crate) fn prepare<P,E:ScalarEffect+Copy,T:?Sized>(runtime:&mut ManagedRuntime<P,(),E,T,()>,source_journal:&joint::Journal,sources:&[Source<E,T>],names:Names)
    ->(out:Result<Batch<E,T>,PreflightError>)
    requires old(runtime).wf(),supported_namespace(sources@,*source_journal),
    ensures final(runtime).wf(),out.is_err() ==> *final(runtime)==*old(runtime),
        out.is_ok() ==> out->Ok_0.bank.wf() && out->Ok_0.calls.len()==0 && order::prefix(sources@,out->Ok_0.order@,sources@.len()) && order::chronological(sources@,out->Ok_0.order@)
            && (out->Ok_0.failure.is_none() ==> (forall|i:int|0<=i<out->Ok_0.providers.len() ==> (#[trigger] out->Ok_0.providers@[i]).owner.wf()) && out->Ok_0.bank.namespace()==source_journal.identity_namespace() && final(runtime).journal_spec()==out->Ok_0.bank.journal()
                && out->Ok_0.slots.wf(&out->Ok_0.bank) && super::slots::published(&out->Ok_0.bank,&out->Ok_0.slots,out->Ok_0.providers@,crate::lifecycle_state::services::capture::sources(final(runtime).publications().entries()))),
{
    let indices=match order::plan(sources) {Ok(indices)=>indices,Err(error)=>return Err(PreflightError::Ordering(error))};
    Ok(run_ordered(runtime,source_journal,sources,names,indices,Mode::Prepare))
}
pub(crate) fn prepare_objects<P,E:ScalarEffect+Copy,T:?Sized>(runtime:&mut ManagedRuntime<P,(),E,T,()>,source_journal:&joint::Journal,sources:&[Source<E,T>],names:Names)
    ->(out:Result<Batch<E,T>,PreflightError>)
    requires old(runtime).wf(),supported_namespace(sources@,*source_journal),
    ensures final(runtime).wf(),out.is_err() ==> *final(runtime)==*old(runtime),
        out.is_ok() ==> out->Ok_0.bank.wf() && out->Ok_0.calls.len()==0 && order::prefix(sources@,out->Ok_0.order@,sources@.len()) && order::chronological(sources@,out->Ok_0.order@)
            && (out->Ok_0.failure.is_none() ==> (forall|i:int|0<=i<out->Ok_0.providers.len() ==> (#[trigger] out->Ok_0.providers@[i]).owner.wf()) && out->Ok_0.bank.namespace()==source_journal.identity_namespace() && final(runtime).journal_spec()==out->Ok_0.bank.journal()
                && out->Ok_0.slots.wf(&out->Ok_0.bank) && super::slots::published(&out->Ok_0.bank,&out->Ok_0.slots,out->Ok_0.providers@,crate::lifecycle_state::services::capture::sources(final(runtime).publications().entries()))),
{
    let indices=match order::plan(sources) {Ok(indices)=>indices,Err(error)=>return Err(PreflightError::Ordering(error))};
    Ok(run_ordered(runtime,source_journal,sources,names,indices,Mode::PrepareObjects))
}
}

verus! {
pub fn provided_in_sources<E:ScalarEffect,T:?Sized>(sources:&[Source<E,T>],port:Port)->(out:bool)
    ensures out==(exists|i:int|0<=i<sources.len() && (#[trigger] sources@[i]).provision_ports().contains(port)),
{
    let mut i=0;while i<sources.len()
        invariant i<=sources.len(),forall|j:int|0<=j<i ==> !(#[trigger] sources@[j]).provision_ports().contains(port),
        decreases sources.len()-i,
    {if sources[i].provides(port) {return true;}i+=1;}false
}
}

verus! {
pub fn provided_for_source<E:ScalarEffect,T:?Sized>(sources:&[Source<E,T>],source:&Source<E,T>,port:Port)->(out:bool)
    requires source.wf(),forall|i:int|0<=i<sources.len() ==> (#[trigger] sources@[i]).wf(),
{
    if source.provides(port) {return true;}
    let environment=match source.declared_environment() {Some(e)=>e,None=>return false};
    let binding=match environment.binding(port) {Some(b)=>b,None=>return false};
    let mut i=0;
    while i<sources.len()
        invariant i<=sources.len(),forall|j:int|0<=j<sources.len() ==> (#[trigger] sources@[j]).wf(),
        decreases sources.len()-i,
    {if sources[i].provides(port) && sources[i].source_origin()==binding.origin {return true;}i+=1;}false
}
}
