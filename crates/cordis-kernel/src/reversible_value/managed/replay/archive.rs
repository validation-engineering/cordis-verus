//! Persistent correspondence for protected calls separated by real cleanup.
//! Each checkpoint retains an authenticated source input and target capture;
//! re-entry checks the currently held cell before the next original invocation.
use super::super::protected_typed::Context;
#[cfg(verus_keep_ghost)]
use super::super::Step;
use super::typed_correspondence::epochs;
use super::{bank::Bank, inputs::Input};
#[cfg(verus_keep_ghost)]
use super::{typed, typed_correspondence as relation};
use crate::reversible_value::payload::{Capture, State};
use vstd::prelude::*;

verus! {
broadcast use vstd::seq_lib::group_seq_properties;
#[derive(Debug)]
pub enum Error {Allocation {step:usize},SourceState {step:usize},SourceOrder {step:usize},TargetState {entry:usize},TargetOrder {entry:usize}}
struct Head<T:?Sized> {input:Input<T>,initial:bool}
impl<T:?Sized> Head<T> {
    spec fn state(&self)->State<T> {if self.initial {self.input.source().before()->Payload_0} else {self.input.source().after()->Payload_0}}
    spec fn wf(&self,bank:&Bank<T>,i:int)->bool {self.input.wf() && self.input.source().result is Payload && self.input.source().address()==bank.address(i) && self.input.identity_spec().namespace()==bank.namespace()}
    fn duplicate(&self)->(out:Self)
        requires self.input.wf(),ensures out.input.wf(),out.input.source()==self.input.source(),out.input.identity_spec()==self.input.identity_spec(),out.initial==self.initial,
    {Self {input:self.input.duplicate(),initial:self.initial}}
}
struct Point<T:?Sized> {source:Head<T>,target:Capture<T>}
impl<T:?Sized> Point<T> {
    spec fn wf(&self,bank:&Bank<T>,i:int,names:Map<u64,u64>)->bool {
        self.source.wf(bank,i) && self.target.wf()
            && self.target.owner().journal_spec()==bank.target_address(i).journal && self.target.owner().key()==bank.target_address(i).key
            && typed::related(names,self.source.state(),self.target.observation().state())
    }
}
struct Entry<T:?Sized> {history:Vec<Point<T>>,source_clock:u64,target_clock:u64,names:Ghost<Map<u64,u64>>}
impl<T:?Sized> Entry<T> {
    spec fn wf(&self,bank:&Bank<T>,i:int)->bool {
        typed::injective(self.names@) && epochs::ordered(self.names@) && typed::bounded(self.names@,self.source_clock,self.target_clock)
            && forall|j:int|0<=j<self.history.len() ==> (#[trigger] self.history@[j]).wf(bank,i,self.names@)
    }
    #[allow(unused_variables)] // Runtime arguments also anchor erased provenance contracts.
    fn select(&self,current:&Capture<T>,bank:&Bank<T>,entry:usize)->(out:Result<Head<T>,Error>)
        requires self.wf(bank,entry as int),current.wf(),current.owner().journal_spec()==bank.target_address(entry as int).journal,current.owner().key()==bank.target_address(entry as int).key,
        ensures out.is_ok() ==> out->Ok_0.wf(bank,entry as int)
            && typed::related(self.names@,out->Ok_0.state(),current.observation().state()) && self.target_clock<=current.revision_spec(),
    {
        if current.revision()<self.target_clock {return Err(Error::TargetOrder {entry});}
        let mut i=0;
        while i<self.history.len()
            invariant self.wf(bank,entry as int),current.wf(),current.owner().journal_spec()==bank.target_address(entry as int).journal,current.owner().key()==bank.target_address(entry as int).key,
                self.target_clock<=current.revision_spec(),i<=self.history.len(),
            decreases self.history.len()-i,
        {
            let point=&self.history[i];
            if current.same_head_at(&point.target) {return Ok(point.source.duplicate());}i+=1;
        }Err(Error::TargetState {entry})
    }
}
pub struct Archive<T:?Sized> {entries:Vec<Entry<T>>}
impl<T:?Sized> Archive<T> {
    pub closed spec fn wf(&self,bank:&Bank<T>)->bool {self.entries.len()==bank.len_spec() && forall|i:int|0<=i<self.entries.len() ==> (#[trigger] self.entries@[i]).wf(bank,i)}
    pub closed spec fn names(&self)->Seq<Map<u64,u64>> {self.entries@.map(|_:int,e:Entry<T>|e.names@)}
    pub closed spec fn source_clocks(&self)->Seq<u64> {self.entries@.map(|_:int,e:Entry<T>|e.source_clock)}
    pub closed spec fn target_clocks(&self)->Seq<u64> {self.entries@.map(|_:int,e:Entry<T>|e.target_clock)}
    pub(crate) fn start(bank:&Bank<T>,context:&Context<'_,T,()>)->(out:Self)
        requires bank.wf(),context.wf(),context.bank(bank),forall|i:int|0<=i<bank.len_spec() ==> #[trigger] context.initial_entry(bank,i),
        ensures out.wf(bank),
    {
        hide(crate::reversible_value::joint::valid);hide(crate::reversible_value::joint::step);
        let mut entries:Vec<Entry<T>>=Vec::new();let mut i=0;
        while i<bank.len()
            invariant bank.wf(),context.wf(),context.bank(bank),i<=bank.len_spec(),entries.len()==i,
                forall|j:int|0<=j<bank.len_spec() ==> #[trigger] context.initial_entry(bank,j),
                forall|j:int|0<=j<i ==> (#[trigger] entries@[j]).wf(bank,j),
            decreases bank.len_spec()-i,
        {
            let input=bank.first_input(i).unwrap();let current=context.capture(i);
            proof {reveal(Context::initial_entry);assert(context.initial_entry(bank,i as int));input.provenance();input.source().result->Payload_0.inverse().source_history();context.bank_entry(bank,i as int);}
            let after=input.payload_after_head().unwrap();let _head=match input.operand() {super::inputs::Operand::Payload {head,..}=>*head,_=>{assert(false);panic!("typed archive entry")}};
            let ghost names=Map::empty().insert(_head,0u64);
            let point=Point {source:Head {input:input.duplicate(),initial:true},target:current};
            let entry=Entry {history:vec![point],source_clock:after-1,target_clock:0,names:Ghost(names)};
            proof {assert(entry.wf(bank,i as int));}
            entries.push(entry);i+=1;
        }Self {entries}
    }
    #[verifier::rlimit(16)]
    #[verifier::spinoff_prover]
    pub(crate) fn prepare(&self,inputs:&[Input<T>],bank:&Bank<T>,context:&Context<'_,T,()>)->(out:Result<Plan<T>,Error>)
        requires self.wf(bank),bank.wf(),context.wf(),context.bank(bank),
            forall|i:int|0<=i<inputs.len() ==> (#[trigger] inputs@[i]).wf() && inputs@[i].identity_spec().namespace()==bank.namespace(),
        ensures out.is_ok() ==> out->Ok_0.wf(bank) && out->Ok_0.steps()==super::typed_tracker::observations(inputs@)
            && out->Ok_0.names()==self.names() && out->Ok_0.before_clocks()==self.source_clocks()
            && epochs::heaps(self.names(),out->Ok_0.before(),context.states(),self.source_clocks(),context.revisions()),
    {
        hide(crate::reversible_value::joint::valid);hide(crate::reversible_value::joint::step);
        let mut heads:Vec<Head<T>>=Vec::new();let mut clocks:Vec<u64>=Vec::new();let mut i=0;
        proof {context.storage_facts();}
        while i<self.entries.len()
            invariant self.wf(bank),bank.wf(),context.wf(),context.bank(bank),i<=self.entries.len(),heads.len()==i,clocks.len()==i,
                context.states().len()==bank.len_spec(),context.revisions().len()==bank.len_spec(),
                forall|j:int|0<=j<i ==> (#[trigger] heads@[j]).wf(bank,j) && clocks@[j]==self.source_clocks()[j]
                    && typed::related(self.names()[j],heads@[j].state(),context.states()[j])
                    && typed::injective(self.names()[j]) && epochs::ordered(self.names()[j]) && typed::bounded(self.names()[j],clocks@[j],context.revisions()[j]),
            decreases self.entries.len()-i,
        {
            let current=context.capture(i);proof {context.bank_entry(bank,i as int);}
            let head=self.entries[i].select(&current,bank,i)?;
            clocks.push(self.entries[i].source_clock);heads.push(head);i+=1;
        }
        let ghost before=head_states(heads@);let ghost before_clocks=clocks@;
        proof {
            assert forall|j:int|0<=j<clocks.len() implies clocks@[j]==self.source_clocks()[j] by {assert(heads@[j].wf(bank,j));}
            assert(before_clocks =~= self.source_clocks());
            assert forall|j:int|0<=j<self.names().len() implies {
                let m=#[trigger] self.names()[j];
                &&& typed::injective(m) && epochs::ordered(m) && typed::bounded(m,before_clocks[j],context.revisions()[j]) && typed::related(m,before[j],context.states()[j])
            } by {assert(heads@[j].wf(bank,j));}
            assert(epochs::heaps(self.names(),before,context.states(),before_clocks,context.revisions()));
        }
        let mut next=Cursor {heads,clocks};let mut indices:Vec<usize>=Vec::new();let mut retained:Vec<Input<T>>=Vec::new();let mut i=0;
        proof {reveal(super::typed_tracker::indexed_after);reveal(indexed_clocks);}
        while i<inputs.len()
            invariant self.wf(bank),bank.wf(),context.wf(),context.bank(bank),next.wf(bank),i<=inputs.len(),indices.len()==i,retained.len()==i,
                forall|j:int|0<=j<inputs.len() ==> (#[trigger] inputs@[j]).wf() && inputs@[j].identity_spec().namespace()==bank.namespace(),
                forall|j:int|0<=j<retained.len() ==> (#[trigger] retained@[j]).wf() && retained@[j].source()==inputs@[j].source() && retained@[j].identity_spec()==inputs@[j].identity_spec(),
                next.states()==super::typed_tracker::indexed_after(before,indices@,super::typed_tracker::observations(inputs@).take(i as int)),
                next.clocks@==indexed_clocks(before_clocks,indices@,super::typed_tracker::observations(inputs@).take(i as int)),
                checked(bank,before,before_clocks,indices@,super::typed_tracker::observations(inputs@).take(i as int)),
                before_clocks==self.source_clocks(),epochs::heaps(self.names(),before,context.states(),before_clocks,context.revisions()),
            decreases inputs.len()-i,
        {
            let input=&inputs[i];let ghost prior=next;let entry=next.advance(input,bank,i)?;let ghost old_indices=indices@;
            indices.push(entry);retained.push(input.duplicate());
            proof {
                let prefix=super::typed_tracker::observations(inputs@).take(i as int);
                assert(super::typed_tracker::observations(inputs@).take(i as int+1) =~= prefix.push(input.source()));
                checked_append(bank,before,before_clocks,old_indices,prefix,input.source(),entry);
            }i+=1;
        }
        proof {assert(super::typed_tracker::observations(inputs@).take(i as int) =~= super::typed_tracker::observations(inputs@));assert(super::typed_tracker::observations(retained@) =~= super::typed_tracker::observations(inputs@));}
        Ok(Plan {next,indices,inputs:retained,before:Ghost(before),before_clocks:Ghost(before_clocks),names:Ghost(self.names())})
    }
}
spec fn head_states<T:?Sized>(heads:Seq<Head<T>>)->Seq<State<T>> {heads.map(|_:int,h:Head<T>|h.state())}
struct Cursor<T:?Sized> {heads:Vec<Head<T>>,clocks:Vec<u64>}
impl<T:?Sized> Cursor<T> {
    spec fn states(&self)->Seq<State<T>> {head_states(self.heads@)}
    spec fn wf(&self,bank:&Bank<T>)->bool {self.heads.len()==bank.len_spec() && self.clocks.len()==self.heads.len() && forall|i:int|0<=i<self.heads.len() ==> (#[trigger] self.heads@[i]).wf(bank,i)}
    fn advance(&mut self,input:&Input<T>,bank:&Bank<T>,step:usize)->(out:Result<usize,Error>)
        requires old(self).wf(bank),bank.wf(),input.wf(),input.identity_spec().namespace()==bank.namespace(),
        ensures final(self).wf(bank),
            out.is_ok() ==> out->Ok_0<bank.len_spec() && input.source().result is Payload && relation::fresh(input.source()) && input.source().result->Payload_0.inverse().wf()
                && bank.address(out->Ok_0 as int)==input.source().address() && input.source().before()->Payload_0==old(self).states()[out->Ok_0 as int]
                && old(self).clocks@[out->Ok_0 as int]<=input.source().result->Payload_0.inverse().before().revision
                && input.source().after()->Payload_0.head==input.source().result->Payload_0.inverse().after().revision
                && input.source().result->Payload_0.inverse().before().revision<input.source().result->Payload_0.inverse().after().revision
                && final(self).states()==old(self).states().update(out->Ok_0 as int,input.source().after()->Payload_0)
                && final(self).clocks@==old(self).clocks@.update(out->Ok_0 as int,input.source().result->Payload_0.inverse().after().revision),
            out.is_err() ==> *final(self)==*old(self),
    {
        hide(crate::reversible_value::joint::valid);hide(crate::reversible_value::joint::step);
        let entry=match bank.find(input) {Some(n)=>n,None=>return Err(Error::Allocation {step})};let previous=&self.heads[entry];
        let same=if previous.initial {input.same_payload_before(&previous.input)==Some(true)} else {input.continues_payload(&previous.input)==Some(true)};
        if !same {return Err(Error::SourceState {step});}
        let after=match input.payload_after_head() {Some(n)=>n,None=>return Err(Error::SourceState {step})};
        proof {input.provenance();input.source().result->Payload_0.inverse().source_history();relation::fresh_step(input.source());}
        if after-1<self.clocks[entry] {return Err(Error::SourceOrder {step});}
        self.heads.set(entry,Head {input:input.duplicate(),initial:false});self.clocks.set(entry,after);
        proof {assert(self.states() =~= old(self).states().update(entry as int,input.source().after()->Payload_0));}
        Ok(entry)
    }
}
#[verifier::opaque]
spec fn indexed_clocks<T:?Sized>(initial:Seq<u64>,indices:Seq<usize>,steps:Seq<Step<T>>)->Seq<u64>
    decreases steps.len(),
{if steps.len()==0 {initial} else {indexed_clocks(initial,indices.drop_last(),steps.drop_last()).update(indices.last() as int,steps.last().result->Payload_0.inverse().after().revision)}}
spec fn checked<T:?Sized>(bank:&Bank<T>,initial:Seq<State<T>>,clocks:Seq<u64>,indices:Seq<usize>,steps:Seq<Step<T>>)->bool {
    super::typed_tracker::checked(bank,initial,indices,steps) && initial.len()==clocks.len()
        && forall|i:int|0<=i<steps.len() ==> {
            let s=#[trigger] steps[i];
            &&& s.result->Payload_0.inverse().wf()
            &&& indexed_clocks(clocks,indices.take(i),steps.take(i))[indices[i] as int]<=s.result->Payload_0.inverse().before().revision
            &&& s.after()->Payload_0.head==s.result->Payload_0.inverse().after().revision
            &&& s.result->Payload_0.inverse().before().revision<s.result->Payload_0.inverse().after().revision
        }
}
proof fn checked_append<T:?Sized>(bank:&Bank<T>,initial:Seq<State<T>>,clocks:Seq<u64>,indices:Seq<usize>,steps:Seq<Step<T>>,s:Step<T>,entry:usize)
    requires checked(bank,initial,clocks,indices,steps),entry<bank.len_spec(),s.result is Payload,relation::fresh(s),s.result->Payload_0.inverse().wf(),
        bank.address(entry as int)==s.address(),s.before()->Payload_0==super::typed_tracker::indexed_after(initial,indices,steps)[entry as int],
        indexed_clocks(clocks,indices,steps)[entry as int]<=s.result->Payload_0.inverse().before().revision,
        s.after()->Payload_0.head==s.result->Payload_0.inverse().after().revision,s.result->Payload_0.inverse().before().revision<s.result->Payload_0.inverse().after().revision,
    ensures checked(bank,initial,clocks,indices.push(entry),steps.push(s)),
        super::typed_tracker::indexed_after(initial,indices.push(entry),steps.push(s))==super::typed_tracker::indexed_after(initial,indices,steps).update(entry as int,s.after()->Payload_0),
        indexed_clocks(clocks,indices.push(entry),steps.push(s))==indexed_clocks(clocks,indices,steps).update(entry as int,s.result->Payload_0.inverse().after().revision),
{
    super::typed_tracker::checked_append(bank,initial,indices,steps,s,entry);reveal(indexed_clocks);
    assert(steps.push(s).drop_last() =~= steps);assert(indices.push(entry).drop_last() =~= indices);
    assert forall|i:int|0<=i<steps.push(s).len() implies {
        let x=#[trigger] steps.push(s)[i];
        &&& x.result->Payload_0.inverse().wf()
        &&& indexed_clocks(clocks,indices.push(entry).take(i),steps.push(s).take(i))[indices.push(entry)[i] as int]<=x.result->Payload_0.inverse().before().revision
        &&& x.after()->Payload_0.head==x.result->Payload_0.inverse().after().revision
        &&& x.result->Payload_0.inverse().before().revision<x.result->Payload_0.inverse().after().revision
    } by {if i<steps.len() {assert(indices.push(entry).take(i) =~= indices.take(i));assert(steps.push(s).take(i) =~= steps.take(i));} else {assert(indices.push(entry).take(i) =~= indices);assert(steps.push(s).take(i) =~= steps);}}
}
#[allow(dead_code)] // Before-states and maps are proof data.
pub(crate) struct Plan<T:?Sized> {next:Cursor<T>,indices:Vec<usize>,inputs:Vec<Input<T>>,before:Ghost<Seq<State<T>>>,before_clocks:Ghost<Seq<u64>>,names:Ghost<Seq<Map<u64,u64>>>}
impl<T:?Sized> Plan<T> {
    pub(crate) closed spec fn indices(&self)->Seq<usize> {self.indices@}
    pub(crate) closed spec fn before(&self)->Seq<State<T>> {self.before@}
    pub(crate) closed spec fn before_clocks(&self)->Seq<u64> {self.before_clocks@}
    pub(crate) closed spec fn after(&self)->Seq<State<T>> {self.next.states()}
    pub(crate) closed spec fn after_clocks(&self)->Seq<u64> {self.next.clocks@}
    pub(crate) closed spec fn names(&self)->Seq<Map<u64,u64>> {self.names@}
    pub(crate) closed spec fn steps(&self)->Seq<Step<T>> {super::typed_tracker::observations(self.inputs@)}
    pub(crate) closed spec fn wf(&self,bank:&Bank<T>)->bool {
        self.next.wf(bank) && self.names().len()==bank.len_spec() && checked(bank,self.before(),self.before_clocks(),self.indices@,self.steps())
            && self.after()==super::typed_tracker::indexed_after(self.before(),self.indices@,self.steps()) && self.after_clocks()==indexed_clocks(self.before_clocks(),self.indices@,self.steps())
            && forall|i:int|0<=i<self.inputs.len() ==> (#[trigger] self.inputs@[i]).wf() && self.inputs@[i].identity_spec().namespace()==bank.namespace()
    }
    pub(crate) proof fn routes(&self,bank:&Bank<T>,routes:Seq<usize>)
        requires self.wf(bank),bank.wf(),super::protected::mapped(bank,routes,self.steps()),
        ensures epochs::inputs(self.before(),self.before_clocks(),routes,self.steps()),self.after()==super::super::protected_typed::after(self.before(),routes,self.steps()),self.after_clocks()==super::super::protected_typed::clocks(self.before_clocks(),routes,self.steps()),
            forall|i:int|0<=i<self.steps().len() ==> self.indices()[i]==routes[(#[trigger] self.steps()[i]).pc as int],
    {
        assert forall|i:int|0<=i<self.steps().len() implies self.steps()[i].pc<routes.len() && self.indices@[i]==routes[self.steps()[i].pc as int] by {
            bank.mapping_entry(self.indices@[i] as int);bank.aliases(self.indices@[i] as int,routes[self.steps()[i].pc as int] as int);
        }
        super::typed_tracker::convert(self.before(),self.indices@,routes,self.steps());convert_clocks(self.before_clocks(),self.indices@,routes,self.steps());
        assert forall|i:int|0<=i<self.steps().len() implies {
            let s=#[trigger] self.steps()[i];let n=routes[s.pc as int] as int;
            &&& s.result is Payload && s.pc<routes.len() && n<self.before().len()
            &&& s.before()->Payload_0==super::super::protected_typed::after(self.before(),routes,self.steps().take(i))[n] && relation::fresh(s)
            &&& s.result->Payload_0.inverse().wf()
            &&& super::super::protected_typed::clocks(self.before_clocks(),routes,self.steps().take(i))[n]<=s.result->Payload_0.inverse().before().revision
            &&& s.after()->Payload_0.head==s.result->Payload_0.inverse().after().revision
            &&& s.result->Payload_0.inverse().before().revision<s.result->Payload_0.inverse().after().revision
        } by {super::typed_tracker::convert(self.before(),self.indices@.take(i),routes,self.steps().take(i));convert_clocks(self.before_clocks(),self.indices@.take(i),routes,self.steps().take(i));}
    }
}
proof fn convert_clocks<T:?Sized>(initial:Seq<u64>,indices:Seq<usize>,routes:Seq<usize>,steps:Seq<Step<T>>)
    requires indices.len()==steps.len(),forall|i:int|0<=i<steps.len() ==> (#[trigger] steps[i]).pc<routes.len() && indices[i]==routes[steps[i].pc as int],
    ensures indexed_clocks(initial,indices,steps)==super::super::protected_typed::clocks(initial,routes,steps),
    decreases steps.len(),
{reveal(indexed_clocks);reveal(super::super::protected_typed::clocks);if steps.len()>0 {convert_clocks(initial,indices.drop_last(),routes,steps.drop_last());}}
}
verus! {
impl<T:?Sized> Archive<T> {
    #[verifier::rlimit(16)]
    #[verifier::spinoff_prover]
    #[allow(unused_variables)] // Runtime arguments also anchor erased provenance contracts.
    pub(crate) fn record<E:crate::reversible_value::effect::ScalarEffect>(&mut self,plan:Plan<T>,source:&super::Source<E,T>,targets:&[Input<T>],bank:&Bank<T>,context:&Context<'_,T,()>,Ghost(certificate):Ghost<epochs::Certificate<T>>)
        requires old(self).wf(bank),bank.wf(),plan.wf(bank),source.wf(),context.wf(),context.bank(bank),certificate.wf(),
            certificate.before_names==old(self).names(),certificate.before_names==plan.names(),certificate.source==plan.steps(),
            certificate.before_source==plan.before(),certificate.before_source_clocks==plan.before_clocks(),
            certificate.after_target==context.states(),certificate.after_target_clocks==context.revisions(),
            super::protected::mapped(bank,certificate.routes,plan.steps()),
            super::typed_tracker::observations(targets@)==certificate.target,relation::allocations(bank,certificate.source,certificate.target),
            forall|i:int|0<=i<targets.len() ==> (#[trigger] targets@[i]).wf() && super::transport::step(source.program().code(),targets@[i].source()),
        ensures final(self).wf(bank),final(self).names()==certificate.after_names,relation::extends(final(self).names(),old(self).names()),
            final(self).source_clocks()==certificate.after_source_clocks,final(self).target_clocks()==certificate.after_target_clocks,
    {
        hide(crate::reversible_value::joint::valid);hide(crate::reversible_value::joint::step);
        proof {certificate.facts();plan.routes(bank,certificate.routes);context.storage_facts();}
        let ghost old_entries=self.entries@;let mut i=0;
        while i<self.entries.len()
            invariant bank.wf(),source.wf(),context.wf(),context.bank(bank),certificate.wf(),plan.wf(bank),i<=self.entries.len(),self.entries.len()==bank.len_spec(),
                certificate.after_source==plan.after(),certificate.after_source_clocks==plan.after_clocks(),certificate.after_target==context.states(),certificate.after_target_clocks==context.revisions(),
                epochs::heaps(certificate.after_names,certificate.after_source,certificate.after_target,certificate.after_source_clocks,certificate.after_target_clocks),relation::extends(certificate.after_names,certificate.before_names),
                certificate.before_names==old(self).names(),old_entries==old(self).entries@,old(self).wf(bank),
                forall|j:int|0<=j<self.entries.len() ==> if j<i {
                    (#[trigger] self.entries@[j]).wf(bank,j) && self.entries@[j].names@==certificate.after_names[j]
                        && self.entries@[j].source_clock==certificate.after_source_clocks[j] && self.entries@[j].target_clock==certificate.after_target_clocks[j]
                } else {self.entries@[j]==old_entries[j]},
            decreases self.entries.len()-i,
        {
            let current=context.capture(i);let entry=&mut self.entries[i];
            proof {
                assert forall|j:int|0<=j<entry.history.len() implies (#[trigger] entry.history@[j]).wf(bank,i as int,certificate.after_names[i as int]) by {
                    let point=entry.history@[j];assert(point.wf(bank,i as int,certificate.before_names[i as int]));
                    assert(certificate.before_names[i as int].contains_key(point.source.state().head));
                }
            }
            entry.source_clock=plan.next.clocks[i];entry.target_clock=current.revision();entry.names=Ghost(certificate.after_names[i as int]);i+=1;
        }
        proof {assert(self.names() =~= certificate.after_names);assert(self.source_clocks() =~= certificate.after_source_clocks);assert(self.target_clocks() =~= certificate.after_target_clocks);}
        let mut i=0;
        while i<targets.len()
            invariant self.wf(bank),bank.wf(),plan.wf(bank),source.wf(),certificate.wf(),self.names()==certificate.after_names,self.source_clocks()==certificate.after_source_clocks,self.target_clocks()==certificate.after_target_clocks,
                certificate.source==plan.steps(),super::typed_tracker::observations(targets@)==certificate.target,relation::allocations(bank,certificate.source,certificate.target),
                relation::paired(certificate.after_names,certificate.routes,certificate.source,certificate.target),i<=targets.len(),
                forall|j:int|0<=j<targets.len() ==> (#[trigger] targets@[j]).wf() && super::transport::step(source.program().code(),targets@[j].source()),
                forall|j:int|0<=j<plan.steps().len() ==> plan.indices@[j]==certificate.routes[(#[trigger] plan.steps()[j]).pc as int],
            decreases targets.len()-i,
        {
            let input=&targets[i];let pc=input.pc();let function=source.function_ref();
            proof {assert(input.source()==certificate.target[i as int]);assert(input.source().result is Payload);assert(super::transport::step(function.code(),input.source()));}
            let value=match &function.code[pc].effect {super::super::Effect::Replace(value)=>value,_=>{assert(false);panic!("recorded typed instruction")}};
            let target=input.after_capture(value);let index=plan.indices[i];
            let point=Point {source:Head {input:plan.inputs[i].duplicate(),initial:false},target};
            proof {
                reveal(relation::allocations);assert(plan.steps()[i as int]==plan.inputs@[i as int].source());assert(index<bank.len_spec());bank.mapping_entry(index as int);
                input.provenance();input.source().result->Payload_0.inverse().provenance();
                assert(point.source.wf(bank,index as int));assert(point.target.wf());
                assert(point.target.owner().journal_spec()==bank.target_address(index as int).journal);
                assert(point.target.owner().key()==bank.target_address(index as int).key);
                assert(typed::related(self.names()[index as int],point.source.state(),point.target.observation().state()));
                assert(point.wf(bank,index as int,self.names()[index as int]));
            }
            self.entries[index].history.push(point);i+=1;
        }
    }
}
}

pub mod projection;
