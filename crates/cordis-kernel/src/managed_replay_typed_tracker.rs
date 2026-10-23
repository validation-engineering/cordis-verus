//! Retained source checkpoints for a real protected typed batch. The checks
//! below run before the corresponding invocation; no payload equality callback
//! or source reread is used.
use super::super::protected_typed::{Context, Error};
use super::{bank::Bank, inputs::Input, Source};
#[cfg(verus_keep_ghost)]
use super::{typed, typed_correspondence as relation};
use crate::reversible_value::effect::ScalarEffect;
use crate::reversible_value::{managed::Step, payload::State};
use vstd::prelude::*;

verus! {
broadcast use vstd::seq_lib::group_seq_properties;
pub(crate) open spec fn observations<T:?Sized>(inputs:Seq<Input<T>>)->Seq<Step<T>> {inputs.map(|_:int,input:Input<T>|input.source())}
struct Checkpoint<T:?Sized> {input:Input<T>,initial:bool}
impl<T:?Sized> Checkpoint<T> {
    spec fn state(&self)->State<T> {
        if self.initial {self.input.source().before()->Payload_0} else {self.input.source().after()->Payload_0}
    }
    spec fn wf(&self,bank:&Bank<T>,i:int)->bool {
        self.input.wf() && self.input.source().result is Payload
            && self.input.identity_spec().namespace()==bank.namespace() && self.input.source().address()==bank.address(i)
    }
    fn duplicate(&self)->(out:Self)
        requires self.input.wf(),ensures out.input.wf(),out.input.source()==self.input.source(),out.input.identity_spec()==self.input.identity_spec(),out.initial==self.initial,
    {Self {input:self.input.duplicate(),initial:self.initial}}
}
#[allow(dead_code)] // Head maps erase; the actual retained checkpoints do not.
pub(crate) struct Tracker<T:?Sized> {checkpoints:Vec<Checkpoint<T>>,names:Ghost<Seq<Map<u64,u64>>>}
impl<T:?Sized> Tracker<T> {
    pub(crate) closed spec fn states(&self)->Seq<State<T>> {self.checkpoints@.map(|_:int,p:Checkpoint<T>|p.state())}
    pub(crate) closed spec fn names(&self)->Seq<Map<u64,u64>> {self.names@}
    pub(crate) closed spec fn wf(&self,bank:&Bank<T>)->bool {
        self.checkpoints.len()==bank.len_spec() && self.names().len()==bank.len_spec()
            && forall|i:int|0<=i<self.checkpoints.len() ==> (#[trigger] self.checkpoints@[i]).wf(bank,i)
    }
    pub(crate) fn start(bank:&Bank<T>,_context:&Context<'_,T,()>)->(out:Self)
        requires bank.wf(),_context.wf(),_context.bank(bank),
            forall|i:int|0<=i<bank.len_spec() ==> #[trigger] _context.initial_entry(bank,i),
        ensures out.wf(bank),relation::heaps(out.names(),out.states(),_context.states()),
    {
        hide(crate::reversible_value::joint::valid);hide(crate::reversible_value::joint::step);
        let mut checkpoints:Vec<Checkpoint<T>>=Vec::new();let ghost names:Seq<Map<u64,u64>>=Seq::empty();let mut i=0;
        proof {_context.storage_facts();}
        while i<bank.len()
            invariant bank.wf(),_context.wf(),_context.bank(bank),i<=bank.len_spec(),checkpoints.len()==i,names.len()==i,
                _context.states().len()==bank.len_spec(),
                forall|j:int|0<=j<bank.len_spec() ==> #[trigger] _context.initial_entry(bank,j),
                forall|j:int|0<=j<i ==> (#[trigger] checkpoints@[j]).wf(bank,j)
                    && typed::related(names[j],checkpoints@[j].state(),_context.states()[j])
                    && typed::injective(names[j]) && typed::bounded(names[j],checkpoints@[j].state().head,_context.states()[j].head),
            decreases bank.len_spec()-i,
        {
            let first=bank.first_input(i).unwrap();
            proof {reveal(Context::initial_entry);first.provenance();}
            let ghost head=first.source().before()->Payload_0.head;
            let ghost previous=checkpoints@;let ghost old_names=names;
            checkpoints.push(Checkpoint {input:first.duplicate(),initial:true});
            proof {
                names=names.push(Map::empty().insert(head,0));
                reveal(Context::initial_entry);
                assert(_context.initial_entry(bank,i as int));
                assert(_context.states()[i as int].value==first.source().before()->Payload_0.value);
                assert(_context.states()[i as int].depth==first.source().before()->Payload_0.depth);
                assert(_context.states()[i as int].head==0);
                assert(first.source().result is Payload);
                assert(checkpoints@[i as int].wf(bank,i as int));
                assert(typed::related(names[i as int],checkpoints@[i as int].state(),_context.states()[i as int]));
                assert(typed::injective(names[i as int]));
                assert(typed::bounded(names[i as int],head,0));
                assert forall|j:int|0<=j<i+1 implies (#[trigger] checkpoints@[j]).wf(bank,j)
                    && typed::related(names[j],checkpoints@[j].state(),_context.states()[j])
                    && typed::injective(names[j]) && typed::bounded(names[j],checkpoints@[j].state().head,_context.states()[j].head) by {
                    if j<i {assert(previous[j].wf(bank,j));assert(names[j]==old_names[j]);}
                }
            }i+=1;
        }
        let out=Self {checkpoints,names:Ghost(names)};
        proof {assert forall|j:int|0<=j<names.len() implies {
            let m=#[trigger] names[j];
            &&& typed::injective(m) && typed::bounded(m,out.states()[j].head,_context.states()[j].head)
            &&& typed::related(m,out.states()[j],_context.states()[j])
        } by {assert(checkpoints@[j].wf(bank,j));}}
        out
    }
    #[verifier::rlimit(12)]
    fn advance(&mut self,input:&Input<T>,bank:&Bank<T>,step:usize)->(out:Result<usize,Error>)
        requires old(self).wf(bank),bank.wf(),input.wf(),input.identity_spec().namespace()==bank.namespace(),
        ensures final(self).wf(bank),final(self).names()==old(self).names(),
            out.is_ok() ==> out->Ok_0<bank.len_spec() && input.source().result is Payload && relation::fresh(input.source())
                && bank.address(out->Ok_0 as int)==input.source().address()
                && input.source().before()->Payload_0==old(self).states()[out->Ok_0 as int]
                && final(self).states()==old(self).states().update(out->Ok_0 as int,input.source().after()->Payload_0),
            out.is_err() ==> final(self).states()==old(self).states(),
    {
        hide(crate::reversible_value::joint::valid);hide(crate::reversible_value::joint::step);
        let entry=match bank.find(input) {Some(entry)=>entry,None=>return Err(Error::SourceAllocation {step})};
        let previous=&self.checkpoints[entry];
        let same=if previous.initial {input.same_payload_before(&previous.input)==Some(true)} else {input.continues_payload(&previous.input)==Some(true)};
        if !same {return Err(Error::SourceState {step});}
        proof {input.provenance();assert(input.source().before()->Payload_0==previous.state());
            assert(input.source().result is Payload);relation::fresh_step(input.source());}
        self.checkpoints.set(entry,Checkpoint {input:input.duplicate(),initial:false});
        proof {assert(self.states() =~= old(self).states().update(entry as int,input.source().after()->Payload_0));}
        Ok(entry)
    }
    #[verifier::rlimit(16)]
    #[verifier::spinoff_prover]
    pub(crate) fn prepare<E:ScalarEffect>(&self,source:&Source<E,T>,bank:&Bank<T>)->(out:Result<Plan<T>,Error>)
        requires self.wf(bank),bank.wf(),source.wf(),source.original().succeeded(),
            forall|i:int|0<=i<source.input_spec().len() ==> source.input_spec()[i].identity_spec().namespace()==bank.namespace(),
        ensures out.is_ok() ==> out->Ok_0.wf(bank) && out->Ok_0.before()==self.states()
            && out->Ok_0.steps()==source.original().result->Ok_0.steps@ && out->Ok_0.prior_names()==self.names(),
    {
        let inputs=source.inputs();
        proof {assert(observations(inputs@) =~= source.original().result->Ok_0.steps@);}
        self.prepare_inputs(inputs,bank)
    }
    #[verifier::rlimit(16)]
    #[verifier::spinoff_prover]
    pub(crate) fn prepare_inputs(&self,inputs:&[Input<T>],bank:&Bank<T>)->(out:Result<Plan<T>,Error>)
        requires self.wf(bank),bank.wf(),forall|i:int|0<=i<inputs.len() ==> (#[trigger] inputs@[i]).wf() && inputs@[i].identity_spec().namespace()==bank.namespace(),
        ensures out.is_ok() ==> out->Ok_0.wf(bank) && out->Ok_0.before()==self.states()
            && out->Ok_0.steps()==observations(inputs@) && out->Ok_0.prior_names()==self.names(),

    {
        hide(crate::reversible_value::joint::valid);hide(crate::reversible_value::joint::step);
        let mut checkpoints:Vec<Checkpoint<T>>=Vec::new();let mut i=0;
        while i<self.checkpoints.len()
            invariant self.wf(bank),i<=self.checkpoints.len(),checkpoints.len()==i,
                forall|j:int|0<=j<i ==> (#[trigger] checkpoints@[j]).wf(bank,j) && checkpoints@[j].state()==self.states()[j],
            decreases self.checkpoints.len()-i,
        {checkpoints.push(self.checkpoints[i].duplicate());i+=1;}
        let mut next=Self {checkpoints,names:self.names};
        let ghost indices:Seq<usize>=Seq::empty();let mut i=0;
        proof {assert(next.states() =~= self.states());reveal(indexed_after);}
        while i<inputs.len()
            invariant self.wf(bank),bank.wf(),i<=inputs.len(),indices.len()==i,
                next.wf(bank),next.names()==self.names(),
                forall|j:int|0<=j<inputs.len() ==> (#[trigger] inputs@[j]).wf() && inputs@[j].identity_spec().namespace()==bank.namespace(),
                next.states()==indexed_after(self.states(),indices,observations(inputs@).take(i as int)),
                checked(bank,self.states(),indices,observations(inputs@).take(i as int)),
            decreases inputs.len()-i,
        {
            let input=&inputs[i];let ghost prior=next.states();let ghost old_indices=indices;
            let _entry=next.advance(input,bank,i)?;
            proof {
                indices=indices.push(_entry);
                let prefix=observations(inputs@).take(i as int);
                assert(observations(inputs@).take(i as int+1) =~= prefix.push(input.source()));
                checked_append(bank,self.states(),old_indices,prefix,input.source(),_entry);
            }i+=1;
        }
        proof {assert(observations(inputs@).take(i as int) =~= observations(inputs@));}
        Ok(Plan {next,before:Ghost(self.states()),indices:Ghost(indices),steps:Ghost(observations(inputs@))})
    }
}
#[verifier::opaque]
pub(crate) open spec fn indexed_after<T:?Sized>(initial:Seq<State<T>>,indices:Seq<usize>,steps:Seq<Step<T>>)->Seq<State<T>>
    decreases steps.len(),
{if steps.len()==0 {initial} else {indexed_after(initial,indices.drop_last(),steps.drop_last()).update(indices.last() as int,steps.last().after()->Payload_0)}}
pub(crate) open spec fn checked<T:?Sized>(bank:&Bank<T>,initial:Seq<State<T>>,indices:Seq<usize>,steps:Seq<Step<T>>)->bool {
    indices.len()==steps.len() && initial.len()==bank.len_spec()
        && forall|i:int|0<=i<steps.len() ==> {
            let s=#[trigger] steps[i];
            &&& indices[i]<bank.len_spec() && s.result is Payload && relation::fresh(s)
            &&& bank.address(indices[i] as int)==s.address()
            &&& s.before()->Payload_0==indexed_after(initial,indices.take(i),steps.take(i))[indices[i] as int]
        }
}
pub(crate) proof fn checked_append<T:?Sized>(bank:&Bank<T>,initial:Seq<State<T>>,indices:Seq<usize>,steps:Seq<Step<T>>,s:Step<T>,entry:usize)
    requires checked(bank,initial,indices,steps),entry<bank.len_spec(),s.result is Payload,relation::fresh(s),
        bank.address(entry as int)==s.address(),s.before()->Payload_0==indexed_after(initial,indices,steps)[entry as int],
    ensures checked(bank,initial,indices.push(entry),steps.push(s)),
        indexed_after(initial,indices.push(entry),steps.push(s))==indexed_after(initial,indices,steps).update(entry as int,s.after()->Payload_0),
{
    reveal(indexed_after);assert(steps.push(s).drop_last() =~= steps);assert(indices.push(entry).drop_last() =~= indices);
    assert forall|j:int|0<=j<steps.push(s).len() implies {
        let x=#[trigger] steps.push(s)[j];
        &&& indices.push(entry)[j]<bank.len_spec() && x.result is Payload && relation::fresh(x)
        &&& bank.address(indices.push(entry)[j] as int)==x.address()
        &&& x.before()->Payload_0==indexed_after(initial,indices.push(entry).take(j),steps.push(s).take(j))[indices.push(entry)[j] as int]
    } by {if j<steps.len() {assert(indices.push(entry).take(j) =~= indices.take(j));assert(steps.push(s).take(j) =~= steps.take(j));}
        else {assert(indices.push(entry).take(j) =~= indices);assert(steps.push(s).take(j) =~= steps);}}
}
#[allow(dead_code)]
pub(crate) struct Plan<T:?Sized> {next:Tracker<T>,before:Ghost<Seq<State<T>>>,indices:Ghost<Seq<usize>>,steps:Ghost<Seq<Step<T>>>}
impl<T:?Sized> Plan<T> {
    pub(crate) closed spec fn before(&self)->Seq<State<T>> {self.before@}
    pub(crate) closed spec fn after(&self)->Seq<State<T>> {self.next.states()}
    pub(crate) closed spec fn prior_names(&self)->Seq<Map<u64,u64>> {self.next.names()}
    pub(crate) closed spec fn steps(&self)->Seq<Step<T>> {self.steps@}
    pub(crate) closed spec fn wf(&self,bank:&Bank<T>)->bool {
        self.next.wf(bank) && checked(bank,self.before(),self.indices@,self.steps())
            && self.after()==indexed_after(self.before(),self.indices@,self.steps())
    }
    pub(crate) proof fn routes(&self,bank:&Bank<T>,routes:Seq<usize>)
        requires self.wf(bank),bank.wf(),super::protected::mapped(bank,routes,self.steps()),
        ensures relation::inputs(self.before(),routes,self.steps()),self.after()==super::super::protected_typed::after(self.before(),routes,self.steps()),
    {
        assert forall|i:int|0<=i<self.steps().len() implies self.steps()[i].pc<routes.len()
            && self.indices@[i]==routes[self.steps()[i].pc as int] by {
            let j=self.indices@[i] as int;let k=routes[self.steps()[i].pc as int] as int;
            bank.mapping_entry(j);bank.aliases(j,k);
        }
        convert(self.before(),self.indices@,routes,self.steps());
        assert forall|i:int|0<=i<self.steps().len() implies {
            let s=#[trigger] self.steps()[i];
            &&& s.result is Payload && s.pc<routes.len() && routes[s.pc as int]<self.before().len()
            &&& s.before()->Payload_0==super::super::protected_typed::after(self.before(),routes,self.steps().take(i))[routes[s.pc as int] as int]
            &&& relation::fresh(s)
        } by {convert(self.before(),self.indices@.take(i),routes,self.steps().take(i));}
    }
    pub(crate) fn finish(self,Ghost(names):Ghost<Seq<Map<u64,u64>>>)->(out:Tracker<T>)
        requires names.len()==self.prior_names().len(),
        ensures out.states()==self.after(),out.names()==names,
            forall|bank:&Bank<T>|self.wf(bank) ==> out.wf(bank),
    {Tracker {checkpoints:self.next.checkpoints,names:Ghost(names)}}
}
pub(crate) proof fn convert<T:?Sized>(initial:Seq<State<T>>,indices:Seq<usize>,routes:Seq<usize>,steps:Seq<Step<T>>)
    requires indices.len()==steps.len(),forall|i:int|0<=i<steps.len() ==> (#[trigger] steps[i]).pc<routes.len() && indices[i]==routes[steps[i].pc as int],
    ensures indexed_after(initial,indices,steps)==super::super::protected_typed::after(initial,routes,steps),
    decreases steps.len(),
{reveal(super::super::protected_typed::after);reveal(indexed_after);if steps.len()>0 {convert(initial,indices.drop_last(),routes,steps.drop_last());}}
}
