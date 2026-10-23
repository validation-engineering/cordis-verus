//! Exclusive scalar storage used by the ordinary managed interpreter.
//! The pool contains real lock guards, not a parallel heap or supplied trace.
#[cfg(verus_keep_ghost)]
use super::{Call, Slot};
use super::{Effect, Owner};
#[cfg(verus_keep_ghost)]
use crate::lifecycle_state::services::NativeEpisode;
use crate::reversible_value::{
    access, effect::EffectError, native_effect, protected::Exclusive, registration, slot,
    ReversibleValue, ValueState,
};
#[cfg(verus_keep_ghost)]
use crate::reversible_value::{effect, effect::ScalarEffect, joint, Applied};
use crate::Port;
use vstd::prelude::*;

verus! {
broadcast use vstd::seq_lib::group_seq_properties;
pub(crate) struct Binding {pub provider:usize,pub port:Port,pub slot:usize}
pub(crate) struct Context<'a> {
    cells:Vec<Option<Exclusive<'a>>>,slots:Vec<slot::protected::Exclusive<'a>>,
    selected:Vec<usize>,bindings:Vec<Binding>,
}
#[derive(Debug)]
pub enum Error {ChangedSlot {index:usize}}
pub open spec fn kernel_only<E,T:?Sized>(code:Seq<Call<E,T>>)->bool {
    forall|i:int|0<=i<code.len() ==> (#[trigger] code[i]).effect is Kernel
}
#[verifier::opaque]
pub(crate) open spec fn after<T:?Sized>(initial:Seq<ValueState>,routes:Seq<usize>,steps:Seq<super::Step<T>>)->Seq<ValueState>
    decreases steps.len(),
{
    if steps.len()==0 {initial} else {
        let s=steps.last();after(initial,routes,steps.drop_last()).update(routes[s.pc as int] as int,s.after()->Scalar_0)
    }
}
#[verifier::opaque]
pub(crate) open spec fn execution<T:?Sized>(initial:Seq<ValueState>,routes:Seq<usize>,steps:Seq<super::Step<T>>)->bool {
    forall|i:int|0<=i<steps.len() ==> {
        let s=#[trigger] steps[i];
        &&& s.result is Scalar && s.pc<routes.len() && routes[s.pc as int]<initial.len()
        &&& s.before()==super::semantics::Value::Scalar(after(initial,routes,steps.take(i))[routes[s.pc as int] as int])
    }
}
pub(crate) proof fn empty<T:?Sized>(initial:Seq<ValueState>,routes:Seq<usize>)
    ensures execution::<T>(initial,routes,Seq::empty()),after::<T>(initial,routes,Seq::empty())==initial,
{reveal(execution);reveal(after);}
pub(crate) proof fn append<T:?Sized>(initial:Seq<ValueState>,routes:Seq<usize>,steps:Seq<super::Step<T>>,s:super::Step<T>)
    requires execution(initial,routes,steps),s.result is Scalar,s.pc<routes.len(),routes[s.pc as int]<initial.len(),
        s.before()==super::semantics::Value::Scalar(after(initial,routes,steps)[routes[s.pc as int] as int]),
    ensures execution(initial,routes,steps.push(s)),
        after(initial,routes,steps.push(s))==after(initial,routes,steps).update(routes[s.pc as int] as int,s.after()->Scalar_0),
{
    reveal(execution);reveal(after);
    assert(steps.push(s).drop_last() =~= steps);
    assert forall|i:int|0<=i<steps.push(s).len() implies {
        let x=#[trigger] steps.push(s)[i];
        &&& x.result is Scalar && x.pc<routes.len() && routes[x.pc as int]<initial.len()
        &&& x.before()==super::semantics::Value::Scalar(after(initial,routes,steps.push(s).take(i))[routes[x.pc as int] as int])
    } by {if i<steps.len() {assert(steps.push(s).take(i) =~= steps.take(i));} else {assert(steps.push(s).take(i) =~= steps);}}
}
impl<E,T:?Sized> super::Function<E,T> {
    pub fn is_kernel_only(&self)->(out:bool) ensures out==kernel_only(self.code()),
    {
        let mut i=0;
        while i<self.code.len()
            invariant i<=self.code.len(),forall|j:int|0<=j<i ==> (#[trigger] self.code()[j]).effect is Kernel,
            decreases self.code.len()-i,
        {if !matches!(&self.code[i].effect,Effect::Kernel(_)) {return false;}i+=1;}true
    }
}
pub(crate) open spec fn addressed<T:?Sized>(targets:Seq<ReversibleValue>,routes:Seq<usize>,steps:Seq<super::Step<T>>)->bool {
    forall|i:int|0<=i<steps.len() ==> {
        let s=#[trigger] steps[i];
        &&& s.pc<routes.len() && routes[s.pc as int]<targets.len()
        &&& s.address()==crate::reversible_value::service_composition::Address {journal:targets[routes[s.pc as int] as int].journal_spec(),key:targets[routes[s.pc as int] as int].object().key}
    }
}
#[verifier::opaque]
pub(crate) open spec fn plan<E:ScalarEffect,T:?Sized>(code:Seq<Call<E,T>>,steps:Seq<super::Step<T>>)->bool {
    super::next(code.len(),steps).is_none() && forall|i:int|0<=i<steps.len() ==> {
        let s=#[trigger] steps[i];
        &&& s.result is Scalar && Some(s.pc)==super::next(code.len(),steps.take(i))
        &&& super::replay::transport::step(code,s)
    }
}
pub(crate) open spec fn same<T:?Sized>(actual:Seq<super::Step<T>>,expected:Seq<super::Step<T>>)->bool {
    actual.len()==expected.len() && forall|i:int|0<=i<actual.len() ==> {
        let a=#[trigger] actual[i];let b=expected[i];
        &&& a.pc==b.pc && a.before()==b.before() && a.after()==b.after() && a.outcome()==b.outcome() && a.next==b.next
    }
}
pub(crate) proof fn plan_position<E:ScalarEffect,T:?Sized>(code:Seq<Call<E,T>>,steps:Seq<super::Step<T>>,count:int)
    requires plan(code,steps),0<=count<=steps.len(),
    ensures super::next(code.len(),steps.take(count)).is_some()==(count<steps.len()),
        count<steps.len() ==> super::next(code.len(),steps.take(count))==Some(steps[count].pc),
{
    hide(super::replay::transport::step);reveal(plan);
    if count==steps.len() {assert(steps.take(count) =~= steps);} else {assert(Some(steps[count].pc)==super::next(code.len(),steps.take(count)));}
}
pub(crate) proof fn plan_step<E:ScalarEffect,T:?Sized>(code:Seq<Call<E,T>>,steps:Seq<super::Step<T>>,at:int)
    requires plan(code,steps),0<=at<steps.len(),ensures super::replay::transport::step(code,steps[at]),steps[at].result is Scalar,
{reveal(plan);}
pub(crate) proof fn input_at<T:?Sized>(initial:Seq<ValueState>,routes:Seq<usize>,steps:Seq<super::Step<T>>,at:int)
    requires execution(initial,routes,steps),0<=at<steps.len(),
    ensures steps[at].pc<routes.len(),routes[steps[at].pc as int]<initial.len(),steps[at].result is Scalar,
        steps[at].before()==super::semantics::Value::Scalar(after(initial,routes,steps.take(at))[routes[steps[at].pc as int] as int]),
{reveal(execution);}
pub(crate) proof fn take_append<T:?Sized>(initial:Seq<ValueState>,routes:Seq<usize>,steps:Seq<super::Step<T>>,at:int)
    requires 0<=at<steps.len(),
    ensures after(initial,routes,steps.take(at+1))==after(initial,routes,steps.take(at)).update(routes[steps[at].pc as int] as int,steps[at].after()->Scalar_0),
{reveal(after);assert(steps.take(at+1).drop_last() =~= steps.take(at));}
#[allow(clippy::manual_while_let_some)] // Keep the remaining-guards invariant explicit.
fn release_slots(mut slots:Vec<slot::protected::Exclusive<'_>>)
    requires forall|i:int|0<=i<slots.len() ==> (#[trigger] slots@[i]).wf(),
{
    while !slots.is_empty()
        invariant forall|i:int|0<=i<slots.len() ==> (#[trigger] slots@[i]).wf(),
        decreases slots.len(),
    {let slot=slots.pop().unwrap();slot.release();}
}
impl<'a> Context<'a> {
    pub(crate) closed spec fn targets(&self)->Seq<ReversibleValue> {self.cells@.map(|_:int,x:Option<Exclusive<'a>>|x.unwrap().target())}
    pub(crate) closed spec fn states(&self)->Seq<ValueState> {self.cells@.map(|_:int,x:Option<Exclusive<'a>>|x.unwrap().state())}
    pub(crate) closed spec fn slot_names(&self)->Seq<slot::Slot> {self.slots@.map(|_:int,x:slot::protected::Exclusive<'a>|x.slot())}
    pub(crate) closed spec fn routes(&self)->Seq<usize> {self.bindings@.map(|_:int,b:Binding|self.selected@[b.slot as int])}
    pub(crate) closed spec fn bindings(&self)->Seq<Binding> {self.bindings@}
    pub(crate) closed spec fn chosen(&self)->Seq<usize> {self.selected@}
    pub(crate) closed spec fn wf(&self)->bool {
        self.selected.len()==self.slots.len()
            && (forall|i:int|0<=i<self.cells.len() ==> (#[trigger] self.cells@[i]).is_some() && self.cells@[i]->Some_0.wf())
            && (forall|i:int|0<=i<self.slots.len() ==> (#[trigger] self.slots@[i]).wf() && self.selected@[i]<self.cells.len()
                && *self.slots@[i].value()==self.targets()[self.selected@[i] as int])
            && (forall|i:int|0<=i<self.bindings.len() ==> (#[trigger] self.bindings@[i]).slot<self.slots.len())
    }
    pub(crate) open spec fn shape(&self,prior:&Self)->bool {
        self.targets()==prior.targets() && self.slot_names()==prior.slot_names()
            && self.chosen()==prior.chosen() && self.bindings()==prior.bindings() && self.routes()==prior.routes()
    }
    pub(crate) open spec fn supports<T:?Sized,M>(&self,episode:NativeEpisode<Slot<T,M>>,ports:Seq<Port>)->bool {
        !episode.closed() && self.bindings().len()==ports.len()
            && forall|i:int|0<=i<ports.len() ==> {
                let b=#[trigger] self.bindings()[i];
                &&& b.port==ports[i] && b.slot<self.slot_names().len()
                &&& episode.selects_slot(b.provider,b.port,self.slot_names()[b.slot as int])
            }
    }
    pub(crate) open spec fn for_call<T:?Sized,M>(&self,episode:NativeEpisode<Slot<T,M>>,pc:usize,port:Port)->bool {
        !episode.closed() && pc<self.bindings().len() && self.bindings()[pc as int].port==port
            && episode.selects_slot(self.bindings()[pc as int].provider,port,self.slot_names()[self.bindings()[pc as int].slot as int])
    }
    pub(crate) open spec fn index(&self,pc:usize)->usize {self.chosen()[self.bindings()[pc as int].slot as int]}
    pub(crate) proof fn call_facts(&self,pc:usize)
        requires self.wf(),pc<self.bindings().len(),
        ensures self.states().len()==self.targets().len(),self.routes().len()==self.bindings().len(),
            self.index(pc)<self.states().len(),self.routes()[pc as int]==self.index(pc),
    {
        let b=self.bindings@[pc as int];assert(b.slot<self.slots.len());assert(self.slots@[b.slot as int].wf());assert(self.selected@[b.slot as int]<self.cells.len());
    }
    pub(crate) fn values(&self)->(out:Vec<ValueState>)
        requires self.wf(),ensures out@==self.states(),
    {
        let mut out=Vec::new();let mut i=0;
        while i<self.cells.len()
            invariant self.wf(),i<=self.cells.len(),out.len()==i,forall|j:int|0<=j<i ==> out@[j]==self.states()[j],
            decreases self.cells.len()-i,
        {out.push(self.cells[i].as_ref().unwrap().state_value());i+=1;}
        proof {assert(out@ =~= self.states());}out
    }
    pub(crate) fn route(&self,pc:usize)->(out:Option<usize>)
        requires self.wf(),ensures out.is_some()==(pc<self.bindings().len()),
            out.is_some() ==> pc<self.routes().len() && out.unwrap()==self.index(pc) && out.unwrap()<self.states().len() && self.routes()[pc as int]==out.unwrap(),
    {
        if pc>=self.bindings.len() {return None;}
        proof {self.call_facts(pc);}Some(self.selected[self.bindings[pc].slot])
    }
    /// All slots are captured while exclusively held, before any cell is used.
    /// Reject a changed initial slot and release every acquired lock on failure.
    pub(crate) fn acquire(values:&'a [ReversibleValue],slots:&'a [slot::Slot])->(out:Result<Self,Error>)
        requires values.len()==slots.len(),forall|i:int|0<=i<slots.len() ==> *slots@[i].initial()==values@[i],
            forall|i:int,j:int|0<=i<j<values.len() ==> values@[i]!=values@[j],
        ensures out.is_ok() ==> out->Ok_0.wf() && out->Ok_0.targets()==values@ && out->Ok_0.slot_names()==slots@
            && out->Ok_0.bindings().len()==0,
    {
        let mut held:Vec<slot::protected::Exclusive<'a>>=Vec::new();let mut i=0;
        while i<slots.len()
            invariant i<=slots.len(),held.len()==i,values.len()==slots.len(),
                forall|j:int|0<=j<slots.len() ==> *slots@[j].initial()==values@[j],
                forall|j:int|0<=j<held.len() ==> (#[trigger] held@[j]).wf() && held@[j].slot()==slots@[j] && *held@[j].value()==values@[j],
            decreases slots.len()-i,
        {
            let lock=slots[i].acquire_exclusive();let capture=lock.capture();
            if capture.revision()!=0 {lock.release();release_slots(held);return Err(Error::ChangedSlot {index:i});}
            proof {capture.initial_selection();assert(*slots@[i as int].initial()==values@[i as int]);assert(*lock.value()==values@[i as int]);}
            held.push(lock);i+=1;
        }
        let mut cells:Vec<Option<Exclusive<'a>>>=Vec::new();let mut selected=Vec::new();let mut i=0;
        while i<values.len()
            invariant values.len()==slots.len(),held.len()==slots.len(),i<=values.len(),cells.len()==i,selected.len()==i,
                forall|j:int|0<=j<held.len() ==> (#[trigger] held@[j]).wf() && held@[j].slot()==slots@[j] && *held@[j].value()==values@[j],
                forall|j:int|0<=j<cells.len() ==> (#[trigger] cells@[j]).is_some() && cells@[j]->Some_0.wf() && cells@[j]->Some_0.target()==values@[j] && selected@[j]==j,
            decreases values.len()-i,
        {cells.push(Some(values[i].acquire_exclusive()));selected.push(i);i+=1;}
        let out=Self {cells,slots:held,selected,bindings:Vec::new()};
        proof {assert(out.targets() =~= values@);assert(out.slot_names() =~= slots@);}
        Ok(out)
    }
    /// Lock the real slots and validate retained replacement receipts before
    /// locking cells. A new slot revision cannot silently change a call's
    /// target; old inverses continue to own their original cells.
    pub(crate) fn acquire_selected(values:&'a [ReversibleValue],slots:&'a [slot::Slot],captures:&[slot::Capture],selected:Vec<usize>)->(out:Result<Self,Error>)
        requires captures.len()==slots.len(),selected.len()==slots.len(),
            forall|i:int|0<=i<slots.len() ==> (#[trigger] captures@[i]).wf() && captures@[i].slot()==slots@[i]
                && selected@[i]<values.len() && *captures@[i].value_spec()==values@[selected@[i] as int],
            forall|i:int,j:int|0<=i<j<values.len() ==> values@[i]!=values@[j],
        ensures out.is_ok() ==> out->Ok_0.wf() && out->Ok_0.targets()==values@ && out->Ok_0.slot_names()==slots@
            && out->Ok_0.chosen()==selected@ && out->Ok_0.bindings().len()==0,
    {
        let mut held:Vec<slot::protected::Exclusive<'a>>=Vec::new();let mut i=0;
        while i<slots.len()
            invariant i<=slots.len(),held.len()==i,captures.len()==slots.len(),selected.len()==slots.len(),
                forall|j:int|0<=j<slots.len() ==> (#[trigger] captures@[j]).wf() && captures@[j].slot()==slots@[j]
                    && selected@[j]<values.len() && *captures@[j].value_spec()==values@[selected@[j] as int],
                forall|j:int|0<=j<held.len() ==> (#[trigger] held@[j]).wf() && held@[j].slot()==slots@[j] && selected@[j]<values.len() && *held@[j].value()==values@[selected@[j] as int],
            decreases slots.len()-i,
        {
            let lock=slots[i].acquire_exclusive();let capture=lock.capture();
            if !capture.same_revision(&captures[i]) {lock.release();release_slots(held);return Err(Error::ChangedSlot {index:i});}
            held.push(lock);i+=1;
        }
        let mut cells:Vec<Option<Exclusive<'a>>>=Vec::new();let mut i=0;
        while i<values.len()
            invariant held.len()==slots.len(),selected.len()==slots.len(),i<=values.len(),cells.len()==i,
                forall|j:int|0<=j<held.len() ==> (#[trigger] held@[j]).wf() && held@[j].slot()==slots@[j]
                    && selected@[j]<values.len() && *held@[j].value()==values@[selected@[j] as int],
                forall|j:int|0<=j<cells.len() ==> (#[trigger] cells@[j]).is_some() && cells@[j]->Some_0.wf() && cells@[j]->Some_0.target()==values@[j],
            decreases values.len()-i,
        {cells.push(Some(values[i].acquire_exclusive()));i+=1;}
        let out=Self {cells,slots:held,selected,bindings:Vec::new()};
        proof {assert(out.targets() =~= values@);assert(out.slot_names() =~= slots@);}
        Ok(out)
    }
    pub(crate) fn bind(&mut self,bindings:Vec<Binding>)
        requires old(self).wf(),forall|i:int|0<=i<bindings.len() ==> (#[trigger] bindings@[i]).slot<old(self).slot_names().len(),
        ensures final(self).wf(),final(self).targets()==old(self).targets(),final(self).states()==old(self).states(),
            final(self).slot_names()==old(self).slot_names(),final(self).chosen()==old(self).chosen(),final(self).bindings()==bindings@,
    {self.bindings=bindings;}
    pub(crate) fn capture<C,G,A,R,T:?Sized,M,X>(&self,owner:&Owner<C,G,A,R,T,M,X>,id:usize,pc:usize,_port:Port)
        ->(out:native_effect::Capture<crate::reversible_value::payload::SharedPayload<T>,M>)
        requires self.wf(),owner.wf(),owner.value_state().is_some(),self.for_call(owner.value_state().unwrap(),pc,_port),
            owner.work_state().accepts(),owner.cleanup_state().acquisition_open(id),
        ensures out.wf(),out.episode()==owner.value_state().unwrap(),out.binding().port_spec()==_port,out.owner().matches(owner,id),
            *out.binding().capture_spec().value_spec()==self.targets()[self.index(pc) as int],
    {
        let binding=&self.bindings[pc];let captured=self.slots[binding.slot].capture();
        owner.capture_selected_native(id,binding.provider,binding.port,captured)
    }
    #[allow(clippy::too_many_arguments)] // Includes the erased prior-receipt map.
    pub(crate) fn apply<C,G,A,R,T:?Sized,M,X>(&mut self,owner:&mut Owner<C,G,A,R,T,M,X>,id:usize,pc:usize,
        capture:native_effect::Capture<crate::reversible_value::payload::SharedPayload<T>,M>,
        instruction:crate::reversible_value::effect::Instruction,branch:crate::reversible_value::Branch,Tracked(previous):Tracked<&registration::ReceiptMap>)
        ->(out:Result<access::Write,EffectError>)
        requires old(self).wf(),old(owner).wf(),pc<old(self).bindings().len(),capture.wf(),
            *capture.binding().capture_spec().value_spec()==old(self).targets()[old(self).index(pc) as int],registration::witnesses(*previous),
        ensures final(self).wf(),final(self).shape(old(self)),
            out.is_err() ==> final(self).states()==old(self).states(),
            out!=Err(EffectError::Closed) ==> final(owner).value_attempts().event().before()==old(self).states()[old(self).index(pc) as int]
                && final(self).states()==old(self).states().update(old(self).index(pc) as int,final(owner).value_attempts().event().after()),
            final(owner).cleanup_state().frame(&old(owner).cleanup_state(),id),
            final(owner).cleanup_state().queues().dom()==old(owner).cleanup_state().queues().dom(),
            final(owner).cleanup_state().domain_ids()==old(owner).cleanup_state().domain_ids(),
            old(owner).cleanup_state().live(id) ==> final(owner).cleanup_state().queues()[id].link()==old(owner).cleanup_state().queues()[id].link()
                && final(owner).cleanup_state().queues()[id].issued()==old(owner).cleanup_state().queues()[id].issued()
                && final(owner).cleanup_state().queues()[id].protocol().selected()==old(owner).cleanup_state().queues()[id].protocol().selected(),
            final(owner).cleanup_state().link()==old(owner).cleanup_state().link(),
            final(owner).wf(),final(owner).execution_journal()==old(owner).execution_journal(),
            final(owner).capture()==old(owner).capture(),final(owner).value_state()==old(owner).value_state(),
            final(owner).work_state()==old(owner).work_state(),final(owner).phase_spec()==old(owner).phase_spec(),
            out.is_err() ==> final(owner).same_runtime(old(owner)),
            out!=Err(EffectError::Interference),
            out!=Err(EffectError::Closed) ==> (out.is_ok()==effect::operation(instruction.model())(final(owner).value_attempts().event().before()).is_some()),
            out!=Err(EffectError::Closed) ==> forall|k:(int,bool)|previous.contains_key(k)
                && #[trigger] previous[k].journal()==final(owner).value_attempts().events().last().journal()
                ==> final(owner).value_attempts().events().last().follows(&previous[k]),
            out.is_ok() ==> forall|k:(int,bool)|previous.contains_key(k)
                && #[trigger] previous[k].journal()==out->Ok_0.admission.registration().write().journal()
                ==> out->Ok_0.admission.registration().write().follows(&previous[k]),
            (out==Err(EffectError::Closed))==!(old(owner).work_state().accepts() && old(owner).cleanup_state().acquisition_open(id)
                && capture.owner().matches(old(owner),id)),
            out==Err(EffectError::Closed) ==> *final(owner)==*old(owner),
            out!=Err(EffectError::Closed) ==> final(owner).value_attempts().appended(&old(owner).value_attempts(),&*capture.binding().capture_spec().value_spec())
               ,
            out.is_err() && out!=Err(EffectError::Closed) ==> crate::reversible_value::attempt::effect_rejection(final(owner).value_attempts().event(),instruction.model(),final(owner).value_attempts().event().before(),out->Err_0)
                && joint::state_at(final(owner).value_attempts().events().last().events(),final(owner).value_attempts().events().last().at())==final(owner).value_attempts().events().last().events().last().state
                && joint::pending_at(final(owner).value_attempts().events().last().events(),final(owner).value_attempts().events().last().at())==final(owner).value_attempts().events().last().events().last().pending,
            out.is_ok() ==> {
                let report=out->Ok_0;
                &&& joint::groups::registration(report.admission.registration().insertion(),final(owner).cleanup_state().link(),id)
                &&& final(owner).cleanup_state().queues()[id].link()==old(owner).cleanup_state().queues()[id].link()
                &&& report.binding==capture.binding() && report.computed(instruction.model(),branch)
                &&& final(owner).cleanup_state().queues()[id].slots()[report.admission.token as int].unwrap()->Value_0.state().before==final(owner).value_attempts().event().before()
                &&& final(owner).cleanup_state().queues()[id].slots()[report.admission.token as int].unwrap()->Value_0.state().after==final(owner).value_attempts().event().after()
                &&& final(owner).cleanup_state().acquisition_open(id)==old(owner).cleanup_state().acquisition_open(id)
                &&& report.recorded(*final(owner),id) && access::selected(capture.episode(),report.binding)
                &&& report.admission.token==old(owner).cleanup_state().queues()[id].slots().len()
                &&& final(owner).cleanup_state().queues()[id].slots().len()==old(owner).cleanup_state().queues()[id].slots().len()+1
                &&& final(owner).cleanup_state().queues()[id].protocol().waiting()==old(owner).cleanup_state().queues()[id].protocol().waiting().push(report.admission.token)
                &&& final(owner).cleanup_state().queues()[id].slots().take(report.admission.token as int)==old(owner).cleanup_state().queues()[id].slots()
                &&& (Applied {outcome:report.admission.outcome,next:report.admission.next,pending:Tracked(None),
                    inverse:final(owner).cleanup_state().queues()[id].slots()[report.admission.token as int].unwrap()->Value_0})
                    .effect_corresponds(&*capture.binding().capture_spec().value_spec(),instruction.model(),branch)
            },
            final(owner).status_links()==old(owner).status_links(),
    {
        proof {self.call_facts(pc);assert(self.bindings@[pc as int].slot<self.selected.len());}
        let index=self.selected[self.bindings[pc].slot];
        proof {assert(index==self.index(pc));assert(self.cells@[index as int].is_some());assert(self.cells@[index as int]->Some_0.wf());
            assert(self.cells@[index as int]->Some_0.target()==self.targets()[index as int]);}
        let out=owner.apply_native_controlled_in(id,capture,instruction,branch,Tracked(previous),&mut self.cells[index]);
        proof {
            assert(self.targets() =~= old(self).targets());assert(self.routes() =~= old(self).routes());
            assert(self.states() =~= old(self).states().update(index as int,self.cells@[index as int]->Some_0.state()));
        }
        out
    }
    pub(crate) fn release(self)
        requires self.wf(),
    {
        let mut pool=self;
        while !pool.cells.is_empty()
            invariant forall|i:int|0<=i<pool.cells.len() ==> (#[trigger] pool.cells@[i]).is_some() && pool.cells@[i]->Some_0.wf(),
                forall|i:int|0<=i<pool.slots.len() ==> (#[trigger] pool.slots@[i]).wf(),
            decreases pool.cells.len(),
        {let cell=pool.cells.pop().unwrap().unwrap();cell.release();}
        release_slots(pool.slots);
    }
}
}

#[cfg(test)]
mod tests {
    use super::Context;
    use crate::reversible_value::{slot::Slot, Branch, Operation, ReversibleValue};
    use std::{
        sync::{mpsc, Arc},
        thread,
        time::Duration,
    };

    #[test]
    fn ordinary_shared_writes_wait_for_the_real_execution_scope() {
        let value = ReversibleValue::new(5);
        let slots = [Slot::new(Arc::new(value.clone()))];
        let values = [value.clone()];
        let context = Context::acquire(&values, &slots).unwrap();
        let (ready_tx, ready_rx) = mpsc::channel();
        let (done_tx, done_rx) = mpsc::channel();
        let writer = thread::spawn(move || {
            ready_tx.send(()).unwrap();
            let result = value.apply(
                Operation::Add(2),
                Branch {
                    matched: None,
                    unmatched: None,
                },
            );
            done_tx.send(result.is_ok()).unwrap();
        });
        ready_rx.recv_timeout(Duration::from_secs(2)).unwrap();
        assert!(matches!(
            done_rx.recv_timeout(Duration::from_millis(50)),
            Err(mpsc::RecvTimeoutError::Timeout)
        ));
        assert_eq!(context.values()[0].value, 5);
        context.release();
        assert!(done_rx.recv_timeout(Duration::from_secs(2)).unwrap());
        writer.join().unwrap();
        assert_eq!(values[0].snapshot().value(), 7);
    }

    #[test]
    fn a_changed_later_slot_releases_every_earlier_lock() {
        let values = [ReversibleValue::new(3), ReversibleValue::new(8)];
        let slots = [
            Slot::new(Arc::new(values[0].clone())),
            Slot::new(Arc::new(values[1].clone())),
        ];
        slots[1]
            .replace(Arc::new(ReversibleValue::new(8)))
            .ok()
            .unwrap();
        assert!(matches!(
            Context::acquire(&values, &slots),
            Err(super::Error::ChangedSlot { index: 1 })
        ));
        // Both operations need the original slot locks, including the first
        // lock acquired before the later slot was rejected.
        assert!(slots[0].replace(Arc::new(values[0].clone())).is_ok());
        assert!(slots[1].replace(Arc::new(values[1].clone())).is_ok());
    }
}
