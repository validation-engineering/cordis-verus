//! A common execution scope for heterogeneous native functions. Both pools
//! retain real guards; dispatch uses the existing interpreter operation and
//! cleanup registration. Projections below observe that one actual execution.
use super::{protected as scalar, protected_typed as payload, Call, Effect, Failure, Owner, Step};
#[cfg(verus_keep_ghost)]
use super::{replay::transport, semantics, Slot};
#[cfg(verus_keep_ghost)]
use crate::lifecycle_state::services::NativeEpisode;
use crate::reversible_value::{effect::ScalarEffect, registration};
use crate::Port;
use vstd::prelude::*;

verus! {
broadcast use vstd::seq_lib::group_seq_properties;
#[verifier::opaque]
pub(crate) open spec fn scalars<T:?Sized>(steps:Seq<Step<T>>)->Seq<Step<T>>
    decreases steps.len(),
{if steps.len()==0 {Seq::empty()} else {let prefix=scalars(steps.drop_last());if steps.last().result is Scalar {prefix.push(steps.last())} else {prefix}}}
#[verifier::opaque]
pub(crate) open spec fn payloads<T:?Sized>(steps:Seq<Step<T>>)->Seq<Step<T>>
    decreases steps.len(),
{if steps.len()==0 {Seq::empty()} else {let prefix=payloads(steps.drop_last());if steps.last().result is Payload {prefix.push(steps.last())} else {prefix}}}
pub(crate) proof fn projections_empty<T:?Sized>()
    ensures scalars::<T>(Seq::empty())==Seq::<Step<T>>::empty(),payloads::<T>(Seq::empty())==Seq::<Step<T>>::empty(),
{reveal(scalars);reveal(payloads);}
pub(crate) proof fn projections_append<T:?Sized>(steps:Seq<Step<T>>,s:Step<T>)
    ensures scalars(steps.push(s))==if s.result is Scalar {scalars(steps).push(s)} else {scalars(steps)},
        payloads(steps.push(s))==if s.result is Payload {payloads(steps).push(s)} else {payloads(steps)},
{reveal(scalars);reveal(payloads);assert(steps.push(s).drop_last() =~= steps);}
#[verifier::opaque]
pub(crate) open spec fn plan<E:ScalarEffect,T:?Sized>(code:Seq<Call<E,T>>,steps:Seq<Step<T>>)->bool {
    super::next(code.len(),steps).is_none() && forall|i:int|0<=i<steps.len() ==> {
        let s=#[trigger] steps[i];
        &&& Some(s.pc)==super::next(code.len(),steps.take(i))
        &&& transport::step(code,s)
        &&& !(code[s.pc as int].effect is Scalar)
        &&& (s.result is Scalar)==(code[s.pc as int].effect is Kernel)
    }
}
#[verifier::rlimit(8)]
#[verifier::spinoff_prover]
pub(crate) proof fn plan_at<E:ScalarEffect,T:?Sized>(code:Seq<Call<E,T>>,steps:Seq<Step<T>>,at:int)
    requires plan(code,steps),0<=at<=steps.len(),
    ensures super::next(code.len(),steps.take(at)).is_some()==(at<steps.len()),
        at<steps.len() ==> super::next(code.len(),steps.take(at))==Some(steps[at].pc)
            && transport::step(code,steps[at]) && !(code[steps[at].pc as int].effect is Scalar)
            && ((steps[at].result is Scalar)==(code[steps[at].pc as int].effect is Kernel)),
{hide(transport::step);hide(super::next);reveal(plan);if at==steps.len() {assert(steps.take(at) =~= steps);}}
pub(crate) open spec fn pair<T:?Sized>(actual:Step<T>,source:Step<T>)->bool {
    actual.pc==source.pc && actual.next==source.next && (actual.result is Scalar)==(source.result is Scalar)
        && (actual.result is Scalar ==> actual.before()==source.before() && actual.after()==source.after() && actual.outcome()==source.outcome())
        && (actual.result is Payload ==> actual.after()->Payload_0.value==source.after()->Payload_0.value)
}
pub(crate) open spec fn same<T:?Sized>(actual:Seq<Step<T>>,source:Seq<Step<T>>)->bool {
    actual.len()==source.len() && forall|i:int|0<=i<actual.len() ==> pair(#[trigger] actual[i],source[i])
}
pub(crate) proof fn align<E:ScalarEffect,T:?Sized>(code:Seq<Call<E,T>>,a:Step<T>,b:Step<T>)
    requires transport::step(code,a),transport::step(code,b),a.pc==b.pc,!(code[a.pc as int].effect is Scalar),
        code[a.pc as int].effect is Kernel ==> a.before()==b.before(),
    ensures pair(a,b),
{
    if code[a.pc as int].effect is Kernel {transport::paired(code,a,b);}
    else {assert(code[a.pc as int].effect is Replace);}
}
pub(crate) proof fn same_scalars<T:?Sized>(actual:Seq<Step<T>>,source:Seq<Step<T>>)
    requires same(actual,source),ensures scalar::same(scalars(actual),scalars(source)),
    decreases actual.len(),
{
    reveal(scalars);
    if actual.len()>0 {
        same_scalars(actual.drop_last(),source.drop_last());
        assert(pair(actual.last(),source.last()));
        assert forall|i:int|0<=i<scalars(actual).len() implies {
            let a=#[trigger] scalars(actual)[i];let b=scalars(source)[i];
            &&& a.pc==b.pc && a.before()==b.before() && a.after()==b.after() && a.outcome()==b.outcome() && a.next==b.next
        } by {}
    }
}
pub(crate) proof fn scalar_input<T:?Sized>(initial:Seq<crate::reversible_value::ValueState>,routes:Seq<usize>,source:Seq<Step<T>>,at:int)
    requires scalar::execution(initial,routes,scalars(source)),0<=at<source.len(),source[at].result is Scalar,
    ensures source[at].pc<routes.len(),routes[source[at].pc as int]<initial.len(),
        source[at].before()==semantics::Value::Scalar(scalar::after(initial,routes,scalars(source.take(at)))[routes[source[at].pc as int] as int]),
    decreases source.len()-at,
{
    reveal(scalars);reveal(scalar::execution);
    if at+1==source.len() {
        assert(source.drop_last() =~= source.take(at));
        let p=scalars(source.take(at));
        assert(scalars(source)==p.push(source[at]));assert(scalars(source)[p.len() as int]==source[at]);
        assert(scalars(source).take(p.len() as int) =~= p);
    } else {
        assert(scalar::execution(initial,routes,scalars(source.drop_last()))) by {
            assert forall|i:int|0<=i<scalars(source.drop_last()).len() implies {
                let s=#[trigger] scalars(source.drop_last())[i];
                &&& s.result is Scalar && s.pc<routes.len() && routes[s.pc as int]<initial.len()
                &&& s.before()==semantics::Value::Scalar(scalar::after(initial,routes,scalars(source.drop_last()).take(i))[routes[s.pc as int] as int])
            } by {assert(scalars(source.drop_last())[i]==scalars(source)[i]);scalar::input_at(initial,routes,scalars(source),i);assert(scalars(source.drop_last()).take(i) =~= scalars(source).take(i));}
        }
        scalar_input(initial,routes,source.drop_last(),at);assert(source.drop_last().take(at) =~= source.take(at));
    }
}
pub(crate) struct Context<'a,T:?Sized,M> {
    pub(crate) scalar:Option<scalar::Context<'a>>,
    pub(crate) payload:Option<payload::Context<'a,T,M>>,
}
impl<'a,T:?Sized,M> Context<'a,T,M> {
    pub(crate) open spec fn wf(&self)->bool {self.scalar.is_some() && self.payload.is_some() && self.scalar->Some_0.wf() && self.payload->Some_0.wf()}
    pub(crate) open spec fn shape(&self,prior:&Self)->bool {self.scalar->Some_0.shape(&prior.scalar->Some_0) && self.payload->Some_0.shape(&prior.payload->Some_0)}
    pub(crate) open spec fn for_call<E>(&self,episode:NativeEpisode<Slot<T,M>>,pc:usize,port:Port,call:Call<E,T>)->bool {
        match call.effect {Effect::Kernel(_)=>self.scalar->Some_0.for_call(episode,pc,port),Effect::Replace(_)=>self.payload->Some_0.for_call(episode,pc,port),_=>false}
    }
    #[verifier::opaque]
    pub(crate) open spec fn supports<E>(&self,episode:NativeEpisode<Slot<T,M>>,ports:Seq<Port>,code:Seq<Call<E,T>>,expected:Seq<Step<T>>)->bool {
        ports.len()==code.len() && forall|i:int|0<=i<expected.len() ==> {
            let pc=(#[trigger] expected[i]).pc;
            &&& pc<code.len() && self.for_call(episode,pc,ports[pc as int],code[pc as int])
        }
    }
    pub(crate) proof fn supports_at<E>(&self,episode:NativeEpisode<Slot<T,M>>,ports:Seq<Port>,code:Seq<Call<E,T>>,expected:Seq<Step<T>>,at:int)
        requires self.supports(episode,ports,code,expected),0<=at<expected.len(),
        ensures expected[at].pc<code.len(),self.for_call(episode,expected[at].pc,ports[expected[at].pc as int],code[expected[at].pc as int]),ports.len()==code.len(),
    {reveal(Context::supports);}
    pub(crate) proof fn supports_frame<E>(&self,prior:&Self,episode:NativeEpisode<Slot<T,M>>,ports:Seq<Port>,code:Seq<Call<E,T>>,expected:Seq<Step<T>>)
        requires self.shape(prior),prior.supports(episode,ports,code,expected),ensures self.supports(episode,ports,code,expected),
    {reveal(Context::supports);}
    pub(crate) fn release(self) requires self.wf(), {self.payload.unwrap().release();self.scalar.unwrap().release();}
}
}

verus! {
impl<'a,T:?Sized,M> Context<'a,T,M> {
    pub(crate) open spec fn admissible<E:ScalarEffect>(&self,pc:usize,call:Call<E,T>)->bool {
        match call.effect {
            Effect::Kernel(i)=>crate::reversible_value::effect::operation(i.model())(self.scalar->Some_0.states()[self.scalar->Some_0.index(pc) as int]).is_some(),
            Effect::Replace(_)=>self.payload->Some_0.revisions()[self.payload->Some_0.routes()[pc as int] as int] as int
                +self.payload->Some_0.states()[self.payload->Some_0.routes()[pc as int] as int].depth as int+2<=u64::MAX,
            _=>false,
        }
    }
    pub(crate) open spec fn landed(&self,prior:&Self,s:Step<T>)->bool {
        match s.result {
            super::ResultStep::Scalar {..}=>{
                let i=prior.scalar->Some_0.index(s.pc) as int;
                &&& s.before()==semantics::Value::Scalar(prior.scalar->Some_0.states()[i])
                &&& s.address()==(crate::reversible_value::service_composition::Address {journal:prior.scalar->Some_0.targets()[i].journal_spec(),key:prior.scalar->Some_0.targets()[i].object().key})
                &&& self.scalar->Some_0.states()==prior.scalar->Some_0.states().update(i,s.after()->Scalar_0)
                &&& self.payload->Some_0.states()==prior.payload->Some_0.states() && self.payload->Some_0.revisions()==prior.payload->Some_0.revisions()
            },
            super::ResultStep::Payload(a)=>{
                let i=prior.payload->Some_0.routes()[s.pc as int] as int;
                &&& s.before()==semantics::Value::Payload(prior.payload->Some_0.states()[i])
                &&& s.address()==(crate::reversible_value::service_composition::Address {journal:prior.payload->Some_0.targets()[i].journal_spec(),key:prior.payload->Some_0.targets()[i].key()})
                &&& a.inverse().before().revision==prior.payload->Some_0.revisions()[i]
                &&& self.payload->Some_0.states()==prior.payload->Some_0.states().update(i,s.after()->Payload_0)
                &&& self.payload->Some_0.revisions()==prior.payload->Some_0.revisions().update(i,a.inverse().after().revision)
                &&& self.scalar->Some_0.states()==prior.scalar->Some_0.states()
            },
        }
    }
    #[allow(clippy::too_many_arguments)] // Includes the erased receipt.
    pub(crate) fn execute<C,G,A,R,X,E:ScalarEffect+Copy>(&mut self,owner:&mut Owner<C,G,A,R,T,M,X>,id:usize,pc:usize,port:Port,call:&Call<E,T>,Tracked(previous):Tracked<&registration::ReceiptMap>)->(out:Result<Step<T>,Failure<T>>)
        requires old(self).wf(),old(owner).wf(),old(owner).value_state().is_some(),
            old(self).for_call(old(owner).value_state().unwrap(),pc,port,*call),
            registration::witnesses(*previous),old(owner).work_state().accepts(),old(owner).cleanup_state().acquisition_open(id),
        ensures final(self).wf(),final(self).shape(old(self)),
            old(self).admissible(pc,*call) ==> out.is_ok(),
            out.is_ok() ==> final(self).landed(old(self),out->Ok_0) && ((out->Ok_0.result is Scalar)==(call.effect is Kernel)),
            out.is_err() ==> final(self).scalar->Some_0.states()==old(self).scalar->Some_0.states()
                && final(self).payload->Some_0.states()==old(self).payload->Some_0.states()
                && final(self).payload->Some_0.revisions()==old(self).payload->Some_0.revisions(),
            final(owner).cleanup_state().frame(&old(owner).cleanup_state(),id),
            final(owner).cleanup_state().queues().dom()==old(owner).cleanup_state().queues().dom(),
            final(owner).cleanup_state().domain_ids()==old(owner).cleanup_state().domain_ids(),
            old(owner).cleanup_state().live(id) ==> final(owner).cleanup_state().queues()[id].link()==old(owner).cleanup_state().queues()[id].link()
                && final(owner).cleanup_state().queues()[id].issued()==old(owner).cleanup_state().queues()[id].issued()
                && final(owner).cleanup_state().queues()[id].protocol().selected()==old(owner).cleanup_state().queues()[id].protocol().selected(),
            final(owner).cleanup_state().queues()[id].link()==old(owner).cleanup_state().queues()[id].link(),
            final(owner).cleanup_state().link()==old(owner).cleanup_state().link(),
            final(owner).wf(),final(owner).execution_journal()==old(owner).execution_journal(),final(owner).status_links()==old(owner).status_links(),
            final(owner).capture()==old(owner).capture(),final(owner).work_state()==old(owner).work_state(),final(owner).value_state()==old(owner).value_state(),final(owner).phase_spec()==old(owner).phase_spec(),
            final(owner).cleanup_state().acquisition_open(id),
            out.is_err() ==> out->Err_0.explained(*call,port,old(owner).value_state().unwrap()),
            out.is_ok() ==> forall|k:(int,bool)|previous.contains_key(k) && #[trigger] previous[k].journal()==out->Ok_0.write().journal() ==> out->Ok_0.write().follows(&previous[k]),
            out.is_err() && out->Err_0.receipt@.is_some() ==> forall|k:(int,bool)|previous.contains_key(k) && #[trigger] previous[k].journal()==out->Err_0.receipt@.unwrap().journal() ==> out->Err_0.receipt@.unwrap().follows(&previous[k]),
            out.is_err() ==> final(owner).cleanup_state()==old(owner).cleanup_state() && out->Err_0.pc==pc
                && (out->Err_0.receipt@.is_some() ==> out->Err_0.receipt@.unwrap().wf()),
            out.is_ok() ==> {
                let s=out->Ok_0;let q=final(owner).cleanup_state().queues()[id];let before=old(owner).cleanup_state().queues()[id];
                &&& s.inserted_into(q.link())
                &&& s.registered(final(owner).cleanup_state().link(),id)
                &&& s.pc==pc && s.corresponds(*call,port,old(owner).value_state().unwrap()) && final(owner).cleanup_state().live(id)
                &&& s.token()==before.slots().len() && q.slots().len()==before.slots().len()+1 && q.slots().take(s.token() as int)==before.slots()
                &&& s.in_slot(q.slots()[s.token() as int]) && q.protocol().waiting()==before.protocol().waiting().push(s.token())
            },
    {
        let mut unused=None;
        match &call.effect {
            Effect::Kernel(_)=>owner.execute_call(id,pc,port,call,Tracked(previous),&mut self.scalar,&mut unused),
            Effect::Replace(_)=>{
                let mut unused=None;
                owner.execute_call(id,pc,port,call,Tracked(previous),&mut unused,&mut self.payload)
            },
            Effect::Scalar(_)=>{assert(false);panic!("uncontrolled mixed instruction")},
        }
    }
}
}
verus! {
pub(crate) proof fn scalar_after_same<T:?Sized>(initial:Seq<crate::reversible_value::ValueState>,routes:Seq<usize>,left:Seq<Step<T>>,right:Seq<Step<T>>)
    requires scalar::same(left,right),ensures scalar::after(initial,routes,left)==scalar::after(initial,routes,right),
    decreases left.len(),
{
    reveal(scalar::after);
    if left.len()>0 {scalar_after_same(initial,routes,left.drop_last(),right.drop_last());}
}
impl<'a,T:?Sized,M> Context<'a,T,M> {
    #[verifier::opaque]
    pub(crate) open spec fn trace(&self,initial:&Self,steps:Seq<Step<T>>)->bool {
        let a=&initial.scalar->Some_0;let b=&initial.payload->Some_0;
        &&& self.shape(initial)
        &&& scalar::execution(a.states(),a.routes(),scalars(steps)) && scalar::addressed(a.targets(),a.routes(),scalars(steps))
        &&& self.scalar->Some_0.states()==scalar::after(a.states(),a.routes(),scalars(steps))
        &&& payload::execution(b.states(),b.revisions(),b.routes(),payloads(steps)) && payload::addressed(b.targets(),b.routes(),payloads(steps))
        &&& self.payload->Some_0.states()==payload::after(b.states(),b.routes(),payloads(steps))
        &&& self.payload->Some_0.revisions()==payload::clocks(b.revisions(),b.routes(),payloads(steps))
    }
    pub(crate) proof fn begin(&self)
        requires self.wf(),ensures self.trace(self,Seq::empty()),
    {
        reveal(Context::trace);projections_empty::<T>();scalar::empty::<T>(self.scalar->Some_0.states(),self.scalar->Some_0.routes());
        payload::empty::<T>(self.payload->Some_0.states(),self.payload->Some_0.revisions(),self.payload->Some_0.routes());
        payload::address_empty::<T>(self.payload->Some_0.targets(),self.payload->Some_0.routes());
    }
    pub(crate) proof fn record(&self,prior:&Self,initial:&Self,steps:Seq<Step<T>>,s:Step<T>,count:nat)
        requires self.wf(),prior.wf(),initial.wf(),self.shape(prior),prior.trace(initial,steps),self.landed(prior,s),count>0,
            prior.payload->Some_0.budget(count),
            s.result is Scalar ==> s.pc<prior.scalar->Some_0.bindings().len(),
            s.result is Payload ==> s.pc<prior.payload->Some_0.bindings().len() && s.result->Payload_0.inverse().wf(),
        ensures self.trace(initial,steps.push(s)),self.payload->Some_0.budget((count-1) as nat),
            s.result is Scalar ==> s.before()==semantics::Value::Scalar(prior.scalar->Some_0.states()[prior.scalar->Some_0.index(s.pc) as int]),
    {
        reveal(Context::trace);projections_append(steps,s);prior.payload->Some_0.storage_facts();self.payload->Some_0.storage_facts();
        if s.result is Scalar {
            prior.scalar->Some_0.call_facts(s.pc);initial.scalar->Some_0.call_facts(s.pc);
            scalar::append(initial.scalar->Some_0.states(),initial.scalar->Some_0.routes(),scalars(steps),s);
            reveal(payload::Context::budget);
            assert forall|i:int|0<=i<self.payload->Some_0.states().len() implies
                (#[trigger] self.payload->Some_0.revisions()[i]) as int+self.payload->Some_0.states()[i].depth as int+2*(count-1)<=u64::MAX by {
                assert(prior.payload->Some_0.revisions()[i] as int+prior.payload->Some_0.states()[i].depth as int+2*count<=u64::MAX);
            }
        } else {
            prior.payload->Some_0.call_facts(s.pc);initial.payload->Some_0.call_facts(s.pc);
            payload::append(initial.payload->Some_0.states(),initial.payload->Some_0.revisions(),initial.payload->Some_0.routes(),payloads(steps),s);
            payload::address_append(initial.payload->Some_0.targets(),initial.payload->Some_0.routes(),payloads(steps),s);
            self.payload->Some_0.consumed(&prior.payload->Some_0,count,prior.payload->Some_0.routes()[s.pc as int] as int,s);
        }
        assert(scalar::addressed(initial.scalar->Some_0.targets(),initial.scalar->Some_0.routes(),scalars(steps.push(s)))) by {
            if s.result is Scalar {
                assert forall|i:int|0<=i<scalars(steps.push(s)).len() implies {
                    let x=#[trigger] scalars(steps.push(s))[i];
                    &&& x.pc<initial.scalar->Some_0.routes().len() && initial.scalar->Some_0.routes()[x.pc as int]<initial.scalar->Some_0.targets().len()
                    &&& x.address()==(crate::reversible_value::service_composition::Address {journal:initial.scalar->Some_0.targets()[initial.scalar->Some_0.routes()[x.pc as int] as int].journal_spec(),key:initial.scalar->Some_0.targets()[initial.scalar->Some_0.routes()[x.pc as int] as int].object().key})
                } by {}
            }
        }
    }
    pub(crate) proof fn ready<E:ScalarEffect>(&self,initial:&Self,code:Seq<Call<E,T>>,ports:Seq<Port>,episode:NativeEpisode<Slot<T,M>>,actual:Seq<Step<T>>,source:Seq<Step<T>>,pc:usize,count:nat)
        requires self.wf(),initial.wf(),self.trace(initial,actual),self.supports(episode,ports,code,source),plan(code,source),
            actual.len()<=source.len(),same(actual,source.take(actual.len() as int)),
            super::next(code.len(),source.take(actual.len() as int))==Some(pc),pc<code.len(),
            scalar::execution(initial.scalar->Some_0.states(),initial.scalar->Some_0.routes(),scalars(source)),
            count>0,self.payload->Some_0.budget(count),
        ensures self.admissible(pc,code[pc as int]),self.for_call(episode,pc,ports[pc as int],code[pc as int]),
            actual.len()<source.len(),source[actual.len() as int].pc==pc,
            code[pc as int].effect is Kernel ==> source[actual.len() as int].before()==semantics::Value::Scalar(self.scalar->Some_0.states()[self.scalar->Some_0.index(pc) as int]),
    {
        reveal(Context::trace);plan_at(code,source,actual.len() as int);self.supports_at(episode,ports,code,source,actual.len() as int);
        if code[pc as int].effect is Kernel {
            self.scalar->Some_0.call_facts(pc);
            same_scalars(actual,source.take(actual.len() as int));
            scalar_after_same(initial.scalar->Some_0.states(),initial.scalar->Some_0.routes(),scalars(actual),scalars(source.take(actual.len() as int)));
            scalar_input(initial.scalar->Some_0.states(),initial.scalar->Some_0.routes(),source,actual.len() as int);
        } else {
            self.payload->Some_0.call_facts(pc);
            self.payload->Some_0.budget_at(count,self.payload->Some_0.routes()[pc as int] as int);
        }
    }
}
pub(crate) proof fn same_append<E:ScalarEffect,T:?Sized>(code:Seq<Call<E,T>>,actual:Seq<Step<T>>,source:Seq<Step<T>>,s:Step<T>)
    requires plan(code,source),actual.len()<source.len(),same(actual,source.take(actual.len() as int)),
        transport::step(code,s),s.pc==source[actual.len() as int].pc,
        code[s.pc as int].effect is Kernel ==> s.before()==source[actual.len() as int].before(),
    ensures same(actual.push(s),source.take(actual.len() as int+1)),
        super::next(code.len(),source.take(actual.len() as int+1))==s.next,
{
    plan_at(code,source,actual.len() as int);align(code,s,source[actual.len() as int]);
    assert forall|i:int|0<=i<actual.push(s).len() implies pair(#[trigger] actual.push(s)[i],source.take(actual.len() as int+1)[i]) by {}
    assert(source.take(actual.len() as int+1).last()==source[actual.len() as int]);
}
}
verus! {
pub(crate) proof fn payload_member<T:?Sized>(steps:Seq<Step<T>>,i:int)->(out:int)
    requires 0<=i<payloads(steps).len(),
    ensures 0<=out<steps.len(),payloads(steps)[i]==steps[out],steps[out].result is Payload,
    decreases steps.len(),
{
    reveal(payloads);
    if steps.last().result is Payload && i==payloads(steps.drop_last()).len() {steps.len() as int-1}
    else {payload_member(steps.drop_last(),i)}
}
/// Position in the payload projection is derived from the actual full path.
pub(crate) proof fn payload_position<T:?Sized>(a:Seq<Step<T>>,b:Seq<Step<T>>,at:int)->(out:int)
    requires same(b,a),0<=at<a.len(),a[at].result is Payload,
    ensures 0<=out<payloads(a).len(),out<payloads(b).len(),payloads(a)[out]==a[at],payloads(b)[out]==b[at],
    decreases a.len(),
{
    reveal(payloads);
    if at==a.len()-1 {
        assert(pair(b[at],a[at]));same_payloads(b.drop_last(),a.drop_last());payloads(a.drop_last()).len() as int
    } else {payload_position(a.drop_last(),b.drop_last(),at)}
}
pub(crate) proof fn same_payloads<T:?Sized>(actual:Seq<Step<T>>,source:Seq<Step<T>>)
    requires same(actual,source),
    ensures super::replay::typed_correspondence::aligned(payloads(source),payloads(actual)),
    decreases actual.len(),
{
    reveal(payloads);
    if actual.len()>0 {
        same_payloads(actual.drop_last(),source.drop_last());assert(pair(actual.last(),source.last()));
        assert forall|i:int|0<=i<payloads(source).len() implies {
            let a=#[trigger] payloads(source)[i];let b=payloads(actual)[i];
            &&& a.result is Payload && b.result is Payload && a.pc==b.pc && a.next==b.next
            &&& a.after()->Payload_0.value==b.after()->Payload_0.value
        } by {}
    }
}
impl<'a,T:?Sized,M> Context<'a,T,M> {
    pub(crate) proof fn typed_inputs(&self,initial:&Self,steps:Seq<Step<T>>)
        requires self.trace(initial,steps),
            forall|i:int|0<=i<steps.len() && (#[trigger] steps[i]).result is Payload ==> steps[i].result->Payload_0.inverse().wf(),
        ensures super::replay::typed_correspondence::inputs(initial.payload->Some_0.states(),initial.payload->Some_0.routes(),payloads(steps)),
    {
        reveal(Context::trace);reveal(payload::execution);
        assert forall|i:int|0<=i<payloads(steps).len() implies {
            let s=#[trigger] payloads(steps)[i];
            &&& s.result is Payload && s.pc<initial.payload->Some_0.routes().len() && initial.payload->Some_0.routes()[s.pc as int]<initial.payload->Some_0.states().len()
            &&& s.before()->Payload_0==payload::after(initial.payload->Some_0.states(),initial.payload->Some_0.routes(),payloads(steps).take(i))[initial.payload->Some_0.routes()[s.pc as int] as int]
            &&& super::replay::typed_correspondence::fresh(s)
        } by {let j=payload_member(steps,i);assert(steps[j].result->Payload_0.inverse().wf());super::replay::typed_correspondence::fresh_step(payloads(steps)[i]);}
    }
}
}
