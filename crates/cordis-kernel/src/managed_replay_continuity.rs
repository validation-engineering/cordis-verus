//! Executable continuity checks over operands retained from real inverse owners.
//! No live-object rereads, callback execution or inverse consumption is involved.
use super::{inputs::Input, Source};
use crate::reversible_value::effect::ScalarEffect;
use crate::reversible_value::managed::Step;
#[cfg(verus_keep_ghost)]
use crate::reversible_value::managed::{recovery::word, semantics};
use vstd::prelude::*;

verus! {
broadcast use vstd::seq_lib::group_seq_properties;
#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub struct Site {pub call:usize,pub step:usize}
#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub enum Error {Unnamed {at:Site},Changed {previous:Site,current:Site}}
struct Observation<'a,T:?Sized> {site:Site,input:&'a Input<T>}

pub closed spec fn call_steps<E:ScalarEffect,T:?Sized>(source:Source<E,T>)->Seq<Step<T>> {
    source.inputs@.map(|_:int,input:Input<T>|input.source())
}
pub open spec fn trace<E:ScalarEffect,T:?Sized>(sources:Seq<Source<E,T>>,order:Seq<usize>)->Seq<Step<T>>
    decreases order.len(),
{
    if order.len()==0 {Seq::empty()} else {trace(sources,order.drop_last())+call_steps(sources[order.last() as int])}
}
spec fn observed<T:?Sized>(items:Seq<Observation<T>>)->Seq<Step<T>> {
    items.map(|_:int,x:Observation<T>|x.input.source())
}
spec fn authentic<E:ScalarEffect,T:?Sized>(sources:Seq<Source<E,T>>,items:Seq<Observation<T>>)->bool {
    forall|i:int|0<=i<items.len() ==> {
        let x=#[trigger] items[i];
        &&& x.site.call<sources.len() && x.site.step<sources[x.site.call as int].inputs.len()
        &&& *x.input==sources[x.site.call as int].inputs@[x.site.step as int]
        &&& x.input.wf()
    }
}
pub closed spec fn input_at<E:ScalarEffect,T:?Sized>(sources:Seq<Source<E,T>>,site:Site)->Input<T> {
    sources[site.call as int].inputs@[site.step as int]
}
pub closed spec fn site_valid<E:ScalarEffect,T:?Sized>(sources:Seq<Source<E,T>>,site:Site)->bool {
    site.call<sources.len() && site.step<sources[site.call as int].inputs.len()
}
pub open spec fn explains<E:ScalarEffect,T:?Sized>(sources:Seq<Source<E,T>>,error:Error)->bool {
    match error {
        Error::Unnamed {at}=>site_valid(sources,at) && input_at(sources,at).identity_spec().number_spec().is_none(),
        Error::Changed {previous,current}=>site_valid(sources,previous) && site_valid(sources,current)
            && input_at(sources,previous).source().address()==input_at(sources,current).source().address()
            && input_at(sources,previous).source().after()!=input_at(sources,current).source().before(),
    }
}
/// This is an erased certificate for the checked source observations, not an
/// executable inverse, a frozen shared heap or a promise that target replay succeeds.
#[allow(dead_code)]
pub struct Checked<T:?Sized> {steps:Ghost<Seq<Step<T>>>}
impl<T:?Sized> Checked<T> {
    pub closed spec fn steps(&self)->Seq<Step<T>> {self.steps@}
    pub closed spec fn wf(&self)->bool {word::composing(self.steps())
        && forall|i:int|0<=i<self.steps().len() ==> (#[trigger] self.steps()[i]).recorded_values()}
    /// The first inputs are derived from real calls. No separate inverse-domain
    /// premise or caller-supplied heap is needed for this finite source word.
    pub proof fn recovery(&self)
        requires self.wf(),
        ensures semantics::replay(self.steps(),word::initial(self.steps()))==Some(word::landed(self.steps(),word::initial(self.steps()))),
            semantics::undo(self.steps(),word::landed(self.steps(),word::initial(self.steps())))==Some(word::initial(self.steps())),
    {word::initial_inputs(self.steps());word::defined(self.steps(),word::initial(self.steps()));}
}
fn collect<'a,E:ScalarEffect,T:?Sized>(sources:&'a [Source<E,T>],order:&[usize])->(out:Vec<Observation<'a,T>>)
    requires forall|i:int|0<=i<sources.len() ==> (#[trigger] sources@[i]).wf(),
        forall|i:int|0<=i<order.len() ==> (#[trigger] order@[i])<sources.len(),
    ensures observed(out@)==trace(sources@,order@),authentic(sources@,out@),
{
    let mut out:Vec<Observation<T>>=Vec::new();let mut i=0;
    while i<order.len()
        invariant i<=order.len(),observed(out@)==trace(sources@,order@.take(i as int)),authentic(sources@,out@),
            forall|k:int|0<=k<sources.len() ==> (#[trigger] sources@[k]).wf(),
            forall|k:int|0<=k<order.len() ==> (#[trigger] order@[k])<sources.len(),
        decreases order.len()-i,
    {
        let call=order[i];let source=&sources[call];let ghost prefix=out@;let mut j=0;
        while j<source.inputs.len()
            invariant j<=source.inputs.len(),source==&sources[call as int],call<sources.len(),source.wf(),
                authentic(sources@,out@),observed(out@)==observed(prefix)+call_steps(*source).take(j as int),
            decreases source.inputs.len()-j,
        {
            let ghost before=out@;
            let x=Observation {site:Site {call,step:j},input:&source.inputs[j]};out.push(x);
            proof {
                assert(out@.drop_last() =~= before);
                assert(observed(out@) =~= observed(before).push(x.input.source()));
                assert(call_steps(*source).take(j+1) =~= call_steps(*source).take(j as int).push(x.input.source()));
                assert(observed(before)==observed(prefix)+call_steps(*source).take(j as int));
                assert(observed(out@) =~= observed(prefix)+call_steps(*source).take(j+1));
            }
            j+=1;
        }
        proof {assert(order@.take(i+1).drop_last() =~= order@.take(i as int));}
        i+=1;
    }
    out
}
fn check_next<E:ScalarEffect,T:?Sized>(_sources:&[Source<E,T>],items:&[Observation<T>],at:usize)->(out:Result<(),Error>)
    requires at<items.len(),authentic(_sources@,items@),
        forall|i:int|0<=i<items.len() ==> (#[trigger] items@[i]).input.identity_spec().namespace()==items@[at as int].input.identity_spec().namespace(),
    ensures out.is_err() ==> explains(_sources@,out->Err_0),
        out.is_ok() ==> forall|i:int|#[trigger] word::adjacent(observed(items@).take(at+1),i,at as int)
            ==> observed(items@)[i].after()==observed(items@)[at as int].before(),
{
    hide(crate::reversible_value::joint::valid);hide(crate::reversible_value::joint::step);
    let current=&items[at];
    if current.input.identity().number().is_none() {return Err(Error::Unnamed {at:current.site});}
    let mut j=at;
    while j>0
        invariant j<=at,at<items.len(),authentic(_sources@,items@),current==&items[at as int],current.input.identity_spec().number_spec().is_some(),
            forall|k:int|0<=k<items.len() ==> (#[trigger] items@[k]).input.identity_spec().namespace()==current.input.identity_spec().namespace(),
            forall|k:int|j<=k<at ==> (#[trigger] items@[k]).input.source().address()!=current.input.source().address(),
        decreases j,
    {
        j-=1;let prior=&items[j];
        let same=match current.input.identity().same(prior.input.identity()) {
            Some(same)=>same,None=>return Err(Error::Unnamed {at:prior.site}),
        };
        if same {
            if !current.input.continues(prior.input) {return Err(Error::Changed {previous:prior.site,current:current.site});}
            proof {
                assert forall|i:int|#[trigger] word::adjacent(observed(items@).take(at+1),i,at as int)
                    implies observed(items@)[i].after()==observed(items@)[at as int].before() by {
                    if i<j {assert(observed(items@).take(at+1)[j as int].address()!=observed(items@).take(at+1)[i].address());}
                    if i>j {assert(items@[i].input.source().address()!=current.input.source().address());}
                }
            }
            return Ok(());
        }
    }
    Ok(())
}
/// Inspect every retained successful step in actual call order. A mismatch is
/// reported with the two real call/step locations; the inputs remain borrowed.
pub fn check<E:ScalarEffect,T:?Sized>(sources:&[Source<E,T>],order:&[usize])->(out:Result<Checked<T>,Error>)
    requires forall|i:int|0<=i<sources.len() ==> (#[trigger] sources@[i]).wf(),
        forall|i:int|0<=i<order.len() ==> (#[trigger] order@[i])<sources.len(),
        forall|i:int,j:int,k:int,l:int|0<=i<sources.len() && 0<=j<sources@[i].input_spec().len()
            && 0<=k<sources.len() && 0<=l<sources@[k].input_spec().len() ==>
            sources@[i].input_spec()[j].identity_spec().namespace()==sources@[k].input_spec()[l].identity_spec().namespace(),
    ensures out.is_ok() ==> out->Ok_0.wf() && out->Ok_0.steps()==trace(sources@,order@),
        out.is_err() ==> explains(sources@,out->Err_0),
{
    hide(crate::reversible_value::joint::valid);hide(crate::reversible_value::joint::step);
    let items=collect(sources,order);let mut i=0;
    proof {
        assert forall|a:int,b:int|0<=a<items.len() && 0<=b<items.len() implies
            items@[a].input.identity_spec().namespace()==items@[b].input.identity_spec().namespace() by {
            let x=items@[a].site;let y=items@[b].site;
            assert(sources@[x.call as int].input_spec()[x.step as int].identity_spec().namespace()
                ==sources@[y.call as int].input_spec()[y.step as int].identity_spec().namespace());
        }
    }
    while i<items.len()
        invariant i<=items.len(),authentic(sources@,items@),observed(items@)==trace(sources@,order@),
            word::composing(observed(items@).take(i as int)),
            forall|a:int,b:int|0<=a<items.len() && 0<=b<items.len() ==>
                items@[a].input.identity_spec().namespace()==items@[b].input.identity_spec().namespace(),
        decreases items.len()-i,
    {
        check_next(sources,items.as_slice(),i)?;
        proof {
            assert forall|a:int,b:int|#[trigger] word::adjacent(observed(items@).take(i+1),a,b)
                implies observed(items@).take(i+1)[a].after()==observed(items@).take(i+1)[b].before() by {
                if b<i {assert(word::adjacent(observed(items@).take(i as int),a,b));}
            }
        }
        i+=1;
    }
    proof {
        assert(observed(items@).take(i as int) =~= observed(items@));
        assert forall|k:int|0<=k<observed(items@).len() implies (#[trigger] observed(items@)[k]).recorded_values() by {
            assert(items@[k].input.wf());items@[k].input.provenance();
            assert(observed(items@)[k]==items@[k].input.source());
        }
    }
    let out=Checked {steps:Ghost(observed(items@))};proof {out.recovery();}Ok(out)
}
}
