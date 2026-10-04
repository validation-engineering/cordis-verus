//! External inputs must travel with the names they reference.
//!
//! Alpha equivalence of configurations alone does not identify two literal
//! retirement commands. These lemmas transport the complete insertion payload,
//! including name-bearing continuation roots, and connect that transport to the
//! inputs extracted from actual mixed executions.
#[cfg(verus_keep_ghost)]
use crate::{
    alpha as names, causal_normalization as causal, fresh_equivariance as equiv,
    fresh_grammar as fresh, fresh_semantics as source, mixed_grammar as g,
    observational_grammar as og, refinement as r, Port,
};
use vstd::prelude::*;

verus! {

pub open spec fn input<I>(rho:names::Renaming,h:fresh::IndexRenaming<I>,value:causal::ExternalInput<I>)->causal::ExternalInput<I> {
    match value {
        causal::ExternalInput::Insert {actor,parent,dependencies,provisions,root}=>causal::ExternalInput::Insert {
            actor:(rho.forward)(actor),parent:names::parent(rho,parent),dependencies,provisions,root:(h.forward)(root)},
        causal::ExternalInput::Retire {actor}=>causal::ExternalInput::Retire {actor:(rho.forward)(actor)},
        causal::ExternalInput::Remove {actor}=>causal::ExternalInput::Remove {actor:(rho.forward)(actor)},
    }
}
pub open spec fn optional<I>(rho:names::Renaming,h:fresh::IndexRenaming<I>,value:Option<causal::ExternalInput<I>>)->Option<causal::ExternalInput<I>> {
    match value {None=>None,Some(value)=>Some(input(rho,h,value))}
}
pub open spec fn inputs<I>(rho:names::Renaming,h:fresh::IndexRenaming<I>,values:Seq<causal::ExternalInput<I>>)->Seq<causal::ExternalInput<I>> {
    values.map(|_:int,value:causal::ExternalInput<I>|input(rho,h,value))
}
pub open spec fn configurations<U,I>(rho:names::Renaming,h:fresh::IndexRenaming<I>,source:Seq<g::Configuration<U,I>>)->Seq<g::Configuration<U,I>> {
    source.map(|_:int,a:g::Configuration<U,I>|fresh::configuration(rho,h,a))
}

pub proof fn extraction<U,I>(rho:names::Renaming,h:fresh::IndexRenaming<I>,after:g::Configuration<U,I>,label:causal::Label)
    requires names::bijective(rho),label.1==r::Rule::Insert ==> r::registered(after.state.control,label.0) && after.roots.dom().contains(label.0),
    ensures causal::input(fresh::configuration(rho,h,after),((rho.forward)(label.0),label.1))
        ==optional(rho,h,causal::input(after,label)),
{
    if label.1==r::Rule::Insert {names::observations(rho,after.state.control,label.0);}
}

pub proof fn compact_transport<I>(rho:names::Renaming,h:fresh::IndexRenaming<I>,source:Seq<Option<causal::ExternalInput<I>>>)
    ensures causal::compact(source.map(|_:int,value:Option<causal::ExternalInput<I>>|optional(rho,h,value)))
        ==inputs(rho,h,causal::compact(source)),
    decreases source.len(),
{
    if source.len()>0 {
        compact_transport(rho,h,source.drop_last());
        let mapped=source.map(|_:int,value:Option<causal::ExternalInput<I>>|optional(rho,h,value));
        assert(mapped.drop_last() =~= source.drop_last().map(|_:int,value:Option<causal::ExternalInput<I>>|optional(rho,h,value)));
        if source.last().is_some() {
            let prefix=causal::compact(source.drop_last());let value=source.last().unwrap();
            assert(inputs(rho,h,prefix.push(value)) =~= inputs(rho,h,prefix).push(input(rho,h,value)));
        }
    } else {assert(source =~= Seq::empty());}
}

/// This is an extraction theorem, not an assumption that a renamed execution
/// uses the same program. Source execution supplies the real Insert poststate.
pub proof fn execution_inputs<A,X,U,B,I>(rho:names::Renaming,h:fresh::IndexRenaming<I>,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    source:Seq<g::Configuration<U,I>>,labels:Seq<causal::Label>)
    requires names::bijective(rho),g::execution(lib,programs,source,labels),
    ensures causal::inputs(configurations(rho,h,source),names::rename_labels(rho,labels))
        ==inputs(rho,h,causal::inputs(source,labels)),
{
    let raw=causal::raw_inputs(source,labels);
    let renamed=causal::raw_inputs(configurations(rho,h,source),names::rename_labels(rho,labels));
    assert(renamed =~= raw.map(|_:int,value:Option<causal::ExternalInput<I>>|optional(rho,h,value))) by {
        assert forall|i:int| 0<=i<labels.len() implies renamed[i]==optional(rho,h,raw[i]) by {
            extraction(rho,h,source[i+1],labels[i]);
        }
    }
    compact_transport(rho,h,raw);
}

/// The same complete input extraction for actual dynamic-allocation traces.
/// Allocation choices in lifecycle labels are transported independently of the
/// external subsequence; every Insert retains its real argument payload.
pub proof fn fresh_execution_inputs<A,X,U,B,I>(rho:names::Renaming,h:fresh::IndexRenaming<I>,lib:source::Library<A,X,U,B>,programs:source::Programs<A,X,U,B,I>,
    trace:Seq<g::Configuration<U,I>>,events:Seq<source::Label>)
    requires names::bijective(rho),source::execution(lib,programs,trace,events),
    ensures causal::inputs(equiv::configurations(rho,h,trace),source::rules(equiv::labels(rho,events)))
        ==inputs(rho,h,causal::inputs(trace,source::rules(events))),
{
    let labels=source::rules(events);let raw=causal::raw_inputs(trace,labels);
    let target=causal::raw_inputs(equiv::configurations(rho,h,trace),source::rules(equiv::labels(rho,events)));
    assert(target =~= raw.map(|_:int,value:Option<causal::ExternalInput<I>>|optional(rho,h,value))) by {
        assert forall|i:int| 0<=i<events.len() implies target[i]==optional(rho,h,raw[i]) by {
            extraction(rho,h,trace[i+1],labels[i]);
        }
    }
    compact_transport(rho,h,raw);
}

/// An actual execution of one natural installed program yields another actual
/// execution and its transported inputs. Neither conclusion is a premise.
pub proof fn natural_execution_inputs<A,X,U,B,I>(rho:names::Renaming,action:fresh::NameAction<I>,eq:spec_fn(Port,U,U)->bool,
    lib:source::Library<A,X,U,B>,programs:source::Programs<A,X,U,B,I>,trace:Seq<g::Configuration<U,I>>,events:Seq<source::Label>)
    requires names::bijective(rho),fresh::supported_action(action),fresh::natural(action,programs),og::primitive_theory(eq,lib),
        source::execution(lib,programs,trace,events),trace.first()==source::empty::<U,I>(),
    ensures {
        let h=fresh::action_map(action,rho);let renamed=equiv::configurations(rho,h,trace);let labels=equiv::labels(rho,events);
        &&& source::execution(lib,programs,renamed,labels) && renamed.first()==source::empty::<U,I>()
        &&& causal::inputs(renamed,source::rules(labels))==inputs(rho,h,causal::inputs(trace,source::rules(events)))
    },
{
    equiv::natural_from_empty(rho,action,eq,lib,programs,trace,events);
    fresh_execution_inputs(rho,fresh::action_map(action,rho),lib,programs,trace,events);
}

pub proof fn round_trip<I>(rho:names::Renaming,h:fresh::IndexRenaming<I>,value:causal::ExternalInput<I>)
    requires names::bijective(rho),fresh::index_bijective(h),
    ensures input(names::inverse(rho),fresh::IndexRenaming {forward:h.backward,backward:h.forward},input(rho,h,value))==value,
{
    match value {causal::ExternalInput::Insert {parent,..}=>{match parent {None=>{},Some(_)=>{}}},_=>{}}
}

pub open spec fn referenced<I>(action:fresh::NameAction<I>,value:causal::ExternalInput<I>)->ISet<usize> {
    match value {
        causal::ExternalInput::Insert {actor,parent,root,..}=>ISet::empty().insert(actor)
            .union(match parent {None=>ISet::empty(),Some(parent)=>ISet::empty().insert(parent)})
            .union((action.support)(root)),
        causal::ExternalInput::Retire {actor}|causal::ExternalInput::Remove {actor}=>ISet::empty().insert(actor),
    }
}
pub proof fn input_agrees<I>(action:fresh::NameAction<I>,rho:names::Renaming,other:names::Renaming,value:causal::ExternalInput<I>)
    requires fresh::supported_action(action),names::bijective(rho),names::bijective(other),
        names::agrees_on(rho,other,referenced(action,value)),
    ensures input(rho,fresh::action_map(action,rho),value)==input(other,fresh::action_map(action,other),value),
{
    match value {
        causal::ExternalInput::Insert {actor,parent,root,..}=>{
            assert(referenced(action,value).contains(actor));
            assert(names::agrees_on(rho,other,(action.support)(root))) by {
                assert forall|n:usize| #[trigger] (action.support)(root).contains(n) implies (rho.forward)(n)==(other.forward)(n) by {
                    assert(referenced(action,value).contains(n));
                }
            }
            match parent {None=>{},Some(parent)=>{assert(referenced(action,value).contains(parent));}}
        },
        causal::ExternalInput::Retire {actor}|causal::ExternalInput::Remove {actor}=>{assert(referenced(action,value).contains(actor));},
    }
}

/// Literal equality requires every referenced payload field to be fixed.
/// Equality of endpoints up to alpha cannot discharge this input condition.
pub open spec fn fixed<I>(rho:names::Renaming,h:fresh::IndexRenaming<I>,value:causal::ExternalInput<I>)->bool {
    match value {
        causal::ExternalInput::Insert {actor,parent,root,..}=>(rho.forward)(actor)==actor
            && names::parent(rho,parent)==parent && (h.forward)(root)==root,
        causal::ExternalInput::Retire {actor}|causal::ExternalInput::Remove {actor}=>(rho.forward)(actor)==actor,
    }
}
pub proof fn literal_input<I>(rho:names::Renaming,h:fresh::IndexRenaming<I>,value:causal::ExternalInput<I>)
    ensures (input(rho,h,value)==value)==fixed(rho,h,value),
{ }
pub proof fn literal_stream<I>(rho:names::Renaming,h:fresh::IndexRenaming<I>,values:Seq<causal::ExternalInput<I>>)
    ensures (inputs(rho,h,values)==values)==(forall|i:int| 0<=i<values.len() ==> fixed(rho,h,values[i])),
{
    assert forall|i:int| 0<=i<values.len() implies (input(rho,h,values[i])==values[i])==fixed(rho,h,values[i]) by {literal_input(rho,h,values[i]);}
    if forall|i:int| 0<=i<values.len() ==> fixed(rho,h,values[i]) {assert(inputs(rho,h,values) =~= values);}
}

/// A birth correspondence swapping the two children transports Retire(2) to
/// Retire(3). Equal literal Retire(2) commands do not express that correspondence.
pub proof fn retirement_requires_transport()
    ensures {
        let rho=names::Renaming {forward:|n:usize|names::swap(2,3,n),backward:|n:usize|names::swap(2,3,n)};
        let h=fresh::IndexRenaming {forward:|x:bool|x,backward:|x:bool|x};
        &&& names::bijective(rho)
        &&& input(rho,h,causal::ExternalInput::Retire {actor:2})==causal::ExternalInput::<bool>::Retire {actor:3}
        &&& input(rho,h,causal::ExternalInput::Retire {actor:2})!=causal::ExternalInput::<bool>::Retire {actor:2}
    },
{
    assert forall|n:usize| names::swap(2,3,names::swap(2,3,n))==n by {names::swap_involution(2,3,n);}
}

} // verus!
