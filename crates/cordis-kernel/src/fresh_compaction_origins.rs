//! A legal surviving source execution supplies every command's retained origin.
#[cfg(verus_keep_ghost)]
use super::{a, origins as o, selected, source};
#[cfg(verus_keep_ghost)]
use crate::{
    closed_region_deletion as region, fresh_grammar as f, fresh_semantics as fs,
    mixed_driver::fresh::{self as driver},
    mixed_driver::{library, library_theory, Blueprint, Index, Transition},
    mixed_grammar as g, semantics as s, Port,
};
use vstd::prelude::*;
verus! {
pub open spec fn known(ts:Seq<Transition>,n:usize)->bool {
    exists|j:int|0<=j<ts.len() && a::birth_spec(ts[j])==Some(n)
}
pub open spec fn recorded(ts:Seq<Transition>)->bool {
    forall|i:int,n:usize|0<=i<ts.len() && o::references(ts[i],n) ==> known(ts.take(i),n)
}
pub proof fn selection_names(ts:Seq<Transition>,keep:Seq<bool>,n:usize)
    requires ts.len()==keep.len(),
    ensures known(selected(ts,keep),n)==(exists|j:int|0<=j<ts.len() && keep[j] && a::birth_spec(ts[j])==Some(n)),
    decreases ts.len(),
{
    if ts.len()>0 {
        selection_names(ts.drop_last(),keep.drop_last(),n);
        let before=selected(ts.drop_last(),keep.drop_last());
        if known(selected(ts,keep),n) {
            let k=choose|k:int|0<=k<selected(ts,keep).len() && a::birth_spec(selected(ts,keep)[k])==Some(n);
            if k<before.len() {
                assert(known(before,n));let j=choose|j:int|0<=j<ts.len()-1 && keep[j] && a::birth_spec(ts[j])==Some(n);
            } else {assert(k==before.len());assert(keep.last() && a::birth_spec(ts.last())==Some(n));}
        }
        if exists|j:int|0<=j<ts.len() && keep[j] && a::birth_spec(ts[j])==Some(n) {
            let j=choose|j:int|0<=j<ts.len() && keep[j] && a::birth_spec(ts[j])==Some(n);
            if j<ts.len()-1 {
                assert(keep.drop_last()[j] && a::birth_spec(ts.drop_last()[j])==Some(n));
                assert(exists|k:int|0<=k<ts.drop_last().len() && keep.drop_last()[k] && a::birth_spec(ts.drop_last()[k])==Some(n));
                assert(known(before,n));let k=choose|k:int|0<=k<before.len() && a::birth_spec(before[k])==Some(n);
                assert(a::birth_spec(selected(ts,keep)[k])==Some(n));
            } else {assert(j==ts.len()-1);assert(a::birth_spec(selected(ts,keep)[before.len() as int])==Some(n));}
        }
    }
}
pub proof fn selection_position(ts:Seq<Transition>,keep:Seq<bool>,i:int)
    requires ts.len()==keep.len(),0<=i<ts.len(),keep[i],
    ensures {
        let prefix=selected(ts.take(i),keep.take(i));let all=selected(ts,keep);
        prefix.len()<all.len() && all[prefix.len() as int]==ts[i] && all.take(prefix.len() as int)==prefix
    },
    decreases ts.len(),
{
    if i<ts.len()-1 {
        selection_position(ts.drop_last(),keep.drop_last(),i);
        assert(ts.drop_last().take(i)==ts.take(i));assert(keep.drop_last().take(i)==keep.take(i));
        let prefix=selected(ts.take(i),keep.take(i));let before=selected(ts.drop_last(),keep.drop_last());
        assert(selected(ts,keep).take(prefix.len() as int)==before.take(prefix.len() as int));
    } else {
        assert(i==ts.len()-1);assert(ts.take(i)==ts.drop_last());assert(keep.take(i)==keep.drop_last());
    }
}
pub proof fn selected_closed(ts:Seq<Transition>,keep:Seq<bool>)
    requires ts.len()==keep.len(),recorded(selected(ts,keep)),
    ensures o::closed(ts,keep),
{
    assert forall|i:int,n:usize|0<=i<ts.len() && keep[i] && o::references(ts[i],n) implies
        exists|j:int|0<=j<i && keep[j] && a::birth_spec(ts[j])==Some(n) by {
        selection_position(ts,keep,i);let before=selected(ts.take(i),keep.take(i));
        assert(known(selected(ts,keep).take(before.len() as int),n));
        selection_names(ts.take(i),keep.take(i),n);
    }
}
#[verifier::spinoff_prover]
pub proof fn step_origins(bank:Seq<Blueprint>,a:g::Configuration<u64,Index>,z:g::Configuration<u64,Index>,t:Transition)
    requires fs::well_formed(library(),driver::programs(bank),a),
        fs::step(library(),driver::programs(bank),a,z,driver::label(t).0,driver::label(t).1,driver::label(t).2),a::payload(t,z),
    ensures forall|n:usize|o::references(t,n) ==> s::registered(a.state,n),
        forall|n:usize|s::registered(z.state,n) && !s::registered(a.state,n) ==> a::birth_spec(t)==Some(n),
{
    library_theory();crate::observational_grammar::exact_theory(|_:Port,x:u64,y:u64|x==y,library());
    let label=driver::label(t);fs::frame(|_:Port,x:u64,y:u64|x==y,library(),driver::programs(bank),a,z,label.0,label.1,label.2);
    if fs::landing(a,z,label.1) {
        fs::run_members(|_:Port,x:u64,y:u64|x==y,library(),driver::programs(bank),a.state,label.0,a.current[label.0].unwrap(),label.2);
        fs::run_admissible(|_:Port,x:u64,y:u64|x==y,library(),driver::programs(bank)(label.0)(a.current[label.0].unwrap()),a.state,label.0,label.2);
    }
    assert forall|n:usize|o::references(t,n) implies s::registered(a.state,n) by {
        match t {Transition::Insert {parent,..}=>{assert(parent==Some(n));},_=>{assert(t.actor()==n);}}
    }
    assert forall|n:usize|s::registered(z.state,n) && !s::registered(a.state,n) implies a::birth_spec(t)==Some(n) by {
        match t {Transition::Insert {actor,..}=>{assert(n==actor);},_=>{
            assert(fs::landing(a,z,label.1));let out=fs::entry(library(),driver::programs(bank),a,label.0,label.2).landed;
            assert(out.spawn.is_some() && out.spawn.unwrap().0==n);assert(g::captured_child(out.receipt)==Some(n));
        }}
    }
}
#[verifier::spinoff_prover]
pub proof fn from_execution(bank:Seq<Blueprint>,states:Seq<g::Configuration<u64,Index>>,ts:Seq<Transition>)
    requires fs::execution(library(),driver::programs(bank),states,driver::labels(ts)),states.first()==g::empty::<u64,Index>(),a::payloads(ts,states),
        forall|i:int|0<=i<states.len() ==> fs::well_formed(library(),driver::programs(bank),states[i]),
    ensures recorded(ts),forall|n:usize|s::registered(states.last().state,n) ==> known(ts,n),
    decreases ts.len(),
{
    if ts.len()>0 {
        let prefix=ts.drop_last();let before=states.drop_last();
        assert(driver::labels(prefix)==driver::labels(ts).drop_last());
        from_execution(bank,before,prefix);let t=ts.last();let last=ts.len() as int-1;
        assert(driver::labels(ts)[last]==driver::label(t));
        assert(states[last]==before.last() && states[last+1]==states.last());
        assert(fs::step(library(),driver::programs(bank),states[last],states[last+1],driver::labels(ts)[last].0,driver::labels(ts)[last].1,driver::labels(ts)[last].2));
        step_origins(bank,before.last(),states.last(),t);
        assert forall|i:int,n:usize|0<=i<ts.len() && o::references(ts[i],n) implies known(ts.take(i),n) by {
            if i<prefix.len() {assert(o::references(prefix[i],n));assert(known(prefix.take(i),n));assert(prefix.take(i)==ts.take(i));}
            else {assert(i==prefix.len());assert(ts.take(i)==prefix);assert(s::registered(before.last().state,n));}
        }
        assert forall|n:usize|s::registered(states.last().state,n) implies known(ts,n) by {
            if s::registered(before.last().state,n) {
                assert(known(prefix,n));let j=choose|j:int|0<=j<prefix.len() && a::birth_spec(prefix[j])==Some(n);assert(a::birth_spec(ts[j])==Some(n));
            } else {assert(a::birth_spec(ts[ts.len() as int-1])==Some(n));}
        }
    }
}
/// Region guards already imply retained-origin closure. No extra target trace
/// or caller-provided origin assumption is needed by executable compaction.
pub proof fn from_region(report:&driver::ScriptReport,bank:Seq<Blueprint>,states:Seq<g::Configuration<u64,Index>>,keep:Seq<bool>,r:region::Region)
    requires source::witness(report,bank,states),source::mask(report.transitions@,keep,r),region::trace::admissible(states,r),
    ensures o::closed(report.transitions@,keep),
{
    library_theory();crate::observational_grammar::exact_theory(|_:Port,x:u64,y:u64|x==y,library());
    region::fresh_trace::from_source(|_:Port,x:u64,y:u64|x==y,library(),driver::programs(bank),states,driver::labels(report.transitions@),r);
    source::labels(report.transitions@,keep,r);
    source::deletion_payloads(report.transitions@,keep,states,r,|t:nat|region::index(states.last().history,r,t));
    let deleted=region::fresh_trace::target(states,driver::labels(report.transitions@),r);
    fs::from_empty_safe(|_:Port,x:u64,y:u64|x==y,library(),driver::programs(bank),deleted,driver::labels(selected(report.transitions@,keep)));
    from_execution(bank,deleted,selected(report.transitions@,keep));selected_closed(report.transitions@,keep);
}
pub open spec fn admitted(report:&driver::ScriptReport,keep:Seq<bool>)->bool {
    exists|bank:Seq<Blueprint>,states:Seq<g::Configuration<u64,Index>>,r:region::Region|
        source::witness(report,bank,states) && source::mask(report.transitions@,keep,r) && region::trace::admissible(states,r)
}
pub proof fn admission_complete(report:&driver::ScriptReport,keep:Seq<bool>)
    requires admitted(report,keep),
    ensures o::closed(report.transitions@,keep),a::history(report.transitions@,report.machine.next_id()),
{
    let (bank,states,r)=choose|bank:Seq<Blueprint>,states:Seq<g::Configuration<u64,Index>>,r:region::Region|
        source::witness(report,bank,states) && source::mask(report.transitions@,keep,r) && region::trace::admissible(states,r);
    from_region(report,bank,states,keep,r);
}

}
