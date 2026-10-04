//! Controlled partial refinement of real mixed-grammar configurations.
//!
//! Function fields are compared on legal inputs with the same control and
//! table observations. This legal-input PER explicitly restricts the tests;
//! it is not the paper's table-only function interpretation in Equation (54).
//! Real callback and restore
//! failures remain observable. No iterator-ID encoding or journal bijection is
//! used; roots/current indices and history/accumulator lengths may differ.
#[cfg(verus_keep_ghost)]
use crate::{
    calculus as c, child_history as ch, dependent_lift as dep, grammar_lift as lift,
    iterators as it, mediated as m, mixed_grammar as g, mixed_observational_runs as rows,
    observational_grammar as og, observational_lift as ol, partial_independence as p,
    preservation as inv, quotient as q, refinement as r, semantics as s, Binding, Phase, Port,
};
use vstd::prelude::*;

verus! {

/// Only registration/control/table legality is observed. Interpreter markers
/// and accumulator tokens are deliberately not compared as raw fields.
pub open spec fn legal_input<U>(eq:spec_fn(Port,U,U)->bool,actor:usize,a:s::State<U>,b:s::State<U>)->bool {
    inv::well_formed(a) && inv::well_formed(b) && s::registered(a,actor) && s::registered(b,actor) && rows::tables_related(eq,a,b)
}
pub open spec fn input_relation<U>(eq:spec_fn(Port,U,U)->bool,actor:usize)->spec_fn(s::State<U>,s::State<U>)->bool {
    |a:s::State<U>,b:s::State<U>|legal_input(eq,actor,a,b)
}
pub open spec fn family<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,actor:usize)->it::PartialFamily<s::State<U>,I> {
    |id:I,state:s::State<U>|match g::run(lib,programs(actor)(id),state,actor) {
        None=>None,Some(y)=>Some(it::PartialIteration {state:y.state,undo:|t:s::State<U>|g::undo(y.receipt,t),next:y.next}),
    }
}
pub open spec fn iterator_related<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,actor:usize,left:I,right:I)->bool {
    q::iterator_related(|a:Option<s::State<U>>,b:Option<s::State<U>>|it::optional_eq(input_relation(eq,actor),a,b),it::encode_partial(family(lib,programs,actor)),left,right)
}
pub open spec fn continuations<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,actor:usize,left:Option<I>,right:Option<I>)->bool {
    q::continuation(|i:I,j:I|iterator_related(eq,lib,programs,actor,i,j),left,right)
}
pub open spec fn accumulator<U,I>(a:g::Configuration<U,I>,actor:usize)->m::PartialMap<s::State<U>> {
    |input:s::State<U>|g::restore(a.history,a.state.accumulators[actor],input,actor)
}
pub open spec fn related<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,b:g::Configuration<U,I>)->bool {
    &&& rows::tables_related(eq,a.state,b.state)
    &&& forall|actor:usize|s::registered(a.state,actor) ==> {
        &&& iterator_related(eq,lib,programs,actor,a.roots[actor],b.roots[actor])
        &&& continuations(eq,lib,programs,actor,a.current[actor],b.current[actor])
        &&& m::partial_related(input_relation(eq,actor),accumulator(a,actor),accumulator(b,actor))
    }
}
pub open spec fn table_programs<A,X,U,B,I>(programs:g::Programs<A,X,U,B,I>)->bool {
    forall|actor:usize,id:I|match #[trigger] programs(actor)(id) {g::Node::Dependent {..}=>true,_=>false}
}
pub open spec fn table_tokens<U,I>(history:Seq<g::Entry<U,I>>,tokens:Seq<nat>)->bool {
    forall|i:int|0<=i<tokens.len() ==> tokens[i]<history.len() && match #[trigger] history[tokens[i] as int].landed.receipt {g::Receipt::Table {..}=>true,_=>false}
}
pub open spec fn live_tables<U,I>(a:g::Configuration<U,I>)->bool {
    forall|actor:usize|s::registered(a.state,actor) ==> table_tokens(a.history,#[trigger] a.state.accumulators[actor])
}

pub proof fn legal_input_per<U>(eq:spec_fn(Port,U,U)->bool,actor:usize,a:s::State<U>,b:s::State<U>,z:s::State<U>)
    requires forall|key:Port| #[trigger] m::key_equivalence(eq,key),legal_input(eq,actor,a,b),
    ensures legal_input(eq,actor,b,a),legal_input(eq,actor,a,a),legal_input(eq,actor,b,b),
        legal_input(eq,actor,b,z) ==> legal_input(eq,actor,a,z),
{
    rows::tables_reflexive(eq,a);rows::tables_reflexive(eq,b);
    assert forall|n:usize|s::registered(b,n) implies {
        &&& b.tables[n].dom()==a.tables[n].dom()
        &&& forall|key:Port|b.tables[n].dom().contains(key) ==> eq(key,b.tables[n][key],a.tables[n][key])
    } by {
        assert(s::registered(a,n));assert(a.tables[n].dom()==b.tables[n].dom());
        assert forall|key:Port|b.tables[n].dom().contains(key) implies eq(key,b.tables[n][key],a.tables[n][key]) by {
            assert(m::key_equivalence(eq,key));let local=|u:U,v:U|eq(key,u,v);assert(c::equivalence(local));assert(local(a.tables[n][key],b.tables[n][key]));
        }
    }
    if legal_input(eq,actor,b,z) {
        assert forall|n:usize|s::registered(a,n) implies {
            &&& a.tables[n].dom()==z.tables[n].dom()
            &&& forall|key:Port|a.tables[n].dom().contains(key) ==> eq(key,a.tables[n][key],z.tables[n][key])
        } by {
            assert(s::registered(b,n));assert(b.tables[n].dom()==z.tables[n].dom());
            assert forall|key:Port|a.tables[n].dom().contains(key) implies eq(key,a.tables[n][key],z.tables[n][key]) by {
                assert(m::key_equivalence(eq,key));let local=|u:U,v:U|eq(key,u,v);assert(c::equivalence(local));
                assert(local(a.tables[n][key],b.tables[n][key]));assert(local(b.tables[n][key],z.tables[n][key]));
            }
        }
    }
}

/// Equality for the actual strict interpreter on arbitrary inputs, including
/// failure. Histories need agree only at the tokens actually interpreted.
pub proof fn restore_extensional<U,I>(left:Seq<g::Entry<U,I>>,right:Seq<g::Entry<U,I>>,tokens:Seq<nat>,input:s::State<U>,actor:usize)
    requires forall|i:int|0<=i<tokens.len() ==> tokens[i]<left.len() && tokens[i]<right.len()
        && #[trigger] left[tokens[i] as int].landed.receipt==right[tokens[i] as int].landed.receipt,
    ensures g::restore(left,tokens,input,actor)==g::restore(right,tokens,input,actor),
    decreases tokens.len(),
{
    if tokens.len()>0 {
        assert(left[tokens.last() as int].landed.receipt==right[tokens.last() as int].landed.receipt);
        let receipt=left[tokens.last() as int].landed.receipt;
        if g::owner(receipt)==actor && g::undo(receipt,input).is_some() {restore_extensional(left,right,tokens.drop_last(),g::undo(receipt,input).unwrap(),actor);}
    }
}
pub proof fn restore_extension<U,I>(history:Seq<g::Entry<U,I>>,entry:g::Entry<U,I>,tokens:Seq<nat>,input:s::State<U>,actor:usize)
    requires forall|i:int|0<=i<tokens.len() ==> #[trigger] tokens[i]<history.len(),
    ensures g::restore(history.push(entry),tokens,input,actor)==g::restore(history,tokens,input,actor),
{
    assert forall|i:int|0<=i<tokens.len() implies tokens[i]<history.push(entry).len() && tokens[i]<history.len()
        && #[trigger] history.push(entry)[tokens[i] as int].landed.receipt==history[tokens[i] as int].landed.receipt by {}
    restore_extensional(history.push(entry),history,tokens,input,actor);
}
pub proof fn restore_append<U,I>(history:Seq<g::Entry<U,I>>,entry:g::Entry<U,I>,tokens:Seq<nat>,input:s::State<U>,actor:usize)
    requires g::owner(entry.landed.receipt)==actor,forall|i:int|0<=i<tokens.len() ==> #[trigger] tokens[i]<history.len(),
    ensures g::restore(history.push(entry),tokens.push(history.len()),input,actor)==match g::undo(entry.landed.receipt,input) {
        None=>None,Some(next)=>g::restore(history,tokens,next,actor),
    },
{
    assert(tokens.push(history.len()).drop_last() =~= tokens);
    if g::undo(entry.landed.receipt,input).is_some() {restore_extension(history,entry,tokens,g::undo(entry.landed.receipt,input).unwrap(),actor);}
}
pub proof fn partial_composition<S>(relation:spec_fn(S,S)->bool,f:m::PartialMap<S>,g:m::PartialMap<S>,a:m::PartialMap<S>,b:m::PartialMap<S>)
    requires m::partial_related(relation,f,g),m::partial_related(relation,a,b),
    ensures m::partial_related(relation,p::compose(f,a),p::compose(g,b)),
{
    assert forall|x:S,y:S| #![trigger p::compose(f,a)(x),p::compose(g,b)(y)] relation(x,y) implies {
        &&& p::compose(f,a)(x).is_some()==p::compose(g,b)(y).is_some()
        &&& (p::compose(f,a)(x).is_some() ==> relation(p::compose(f,a)(x).unwrap(),p::compose(g,b)(y).unwrap()))
    } by {if a(x).is_some(){assert(relation(a(x).unwrap(),b(y).unwrap()));}}
}
pub proof fn append_accumulators<U,I>(eq:spec_fn(Port,U,U)->bool,left:g::Configuration<U,I>,right:g::Configuration<U,I>,actor:usize,a:g::Entry<U,I>,b:g::Entry<U,I>)
    requires g::owner(a.landed.receipt)==actor,g::owner(b.landed.receipt)==actor,
        forall|i:int|0<=i<left.state.accumulators[actor].len() ==> #[trigger] left.state.accumulators[actor][i]<left.history.len(),
        forall|i:int|0<=i<right.state.accumulators[actor].len() ==> #[trigger] right.state.accumulators[actor][i]<right.history.len(),
        m::partial_related(input_relation(eq,actor),accumulator(left,actor),accumulator(right,actor)),
        m::partial_related(input_relation(eq,actor),|s:s::State<U>|g::undo(a.landed.receipt,s),|s:s::State<U>|g::undo(b.landed.receipt,s)),
    ensures m::partial_related(input_relation(eq,actor),
        |s:s::State<U>|g::restore(left.history.push(a),left.state.accumulators[actor].push(left.history.len()),s,actor),
        |s:s::State<U>|g::restore(right.history.push(b),right.state.accumulators[actor].push(right.history.len()),s,actor)),
{
    let x=|s:s::State<U>|g::undo(a.landed.receipt,s);let y=|s:s::State<U>|g::undo(b.landed.receipt,s);
    partial_composition(input_relation(eq,actor),accumulator(left,actor),accumulator(right,actor),x,y);
    assert((|s:s::State<U>|g::restore(left.history.push(a),left.state.accumulators[actor].push(left.history.len()),s,actor)) =~= p::compose(accumulator(left,actor),x)) by {
        assert forall|s:s::State<U>| #[trigger] g::restore(left.history.push(a),left.state.accumulators[actor].push(left.history.len()),s,actor)==p::compose(accumulator(left,actor),x)(s) by {restore_append(left.history,a,left.state.accumulators[actor],s,actor);}
    }
    assert((|s:s::State<U>|g::restore(right.history.push(b),right.state.accumulators[actor].push(right.history.len()),s,actor)) =~= p::compose(accumulator(right,actor),y)) by {
        assert forall|s:s::State<U>| #[trigger] g::restore(right.history.push(b),right.state.accumulators[actor].push(right.history.len()),s,actor)==p::compose(accumulator(right,actor),y)(s) by {restore_append(right.history,b,right.state.accumulators[actor],s,actor);}
    }
}

pub proof fn restore_frame<U,I>(history:Seq<g::Entry<U,I>>,tokens:Seq<nat>,input:s::State<U>,actor:usize)
    requires inv::well_formed(input),table_tokens(history,tokens),g::restore(history,tokens,input,actor).is_some(),
    ensures inv::well_formed(g::restore(history,tokens,input,actor).unwrap()),
        g::restore(history,tokens,input,actor).unwrap().control==input.control,
        g::restore(history,tokens,input,actor).unwrap().effects==input.effects,
        g::restore(history,tokens,input,actor).unwrap().iterators==input.iterators,
        g::restore(history,tokens,input,actor).unwrap().accumulators==input.accumulators,
    decreases tokens.len(),
{
    if tokens.len()>0 {
        let receipt=history[tokens.last() as int].landed.receipt;
        if let g::Receipt::Table {receipt}=receipt {lift::undo_preservation(receipt,input);}
        restore_frame(history,tokens.drop_last(),g::undo(receipt,input).unwrap(),actor);
    }
}
pub proof fn live_unreferenced<U,I>(a:g::Configuration<U,I>,child:usize)
    requires live_tables(a),
    ensures ch::remove_unreferenced(g::kind(a.history),a.state,child),
{
    assert forall|actor:usize,token:nat|s::registered(a.state,actor) && a.state.accumulators[actor].contains(token)
        implies g::kind(a.history)(token)!=Some(child) by {
        let i=choose|i:int|0<=i<a.state.accumulators[actor].len() && a.state.accumulators[actor][i]==token;
        assert(table_tokens(a.history,a.state.accumulators[actor]));assert(token<a.history.len());
    }
}

pub proof fn call_related<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,actor:usize,i:I,j:I,a:s::State<U>,b:s::State<U>)
    requires legal_input(eq,actor,a,b),iterator_related(eq,lib,programs,actor,i,j),g::run(lib,programs(actor)(i),a,actor).is_some(),
    ensures {
        let x=g::run(lib,programs(actor)(i),a,actor).unwrap();let out=g::run(lib,programs(actor)(j),b,actor);
        &&& out.is_some() && legal_input(eq,actor,x.state,out.unwrap().state)
        &&& m::partial_related(input_relation(eq,actor),|s:s::State<U>|g::undo(x.receipt,s),|s:s::State<U>|g::undo(out.unwrap().receipt,s))
        &&& continuations(eq,lib,programs,actor,x.next,out.unwrap().next)
    },
{
    let f=family(lib,programs,actor);let relation=input_relation(eq,actor);let base=|a:Option<s::State<U>>,b:Option<s::State<U>>|it::optional_eq(relation,a,b);let encoded=it::encode_partial(f);
    q::iterator_unfolding(base,encoded,i,j);assert(base(Some(a),Some(b)));
    assert(base(encoded(i,Some(a)).state,encoded(j,Some(b)).state));assert(f(j,b).is_some());
    let x=f(i,a).unwrap();let y=f(j,b).unwrap();
    assert(m::partial_related(relation,x.undo,y.undo)) by {
        assert forall|s:s::State<U>,t:s::State<U>| #![trigger (x.undo)(s),(y.undo)(t)] relation(s,t) implies {
            &&& (x.undo)(s).is_some()==(y.undo)(t).is_some()
            &&& ((x.undo)(s).is_some() ==> relation((x.undo)(s).unwrap(),(y.undo)(t).unwrap()))
        } by {assert(base(Some(s),Some(t)));assert(base((encoded(i,Some(a)).undo)(Some(s)),(encoded(j,Some(b)).undo)(Some(t))));}
    }
}


pub proof fn guard_observations<U>(eq:spec_fn(Port,U,U)->bool,a:s::State<U>,b:s::State<U>,actor:usize,view:ISet<Binding>)
    requires rows::tables_related(eq,a,b),
    ensures s::target(a,actor,view)==s::target(b,actor,view),s::coherent(a,actor)==s::coherent(b,actor),
{
    assert forall|key:Port,n:usize|s::publishes(a,key,n)==s::publishes(b,key,n) by {
        if s::registered(a,n) {assert(a.tables[n].dom()==b.tables[n].dom());}
    }
}
pub proof fn empty_accumulators<U,I>(eq:spec_fn(Port,U,U)->bool,actor:usize,left:Seq<g::Entry<U,I>>,right:Seq<g::Entry<U,I>>)
    ensures m::partial_related(input_relation(eq,actor),
        |s:s::State<U>|g::restore(left,Seq::empty(),s,actor),|s:s::State<U>|g::restore(right,Seq::empty(),s,actor)),
{ }

/// Fields remain meaningful independently of control edits: both actual
/// restore programs are functions of their argument, not of the current table.
pub proof fn framed_related<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,b:g::Configuration<U,I>,x:g::Configuration<U,I>,y:g::Configuration<U,I>)
    requires related(eq,lib,programs,a,b),rows::tables_related(eq,x.state,y.state),
        x.state.control.fibers.dom()==a.state.control.fibers.dom(),
        x.roots==a.roots,y.roots==b.roots,x.current==a.current,y.current==b.current,
        x.history==a.history,y.history==b.history,
        x.state.accumulators==a.state.accumulators,y.state.accumulators==b.state.accumulators,
    ensures related(eq,lib,programs,x,y),
{
    assert forall|n:usize|s::registered(x.state,n) implies {
        &&& iterator_related(eq,lib,programs,n,x.roots[n],y.roots[n])
        &&& continuations(eq,lib,programs,n,x.current[n],y.current[n])
        &&& m::partial_related(input_relation(eq,n),accumulator(x,n),accumulator(y,n))
    } by {assert(s::registered(a.state,n));}
}
pub proof fn edit_related<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,b:g::Configuration<U,I>,actor:usize,
    phase:Phase,view:ISet<Binding>,left:Option<I>,right:Option<I>,lt:Seq<nat>,rt:Seq<nat>)
    requires related(eq,lib,programs,a,b),s::registered(a.state,actor),
        continuations(eq,lib,programs,actor,left,right),
        m::partial_related(input_relation(eq,actor),|s:s::State<U>|g::restore(a.history,lt,s,actor),|s:s::State<U>|g::restore(b.history,rt,s,actor)),
    ensures related(eq,lib,programs,g::edit(a,actor,phase,view,left,lt),g::edit(b,actor,phase,view,right,rt)),
{
    let x=g::edit(a,actor,phase,view,left,lt);let y=g::edit(b,actor,phase,view,right,rt);
    assert forall|n:usize|s::registered(x.state,n) implies {
        &&& x.state.tables[n].dom()==y.state.tables[n].dom()
        &&& forall|key:Port|x.state.tables[n].dom().contains(key) ==> eq(key,x.state.tables[n][key],y.state.tables[n][key])
    } by {assert(s::registered(a.state,n));}
    assert forall|n:usize|s::registered(x.state,n) implies {
        &&& iterator_related(eq,lib,programs,n,x.roots[n],y.roots[n])
        &&& continuations(eq,lib,programs,n,x.current[n],y.current[n])
        &&& m::partial_related(input_relation(eq,n),accumulator(x,n),accumulator(y,n))
    } by {assert(s::registered(a.state,n));if n!=actor {}}
}

pub proof fn table_run_frame<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,actor:usize,id:I,a:s::State<U>)
    requires table_programs(programs),inv::well_formed(a),g::run(lib,programs(actor)(id),a,actor).is_some(),
    ensures {
        let y=g::run(lib,programs(actor)(id),a,actor).unwrap();
        &&& inv::well_formed(y.state) && y.state.control==a.control && y.state.effects==a.effects
        &&& y.state.iterators==a.iterators && y.state.accumulators==a.accumulators
        &&& y.spawn.is_none() && g::owner(y.receipt)==actor
        &&& match y.receipt {g::Receipt::Table {..}=>true,_=>false}
    },
{
    match programs(actor)(id) {g::Node::Dependent {node}=>{lift::run_preservation(dep::stage(lib,node),a,actor);},_=>{}}
}

/// Append each side's own authentic entry, with independently sized histories.
/// No relation between raw token numbers or accumulator lengths is needed.
#[verifier::spinoff_prover]
pub proof fn land_related<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,b:g::Configuration<U,I>,actor:usize,phase:Phase)
    requires related(eq,lib,programs,a,b),table_programs(programs),g::tokens_valid(a),g::tokens_valid(b),
        inv::well_formed(a.state),inv::well_formed(b.state),s::registered(a.state,actor),a.current[actor].is_some(),
        g::run(lib,programs(actor)(a.current[actor].unwrap()),a.state,actor).is_some(),
    ensures related(eq,lib,programs,g::land(lib,programs,a,actor,phase),g::land(lib,programs,b,actor,phase)),
        g::run(lib,programs(actor)(b.current[actor].unwrap()),b.state,actor).is_some(),
        b.current[actor].is_some(),
        g::entry(lib,programs,a,actor).landed.next.is_some()==g::entry(lib,programs,b,actor).landed.next.is_some(),
{
    assert(continuations(eq,lib,programs,actor,a.current[actor],b.current[actor]));
    let i=a.current[actor].unwrap();let j=b.current[actor].unwrap();
    call_related(eq,lib,programs,actor,i,j,a.state,b.state);
    table_run_frame(lib,programs,actor,i,a.state);table_run_frame(lib,programs,actor,j,b.state);
    let x=g::entry(lib,programs,a,actor);let y=g::entry(lib,programs,b,actor);
    append_accumulators(eq,a,b,actor,x,y);
    let u=g::Configuration {state:x.landed.state,history:a.history.push(x),..a};
    let v=g::Configuration {state:y.landed.state,history:b.history.push(y),..b};
    assert(related(eq,lib,programs,u,v)) by {
        assert forall|n:usize|s::registered(u.state,n) implies {
            &&& iterator_related(eq,lib,programs,n,u.roots[n],v.roots[n])
            &&& continuations(eq,lib,programs,n,u.current[n],v.current[n])
            &&& m::partial_related(input_relation(eq,n),accumulator(u,n),accumulator(v,n))
        } by {
            assert(s::registered(a.state,n));assert(s::registered(b.state,n));
            assert(accumulator(u,n) =~= accumulator(a,n)) by {
                assert forall|s:s::State<U>| #[trigger] accumulator(u,n)(s)==accumulator(a,n)(s) by {restore_extension(a.history,x,a.state.accumulators[n],s,n);}
            }
            assert(accumulator(v,n) =~= accumulator(b,n)) by {
                assert forall|s:s::State<U>| #[trigger] accumulator(v,n)(s)==accumulator(b,n)(s) by {restore_extension(b.history,y,b.state.accumulators[n],s,n);}
            }
        }
    }
    edit_related(eq,lib,programs,u,v,actor,phase,a.state.control.fibers[actor].committed,
        if phase==Phase::Loading {x.landed.next} else {None},if phase==Phase::Loading {y.landed.next} else {None},
        a.state.accumulators[actor].push(a.history.len()),b.state.accumulators[actor].push(b.history.len()));
}

pub open spec fn successor<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,z:g::Configuration<U,I>,b:g::Configuration<U,I>,actor:usize,rule:r::Rule,new_root:I)->g::Configuration<U,I> {
    match rule {
        r::Rule::Insert=>g::Configuration {state:s::State {control:z.state.control,tables:b.state.tables.insert(actor,IMap::empty()),effects:b.state.effects.insert(actor,0),
            iterators:b.state.iterators.insert(actor,None),accumulators:b.state.accumulators.insert(actor,Seq::empty())},
            roots:b.roots.insert(actor,new_root),current:b.current.insert(actor,None),history:b.history},
        r::Rule::Retire=>g::Configuration {state:s::with_control(b.state,z.state.control),..b},
        r::Rule::Remove=>g::Configuration {state:s::erase(b.state,actor),roots:b.roots.remove(actor),current:b.current.remove(actor),history:b.history},
        r::Rule::Begin=>g::edit(b,actor,Phase::Loading,z.state.control.fibers[actor].committed,Some(b.roots[actor]),Seq::empty()),
        r::Rule::Iter=>g::land(lib,programs,b,actor,Phase::Loading),
        r::Rule::Finish=>g::land(lib,programs,b,actor,Phase::Active),
        r::Rule::Divert=>if g::landing(a,z,rule) {g::land(lib,programs,b,actor,Phase::Unloading)} else {g::edit(b,actor,Phase::Unloading,b.state.control.fibers[actor].committed,None,b.state.accumulators[actor])},
        r::Rule::Leave=>g::edit(b,actor,Phase::Unloading,b.state.control.fibers[actor].committed,None,b.state.accumulators[actor]),
        r::Rule::Unload=>g::unload(b,actor),
        _=>b,
    }
}

#[verifier::spinoff_prover]
pub proof fn insert_simulates<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,z:g::Configuration<U,I>,b:g::Configuration<U,I>,actor:usize,new_root:I)
    requires related(eq,lib,programs,a,b),g::step(lib,programs,a,z,actor,r::Rule::Insert),
        iterator_related(eq,lib,programs,actor,z.roots[actor],new_root),g::component_member(lib,programs,z.state,actor,new_root),
    ensures g::step(lib,programs,b,successor(lib,programs,a,z,b,actor,r::Rule::Insert,new_root),actor,r::Rule::Insert),
        related(eq,lib,programs,z,successor(lib,programs,a,z,b,actor,r::Rule::Insert,new_root)),
{
    let y=successor(lib,programs,a,z,b,actor,r::Rule::Insert,new_root);
    assert(inv::insert_map(b.state,y.state,actor));
    assert(g::component_member(lib,programs,y.state,actor,new_root));
    assert(rows::tables_related(eq,z.state,y.state)) by {
        assert forall|n:usize|s::registered(z.state,n) implies {
            &&& z.state.tables[n].dom()==y.state.tables[n].dom()
            &&& forall|key:Port|z.state.tables[n].dom().contains(key) ==> eq(key,z.state.tables[n][key],y.state.tables[n][key])
        } by {if n!=actor {assert(s::registered(a.state,n));}}
    }
    empty_accumulators(eq,actor,a.history,b.history);
    assert forall|n:usize|s::registered(z.state,n) implies {
        &&& iterator_related(eq,lib,programs,n,z.roots[n],y.roots[n])
        &&& continuations(eq,lib,programs,n,z.current[n],y.current[n])
        &&& m::partial_related(input_relation(eq,n),accumulator(z,n),accumulator(y,n))
    } by {if n!=actor {assert(s::registered(a.state,n));}}
}

#[verifier::spinoff_prover]
pub proof fn unloading_related<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,b:g::Configuration<U,I>,actor:usize)
    requires related(eq,lib,programs,a,b),inv::well_formed(a.state),inv::well_formed(b.state),s::registered(a.state,actor),
        live_tables(a),live_tables(b),g::restore(a.history,a.state.accumulators[actor],a.state,actor).is_some(),
    ensures g::restore(b.history,b.state.accumulators[actor],b.state,actor).is_some(),
        related(eq,lib,programs,g::unload(a,actor),g::unload(b,actor)),
{
    assert(m::partial_related(input_relation(eq,actor),accumulator(a,actor),accumulator(b,actor)));
    assert(legal_input(eq,actor,a.state,b.state));assert(accumulator(a,actor)(a.state).is_some());
    assert(accumulator(b,actor)(b.state).is_some());
    let x=g::restore(a.history,a.state.accumulators[actor],a.state,actor).unwrap();let y=g::restore(b.history,b.state.accumulators[actor],b.state,actor).unwrap();
    restore_frame(a.history,a.state.accumulators[actor],a.state,actor);restore_frame(b.history,b.state.accumulators[actor],b.state,actor);
    let u=g::Configuration {state:x,..a};let v=g::Configuration {state:y,..b};
    framed_related(eq,lib,programs,a,b,u,v);empty_accumulators(eq,actor,a.history,b.history);
    edit_related(eq,lib,programs,u,v,actor,Phase::Inactive,ISet::empty(),None,None,Seq::empty(),Seq::empty());
}

/// The target is built from its own programs and history. In particular its
/// strict forward / restore success and its syntax-membership invariant are
/// conclusions, not an assumed legal destination execution.
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn step_simulates<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,z:g::Configuration<U,I>,b:g::Configuration<U,I>,actor:usize,rule:r::Rule,new_root:I)
    requires og::primitive_theory(eq,lib),table_programs(programs),g::well_formed(lib,programs,a),g::well_formed(lib,programs,b),
        related(eq,lib,programs,a,b),live_tables(a),live_tables(b),g::step(lib,programs,a,z,actor,rule),
        rule==r::Rule::Insert ==> iterator_related(eq,lib,programs,actor,z.roots[actor],new_root) && g::component_member(lib,programs,z.state,actor,new_root),
    ensures g::step(lib,programs,b,successor(lib,programs,a,z,b,actor,rule,new_root),actor,rule),
        related(eq,lib,programs,z,successor(lib,programs,a,z,b,actor,rule,new_root)),
        g::well_formed(lib,programs,successor(lib,programs,a,z,b,actor,rule,new_root)),
{
    let y=successor(lib,programs,a,z,b,actor,rule,new_root);
    guard_observations(eq,a.state,b.state,actor,if rule==r::Rule::Begin {z.state.control.fibers[actor].committed} else {ISet::empty()});
    ol::frame(eq,lib,programs,a,z,actor,rule);
    match rule {
        r::Rule::Insert=>{insert_simulates(eq,lib,programs,a,z,b,actor,new_root);},
        r::Rule::Retire=>{
            assert(s::child_retire(b.state,y.state,actor));
            assert(rows::tables_related(eq,z.state,y.state)) by {
                assert forall|n:usize|s::registered(z.state,n) implies {
                    &&& z.state.tables[n].dom()==y.state.tables[n].dom()
                    &&& forall|key:Port|z.state.tables[n].dom().contains(key) ==> eq(key,z.state.tables[n][key],y.state.tables[n][key])
                } by {assert(s::registered(a.state,n));}
            }
            assert(r::step(a.state.control,z.state.control,actor,r::Rule::Retire));
            assert(z.state.control.fibers.dom() =~= a.state.control.fibers.dom()) by {
                assert forall|n:usize|z.state.control.fibers.dom().contains(n)==a.state.control.fibers.dom().contains(n) by {
                    if n!=actor {assert(r::registered(a.state.control,n)==r::registered(z.state.control,n));}
                }
            }
            framed_related(eq,lib,programs,a,b,z,y);
        },
        r::Rule::Remove=>{
            live_unreferenced(b,actor);assert(b.state.tables[actor].is_empty());
            assert(rows::tables_related(eq,z.state,y.state)) by {
                assert forall|n:usize|s::registered(z.state,n) implies {
                    &&& z.state.tables[n].dom()==y.state.tables[n].dom()
                    &&& forall|key:Port|z.state.tables[n].dom().contains(key) ==> eq(key,z.state.tables[n][key],y.state.tables[n][key])
                } by {assert(n!=actor);assert(s::registered(a.state,n));}
            }
            assert forall|n:usize|s::registered(z.state,n) implies {
                &&& iterator_related(eq,lib,programs,n,z.roots[n],y.roots[n])
                &&& continuations(eq,lib,programs,n,z.current[n],y.current[n])
                &&& m::partial_related(input_relation(eq,n),accumulator(z,n),accumulator(y,n))
            } by {assert(n!=actor);assert(s::registered(a.state,n));}
        },
        r::Rule::Begin=>{
            empty_accumulators(eq,actor,a.history,b.history);
            edit_related(eq,lib,programs,a,b,actor,Phase::Loading,z.state.control.fibers[actor].committed,Some(a.roots[actor]),Some(b.roots[actor]),Seq::empty(),Seq::empty());
        },
        r::Rule::Iter | r::Rule::Finish | r::Rule::Divert=>{
            if g::landing(a,z,rule) {
                let phase=if rule==r::Rule::Iter {Phase::Loading} else if rule==r::Rule::Finish {Phase::Active} else {Phase::Unloading};
                land_related(eq,lib,programs,a,b,actor,phase);
            } else {
                assert(z==g::edit(a,actor,Phase::Unloading,a.state.control.fibers[actor].committed,None,a.state.accumulators[actor]));
                edit_related(eq,lib,programs,a,b,actor,Phase::Unloading,a.state.control.fibers[actor].committed,None,None,a.state.accumulators[actor],b.state.accumulators[actor]);
            }
        },
        r::Rule::Leave=>{edit_related(eq,lib,programs,a,b,actor,Phase::Unloading,a.state.control.fibers[actor].committed,None,None,a.state.accumulators[actor],b.state.accumulators[actor]);},
        r::Rule::Unload=>{unloading_related(eq,lib,programs,a,b,actor);},
        _=>{},
    }
    assert(g::step(lib,programs,b,y,actor,rule));
    ol::configuration_preservation(eq,lib,programs,b,y,actor,rule);
}


/// Table-only live receipts are an inductive execution property. The live
/// condition constrains exactly the tokens consulted by Remove.
#[verifier::spinoff_prover]
pub proof fn live_tables_preserved<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,z:g::Configuration<U,I>,actor:usize,rule:r::Rule)
    requires og::primitive_theory(eq,lib),table_programs(programs),g::well_formed(lib,programs,a),live_tables(a),g::step(lib,programs,a,z,actor,rule),
    ensures live_tables(z),
{
    ol::frame(eq,lib,programs,a,z,actor,rule);
    if g::landing(a,z,rule) {table_run_frame(lib,programs,actor,a.current[actor].unwrap(),a.state);}
    if rule==r::Rule::Unload {restore_frame(a.history,a.state.accumulators[actor],a.state,actor);}
    assert forall|n:usize|s::registered(z.state,n) implies table_tokens(z.history,#[trigger] z.state.accumulators[n]) by {
        assert forall|i:int|0<=i<z.state.accumulators[n].len() implies z.state.accumulators[n][i]<z.history.len()
            && match #[trigger] z.history[z.state.accumulators[n][i] as int].landed.receipt {g::Receipt::Table {..}=>true,_=>false} by {
            assert(s::registered(a.state,n));assert(table_tokens(a.history,a.state.accumulators[n]));
            if n==actor && g::landing(a,z,rule) && i==a.state.accumulators[n].len() {
                assert(z.state.accumulators[n][i]==a.history.len());assert(z.history[a.history.len() as int]==g::entry(lib,programs,a,actor));
            } else {
                assert(i<a.state.accumulators[n].len());assert(z.state.accumulators[n][i]==a.state.accumulators[n][i]);
                let token=a.state.accumulators[n][i];assert(token<a.history.len());assert(z.history[token as int]==a.history[token as int]);
            }
        }
    }
}

/// Reusable one-step package: endpoint membership/typing and the live Table
/// condition are derived by actual preservation after constructing the step.
pub proof fn controlled_partial_refinement<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,z:g::Configuration<U,I>,b:g::Configuration<U,I>,actor:usize,rule:r::Rule,new_root:I)
    requires og::primitive_theory(eq,lib),table_programs(programs),g::well_formed(lib,programs,a),g::well_formed(lib,programs,b),
        related(eq,lib,programs,a,b),live_tables(a),live_tables(b),g::step(lib,programs,a,z,actor,rule),
        rule==r::Rule::Insert ==> iterator_related(eq,lib,programs,actor,z.roots[actor],new_root) && g::component_member(lib,programs,z.state,actor,new_root),
    ensures {
        let y=successor(lib,programs,a,z,b,actor,rule,new_root);
        &&& g::step(lib,programs,b,y,actor,rule) && related(eq,lib,programs,z,y)
        &&& g::well_formed(lib,programs,y) && g::well_formed(lib,programs,z) && live_tables(y) && live_tables(z)
    },
{
    step_simulates(eq,lib,programs,a,z,b,actor,rule,new_root);ol::configuration_preservation(eq,lib,programs,a,z,actor,rule);
    live_tables_preserved(eq,lib,programs,a,z,actor,rule);
    live_tables_preserved(eq,lib,programs,b,successor(lib,programs,a,z,b,actor,rule,new_root),actor,rule);
}

/// Empty registry inputs are outside the PER, even though pure table
/// observations alone would equate them with some registered empty states.
pub proof fn unregistered_outside_domain<U>(eq:spec_fn(Port,U,U)->bool,actor:usize,a:s::State<U>)
    requires !s::registered(a,actor),
    ensures !legal_input(eq,actor,a,a),
{ }


pub open spec fn replay<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,states:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,roots:Seq<I>,initial:g::Configuration<U,I>)->Seq<g::Configuration<U,I>>
    decreases labels.len(),
{
    if labels.len()==0 {seq![initial]}
    else {
        let previous=replay(lib,programs,states.drop_last(),labels.drop_last(),roots.drop_last(),initial);
        previous.push(successor(lib,programs,states[states.len()-2],states.last(),previous.last(),labels.last().0,labels.last().1,roots.last()))
    }
}

/// Construct the complete target trace. Only external Insert payloads require
/// a fresh root correspondence and an independent least-syntax membership
/// check. All target forward domains, undo domains and intermediate invariants
/// follow from the initial field relation and actual source execution.
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn execution_simulates<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,states:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,roots:Seq<I>,initial:g::Configuration<U,I>)
    requires og::primitive_theory(eq,lib),table_programs(programs),g::execution(lib,programs,states,labels),roots.len()==labels.len(),
        g::well_formed(lib,programs,states.first()),g::well_formed(lib,programs,initial),live_tables(states.first()),live_tables(initial),
        related(eq,lib,programs,states.first(),initial),
        forall|i:int|0<=i<labels.len() && labels[i].1==r::Rule::Insert ==> {
            &&& iterator_related(eq,lib,programs,labels[i].0,states[i+1].roots[labels[i].0],roots[i])
            &&& g::component_member(lib,programs,states[i+1].state,labels[i].0,roots[i])
        },
    ensures {
        let target=replay(lib,programs,states,labels,roots,initial);
        &&& target.len()==states.len() && target.first()==initial && g::execution(lib,programs,target,labels)
        &&& forall|i:int|0<=i<states.len() ==> related(eq,lib,programs,states[i],target[i])
            && g::well_formed(lib,programs,states[i]) && g::well_formed(lib,programs,target[i]) && live_tables(states[i]) && live_tables(target[i])
    },
    decreases labels.len(),
{
    if labels.len()>0 {
        let shorter=states.drop_last();let steps=labels.drop_last();let code=roots.drop_last();
        assert(g::execution(lib,programs,shorter,steps)) by {
            assert forall|i:int|0<=i<steps.len() implies g::step(lib,programs,shorter[i],shorter[i+1],steps[i].0,steps[i].1) by {}
        }
        execution_simulates(eq,lib,programs,shorter,steps,code,initial);
        let previous=replay(lib,programs,shorter,steps,code,initial);let last=(labels.len()-1) as int;
        assert(states[last]==shorter.last());assert(previous.last()==previous[last]);
        controlled_partial_refinement(eq,lib,programs,states[last],states[last+1],previous.last(),labels[last].0,labels[last].1,roots[last]);
        let target=replay(lib,programs,states,labels,roots,initial);
        assert forall|i:int|0<=i<labels.len() implies g::step(lib,programs,target[i],target[i+1],labels[i].0,labels[i].1) by {
            if i<last {assert(g::step(lib,programs,previous[i],previous[i+1],steps[i].0,steps[i].1));}
        }
        assert forall|i:int|0<=i<states.len() implies related(eq,lib,programs,states[i],target[i])
            && g::well_formed(lib,programs,states[i]) && g::well_formed(lib,programs,target[i]) && live_tables(states[i]) && live_tables(target[i]) by {
            if i<states.len()-1 {assert(shorter[i]==states[i]);assert(previous[i]==target[i]);}
        }
    } else {assert(states.len()==1);assert(states.first()==states[0]);}
}
}
