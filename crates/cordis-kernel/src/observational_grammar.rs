//! Observational witnesses for the existing strict dependent grammar.
//!
//! The syntax, least membership and partial interpreter are unchanged. Returned
//! inverses must actually succeed and recover the observation of their input;
//! they need not recover the identical raw representative. Failure and typed
//! value, argument and outcome fibers remain part of the primitive contract.
#[cfg(verus_keep_ghost)]
use crate::{
    calculus, contexts as c, dependent_grammar as d, iterators as it, mediated as m,
    observation as o, quotient as q,
};
use vstd::prelude::*;

verus! {

pub open spec fn operation_respects<U,B>(eq:spec_fn(U,U)->bool,op:m::Operation<U,B>)->bool {
    forall|a:U,b:U| #![trigger op(a),op(b)] eq(a,b) ==> {
        &&& op(a).is_some()==op(b).is_some()
        &&& (op(a).is_some() ==> {
            let x=op(a).unwrap();let y=op(b).unwrap();
            &&& eq(x.value,y.value) && x.outcome==y.outcome
            &&& m::partial_related(eq,x.undo,y.undo)
        })
    }
}
pub open spec fn operation_witness<U,B>(eq:spec_fn(U,U)->bool,op:m::Operation<U,B>)->bool {
    forall|a:U| #[trigger] op(a).is_some() ==> {
        let y=op(a).unwrap();
        &&& (y.undo)(y.value).is_some()
        &&& eq((y.undo)(y.value).unwrap(),a)
    }
}
pub open spec fn operation_admissible<U,B>(eq:spec_fn(U,U)->bool,op:m::Operation<U,B>)->bool {
    operation_respects(eq,op) && operation_witness(eq,op)
}
pub open spec fn primitive_theory<K,A,X,U,B>(eq:spec_fn(K,U,U)->bool,lib:d::Library<K,A,X,U,B>)->bool {
    &&& (forall|k:K| #[trigger] m::key_equivalence(eq,k))
    &&& (forall|a:A,x:X| #![trigger d::operation_typed(lib,a,x)]
        lib.allowed.contains(a) && (lib.arguments)(a,x) ==> {
            &&& d::operation_typed(lib,a,x)
            &&& operation_admissible(|u:U,v:U|eq((lib.key)(a),u,v),(lib.apply)(a,x))
        })
}

pub proof fn exact_operation<U,B>(eq:spec_fn(U,U)->bool,op:m::Operation<U,B>)
    requires calculus::equivalence(eq),m::operation_admissible(eq,op),
    ensures operation_admissible(eq,op),
{ }
pub proof fn exact_theory<K,A,X,U,B>(eq:spec_fn(K,U,U)->bool,lib:d::Library<K,A,X,U,B>)
    requires d::primitive_theory(eq,lib),
    ensures primitive_theory(eq,lib),
{
    reveal(primitive_theory);reveal(d::primitive_theory);
    assert forall|k:K| #[trigger] m::key_equivalence(eq,k) by {}
    assert forall|a:A,x:X| lib.allowed.contains(a) && (lib.arguments)(a,x) implies
        #[trigger] d::operation_typed(lib,a,x)
        && operation_admissible(|u:U,v:U|eq((lib.key)(a),u,v),(lib.apply)(a,x)) by {
        assert(m::key_equivalence(eq,(lib.key)(a)));
        assert(d::operation_typed(lib,a,x));
        assert(m::operation_admissible(|u:U,v:U|eq((lib.key)(a),u,v),(lib.apply)(a,x)));
        exact_operation(|u:U,v:U|eq((lib.key)(a),u,v),(lib.apply)(a,x));
    }

}
pub proof fn context_equivalence<K,A,X,U,B>(eq:spec_fn(K,U,U)->bool,lib:d::Library<K,A,X,U,B>,observed:ISet<K>)
    requires primitive_theory(eq,lib),
    ensures calculus::equivalence(|a:Map<K,U>,b:Map<K,U>|d::context_equal(eq,observed,a,b)),
{
    assert forall|k:K| observed.contains(k) implies calculus::equivalence(|a:U,b:U|eq(k,a,b)) by {assert(m::key_equivalence(eq,k));}
    o::context_equivalence(eq,observed);
    let ctx=|a:Map<K,U>,b:Map<K,U>|d::context_equal(eq,observed,a,b);
    let ambient=|a:IMap<K,U>,b:IMap<K,U>|o::context_equal(eq,observed,a,b);
    assert(calculus::equivalence(ambient));
    assert forall|a:Map<K,U>| #[trigger] ctx(a,a) by {assert(ambient(c::embed(a),c::embed(a)));}
    assert forall|a:Map<K,U>,b:Map<K,U>|ctx(a,b) implies #[trigger] ctx(b,a) by {
        assert(ambient(c::embed(a),c::embed(b)));
        assert(ambient(c::embed(b),c::embed(a)));
    }
    assert forall|a:Map<K,U>,b:Map<K,U>,z:Map<K,U>| #[trigger] ctx(a,b) && #[trigger] ctx(b,z) implies ctx(a,z) by {
        assert(ambient(c::embed(a),c::embed(b)));assert(ambient(c::embed(b),c::embed(z)));
        assert(ambient(c::embed(a),c::embed(z)));
    }
}

pub proof fn stage_admissible<K,A,X,U,B,I>(id:I,eq:spec_fn(K,U,U)->bool,lib:d::Library<K,A,X,U,B>,node:d::Node<K,A,X,U,B,I>,declared:ISet<K>,provisions:ISet<K>,observed:ISet<K>)
    requires primitive_theory(eq,lib),d::permitted(lib,declared,provisions,node),d::covers(lib,observed,node),
    ensures it::partial_respects(|s:Map<K,U>,t:Map<K,U>|d::context_equal(eq,observed,s,t),|_:I,s:Map<K,U>|d::run(lib,node,s),id),
        forall|s:Map<K,U>| #[trigger] d::run(lib,node,s).is_some() ==> {
            let y=d::run(lib,node,s).unwrap();
            &&& (y.undo)(y.state).is_some()
            &&& d::context_equal(eq,observed,(y.undo)(y.state).unwrap(),s)
        },
        forall|s:Map<K,U>| c::typed(lib.values,s) && #[trigger] d::run(lib,node,s).is_some() ==> c::typed(lib.values,d::run(lib,node,s).unwrap().state),
{
    let ctx=|s:Map<K,U>,t:Map<K,U>|d::context_equal(eq,observed,s,t);
    assert forall|s:Map<K,U>,t:Map<K,U>| #![trigger d::run(lib,node,s),d::run(lib,node,t)] ctx(s,t) implies {
        &&& d::run(lib,node,s).is_some()==d::run(lib,node,t).is_some()
        &&& (d::run(lib,node,s).is_some() ==> {
            let x=d::run(lib,node,s).unwrap();let y=d::run(lib,node,t).unwrap();
            &&& ctx(x.state,y.state)
            &&& m::partial_related(ctx,x.undo,y.undo)
            &&& x.next==y.next
        })
    } by {
        match node {
            d::Node::Unit=>{},
            d::Node::Operation {operation:a,argument:x,select}=>{
                let k=(lib.key)(a);let op=(lib.apply)(a,x);
                assert(d::operation_typed(lib,a,x));assert(operation_admissible(|u:U,v:U|eq(k,u,v),op));
                if s.dom().contains(k) {
                    assert(eq(k,s[k],t[k]));assert(op(s[k]).is_some()==op(t[k]).is_some());
                    if op(s[k]).is_some() {
                        let p=op(s[k]).unwrap();let q=op(t[k]).unwrap();
                        assert(p.outcome==q.outcome);
                        d::update_related(eq,observed,k,s,t,p.value,q.value);d::inverse_respects(eq,observed,k,p.undo,q.undo);
                    }
                }
            },
            d::Node::Provision {key,value,..}=>{
                assert(m::key_equivalence(eq,key));let local=|u:U,v:U|eq(key,u,v);assert(calculus::equivalence(local));assert(local(value,value));assert(eq(key,value,value));
                if !s.dom().contains(key) {d::update_related(eq,observed,key,s,t,value,value);}
                let undo=|p:Map<K,U>|c::revoke(p,key);
                assert(m::partial_related(ctx,undo,undo)) by {
                    assert forall|a:Map<K,U>,b:Map<K,U>| #![trigger undo(a),undo(b)] ctx(a,b) implies {
                        &&& undo(a).is_some()==undo(b).is_some()
                        &&& (undo(a).is_some() ==> ctx(undo(a).unwrap(),undo(b).unwrap()))
                    } by {c::finite_embedding(a,a,key,value);c::finite_embedding(b,b,key,value);m::remove_related(eq,observed,key,c::embed(a),c::embed(b));}
                }
            },
        }
    }
    context_equivalence(eq,lib,observed);
    assert forall|s:Map<K,U>| #[trigger] d::run(lib,node,s).is_some() implies {
        let y=d::run(lib,node,s).unwrap();
        &&& (y.undo)(y.state).is_some()
        &&& d::context_equal(eq,observed,(y.undo)(y.state).unwrap(),s)
    } by {
        assert(ctx(s,s));
        match node {
            d::Node::Unit=>{},
            d::Node::Operation {operation:a,argument:x,..}=>{
                let k=(lib.key)(a);let op=(lib.apply)(a,x);let y=op(s[k]).unwrap();
                assert(d::operation_typed(lib,a,x));
                assert(operation_admissible(|u:U,v:U|eq(k,u,v),op));
                assert((y.undo)(y.value).is_some());let restored=(y.undo)(y.value).unwrap();
                assert(eq(k,restored,s[k]));
                d::update_related(eq,observed,k,s,s,restored,s[k]);
                assert(s.insert(k,s[k]) =~= s);
                assert(s.insert(k,y.value).insert(k,restored) =~= s.insert(k,restored));
            },
            d::Node::Provision {key,value,..}=>{assert(s.insert(key,value).remove(key) =~= s);},
        }
    }
    assert forall|s:Map<K,U>| c::typed(lib.values,s) && #[trigger] d::run(lib,node,s).is_some() implies c::typed(lib.values,d::run(lib,node,s).unwrap().state) by {
        match node {
            d::Node::Operation {operation:a,argument:x,..}=>{assert(d::operation_typed(lib,a,x));},
            _=>{},
        }
    }
}

pub proof fn selected_continuation<K,A,X,U,B,I>(eq:spec_fn(K,U,U)->bool,lib:d::Library<K,A,X,U,B>,node:d::Node<K,A,X,U,B,I>,declared:ISet<K>,provisions:ISet<K>,names:ISet<I>,s:Map<K,U>)
    requires primitive_theory(eq,lib),d::permitted(lib,declared,provisions,node),d::continuations(lib,node,names),d::run(lib,node,s).is_some(),d::run(lib,node,s).unwrap().next.is_some(),
    ensures names.contains(d::run(lib,node,s).unwrap().next.unwrap()),
{
    match node {
        d::Node::Operation {operation:a,argument:x,select}=>{
            let k=(lib.key)(a);let op=(lib.apply)(a,x);
            assert(d::operation_typed(lib,a,x));assert((lib.outcomes)(a,op(s[k]).unwrap().outcome));
        },
        _=>{},
    }
}
/// The least grammar implies the least iterator type even for uncountable
/// continuation indices and outcome branching without a common finite rank.
pub proof fn grammar_inductive<K,A,X,U,B,I>(eq:spec_fn(K,U,U)->bool,lib:d::Library<K,A,X,U,B>,program:d::Program<K,A,X,U,B,I>,declared:ISet<K>,provisions:ISet<K>,id:I)
    requires primitive_theory(eq,lib),d::member(lib,program,declared,provisions,id),
    ensures it::inductive_member(it::encode_partial(d::family(lib,program)),id),
{
    let encoded=it::encode_partial(d::family(lib,program));let good=it::inductive_members(encoded);
    assert(d::closed(lib,program,declared,provisions,good)) by {
        assert forall|i:I| d::permitted(lib,declared,provisions,program(i)) && d::continuations(lib,program(i),good) implies good.contains(i) by {
            assert forall|s:Option<Map<K,U>>| #[trigger] encoded(i,s).next.is_some() implies good.contains(encoded(i,s).next.unwrap()) by {
                assert(s.is_some());assert(d::run(lib,program(i),s.unwrap()).is_some());
                selected_continuation(eq,lib,program(i),declared,provisions,good,s.unwrap());
            }
            it::inductive_constructor(encoded,i);
        }
    }
    assert(good.contains(id));
}
/// Observational Lemma 39 for the same dependent finite context grammar. The observed keys need
/// only cover reachable stages, independently of the declaration set. Actual
/// raw outcomes select recursively witnessed continuations; failure is kept.
pub proof fn grammar_paper_witnessed<K,A,X,U,B,I>(eq:spec_fn(K,U,U)->bool,lib:d::Library<K,A,X,U,B>,program:d::Program<K,A,X,U,B,I>,declared:ISet<K>,provisions:ISet<K>,observed:ISet<K>,id:I)
    requires primitive_theory(eq,lib),provisions.subset_of(declared),d::member(lib,program,declared,provisions,id),d::covered(lib,program,observed,id),
    ensures it::paper_partial_witnessed(|s:Map<K,U>,t:Map<K,U>|d::context_equal(eq,observed,s,t),d::family(lib,program),id),
        forall|s:Map<K,U>| #[trigger] d::run(lib,program(id),s).is_some() ==> {
            let y=d::run(lib,program(id),s).unwrap();
            &&& (y.undo)(y.state).is_some()
            &&& d::context_equal(eq,observed,(y.undo)(y.state).unwrap(),s)
        },
        forall|s:Map<K,U>| c::typed(lib.values,s) && #[trigger] d::run(lib,program(id),s).is_some() ==> c::typed(lib.values,d::run(lib,program(id),s).unwrap().state),
{
    let names=ISet::new(|i:I|d::member(lib,program,declared,provisions,i) && d::covered(lib,program,observed,i));
    let ctx=|s:Map<K,U>,t:Map<K,U>|d::context_equal(eq,observed,s,t);let f=d::family(lib,program);
    assert forall|k:K| observed.contains(k) implies calculus::equivalence(|u:U,v:U|eq(k,u,v)) by {assert(m::key_equivalence(eq,k));}
    o::context_equivalence(eq,observed);
    assert forall|i:I| names.contains(i) implies it::partial_respects(ctx,f,i) by {
        d::member_unfolding(lib,program,declared,provisions,i);d::covered_unfolding(lib,program,observed,i);
        stage_admissible(i,eq,lib,program(i),declared,provisions,observed);
        let one=|_:I,s:Map<K,U>|d::run(lib,program(i),s);
        assert forall|a:Map<K,U>,b:Map<K,U>| #![trigger f(i,a),f(i,b)] ctx(a,b) implies {
            &&& f(i,a).is_some()==f(i,b).is_some()
            &&& (f(i,a).is_some() ==> ctx(f(i,a).unwrap().state,f(i,b).unwrap().state)
                && m::partial_related(ctx,f(i,a).unwrap().undo,f(i,b).unwrap().undo)
                && f(i,a).unwrap().next==f(i,b).unwrap().next)
        } by {assert(one(i,a)==f(i,a));assert(one(i,b)==f(i,b));}
    }
    assert forall|i:I,s:Map<K,U>| #![trigger f(i,s)] names.contains(i) && f(i,s).is_some() implies {
        let yielded=f(i,s).unwrap();
        &&& (yielded.undo)(yielded.state).is_some()
        &&& ctx((yielded.undo)(yielded.state).unwrap(),s)
        &&& (yielded.next.is_some() ==> names.contains(yielded.next.unwrap()))
    } by {
        d::member_unfolding(lib,program,declared,provisions,i);d::covered_unfolding(lib,program,observed,i);
        stage_admissible(i,eq,lib,program(i),declared,provisions,observed);
        let ambient=|a:IMap<K,U>,b:IMap<K,U>|o::context_equal(eq,observed,a,b);assert(calculus::equivalence(ambient));assert(ambient(c::embed(s),c::embed(s)));assert(ctx(s,s));
        if f(i,s).unwrap().next.is_some() {
            selected_continuation(eq,lib,program(i),declared,provisions,d::members(lib,program,declared,provisions),s);
            selected_continuation(eq,lib,program(i),declared,provisions,ISet::new(|j:I|d::covered(lib,program,observed,j)),s);
        }
    }
    it::partial_family_coinduction(ctx,f,names,id);
    grammar_inductive(eq,lib,program,declared,provisions,id);
    d::member_unfolding(lib,program,declared,provisions,id);d::covered_unfolding(lib,program,observed,id);
    stage_admissible(id,eq,lib,program(id),declared,provisions,observed);
}


/// Every successful application of a captured inverse preserves value fibers.
pub proof fn stage_inverse_typed<K,A,X,U,B,I>(eq:spec_fn(K,U,U)->bool,lib:d::Library<K,A,X,U,B>,node:d::Node<K,A,X,U,B,I>,declared:ISet<K>,provisions:ISet<K>,input:Map<K,U>,current:Map<K,U>)
    requires primitive_theory(eq,lib),d::permitted(lib,declared,provisions,node),d::run(lib,node,input).is_some(),
        c::typed(lib.values,current),(d::run(lib,node,input).unwrap().undo)(current).is_some(),
    ensures c::typed(lib.values,(d::run(lib,node,input).unwrap().undo)(current).unwrap()),
{
    match node {
        d::Node::Operation {operation:a,argument:x,..}=>{
            assert(d::operation_typed(lib,a,x));
            let k=(lib.key)(a);let op=(lib.apply)(a,x);let y=op(input[k]).unwrap();
            assert((y.undo)(current[k]).is_some());assert((lib.values)(k,(y.undo)(current[k]).unwrap()));
        },_=>{},
    }
}
pub proof fn grammar_self_related<K,A,X,U,B,I>(eq:spec_fn(K,U,U)->bool,lib:d::Library<K,A,X,U,B>,program:d::Program<K,A,X,U,B,I>,declared:ISet<K>,provisions:ISet<K>,observed:ISet<K>,id:I)
    requires primitive_theory(eq,lib),provisions.subset_of(declared),d::member(lib,program,declared,provisions,id),d::covered(lib,program,observed,id),
    ensures q::iterator_related(|a:Option<Map<K,U>>,b:Option<Map<K,U>>|it::optional_eq(|s:Map<K,U>,t:Map<K,U>|d::context_equal(eq,observed,s,t),a,b),
        it::encode_partial(d::family(lib,program)),id,id),
{
    grammar_paper_witnessed(eq,lib,program,declared,provisions,observed,id);
    let ctx=|s:Map<K,U>,t:Map<K,U>|d::context_equal(eq,observed,s,t);let f=d::family(lib,program);
    let names=choose|names:ISet<I>|names.contains(id)&&it::partial_witness_closed(ctx,f,names);
    assert(it::partial_witness_closed(ctx,f,names));
}
/// Definedness, inverse domains and the actual selected continuation respect
/// the same quotient, with continuations related by greatest bisimulation.
pub proof fn grammar_observational_step<K,A,X,U,B,I>(eq:spec_fn(K,U,U)->bool,lib:d::Library<K,A,X,U,B>,program:d::Program<K,A,X,U,B,I>,declared:ISet<K>,provisions:ISet<K>,observed:ISet<K>,id:I,a:Map<K,U>,b:Map<K,U>)
    requires primitive_theory(eq,lib),provisions.subset_of(declared),d::member(lib,program,declared,provisions,id),d::covered(lib,program,observed,id),
        d::context_equal(eq,observed,a,b),
    ensures {
        let x=d::run(lib,program(id),a);let y=d::run(lib,program(id),b);
        let ctx=|s:Map<K,U>,t:Map<K,U>|d::context_equal(eq,observed,s,t);
        let base=|s:Option<Map<K,U>>,t:Option<Map<K,U>>|it::optional_eq(ctx,s,t);
        &&& x.is_some()==y.is_some()
        &&& (x.is_some() ==> {
            &&& ctx(x.unwrap().state,y.unwrap().state)
            &&& m::partial_related(ctx,x.unwrap().undo,y.unwrap().undo)
            &&& q::continuation(|i:I,j:I|q::iterator_related(base,it::encode_partial(d::family(lib,program)),i,j),x.unwrap().next,y.unwrap().next)
        })
    },
{
    grammar_self_related(eq,lib,program,declared,provisions,observed,id);
    d::member_unfolding(lib,program,declared,provisions,id);d::covered_unfolding(lib,program,observed,id);
    stage_admissible(id,eq,lib,program(id),declared,provisions,observed);
    let ctx=|s:Map<K,U>,t:Map<K,U>|d::context_equal(eq,observed,s,t);
    let base=|s:Option<Map<K,U>>,t:Option<Map<K,U>>|it::optional_eq(ctx,s,t);let encoded=it::encode_partial(d::family(lib,program));
    q::iterator_unfolding(base,encoded,id,id);assert(base(Some(a),Some(b)));
    assert(q::continuation(|i:I,j:I|q::iterator_related(base,encoded,i,j),encoded(id,Some(a)).next,encoded(id,Some(b)).next));
    let one=|_:I,s:Map<K,U>|d::run(lib,program(id),s);
    assert(it::partial_respects(ctx,one,id));
    assert(one(id,a)==d::run(lib,program(id),a));assert(one(id,b)==d::run(lib,program(id),b));
    assert(one(id,a).is_some()==one(id,b).is_some());
    if one(id,a).is_some() {
        assert(ctx(one(id,a).unwrap().state,one(id,b).unwrap().state));
        assert(m::partial_related(ctx,one(id,a).unwrap().undo,one(id,b).unwrap().undo));
    }
}

/// The inverse canonicalizes an unobserved counter; both forward and inverse
/// remain undefined at values whose visible boolean is false.
pub open spec fn canonical_operation()->m::Operation<(bool,int),()> {
    |v:(bool,int)|if !v.0 {None} else {Some(m::ValueYield {
        value:(true,v.1+1),outcome:(),undo:|w:(bool,int)|if w.0 {Some((true,0))}else{None},
    })}
}
pub open spec fn canonical_library()->d::Library<(),(),(),(bool,int),()> {
    d::Library {values:|_:(),_v:(bool,int)|true,arguments:|_:(),_:()|true,outcomes:|_:(),_:()|true,
        key:|_:()|(),allowed:ISet::full(),apply:|_:(),_:()|canonical_operation()}
}
pub open spec fn visible()->spec_fn((),(bool,int),(bool,int))->bool {|_:(),a:(bool,int),b:(bool,int)|a.0==b.0}
pub open spec fn canonical_program()->d::Program<(),(),(),(bool,int),(),bool> {
    |finished:bool|if finished {d::Node::Unit} else {
        d::Node::Operation {operation:(),argument:(),select:|_:()|Some(true)}
    }
}
pub proof fn canonical_theory()
    ensures primitive_theory(visible(),canonical_library()),!d::primitive_theory(visible(),canonical_library()),
        canonical_library().allowed.contains(()),
{
    let op=canonical_operation();let eq=|a:(bool,int),b:(bool,int)|a.0==b.0;
    assert(operation_admissible(eq,op));assert(d::operation_typed(canonical_library(),(),()));
    assert(!m::operation_admissible(eq,op)) by {
        assert(op((true,7)).is_some());
        assert((op((true,7)).unwrap().undo)(op((true,7)).unwrap().value)==Some((true,0)));
    }
}
/// The existing interpreter and least grammar exhibit genuine quotient
/// recovery, strict failure, and greatest observational iterator membership.
pub proof fn canonical_grammar_witness()
    ensures {
        let lib=canonical_library();let program=canonical_program();let keys=ISet::full();
        let input=Map::empty().insert((),(true,7));let out=d::run(lib,program(false),input).unwrap();
        &&& d::member(lib,program,keys,ISet::empty(),false)
        &&& d::run(lib,program(false),input).is_some() && out.state[()]==(true,8) && out.next==Some(true)
        &&& (out.undo)(out.state)==Some(Map::empty().insert((),(true,0)))
        &&& (out.undo)(out.state)!=Some(input)
        &&& d::context_equal(visible(),keys,(out.undo)(out.state).unwrap(),input)
        &&& d::run(lib,program(false),Map::empty()).is_none()
        &&& d::run(lib,program(false),Map::empty().insert((),(false,7))).is_none()
        &&& (out.undo)(Map::empty().insert((),(false,8))).is_none()
        &&& it::paper_partial_witnessed(|a:Map<(),(bool,int)>,b:Map<(),(bool,int)>|d::context_equal(visible(),keys,a,b),d::family(lib,program),false)
    },
{
    canonical_theory();let lib=canonical_library();let program=canonical_program();let keys=ISet::full();
    d::constructor_member(lib,program,keys,ISet::empty(),true);
    d::constructor_member(lib,program,keys,ISet::empty(),false);
    assert(d::covered(lib,program,keys,false)) by {
        let names=ISet::<bool>::full();
        assert forall|i:bool|names.contains(i) implies d::covers(lib,keys,program(i))&&d::continuations(lib,program(i),names) by {}
        assert(names.contains(false));
    }
    grammar_paper_witnessed(visible(),lib,program,keys,ISet::empty(),keys,false);
    let input=Map::empty().insert((),(true,7));let out=d::run(lib,program(false),input).unwrap();
    assert(out.state.insert((),(true,0)) =~= Map::empty().insert((),(true,0)));
    assert(input[()]==(true,7));
}

} // verus!
