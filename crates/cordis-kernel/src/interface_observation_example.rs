//! A nonterminating, nonliteral family and the necessity of outside frames.
#[cfg(verus_keep_ghost)]
use crate::{
    coeffects, interface_observation as frame, iterators as it, observation as o, quotient as q,
};
use vstd::prelude::*;

verus! {

pub struct Value {pub visible:int,pub hidden:int}
pub open spec fn equality()->spec_fn(nat,Value,Value)->bool { |_:nat,a:Value,b:Value|a.visible==b.visible }
pub open spec fn project()->spec_fn(IMap<nat,Value>)->IMap<nat,Value> { |a:IMap<nat,Value>|a }
pub open spec fn keys()->ISet<nat> { ISet::empty().insert(0nat) }
pub open spec fn family()->q::IteratorFamily<IMap<nat,Value>,bool> {
    |id:bool,a:IMap<nat,Value>| {
        let state=if a.dom().contains(0nat) {
            a.insert(0nat,Value {visible:a[0nat].visible+1,hidden:a[0nat].hidden+if id {10int}else{20int}})
        } else {a};
        q::Iteration {state,undo:|b:IMap<nat,Value>|coeffects::put(b,0nat,coeffects::get(a,0nat)),next:Some(id)}
    }
}

pub proof fn local_family()
    ensures frame::framed(keys(),project(),family(),ISet::full()),
        q::bisimulation(frame::observed(equality(),keys(),project()),family(),|_:bool,_:bool|true),
        forall|id:bool| #[trigger] it::witnessed(frame::observed(equality(),keys(),project()),family(),id),
{
    let f=family();let local=frame::observed(equality(),keys(),project());let all=|_:bool,_:bool|true;
    assert(frame::framed(keys(),project(),f,ISet::full())) by {
        assert forall|id:bool,a:IMap<nat,Value>| #![trigger f(id,a)] ISet::<bool>::full().contains(id) implies {
            let y=f(id,a);
            &&& frame::outside(keys(),project(),a,y.state)
            &&& frame::map_frame(keys(),project(),y.undo)
            &&& (y.next.is_some() ==> ISet::<bool>::full().contains(y.next.unwrap()))
        } by {
            assert forall|b:IMap<nat,Value>| #[trigger] frame::outside(keys(),project(),b,(f(id,a).undo)(b)) by {}
        }
    }
    assert(q::bisimulation(local,f,all)) by {
        assert forall|i:bool,j:bool,a:IMap<nat,Value>,b:IMap<nat,Value>| #![trigger f(i,a),f(j,b)] all(i,j) && local(a,b) implies {
            let x=f(i,a);let y=f(j,b);
            &&& local(x.state,y.state) && o::related_maps(local,x.undo,y.undo)
            &&& q::continuation(all,x.next,y.next)
        } by {
            assert(keys().contains(0nat));
            assert(o::context_equal(equality(),keys(),a,b));
            assert(a.dom().contains(0nat)==b.dom().contains(0nat));
            if a.dom().contains(0nat) {assert(a[0nat].visible==b[0nat].visible);}
        }
    }
    assert(it::witnessed_closed(local,f,ISet::full())) by {
        assert forall|id:bool| ISet::<bool>::full().contains(id) implies {
            &&& q::iterator_related(local,f,id,id)
            &&& forall|a:IMap<nat,Value>| #[trigger] local((f(id,a).undo)(f(id,a).state),a)
            &&& forall|a:IMap<nat,Value>| #[trigger] f(id,a).next.is_some() ==> ISet::<bool>::full().contains(f(id,a).next.unwrap())
        } by {assert(all(id,id));}
    }
    assert forall|id:bool| #[trigger] it::witnessed(local,f,id) by {assert(ISet::<bool>::full().contains(id));}
}

/// Distinct iterator IDs and raw values remain related at all keys. Both
/// iterators continue forever; no shared finite execution rank is used.
pub proof fn nonliteral_iterators()
    ensures {
        let global=frame::observed(equality(),ISet::full(),project());let f=family();
        let input=IMap::empty().insert(0nat,Value {visible:7,hidden:0}).insert(1nat,Value {visible:99,hidden:3});
        &&& q::iterator_related(global,f,false,true)
        &&& it::witnessed(global,f,false) && it::witnessed(global,f,true)
        &&& f(false,input).state!=f(true,input).state
        &&& f(false,input).state[0nat].visible==8 && f(true,input).state[0nat].visible==8
        &&& f(false,input).state[0nat].hidden==20 && f(true,input).state[0nat].hidden==10
        &&& f(false,input).state[1nat]==input[1nat] && f(true,input).state[1nat]==input[1nat]
        &&& f(false,input).next==Some(false) && f(true,input).next==Some(true)
    },
{
    local_family();let local=frame::observed(equality(),keys(),project());let f=family();
    assert(q::iterator_related(local,f,false,true));
    frame::iterators(equality(),keys(),project(),f,ISet::full(),false,true);
    frame::witnesses(equality(),keys(),project(),f,ISet::full(),false);
    frame::witnesses(equality(),keys(),project(),f,ISet::full(),true);
}

/// Local respect alone says nothing about a function's writes outside S.
pub proof fn frame_is_necessary()
    ensures {
        let eq=|_:nat,a:int,b:int|a==b;let p=|a:IMap<nat,int>|a;let s=ISet::empty().insert(0nat);
        let f=|a:IMap<nat,int>|a;let g=|a:IMap<nat,int>|a.insert(1nat,0int);
        &&& o::related_maps(frame::observed(eq,s,p),f,g)
        &&& frame::map_frame(s,p,f) && !frame::map_frame(s,p,g)
        &&& !o::related_maps(frame::observed(eq,ISet::full(),p),f,g)
    },
{
    let eq=|_:nat,a:int,b:int|a==b;let p=|a:IMap<nat,int>|a;let s=ISet::empty().insert(0nat);
    let f=|a:IMap<nat,int>|a;let g=|a:IMap<nat,int>|a.insert(1nat,0int);
    let empty=IMap::<nat,int>::empty();
    assert(!frame::outside(s,p,empty,g(empty))) by {assert(!s.contains(1nat));assert(g(empty).dom().contains(1nat));}
    assert(frame::observed(eq,ISet::full(),p)(empty,empty));
    assert(!frame::observed(eq,ISet::full(),p)(f(empty),g(empty))) by {assert(ISet::<nat>::full().contains(1nat));}
}

} // verus!
