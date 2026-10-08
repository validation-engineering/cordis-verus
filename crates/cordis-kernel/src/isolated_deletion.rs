//! Constructive deletion infrastructure for an isolated activation episode.
//!
//! Surviving journals use compressed history indices. Raw partial operations
//! and their captured inverses are transported only when the removed component
//! is outside their actual declarations/provider references. The registered owner
//! remains present, Inactive and empty, while external retirement is retained.
#[cfg(verus_keep_ghost)]
use crate::{
    child_history as ch, dependent_grammar as d, dependent_lift as dep, grammar_lift as lift,
    mixed_grammar as g, mixed_syntax as syntax, mixed_transposition as t,
    observational_grammar as og, observational_lift as ol, preservation as inv, projection as p,
    recovery_examples as ex, refinement as r, semantics as s, Binding, Phase, Port,
};
use vstd::prelude::*;

verus! {

/// Number of retained entries strictly before an original history index.
pub open spec fn index<U,I>(history:Seq<g::Entry<U,I>>,removed:usize,token:nat)->nat
    decreases token,
{
    if token==0 {0} else {index(history,removed,(token-1) as nat)
        + if g::owner(history[token as int-1].landed.receipt)==removed {0nat} else {1nat}}
}
pub open spec fn count<U,I>(history:Seq<g::Entry<U,I>>,removed:usize)->nat {
    index(history,removed,history.len())
}
pub proof fn index_prefix<U,I>(left:Seq<g::Entry<U,I>>,right:Seq<g::Entry<U,I>>,removed:usize,token:nat)
    requires token<=left.len(),token<=right.len(),forall|i:int| 0<=i<token ==> left[i]==right[i],
    ensures index(left,removed,token)==index(right,removed,token),
    decreases token,
{
    if token>0 {index_prefix(left,right,removed,(token-1) as nat);}
}
pub proof fn index_monotone<U,I>(history:Seq<g::Entry<U,I>>,removed:usize,low:nat,high:nat)
    requires low<=high<=history.len(),
    ensures index(history,removed,low)<=index(history,removed,high),
        low<high && g::owner(history[low as int].landed.receipt)!=removed
            ==> index(history,removed,low)<index(history,removed,high),
    decreases high-low,
{
    if low<high {index_monotone(history,removed,low,(high-1) as nat);}
}

pub open spec fn rename_tokens(tokens:Seq<nat>,rho:spec_fn(nat)->nat)->Seq<nat> {
    tokens.map(|_i:int,t:nat|rho(t))
}
pub open spec fn suspend<U>(a:s::State<U>,removed:usize,rho:spec_fn(nat)->nat)->s::State<U> {
    let f=a.control.fibers[removed];
    s::State {control:r::State {fibers:a.control.fibers.insert(removed,r::Fiber {
        parent:f.parent,retired:f.retired,phase:Phase::Inactive,dependencies:f.dependencies,
        provisions:f.provisions,committed:ISet::empty()})},tables:a.tables.insert(removed,IMap::empty()),
        effects:a.effects,iterators:a.iterators.insert(removed,None),
        accumulators:IMap::new(|n:usize|a.accumulators.dom().contains(n),
            |n:usize|if n==removed {Seq::empty()} else {rename_tokens(a.accumulators[n],rho)})}
}
pub open spec fn renaming<U,I>(history:Seq<g::Entry<U,I>>,removed:usize)->spec_fn(nat)->nat {
    |token:nat|index(history,removed,token)
}
pub open spec fn isolated<U>(a:s::State<U>,removed:usize)->bool {
    &&& s::registered(a,removed) && a.control.fibers[removed].dependencies.is_empty()
    &&& forall|n:usize| s::registered(a,n) && n!=removed ==> dep::declarations(a,n).disjoint(a.control.fibers[removed].provisions)
}
pub open spec fn receipt_avoids<U>(receipt:g::Receipt<U>,removed:usize)->bool {
    g::owner(receipt)!=removed && match receipt {
        g::Receipt::Table {receipt}=>match receipt.inverse {lift::Inverse::Operation {provider,..}=>provider!=removed,_=>true},
        g::Receipt::Child {child,..}=>child!=removed,
    }
}
pub open spec fn receipt_local<U>(receipt:g::Receipt<U>,removed:usize)->bool {
    match receipt {
        g::Receipt::Table {receipt}=>receipt.actor==removed && match receipt.inverse {
            lift::Inverse::Operation {provider,..}=>provider==removed,_=>true},
        g::Receipt::Child {..}=>false,
    }
}

pub proof fn suspend_update<U>(a:s::State<U>,removed:usize,rho:spec_fn(nat)->nat,provider:usize,key:Port,value:Option<U>)
    ensures provider!=removed ==> suspend(p::update_slot(a,provider,key,value),removed,rho)
        ==p::update_slot(suspend(a,removed,rho),provider,key,value),
        provider==removed ==> suspend(p::update_slot(a,provider,key,value),removed,rho)==suspend(a,removed,rho),
{
    if provider!=removed {
        assert(suspend(p::update_slot(a,provider,key,value),removed,rho).tables
            =~= p::update_slot(suspend(a,removed,rho),provider,key,value).tables);
    } else {assert(suspend(p::update_slot(a,provider,key,value),removed,rho).tables =~= suspend(a,removed,rho).tables);}
}
pub proof fn suspend_edit<U>(a:s::State<U>,removed:usize,rho:spec_fn(nat)->nat,actor:usize,phase:Phase,
    committed:ISet<Binding>,iterator:Option<nat>,tokens:Seq<nat>)
    requires a.accumulators.dom().contains(removed),
    ensures actor!=removed ==> suspend(s::edit(a,actor,phase,committed,iterator,tokens),removed,rho)
        ==s::edit(suspend(a,removed,rho),actor,phase,committed,iterator,rename_tokens(tokens,rho)),
        actor==removed ==> suspend(s::edit(a,actor,phase,committed,iterator,tokens),removed,rho)==suspend(a,removed,rho),
{
    let left=suspend(s::edit(a,actor,phase,committed,iterator,tokens),removed,rho);
    if actor!=removed {
        let right=s::edit(suspend(a,removed,rho),actor,phase,committed,iterator,rename_tokens(tokens,rho));
        assert(left.control.fibers =~= right.control.fibers);assert(left.iterators =~= right.iterators);
        assert(left.accumulators =~= right.accumulators);
    } else {
        let right=suspend(a,removed,rho);assert(left.control.fibers =~= right.control.fibers);
        assert(left.iterators =~= right.iterators);assert(left.accumulators =~= right.accumulators);
    }
}

/// Declaration separation determines the actual committed provider before the
/// raw callback is applied. No totalization or off-domain callback is used.
pub proof fn run_transport<A,X,U,B,I>(lib:g::Library<A,X,U,B>,node:g::Node<A,X,U,B,I>,a:s::State<U>,actor:usize,
    removed:usize,rho:spec_fn(nat)->nat)
    requires inv::well_formed(a),isolated(a,removed),actor!=removed,g::run(lib,node,a,actor).is_some(),
        syntax::permitted(lib,dep::declarations(a,actor),a.control.fibers[actor].provisions,node),
    ensures {
        let old=g::run(lib,node,a,actor).unwrap();let new=g::run(lib,node,suspend(a,removed,rho),actor).unwrap();
        &&& g::run(lib,node,suspend(a,removed,rho),actor).is_some()
        &&& new.receipt==old.receipt && new.next==old.next && new.spawn==old.spawn
        &&& new.state==suspend(old.state,removed,rho) && receipt_avoids(old.receipt,removed)
    },
{
    let z=suspend(a,removed,rho);
    match node {
        g::Node::Dependent {node}=>{match node {
            d::Node::Operation {operation,argument,..}=>{
                let key=(lib.key)(operation);lift::resolution_sound(a,actor,key);
                let provider=lift::resolve(a,actor,key).unwrap();
                assert(dep::declarations(a,actor).contains(key));assert(provider!=removed);
                assert(lift::resolve(a,actor,key)==lift::resolve(z,actor,key));
                let value=(lib.apply)(operation,argument)(a.tables[provider][key]).unwrap().value;
                suspend_update(a,removed,rho,provider,key,Some(value));
            },
            d::Node::Provision {key,value,..}=>{suspend_update(a,removed,rho,actor,key,Some(value));},
            _=>{},
        }},
        g::Node::Child {child,dependencies,provisions,..}=>{
            assert(!s::registered(a,child));assert(child!=removed);
            let created=g::create(z,actor,child,dependencies,provisions);
            assert(r::frame(z.control,created.control,child));
            assert(r::step(z.control,created.control,child,r::Rule::Insert));
            let old=g::create(a,actor,child,dependencies,provisions);
            assert(created.control.fibers =~= suspend(old,removed,rho).control.fibers);
            assert(created.tables =~= suspend(old,removed,rho).tables);
            assert(created.effects =~= suspend(old,removed,rho).effects);
            assert(created.iterators =~= suspend(old,removed,rho).iterators);
            assert(rename_tokens(Seq::<nat>::empty(),rho) =~= Seq::<nat>::empty());
            assert(created.accumulators =~= suspend(old,removed,rho).accumulators);
        },
    }
}

pub proof fn own_run_stutters<A,X,U,B,I>(lib:g::Library<A,X,U,B>,node:d::Node<Port,A,X,U,B,I>,a:s::State<U>,removed:usize,rho:spec_fn(nat)->nat)
    requires inv::well_formed(a),isolated(a,removed),dep::run(lib,node,a,removed).is_some(),
    ensures suspend(dep::run(lib,node,a,removed).unwrap().state,removed,rho)==suspend(a,removed,rho),
        receipt_local(g::Receipt::Table {receipt:dep::run(lib,node,a,removed).unwrap().receipt},removed),
{
    match node {
        d::Node::Operation {operation,argument,..}=>{
            let key=(lib.key)(operation);lift::resolution_sound(a,removed,key);
            let provider=lift::resolve(a,removed,key).unwrap();assert(provider==removed);
            suspend_update(a,removed,rho,provider,key,Some((lib.apply)(operation,argument)(a.tables[provider][key]).unwrap().value));
        },
        d::Node::Provision {key,value,..}=>{suspend_update(a,removed,rho,removed,key,Some(value));},
        _=>{},
    }
}

/// Captured child names and committed providers are retained literally.
/// Consequently successful partial inverse application transports unchanged.
pub proof fn undo_transport<U>(receipt:g::Receipt<U>,a:s::State<U>,removed:usize,rho:spec_fn(nat)->nat)
    requires receipt_avoids(receipt,removed),g::undo(receipt,a).is_some(),
    ensures g::undo(receipt,suspend(a,removed,rho)).is_some(),
        g::undo(receipt,suspend(a,removed,rho)).unwrap()==suspend(g::undo(receipt,a).unwrap(),removed,rho),
{
    match receipt {
        g::Receipt::Table {receipt}=>{match receipt.inverse {
            lift::Inverse::Operation {provider,key,undo}=>{
                assert(lift::resolve(a,receipt.actor,key)==lift::resolve(suspend(a,removed,rho),receipt.actor,key));
                suspend_update(a,removed,rho,provider,key,Some(undo(a.tables[provider][key]).unwrap()));
            },
            lift::Inverse::Provision {key}=>{suspend_update(a,removed,rho,receipt.actor,key,None);},
            _=>{},
        }},
        g::Receipt::Child {child,..}=>{
            assert(g::undo(receipt,suspend(a,removed,rho)).unwrap().control.fibers
                =~= suspend(g::undo(receipt,a).unwrap(),removed,rho).control.fibers);
        },
    }
}
pub proof fn own_undo_stutters<U>(receipt:g::Receipt<U>,a:s::State<U>,removed:usize,rho:spec_fn(nat)->nat)
    requires receipt_local(receipt,removed),g::undo(receipt,a).is_some(),
    ensures suspend(g::undo(receipt,a).unwrap(),removed,rho)==suspend(a,removed,rho),
{
    match receipt {
        g::Receipt::Table {receipt}=>{match receipt.inverse {
            lift::Inverse::Operation {provider,key,undo}=>{suspend_update(a,removed,rho,provider,key,Some(undo(a.tables[provider][key]).unwrap()));},
            lift::Inverse::Provision {key}=>{suspend_update(a,removed,rho,removed,key,None);},
            _=>{},
        }},
        _=>{},
    }
}

/// Retained entries have authentic target inputs. The relation compares their
/// actual receipts; it never invents a new target entry with an old input.
pub open spec fn histories<U,I>(source:Seq<g::Entry<U,I>>,target:Seq<g::Entry<U,I>>,removed:usize)->bool {
    &&& target.len()==count(source,removed)
    &&& forall|i:int| 0<=i<source.len() && g::owner(source[i].landed.receipt)!=removed ==> {
        let j=index(source,removed,i as nat);
        &&& j<target.len()
        &&& target[j as int].landed.receipt==source[i].landed.receipt
        &&& target[j as int].iterator==source[i].iterator
        &&& target[j as int].landed.next==source[i].landed.next
        &&& target[j as int].landed.spawn==source[i].landed.spawn
    }
}
pub open spec fn local_history<U,I>(history:Seq<g::Entry<U,I>>,removed:usize)->bool {
    forall|i:int| 0<=i<history.len() ==> if g::owner(history[i].landed.receipt)==removed {
        receipt_local(history[i].landed.receipt,removed)
    } else {receipt_avoids(history[i].landed.receipt,removed)}
}
pub open spec fn related<U,I>(source:g::Configuration<U,I>,target:g::Configuration<U,I>,removed:usize)->bool {
    target.state==suspend(source.state,removed,renaming(source.history,removed))
        && target.roots==source.roots && target.current==source.current.insert(removed,None)
        && histories(source.history,target.history,removed)
}

pub proof fn histories_push<U,I>(source:Seq<g::Entry<U,I>>,target:Seq<g::Entry<U,I>>,removed:usize,old:g::Entry<U,I>,new:g::Entry<U,I>)
    requires histories(source,target,removed),g::owner(old.landed.receipt)!=removed,
        old.iterator==new.iterator,old.landed.receipt==new.landed.receipt,
        old.landed.next==new.landed.next,old.landed.spawn==new.landed.spawn,
    ensures histories(source.push(old),target.push(new),removed),
        forall|t:nat| t<=source.len() ==> index(source.push(old),removed,t)==index(source,removed,t),
{
    assert forall|t:nat| t<=source.len() implies index(source.push(old),removed,t)==index(source,removed,t) by {
        index_prefix(source.push(old),source,removed,t);
    }
    assert forall|i:int| 0<=i<source.push(old).len() && g::owner(source.push(old)[i].landed.receipt)!=removed implies {
        let j=index(source.push(old),removed,i as nat);
        &&& j<target.push(new).len()
        &&& target.push(new)[j as int].landed.receipt==source.push(old)[i].landed.receipt
        &&& target.push(new)[j as int].iterator==source.push(old)[i].iterator
        &&& target.push(new)[j as int].landed.next==source.push(old)[i].landed.next
        &&& target.push(new)[j as int].landed.spawn==source.push(old)[i].landed.spawn
    } by {
        if i<source.len() {assert(index(source,removed,i as nat)<target.len());}
        else {assert(i==source.len());assert(index(source.push(old),removed,i as nat)==target.len());}
    }
}
pub proof fn histories_skip<U,I>(source:Seq<g::Entry<U,I>>,target:Seq<g::Entry<U,I>>,removed:usize,entry:g::Entry<U,I>)
    requires histories(source,target,removed),g::owner(entry.landed.receipt)==removed,
    ensures histories(source.push(entry),target,removed),
        forall|t:nat| t<=source.len() ==> index(source.push(entry),removed,t)==index(source,removed,t),
{
    assert forall|t:nat| t<=source.len() implies index(source.push(entry),removed,t)==index(source,removed,t) by {
        index_prefix(source.push(entry),source,removed,t);
    }
    assert forall|i:int| 0<=i<source.push(entry).len() && g::owner(source.push(entry)[i].landed.receipt)!=removed implies {
        let j=index(source.push(entry),removed,i as nat);
        &&& j<target.len()
        &&& target[j as int].landed.receipt==source.push(entry)[i].landed.receipt
        &&& target[j as int].iterator==source.push(entry)[i].iterator
        &&& target[j as int].landed.next==source.push(entry)[i].landed.next
        &&& target[j as int].landed.spawn==source.push(entry)[i].landed.spawn
    } by {assert(i<source.len());}
}

pub proof fn restore_transport<U,I>(source:Seq<g::Entry<U,I>>,target:Seq<g::Entry<U,I>>,tokens:Seq<nat>,a:s::State<U>,actor:usize,removed:usize)
    requires histories(source,target,removed),local_history(source,removed),actor!=removed,
        g::restore(source,tokens,a,actor).is_some(),
    ensures g::restore(target,rename_tokens(tokens,renaming(source,removed)),suspend(a,removed,renaming(source,removed)),actor).is_some(),
        g::restore(target,rename_tokens(tokens,renaming(source,removed)),suspend(a,removed,renaming(source,removed)),actor).unwrap()
            ==suspend(g::restore(source,tokens,a,actor).unwrap(),removed,renaming(source,removed)),
    decreases tokens.len(),
{
    if tokens.len()>0 {
        let token=tokens.last();let receipt=source[token as int].landed.receipt;
        let rho=renaming(source,removed);let mapped=rename_tokens(tokens,rho);
        assert(g::owner(receipt)==actor);assert(receipt_avoids(receipt,removed));
        assert(mapped.last()==rho(token));assert(target[rho(token) as int].landed.receipt==receipt);
        undo_transport(receipt,a,removed,rho);
        let next=g::undo(receipt,a).unwrap();restore_transport(source,target,tokens.drop_last(),next,actor,removed);
        assert(mapped.drop_last() =~= rename_tokens(tokens.drop_last(),rho));
    }
}
pub proof fn own_restore_stutters<U,I>(history:Seq<g::Entry<U,I>>,tokens:Seq<nat>,a:s::State<U>,removed:usize,rho:spec_fn(nat)->nat)
    requires local_history(history,removed),g::restore(history,tokens,a,removed).is_some(),
    ensures suspend(g::restore(history,tokens,a,removed).unwrap(),removed,rho)==suspend(a,removed,rho),
    decreases tokens.len(),
{
    if tokens.len()>0 {
        let receipt=history[tokens.last() as int].landed.receipt;
        own_undo_stutters(receipt,a,removed,rho);
        own_restore_stutters(history,tokens.drop_last(),g::undo(receipt,a).unwrap(),removed,rho);
    }
}

pub proof fn suspend_target<U>(a:s::State<U>,removed:usize,rho:spec_fn(nat)->nat,actor:usize,view:ISet<Binding>)
    requires inv::well_formed(a),isolated(a,removed),s::registered(a,actor),actor!=removed,
    ensures s::target(a,actor,view)==s::target(suspend(a,removed,rho),actor,view),
        s::coherent(a,actor)==s::coherent(suspend(a,removed,rho),actor),
{
    let z=suspend(a,removed,rho);
    assert forall|key:Port,n:usize| a.control.fibers[actor].dependencies.contains(key)
        implies s::publishes(a,key,n)==s::publishes(z,key,n) by {
        if n==removed {assert(!a.control.fibers[removed].provisions.contains(key));}
    }
}

pub proof fn suspend_append<U,I>(a:s::State<U>,history:Seq<g::Entry<U,I>>,entry:g::Entry<U,I>,removed:usize)
    requires forall|n:usize,i:int| a.accumulators.dom().contains(n) && n!=removed && 0<=i<a.accumulators[n].len()
        ==> a.accumulators[n][i]<=history.len(),
    ensures suspend(a,removed,renaming(history.push(entry),removed))==suspend(a,removed,renaming(history,removed)),
{
    let left=suspend(a,removed,renaming(history.push(entry),removed));let right=suspend(a,removed,renaming(history,removed));
    assert(left.accumulators =~= right.accumulators) by {
        assert forall|n:usize| left.accumulators.dom().contains(n) implies left.accumulators[n]==right.accumulators[n] by {
            if n!=removed {
                assert(left.accumulators[n] =~= right.accumulators[n]) by {
                    assert forall|i:int| 0<=i<a.accumulators[n].len() implies left.accumulators[n][i]==right.accumulators[n][i] by {
                        index_prefix(history.push(entry),history,removed,a.accumulators[n][i]);
                    }
                }
            }
        }
    }
}
pub open spec fn keep(actor:usize,rule:r::Rule,removed:usize)->bool {
    actor!=removed || rule==r::Rule::Retire || rule==r::Rule::Insert || rule==r::Rule::Remove
}
/// A retained landing uses the target interpreter's own input and minted token.
pub open spec fn successor<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    a:g::Configuration<U,I>,z:g::Configuration<U,I>,target:g::Configuration<U,I>,actor:usize,rule:r::Rule,removed:usize)->g::Configuration<U,I> {
    g::Configuration {state:suspend(z.state,removed,renaming(z.history,removed)),roots:z.roots,current:z.current.insert(removed,None),
        history:if g::landing(a,z,rule) && actor!=removed {target.history.push(g::entry(lib,programs,target,actor))} else {target.history}}
}

pub open spec fn table_stage<A,X,U,B,I>(node:g::Node<A,X,U,B,I>)->bool {match node {g::Node::Dependent {..}=>true,_=>false}}
pub open spec fn dependent<A,X,U,B,I>(node:g::Node<A,X,U,B,I>)->d::Node<Port,A,X,U,B,I> {match node {g::Node::Dependent {node}=>node,_=>d::Node::Unit}}

pub proof fn local_history_step<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    a:g::Configuration<U,I>,z:g::Configuration<U,I>,actor:usize,rule:r::Rule,removed:usize)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a),g::step(lib,programs,a,z,actor,rule),
        isolated(a.state,removed),local_history(a.history,removed),
        actor==removed && g::landing(a,z,rule) ==> table_stage(programs(actor)(a.current[actor].unwrap())),
    ensures local_history(z.history,removed),
{
    ol::frame(eq,lib,programs,a,z,actor,rule);
    if g::landing(a,z,rule) {
        let id=a.current[actor].unwrap();let node=programs(actor)(id);
        ol::run_members(eq,lib,programs,a.state,actor,id);
        if actor==removed {own_run_stutters(lib,dependent(node),a.state,removed,renaming(a.history,removed));}
        else {run_transport(lib,node,a.state,actor,removed,renaming(a.history,removed));}
        assert forall|i:int| 0<=i<z.history.len() implies if g::owner(z.history[i].landed.receipt)==removed {
            receipt_local(z.history[i].landed.receipt,removed)
        } else {receipt_avoids(z.history[i].landed.receipt,removed)} by {
            if i<a.history.len() {assert(z.history[i]==a.history[i]);} else {assert(i==a.history.len());}
        }
    }
}

pub proof fn landing_transport<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    a:g::Configuration<U,I>,z:g::Configuration<U,I>,target:g::Configuration<U,I>,actor:usize,rule:r::Rule,removed:usize)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a),g::step(lib,programs,a,z,actor,rule),g::landing(a,z,rule),
        isolated(a.state,removed),related(a,target,removed),actor!=removed,
    ensures related(z,successor(lib,programs,a,z,target,actor,rule,removed),removed),
        successor(lib,programs,a,z,target,actor,rule,removed)==g::land(lib,programs,target,actor,z.state.control.fibers[actor].phase),
        g::step(lib,programs,target,successor(lib,programs,a,z,target,actor,rule,removed),actor,rule),
{
    ol::frame(eq,lib,programs,a,z,actor,rule);ol::configuration_preservation(eq,lib,programs,a,z,actor,rule);
    let id=a.current[actor].unwrap();let node=programs(actor)(id);let rho=renaming(a.history,removed);
    ol::run_members(eq,lib,programs,a.state,actor,id);
    ol::run_admissible(eq,lib,node,a.state,actor);run_transport(lib,node,a.state,actor,removed,rho);
    let old=g::entry(lib,programs,a,actor);let new=g::entry(lib,programs,target,actor);
    let phase=z.state.control.fibers[actor].phase;let out=successor(lib,programs,a,z,target,actor,rule,removed);
    histories_push(a.history,target.history,removed,old,new);
    suspend_target(a.state,removed,rho,actor,a.state.control.fibers[actor].committed);
    assert forall|n:usize,i:int| z.state.accumulators.dom().contains(n) && n!=removed && 0<=i<z.state.accumulators[n].len()
        implies z.state.accumulators[n][i]<=a.history.len() by {assert(s::registered(z.state,n));}
    suspend_append(z.state,a.history,old,removed);
    let next=if phase==Phase::Loading {old.landed.next} else {None};
    suspend_edit(old.landed.state,removed,rho,actor,phase,a.state.control.fibers[actor].committed,
        dep::marker(next),a.state.accumulators[actor].push(a.history.len()));
    assert(rename_tokens(a.state.accumulators[actor].push(a.history.len()),rho)
        =~= rename_tokens(a.state.accumulators[actor],rho).push(target.history.len()));
    let result=g::land(lib,programs,target,actor,phase);
    assert(out.current =~= result.current);
    assert(out==result);
}

pub proof fn own_landing_stutters<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    a:g::Configuration<U,I>,z:g::Configuration<U,I>,target:g::Configuration<U,I>,rule:r::Rule,removed:usize)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a),g::step(lib,programs,a,z,removed,rule),g::landing(a,z,rule),
        isolated(a.state,removed),related(a,target,removed),table_stage(programs(removed)(a.current[removed].unwrap())),
    ensures related(z,target,removed),
{
    ol::frame(eq,lib,programs,a,z,removed,rule);ol::configuration_preservation(eq,lib,programs,a,z,removed,rule);
    let node=dependent(programs(removed)(a.current[removed].unwrap()));let rho=renaming(a.history,removed);
    own_run_stutters(lib,node,a.state,removed,rho);
    let old=g::entry(lib,programs,a,removed);histories_skip(a.history,target.history,removed,old);
    assert forall|n:usize,i:int| z.state.accumulators.dom().contains(n) && n!=removed && 0<=i<z.state.accumulators[n].len()
        implies z.state.accumulators[n][i]<=a.history.len() by {assert(s::registered(z.state,n));}
    suspend_append(z.state,a.history,old,removed);
    let phase=z.state.control.fibers[removed].phase;let next=if phase==Phase::Loading {old.landed.next} else {None};
    lift::run_preservation(dep::stage(lib,node),a.state,removed);
    suspend_edit(old.landed.state,removed,rho,removed,phase,a.state.control.fibers[removed].committed,
        dep::marker(next),a.state.accumulators[removed].push(a.history.len()));
    assert(z.current.insert(removed,None) =~= a.current.insert(removed,None));
}

pub proof fn remove_unreferenced_transport<U,I>(a:g::Configuration<U,I>,target:g::Configuration<U,I>,actor:usize,removed:usize)
    requires g::tokens_valid(a),inv::well_formed(a.state),s::registered(a.state,removed),related(a,target,removed),
        ch::remove_unreferenced(g::kind(a.history),a.state,actor),
    ensures ch::remove_unreferenced(g::kind(target.history),target.state,actor),
{
    assert forall|n:usize,t:nat| s::registered(target.state,n) && target.state.accumulators[n].contains(t)
        implies g::kind(target.history)(t)!=Some(actor) by {
        assert(n!=removed);assert(s::registered(a.state,n));
        let i=choose|i:int| 0<=i<target.state.accumulators[n].len() && target.state.accumulators[n][i]==t;
        let old=a.state.accumulators[n][i];assert(a.state.accumulators[n].contains(old));
        ch::removal_excludes_retained_token(g::kind(a.history),a.state,actor,n,old);
        assert(old<a.history.len());assert(g::owner(a.history[old as int].landed.receipt)==n);
        assert(t==index(a.history,removed,old));assert(t<target.history.len());
        assert(g::kind(target.history)(t)==g::kind(a.history)(old));
    }
}

/// Every source guard is transported from declarations, actual partial run and
/// actual LIFO receipts. Target legality is a conclusion, never a premise.
pub proof fn suspend_frame<U>(a:s::State<U>,z:s::State<U>,removed:usize,rho:spec_fn(nat)->nat,actor:usize)
    requires s::registered(a,removed),s::registered(z,removed),r::frame(a.control,z.control,actor),
    ensures r::frame(suspend(a,removed,rho).control,suspend(z,removed,rho).control,actor),
{
    let left=suspend(a,removed,rho).control;let right=suspend(z,removed,rho).control;
    assert forall|n:usize| n!=actor implies r::registered(left,n)==r::registered(right,n)
        && (r::registered(left,n) ==> left.fibers[n]==right.fibers[n]) by {
        assert(r::registered(a.control,n)==r::registered(z.control,n));
        if n==removed {assert(a.control.fibers[n]==z.control.fibers[n]);}
        else if r::registered(a.control,n) {assert(a.control.fibers[n]==z.control.fibers[n]);}
    }
}

pub proof fn suspend_control_step<U>(a:s::State<U>,z:s::State<U>,removed:usize,rho:spec_fn(nat)->nat,actor:usize,rule:r::Rule)
    requires s::registered(a,removed),s::registered(z,removed),r::step(a.control,z.control,actor,rule),
        rule==r::Rule::Insert || rule==r::Rule::Remove || rule==r::Rule::Retire,
    ensures r::step(suspend(a,removed,rho).control,suspend(z,removed,rho).control,actor,rule),
{
    let left=suspend(a,removed,rho).control;let right=suspend(z,removed,rho).control;
    suspend_frame(a,z,removed,rho,actor);
    match rule {
        r::Rule::Insert=>{
            assert(actor!=removed);
            assert forall|n:usize,key:Port| r::registered(left,n) && left.fibers[n].provisions.contains(key)
                implies !right.fibers[actor].provisions.contains(key) by {
                assert(r::registered(a.control,n));assert(a.control.fibers[n].provisions.contains(key));
            }
        },
        r::Rule::Remove=>{
            assert(actor!=removed);
            assert forall|n:usize| r::registered(left,n) implies left.fibers[n].parent!=Some(actor) by {
                assert(r::registered(a.control,n));assert(a.control.fibers[n].parent!=Some(actor));
            }
        },
        _=>{},
    }
}

pub proof fn orchestration_transport<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    a:g::Configuration<U,I>,z:g::Configuration<U,I>,target:g::Configuration<U,I>,actor:usize,rule:r::Rule,removed:usize)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a),g::step(lib,programs,a,z,actor,rule),
        isolated(a.state,removed),s::registered(z.state,removed),related(a,target,removed),local_history(a.history,removed),
        !g::landing(a,z,rule),rule==r::Rule::Insert || rule==r::Rule::Remove || rule==r::Rule::Retire,
    ensures related(z,successor(lib,programs,a,z,target,actor,rule,removed),removed),
        keep(actor,rule,removed) ==> g::step(lib,programs,target,successor(lib,programs,a,z,target,actor,rule,removed),actor,rule),
        !keep(actor,rule,removed) ==> related(z,target,removed),
{
    hide(g::well_formed);hide(g::history_sound);hide(g::members);hide(og::primitive_theory);
    hide(syntax::member);hide(local_history);hide(histories);
    assert(inv::well_formed(a.state) && g::tokens_valid(a) && dep::typed(lib,a.state)
        && dep::finite_context(a.state) && g::history_sound(lib,programs,a.history)) by {reveal(g::well_formed);}
    ol::frame(eq,lib,programs,a,z,actor,rule);
    let rho=renaming(a.history,removed);let out=successor(lib,programs,a,z,target,actor,rule,removed);
    assert(a.history==z.history);assert(related(z,out,removed));
    match rule {

            r::Rule::Insert=>{
                assert(actor!=removed);
                assert(r::frame(a.state.control,z.state.control,actor));
                assert forall|n:usize| n!=actor implies s::registered(target.state,n)==s::registered(out.state,n)
                    && (s::registered(target.state,n) ==> target.state.control.fibers[n]==out.state.control.fibers[n]) by {
                    assert(s::registered(a.state,n)==s::registered(z.state,n));
                    if s::registered(a.state,n) {assert(a.state.control.fibers[n]==z.state.control.fibers[n]);}
                }
                suspend_frame(a.state,z.state,removed,rho,actor);
                assert(r::frame(target.state.control,out.state.control,actor));
                suspend_control_step(a.state,z.state,removed,rho,actor,rule);
                assert(r::step(target.state.control,out.state.control,actor,rule));
                assert(out.state.tables =~= target.state.tables.insert(actor,IMap::empty()));
                assert(out.state.iterators =~= target.state.iterators.insert(actor,None));
                assert(rename_tokens(Seq::<nat>::empty(),rho) =~= Seq::<nat>::empty());
                assert(out.state.accumulators =~= target.state.accumulators.insert(actor,Seq::empty()));
                assert(out.current =~= target.current.insert(actor,None));
                assert(g::step(lib,programs,target,out,actor,rule));
            },
            r::Rule::Remove=>{
                assert(actor!=removed);remove_unreferenced_transport(a,target,actor,removed);
                assert forall|n:usize| s::registered(target.state,n) implies target.state.control.fibers[n].parent!=Some(actor) by {
                    assert(s::registered(a.state,n));assert(a.state.control.fibers[n].parent!=Some(actor));
                }
                suspend_frame(a.state,z.state,removed,rho,actor);
                assert(r::frame(target.state.control,out.state.control,actor));
                suspend_control_step(a.state,z.state,removed,rho,actor,rule);
                assert(r::step(target.state.control,out.state.control,actor,rule));
                let erased=s::erase(target.state,actor);
                assert(out.state.control.fibers =~= erased.control.fibers);
                assert(out.state.tables =~= erased.tables);assert(out.state.effects =~= erased.effects);
                assert(out.state.iterators =~= erased.iterators);assert(out.state.accumulators =~= erased.accumulators);
                assert(out.current =~= target.current.remove(actor));
                assert(g::step(lib,programs,target,out,actor,rule));
            },
            r::Rule::Retire=>{
                suspend_frame(a.state,z.state,removed,rho,actor);
                assert(r::frame(target.state.control,out.state.control,actor));
                assert(s::child_retire(target.state,out.state,actor));
                assert(out.current =~= target.current);
                assert(g::step(lib,programs,target,out,actor,rule));
            },
        _=>{},
    }
}

pub proof fn edit_transport<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    a:g::Configuration<U,I>,z:g::Configuration<U,I>,target:g::Configuration<U,I>,actor:usize,rule:r::Rule,removed:usize)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a),g::step(lib,programs,a,z,actor,rule),
        isolated(a.state,removed),s::registered(z.state,removed),related(a,target,removed),local_history(a.history,removed),
        !g::landing(a,z,rule),rule==r::Rule::Begin || rule==r::Rule::Divert || rule==r::Rule::Leave,
    ensures related(z,successor(lib,programs,a,z,target,actor,rule,removed),removed),
        keep(actor,rule,removed) ==> g::step(lib,programs,target,successor(lib,programs,a,z,target,actor,rule,removed),actor,rule),
        !keep(actor,rule,removed) ==> related(z,target,removed),
{
    hide(g::well_formed);hide(g::history_sound);hide(g::members);hide(og::primitive_theory);
    hide(syntax::member);hide(local_history);hide(histories);
    assert(inv::well_formed(a.state) && g::tokens_valid(a) && dep::typed(lib,a.state)
        && dep::finite_context(a.state) && g::history_sound(lib,programs,a.history)) by {reveal(g::well_formed);}
    ol::frame(eq,lib,programs,a,z,actor,rule);
    let rho=renaming(a.history,removed);let out=successor(lib,programs,a,z,target,actor,rule,removed);
    assert(a.history==z.history);assert(related(z,out,removed));
    match rule {
            r::Rule::Begin | r::Rule::Divert | r::Rule::Leave=>{
                let f=z.state.control.fibers[actor];
                suspend_edit(a.state,removed,rho,actor,f.phase,f.committed,z.state.iterators[actor],z.state.accumulators[actor]);
                if actor==removed {
                    assert(out.current =~= target.current);assert(out==target);
                } else {
                    suspend_target(a.state,removed,rho,actor,f.committed);
                    if rule==r::Rule::Begin {
                        assert(rename_tokens(Seq::<nat>::empty(),rho) =~= Seq::<nat>::empty());
                        assert(out.current =~= target.current.insert(actor,Some(target.roots[actor])));
                        assert(out==g::edit(target,actor,Phase::Loading,f.committed,Some(target.roots[actor]),Seq::empty()));
                    } else {
                        assert(z==g::edit(a,actor,Phase::Unloading,a.state.control.fibers[actor].committed,None,a.state.accumulators[actor]));
                        assert(out.current =~= target.current.insert(actor,None));
                        assert(out==g::edit(target,actor,Phase::Unloading,f.committed,None,target.state.accumulators[actor]));
                    }
                    assert(g::step(lib,programs,target,out,actor,rule));
                }
            },
        _=>{},
    }
}

pub proof fn unload_transport<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    a:g::Configuration<U,I>,z:g::Configuration<U,I>,target:g::Configuration<U,I>,actor:usize,rule:r::Rule,removed:usize)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a),g::step(lib,programs,a,z,actor,rule),
        isolated(a.state,removed),s::registered(z.state,removed),related(a,target,removed),local_history(a.history,removed),
        !g::landing(a,z,rule),rule==r::Rule::Unload,
    ensures related(z,successor(lib,programs,a,z,target,actor,rule,removed),removed),
        keep(actor,rule,removed) ==> g::step(lib,programs,target,successor(lib,programs,a,z,target,actor,rule,removed),actor,rule),
        !keep(actor,rule,removed) ==> related(z,target,removed),
{
    hide(g::well_formed);hide(g::history_sound);hide(g::members);hide(og::primitive_theory);
    hide(syntax::member);hide(local_history);hide(histories);
    assert(inv::well_formed(a.state) && g::tokens_valid(a) && dep::typed(lib,a.state)
        && dep::finite_context(a.state) && g::history_sound(lib,programs,a.history)) by {reveal(g::well_formed);}
    ol::frame(eq,lib,programs,a,z,actor,rule);
    let rho=renaming(a.history,removed);let out=successor(lib,programs,a,z,target,actor,rule,removed);
    assert(a.history==z.history);assert(related(z,out,removed));
    match rule {
            r::Rule::Unload=>{
                let restored=g::restore(a.history,a.state.accumulators[actor],a.state,actor).unwrap();
                g::restore_preservation(lib,programs,a.history,a.state.accumulators[actor],a.state,actor);
                suspend_edit(restored,removed,rho,actor,Phase::Inactive,ISet::empty(),None,Seq::empty());
                if actor==removed {
                    own_restore_stutters(a.history,a.state.accumulators[actor],a.state,removed,rho);
                    assert(out.current =~= target.current);assert(out==target);
                } else {
                    restore_transport(a.history,target.history,a.state.accumulators[actor],a.state,actor,removed);
                    assert(rename_tokens(Seq::<nat>::empty(),rho) =~= Seq::<nat>::empty());
                    assert(!r::relied(target.state.control,actor)) by {
                        if r::relied(target.state.control,actor) {
                            let (n,b)=choose|n:usize,b:Binding| r::registered(target.state.control,n) && n!=actor
                                && target.state.control.fibers[n].phase!=Phase::Inactive && target.state.control.fibers[n].committed.contains(b) && b.provider==actor;
                            assert(n!=removed);assert(r::relied(a.state.control,actor));
                        }
                    }
                    assert(out.current =~= target.current.insert(actor,None));
                    assert(out==g::unload(target,actor));assert(g::step(lib,programs,target,out,actor,rule));
                }
            },
        _=>{},
    }
}

#[verifier::rlimit(20)]
pub proof fn step_transport<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    a:g::Configuration<U,I>,z:g::Configuration<U,I>,target:g::Configuration<U,I>,actor:usize,rule:r::Rule,removed:usize)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a),g::step(lib,programs,a,z,actor,rule),
        isolated(a.state,removed),s::registered(z.state,removed),related(a,target,removed),local_history(a.history,removed),
        actor==removed && g::landing(a,z,rule) ==> table_stage(programs(actor)(a.current[actor].unwrap())),
    ensures local_history(z.history,removed),
        keep(actor,rule,removed) ==> {
            let out=successor(lib,programs,a,z,target,actor,rule,removed);
            &&& g::step(lib,programs,target,out,actor,rule) && related(z,out,removed)
        },
        !keep(actor,rule,removed) ==> related(z,target,removed),
{
    local_history_step(eq,lib,programs,a,z,actor,rule,removed);
    if g::landing(a,z,rule) {
        if actor==removed {own_landing_stutters(eq,lib,programs,a,z,target,rule,removed);}
        else {landing_transport(eq,lib,programs,a,z,target,actor,rule,removed);}
    } else {
        match rule {
            r::Rule::Insert | r::Rule::Remove | r::Rule::Retire=>{orchestration_transport(eq,lib,programs,a,z,target,actor,rule,removed);},
            r::Rule::Begin | r::Rule::Divert | r::Rule::Leave=>{edit_transport(eq,lib,programs,a,z,target,actor,rule,removed);},
            r::Rule::Unload=>{unload_transport(eq,lib,programs,a,z,target,actor,rule,removed);},
            _=>{},
        }
    }
}

#[verifier::opaque]
pub open spec fn labels_without(labels:Seq<(usize,r::Rule)>,removed:usize)->Seq<(usize,r::Rule)>
    decreases labels.len(),
{
    if labels.len()==0 {Seq::empty()} else {
        let previous=labels_without(labels.drop_last(),removed);let label=labels.last();
        if keep(label.0,label.1,removed) {previous.push(label)} else {previous}
    }
}
#[verifier::opaque]
pub open spec fn delete<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,source:Seq<g::Configuration<U,I>>,
    labels:Seq<(usize,r::Rule)>,removed:usize)->Seq<g::Configuration<U,I>>
    decreases labels.len(),
{
    if labels.len()==0 {seq![source.first()]} else {
        let prefix=delete(lib,programs,source.drop_last(),labels.drop_last(),removed);
        let label=labels.last();
        if keep(label.0,label.1,removed) {
            prefix.push(successor(lib,programs,source[source.len()-2],source.last(),prefix.last(),label.0,label.1,removed))
        } else {prefix}
    }
}
/// Only source syntax/interfaces are restricted. Every foreign lifecycle and
/// external orchestration rule remains available, including foreign children.
pub open spec fn separation<A,X,U,B,I>(programs:g::Programs<A,X,U,B,I>,source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,removed:usize)->bool {
    &&& forall|i:int| 0<=i<source.len() ==> isolated(source[i].state,removed)
    &&& forall|i:int| 0<=i<labels.len() && labels[i].0==removed && g::landing(source[i],source[i+1],labels[i].1)
        ==> table_stage(programs(removed)(source[i].current[removed].unwrap()))
}
pub proof fn initial_related<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,removed:usize)
    requires g::well_formed(lib,programs,a),s::registered(a.state,removed),a.history.len()==0,
        a.state.control.fibers[removed].phase==Phase::Inactive,a.state.tables[removed].is_empty(),
    ensures related(a,a,removed),local_history(a.history,removed),
{
    assert forall|n:usize| a.state.accumulators.dom().contains(n) implies a.state.accumulators[n].len()==0 by {
        assert(s::registered(a.state,n));
        if a.state.accumulators[n].len()>0 {assert(a.state.accumulators[n][0]<a.history.len());}
    }
    let z=suspend(a.state,removed,renaming(a.history,removed));
    assert(a.state.control.fibers[removed].committed =~= ISet::<Binding>::empty());
    assert(a.state.tables[removed] =~= IMap::<Port,U>::empty());
    assert(a.state.control.fibers =~= z.control.fibers);assert(a.state.tables =~= z.tables);
    assert(a.state.iterators =~= z.iterators);
    assert(a.state.accumulators =~= z.accumulators) by {
        assert forall|n:usize| a.state.accumulators.dom().contains(n) implies a.state.accumulators[n]==z.accumulators[n] by {
            assert(a.state.accumulators[n].len()==0);assert(a.state.accumulators[n] =~= z.accumulators[n]);
        }
    }
    assert(a.state.iterators[removed]==dep::marker(a.current[removed]));
    assert(a.current[removed].is_none());assert(a.current.insert(removed,None) =~= a.current);
}

/// A constructed legal execution for every finite source prefix, with fresh
/// compressed journal indices and original raw dependent outcomes. No legal
/// surviving execution or completed recovery is supplied by the caller.
#[verifier::rlimit(25)]
#[verifier::spinoff_prover]
pub proof fn delete_execution<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,removed:usize)
    requires og::primitive_theory(eq,lib),g::execution(lib,programs,source,labels),g::well_formed(lib,programs,source.first()),
        source.first().history.len()==0,source.first().state.control.fibers[removed].phase==Phase::Inactive,
        source.first().state.tables[removed].is_empty(),separation(programs,source,labels,removed),
    ensures {
        let target=delete(lib,programs,source,labels,removed);let kept=labels_without(labels,removed);
        &&& g::execution(lib,programs,target,kept) && target.first()==source.first()
        &&& related(source.last(),target.last(),removed) && local_history(source.last().history,removed)
        &&& g::well_formed(lib,programs,source.last())
        &&& forall|i:int| 0<=i<target.len() ==> g::well_formed(lib,programs,target[i])
    },
    decreases labels.len(),
{
    reveal(delete);reveal(labels_without);
    let target=delete(lib,programs,source,labels,removed);let kept=labels_without(labels,removed);
    if labels.len()==0 {
        assert(source.len()==1);assert(source.first()==source.last());
        assert(target==seq![source.first()]);assert(kept==Seq::<(usize,r::Rule)>::empty());
        initial_related(lib,programs,source.first(),removed);
        assert forall|i:int| 0<=i<target.len() implies g::well_formed(lib,programs,target[i]) by {
            assert(i==0);assert(target[i]==source.first());
        }
    } else {
        let previous=labels.drop_last();let prefix=source.drop_last();
        assert(prefix.len()==previous.len()+1);
        assert(prefix.first()==source.first());
        assert(g::execution(lib,programs,prefix,previous)) by {
            assert forall|i:int| 0<=i<previous.len() implies g::step(lib,programs,prefix[i],prefix[i+1],previous[i].0,previous[i].1) by {
                assert(prefix[i]==source[i]);assert(prefix[i+1]==source[i+1]);assert(previous[i]==labels[i]);
                assert(g::step(lib,programs,source[i],source[i+1],labels[i].0,labels[i].1));
            }
        }
        assert(separation(programs,prefix,previous,removed)) by {
            assert forall|i:int| 0<=i<prefix.len() implies isolated(prefix[i].state,removed) by {
                assert(prefix[i]==source[i]);assert(isolated(source[i].state,removed));
            }
            assert forall|i:int| 0<=i<previous.len() && previous[i].0==removed && g::landing(prefix[i],prefix[i+1],previous[i].1)
                implies table_stage(programs(removed)(prefix[i].current[removed].unwrap())) by {
                assert(prefix[i]==source[i]);assert(prefix[i+1]==source[i+1]);assert(previous[i]==labels[i]);
            }
        }
        delete_execution(eq,lib,programs,prefix,previous,removed);
        let before=delete(lib,programs,prefix,previous,removed);let earlier=labels_without(previous,removed);let label=labels.last();
        let a=prefix.last();let z=source.last();
        assert(a==source[source.len()-2]);
        assert(g::execution(lib,programs,before,earlier));
        assert(before.len()>0);
        assert(before.first()==source.first());
        assert(g::well_formed(lib,programs,a));
        assert(g::well_formed(lib,programs,before.last()));
        assert(related(a,before.last(),removed));
        assert(local_history(a.history,removed));
        assert(g::step(lib,programs,a,z,label.0,label.1));
        assert(isolated(a.state,removed));assert(isolated(z.state,removed));
        step_transport(eq,lib,programs,a,z,before.last(),label.0,label.1,removed);
        ol::configuration_preservation(eq,lib,programs,a,z,label.0,label.1);
        if keep(label.0,label.1,removed) {
            let out=successor(lib,programs,a,z,before.last(),label.0,label.1,removed);
            assert(target==before.push(out));assert(kept==earlier.push(label));
            assert(g::step(lib,programs,before.last(),out,label.0,label.1));
            assert(related(z,out,removed));
            ol::configuration_preservation(eq,lib,programs,before.last(),out,label.0,label.1);
            crate::old_journal_closure::append_execution(lib,programs,before,earlier,out,label.0,label.1);
            assert(target.first()==before.first());assert(target.last()==out);
            assert forall|i:int| 0<=i<target.len() implies g::well_formed(lib,programs,target[i]) by {
                if i<before.len() {
                    assert(target[i]==before[i]);assert(g::well_formed(lib,programs,before[i]));
                } else {assert(i==before.len());assert(target[i]==out);}
            }
        } else {
            assert(target==before);assert(kept==earlier);
            assert(related(z,before.last(),removed));
        }
    }
}

/// Every original time prefix receives its own legal filtered execution,
/// including prefixes that stop while the removed episode is still Loading.
pub open spec fn prefix_valid<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,removed:usize,i:int)->bool {
    let prefix=source.take(i+1);let steps=labels.take(i);let target=delete(lib,programs,prefix,steps,removed);
    g::execution(lib,programs,target,labels_without(steps,removed))
        && target.first()==source.first() && related(source[i],target.last(),removed)
}
pub proof fn every_prefix<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,removed:usize)
    requires og::primitive_theory(eq,lib),g::execution(lib,programs,source,labels),g::well_formed(lib,programs,source.first()),
        separation(programs,source,labels,removed),
        source.first().history.len()==0,source.first().state.control.fibers[removed].phase==Phase::Inactive,
        source.first().state.tables[removed].is_empty(),
    ensures forall|i:int| 0<=i<source.len() ==> #[trigger] prefix_valid(lib,programs,source,labels,removed,i),
{
    assert forall|i:int| 0<=i<source.len() implies #[trigger] prefix_valid(lib,programs,source,labels,removed,i) by {
        let prefix=source.take(i+1);let steps=labels.take(i);
        assert(g::execution(lib,programs,prefix,steps));assert(separation(programs,prefix,steps,removed));
        assert(prefix.first()==source.first());assert(prefix.last()==source[i]);
        delete_execution(eq,lib,programs,prefix,steps,removed);
    }
}

/// At an actual closed episode endpoint the owner table is proved empty from
/// its provision receipts. Thus the constructed surviving execution has the
/// same complete table observation and control state, despite token renumbering.
pub proof fn inactive_table_empty<U,I>(a:g::Configuration<U,I>,actor:usize)
    requires inv::well_formed(a.state),s::registered(a.state,actor),a.state.control.fibers[actor].phase==Phase::Inactive,
        crate::mixed_recovery::provided_journals(a),
    ensures a.state.tables[actor].is_empty(),
{
    assert(a.state.accumulators[actor].len()==0);assert(crate::mixed_recovery::own_word(a,actor).len()==0);
    assert forall|key:Port| !a.state.tables[actor].dom().contains(key) by {
        if a.state.tables[actor].dom().contains(key) {assert(crate::entangled::erases(crate::mixed_recovery::own_word(a,actor),key));}
    }
}

pub proof fn closed_observation<U,I>(a:g::Configuration<U,I>,target:g::Configuration<U,I>,removed:usize)
    requires inv::well_formed(a.state),inv::well_formed(target.state),s::registered(a.state,removed),related(a,target,removed),
        a.state.control.fibers[removed].phase==Phase::Inactive,a.state.tables[removed].is_empty(),
    ensures target.state.control==a.state.control,target.state.tables==a.state.tables,
        p::project(target.state,ISet::full())==p::project(a.state,ISet::full()),
{
    assert(a.state.tables[removed] =~= IMap::<Port,U>::empty());
    assert(a.state.control.fibers[removed].committed =~= ISet::<Binding>::empty());
    assert(target.state.control.fibers =~= a.state.control.fibers);assert(target.state.tables =~= a.state.tables);
    p::unique_owner(a.state);p::unique_owner(target.state);
    assert(p::bindings_equal(a.state,target.state));p::projection_equal(a.state,target.state,ISet::full());
}

#[verifier::rlimit(20)]
pub proof fn closed_execution<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,removed:usize)
    requires og::primitive_theory(eq,lib),g::execution(lib,programs,source,labels),g::well_formed(lib,programs,source.first()),
        source.first().history.len()==0,source.first().state.control.fibers[removed].phase==Phase::Inactive,
        forall|n:usize| s::registered(source.first().state,n) ==> source.first().state.tables[n].is_empty(),
        separation(programs,source,labels,removed),source.last().state.control.fibers[removed].phase==Phase::Inactive,
    ensures {
        let target=delete(lib,programs,source,labels,removed);
        &&& g::execution(lib,programs,target,labels_without(labels,removed)) && target.first()==source.first()
        &&& related(source.last(),target.last(),removed)
        &&& target.last().state.control==source.last().state.control && target.last().state.tables==source.last().state.tables
        &&& p::project(target.last().state,ISet::full())==p::project(source.last().state,ISet::full())
        &&& source.last().state.tables[removed].is_empty()
    },
{
    delete_execution(eq,lib,programs,source,labels,removed);
    assert(crate::mixed_recovery::provided_journals(source.first()));
    crate::observational_execution::trace_provided_journals(eq,lib,programs,source,labels);
    let a=source.last();let target=delete(lib,programs,source,labels,removed).last();
    inactive_table_empty(a,removed);
    closed_observation(a,target,removed);
}

#[verifier::opaque]
pub open spec fn example_trace()->Seq<g::Configuration<int,ex::Stage>> {
    let empty=g::empty::<int,ex::Stage>();
    let first=t::insert(empty,0,None,ISet::empty(),ex::provided(0),ex::Stage::Provide);
    let a0=t::insert(first,1,None,ISet::empty(),ex::provided(1),ex::Stage::Provide);
    let a1=g::edit(a0,0,Phase::Loading,ISet::empty(),Some(ex::Stage::Provide),Seq::empty());
    let a2=g::land(ex::library(),ex::programs(),a1,0,Phase::Loading);
    let a3=g::edit(a2,1,Phase::Loading,ISet::empty(),Some(ex::Stage::Provide),Seq::empty());
    let a4=g::land(ex::library(),ex::programs(),a3,1,Phase::Loading);
    let a5=g::land(ex::library(),ex::programs(),a4,0,Phase::Active);
    let a6=g::land(ex::library(),ex::programs(),a5,1,Phase::Active);
    let a7=crate::mixed_orchestration::retire(a6,0);
    let a8=g::edit(a7,0,Phase::Unloading,ISet::empty(),None,a7.state.accumulators[0usize]);
    let a9=g::unload(a8,0);
    let a10=crate::mixed_orchestration::retire(a9,1);
    let a11=g::edit(a10,1,Phase::Unloading,ISet::empty(),None,a10.state.accumulators[1usize]);
    let a12=g::unload(a11,1);
    seq![a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12]
}
pub open spec fn example_labels()->Seq<(usize,r::Rule)> {
    seq![(0usize,r::Rule::Begin),(0usize,r::Rule::Iter),(1usize,r::Rule::Begin),(1usize,r::Rule::Iter),
        (0usize,r::Rule::Finish),(1usize,r::Rule::Finish),(0usize,r::Rule::Retire),(0usize,r::Rule::Leave),
        (0usize,r::Rule::Unload),(1usize,r::Rule::Retire),(1usize,r::Rule::Leave),(1usize,r::Rule::Unload)]
}
#[verifier::rlimit(30)]
pub proof fn example_execution()
    ensures g::execution(ex::library(),ex::programs(),example_trace(),example_labels()),
        g::well_formed(ex::library(),ex::programs(),example_trace().first()),
        separation(ex::programs(),example_trace(),example_labels(),0),
        example_trace().first().history.len()==0,example_trace().first().state.control.fibers[0usize].phase==Phase::Inactive,
        forall|n:usize| s::registered(example_trace().first().state,n) ==> example_trace().first().state.tables[n].is_empty(),
        example_trace().last().state.control.fibers[0usize].phase==Phase::Inactive,
        example_trace()[6].state.accumulators[1usize]==seq![1nat,3nat],
        example_trace().last().history.len()==4,
        g::owner(example_trace().last().history[0].landed.receipt)==0,
        g::owner(example_trace().last().history[1].landed.receipt)==1,
        g::owner(example_trace().last().history[2].landed.receipt)==0,
        g::owner(example_trace().last().history[3].landed.receipt)==1,
{
    reveal(example_trace);let lib=ex::library();let programs=ex::programs();
    ex::primitive_theory();og::exact_theory(ex::equality(),lib);ex::root_members();
    syntax::constructor_member(lib,programs,0,ex::provided(0),ex::provided(0),ex::Stage::Provide);
    assert(ISet::<Port>::empty().union(ex::provided(0)) =~= ex::provided(0));
    assert(ISet::<Port>::empty().union(ex::provided(1)) =~= ex::provided(1));
    let empty=g::empty::<int,ex::Stage>();let first=t::insert(empty,0,None,ISet::empty(),ex::provided(0),ex::Stage::Provide);
    g::empty_well_formed(lib,programs);
    t::insertion_step(lib,programs,empty,0,None,ISet::empty(),ex::provided(0),ex::Stage::Provide);
    ol::configuration_preservation(ex::equality(),lib,programs,empty,first,0,r::Rule::Insert);
    t::insertion_step(lib,programs,first,1,None,ISet::empty(),ex::provided(1),ex::Stage::Provide);
    let states=example_trace();ol::configuration_preservation(ex::equality(),lib,programs,first,states[0],1,r::Rule::Insert);
    assert(g::step(lib,programs,states[0],states[1],0,r::Rule::Begin));
    assert(g::step(lib,programs,states[1],states[2],0,r::Rule::Iter));
    assert(g::step(lib,programs,states[2],states[3],1,r::Rule::Begin));
    assert(g::step(lib,programs,states[3],states[4],1,r::Rule::Iter));
    assert(g::step(lib,programs,states[4],states[5],0,r::Rule::Finish));
    assert(g::step(lib,programs,states[5],states[6],1,r::Rule::Finish));
    ch::concrete_child_retirement(states[6].state,0);
    assert(g::step(lib,programs,states[6],states[7],0,r::Rule::Retire));
    assert(g::step(lib,programs,states[7],states[8],0,r::Rule::Leave));
    assert(states[8].state.accumulators[0usize] =~= seq![0nat,2nat]);
    assert(states[6].state.accumulators[1usize] =~= seq![1nat,3nat]);
    reveal_with_fuel(g::restore,3);
    assert(g::step(lib,programs,states[8],states[9],0,r::Rule::Unload));
    ch::concrete_child_retirement(states[9].state,1);
    assert(g::step(lib,programs,states[9],states[10],1,r::Rule::Retire));
    assert(g::step(lib,programs,states[10],states[11],1,r::Rule::Leave));
    assert(g::step(lib,programs,states[11],states[12],1,r::Rule::Unload));
    assert forall|i:int| 0<=i<example_labels().len() implies g::step(lib,programs,states[i],states[i+1],example_labels()[i].0,example_labels()[i].1) by {
        if i==0 {} else if i==1 {} else if i==2 {} else if i==3 {} else if i==4 {} else if i==5 {}
        else if i==6 {} else if i==7 {} else if i==8 {} else if i==9 {} else if i==10 {} else {assert(i==11);}
    }
    assert forall|i:int| 0<=i<states.len() implies isolated(states[i].state,0) by {
        if i==0 {} else if i==1 {} else if i==2 {} else if i==3 {} else if i==4 {} else if i==5 {}
        else if i==6 {} else if i==7 {} else if i==8 {} else if i==9 {} else if i==10 {} else if i==11 {} else {assert(i==12);}
    }
    assert forall|i:int| 0<=i<example_labels().len() && example_labels()[i].0==0 && g::landing(states[i],states[i+1],example_labels()[i].1)
        implies table_stage(programs(0)(states[i].current[0usize].unwrap())) by {
        if i==0 {} else if i==1 {} else if i==4 {} else if i==6 {} else if i==7 {} else {assert(i==8);}
    }
}

/// Both components execute real integer translations. The surviving component
/// later unloads using [0,1], compressed from actual source tokens [1,3].
pub proof fn four_entry_count<U,I>(history:Seq<g::Entry<U,I>>,removed:usize,foreign:usize)
    requires history.len()==4,removed!=foreign,
        g::owner(history[0].landed.receipt)==removed,g::owner(history[1].landed.receipt)==foreign,
        g::owner(history[2].landed.receipt)==removed,g::owner(history[3].landed.receipt)==foreign,
    ensures count(history,removed)==2,index(history,removed,1)==0,index(history,removed,3)==1,
{
    reveal_with_fuel(index,5);
}
pub proof fn example_filtered_labels()
    ensures labels_without(example_labels(),0)==seq![(1usize,r::Rule::Begin),(1usize,r::Rule::Iter),(1usize,r::Rule::Finish),
        (0usize,r::Rule::Retire),(1usize,r::Rule::Retire),(1usize,r::Rule::Leave),(1usize,r::Rule::Unload)],
{
    reveal_with_fuel(labels_without,13);
    assert(labels_without(example_labels(),0) =~= seq![(1usize,r::Rule::Begin),(1usize,r::Rule::Iter),(1usize,r::Rule::Finish),
        (0usize,r::Rule::Retire),(1usize,r::Rule::Retire),(1usize,r::Rule::Leave),(1usize,r::Rule::Unload)]);
}

#[verifier::rlimit(25)]
pub proof fn actual_filtered_unload()
    ensures {
        let source=example_trace();let target=delete(ex::library(),ex::programs(),source,example_labels(),0);
        &&& g::execution(ex::library(),ex::programs(),target,labels_without(example_labels(),0))
        &&& target.first()==source.first() && target.last().state.tables==source.last().state.tables
        &&& target.last().state.control==source.last().state.control
        &&& target.last().history.len()==2 && source.last().history.len()==4
        &&& labels_without(example_labels(),0)==seq![(1usize,r::Rule::Begin),(1usize,r::Rule::Iter),(1usize,r::Rule::Finish),
            (0usize,r::Rule::Retire),(1usize,r::Rule::Retire),(1usize,r::Rule::Leave),(1usize,r::Rule::Unload)]
    },
{
    hide(ex::library);hide(ex::programs);hide(g::execution);hide(g::well_formed);hide(og::primitive_theory);
    example_execution();ex::primitive_theory();og::exact_theory(ex::equality(),ex::library());
    closed_execution(ex::equality(),ex::library(),ex::programs(),example_trace(),example_labels(),0);
    four_entry_count(example_trace().last().history,0,1);example_filtered_labels();
}

} // verus!
