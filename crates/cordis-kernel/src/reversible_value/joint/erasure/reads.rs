//! Exact source reads used to transport the production Journal guards.
//! Native revision/publication changes are irrelevant to these specific guards;
//! the referenced actor's registration and owner are not.
#[cfg(verus_keep_ghost)]
use super::super::{Change, Record};
use vstd::prelude::*;
verus! {
pub open spec fn get<K,V>(m:Map<K,V>,k:K)->Option<V> {if m.contains_key(k) {Some(m[k])} else {None}}
pub open spec fn native_row(a:Map<nat,Record>,b:Map<nat,Record>,key:nat,id:usize)->bool {
    a.contains_key(key)==b.contains_key(key) && (a.contains_key(key) ==> {
        &&& (a[key] is Native)==(b[key] is Native)
        &&& a[key] is Native ==> {
            let x=a[key]->Native_state;let y=b[key]->Native_state;
            &&& x.control.fibers.dom().contains(id)==y.control.fibers.dom().contains(id)
            &&& x.control.fibers.dom().contains(id) ==> x.control.fibers[id]==y.control.fibers[id]
            &&& get(x.owners,id)==get(y.owners,id)
        }
    })
}
pub open spec fn same(a:Map<nat,Record>,b:Map<nat,Record>,before:Record,change:Change)->bool {
    match change {
        Change::Sources {..}=>before is Sources && get(a,before->Sources_state.configuration)==get(b,before->Sources_state.configuration),
        Change::Recipes {event}=>before is Recipes && native_row(a,b,before->Recipes_state.native,event.actor()),
        Change::Control {event}=>before is Control && {
            let s=before->Control_state;
            match event {
                super::super::control::Event::Restart {..}|super::super::control::Event::Release=>native_row(a,b,s.native,s.owner),
                super::super::control::Event::Begin {groups,..}=>native_row(a,b,s.native,s.owner) && get(a,groups)==get(b,groups),
                _=>true,
            }
        },
        Change::Host {event}=>before is Host && {
            let s=before->Host_state;
            match event {
                super::super::host::Event::EffectInitialized|super::super::host::Event::EffectFinished=>
                    get(a,s.owner.unwrap())==get(b,s.owner.unwrap()) &&
                    (event==super::super::host::Event::EffectInitialized && a.contains_key(s.owner.unwrap())
                        && a[s.owner.unwrap()] is Groups && a[s.owner.unwrap()]->Groups_state.queues.contains_key(s.kind->Effect_group)
                        ==> {let key=a[s.owner.unwrap()]->Groups_state.queues[s.kind->Effect_group].0;get(a,key)==get(b,key)}),
                _=>true,
            }
        },
        Change::Groups {event}=>before is Groups && match event {
            super::super::groups::Event::Add {key,..}=>get(a,key)==get(b,key),
            super::super::groups::Event::Remove {id}=>get(a,before->Groups_state.queues[id].0)==get(b,before->Groups_state.queues[id].0),
            super::super::groups::Event::Seal=>forall|id:usize|before->Groups_state.queues.contains_key(id) ==>
                get(a,before->Groups_state.queues[id].0)==get(b,before->Groups_state.queues[id].0),
            _=>true,
        },
        _=>true,
    }
}
pub proof fn transport(a:Map<nat,Record>,b:Map<nat,Record>,before:Record,change:Change)
    requires super::super::guard(a,before,change),same(a,b,before,change),
    ensures super::super::guard(b,before,change),
{
    reveal(super::super::host::guard);reveal(super::super::control::guard);reveal(super::super::groups::guard);
    if let Change::Groups {event:super::super::groups::Event::Seal}=change {
        assert forall|id:usize|#[trigger] before->Groups_state.queues.contains_key(id) implies
            super::super::groups::drained(b,before->Groups_state.queues[id]) by {
            assert(super::super::groups::drained(a,before->Groups_state.queues[id]));
        }
    }
}
/// RegisterInverse's index is a history pointer, not part of a queue transition
/// or of the cross-record read set.
pub proof fn scalar_restore(a:Record,b:Record,inverse:super::super::super::InverseState,before:super::super::super::ValueState,after:super::super::super::ValueState,x:nat,y:nat)
    ensures super::super::changes(a,b,Change::Value {event:super::super::super::Event::Restore {inverse,before,after,origin:x}})
        ==super::super::changes(a,b,Change::Value {event:super::super::super::Event::Restore {inverse,before,after,origin:y}}),
{reveal(super::super::changes);}
pub proof fn registration(a:Record,b:Record,x:nat,y:nat)
    ensures super::super::changes(a,b,Change::RegisterInverse {write:x})==super::super::changes(a,b,Change::RegisterInverse {write:y}),
{
    reveal(super::super::changes);
}
}
