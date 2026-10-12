//! The current lookup table of the actual multi-version publication store.
//! Retained revoked values are a separate lease observation, not visible entries
//! of the paper's table. These lemmas connect concrete payload operations to
//! key-local table updates without identifying the two observations.
use super::PublicationStore;
#[cfg(verus_keep_ghost)]
use crate::publication::{Publication, PublicationId, PublicationRegistry};
#[cfg(verus_keep_ghost)]
use crate::Port;
use vstd::prelude::*;

verus! {
impl<T> PublicationStore<T> {
    pub open spec fn exposes(&self,i:int,key:Port)->bool {
        0<=i<self.values().len() && self.registry_view().publications()[i].visible
            && self.registry_view().publications()[i].port==key
    }
    pub open spec fn lookup(&self,key:Port)->Option<T> {
        if exists|i:int| self.exposes(i,key) {
            let i=choose|i:int| self.exposes(i,key);
            self.values()[i]
        } else {None}
    }
    pub open spec fn visible_table(&self)->IMap<Port,T> {
        IMap::new(|key:Port|self.lookup(key).is_some(),|key:Port|self.lookup(key).unwrap())
    }
    pub proof fn visible_at(&self,i:int,key:Port)
        requires self.wf(),self.exposes(i,key),
        ensures self.lookup(key)==self.values()[i],self.lookup(key).is_some(),
    {
        reveal(PublicationRegistry::wf);
        let selected=choose|j:int|self.exposes(j,key);
        if selected<i {assert(!self.registry_view().publications()[selected].visible);}
        if i<selected {assert(!self.registry_view().publications()[i].visible);}
        assert(selected==i);
    }

    pub proof fn appended_value(&self,prior:&Self,owner:usize,generation:u64,key:Port,value:T)
        requires self.wf(),prior.wf(),self.values()==prior.values().push(Some(value)),
            self.registry_view().publications()==prior.registry_view().publications().push(
                Publication {owner,generation,port:key,slot:prior.values().len() as usize,visible:true,retained:true}),
        ensures prior.lookup(key).is_none(),
            self.visible_table()==crate::coeffects::put(prior.visible_table(),key,Some(value)),
            forall|query:Port| self.lookup(query)==if query==key {Some(value)} else {prior.lookup(query)},
    {
        let n=prior.values().len() as int;
        self.visible_at(n,key);
        reveal(PublicationRegistry::wf);
        if prior.lookup(key).is_some() {
            let i=choose|i:int|prior.exposes(i,key);
            assert(self.registry_view().publications()[i].visible);
            assert(self.registry_view().publications()[n].visible);
            assert(false);
        }
        assert forall|query:Port| self.lookup(query)==if query==key {Some(value)} else {prior.lookup(query)} by {
            if query!=key {
                if prior.lookup(query).is_some() {
                    let i=choose|i:int|prior.exposes(i,query);
                    prior.visible_at(i,query);self.visible_at(i,query);
                } else if self.lookup(query).is_some() {
                    let i=choose|i:int|self.exposes(i,query);
                    assert(i!=n);assert(prior.exposes(i,query));prior.visible_at(i,query);
                }
            }
        }
        assert(self.visible_table() =~= prior.visible_table().insert(key,value));
    }

    pub proof fn replaced_value(&self,prior:&Self,id:PublicationId,value:T)
        requires self.wf(),prior.wf(),id.0<prior.values().len(),prior.registry_view().publications()[id.0 as int].visible,
            self.registry_view().publications()==prior.registry_view().publications(),
            self.values()==prior.values().update(id.0 as int,Some(value)),
        ensures self.visible_table()==crate::coeffects::put(prior.visible_table(),prior.registry_view().publications()[id.0 as int].port,Some(value)),
            prior.lookup(prior.registry_view().publications()[id.0 as int].port)==prior.values()[id.0 as int],
    {
        let key=prior.registry_view().publications()[id.0 as int].port;
        prior.visible_at(id.0 as int,key);self.visible_at(id.0 as int,key);
        assert forall|query:Port| self.lookup(query)==if query==key {Some(value)} else {prior.lookup(query)} by {
            if query!=key {
                if prior.lookup(query).is_some() {
                    let i=choose|i:int|prior.exposes(i,query);
                    assert(i!=id.0);prior.visible_at(i,query);self.visible_at(i,query);
                } else if self.lookup(query).is_some() {
                    let i=choose|i:int|self.exposes(i,query);
                    assert(prior.exposes(i,query));prior.visible_at(i,query);
                }
            }
        }
        assert(self.visible_table() =~= prior.visible_table().insert(key,value));
    }

    pub proof fn revoked_value(&self,prior:&Self,id:PublicationId)
        requires self.wf(),prior.wf(),id.0<prior.values().len(),self.values()==prior.values(),
            self.registry_view().publications()==prior.registry_view().publications().update(id.0 as int,
                Publication {visible:false,..prior.registry_view().publications()[id.0 as int]}),
        ensures self.visible_table()==if prior.registry_view().publications()[id.0 as int].visible {
            prior.visible_table().remove(prior.registry_view().publications()[id.0 as int].port)
        } else {prior.visible_table()},
    {
        let key=prior.registry_view().publications()[id.0 as int].port;
        let removed=prior.registry_view().publications()[id.0 as int].visible;
        assert forall|query:Port| self.lookup(query)==if removed && query==key {None} else {prior.lookup(query)} by {
            if removed && query==key {
                reveal(PublicationRegistry::wf);
                if self.lookup(query).is_some() {
                    let i=choose|i:int|self.exposes(i,query);
                    assert(i!=id.0);prior.visible_at(i,query);prior.visible_at(id.0 as int,query);
                    if i<id.0 {assert(!prior.registry_view().publications()[i].visible);}
                    else {assert(!prior.registry_view().publications()[id.0 as int].visible);}
                    assert(false);
                }
            } else if prior.lookup(query).is_some() {
                let i=choose|i:int|prior.exposes(i,query);
                assert(i!=id.0);prior.visible_at(i,query);self.visible_at(i,query);
            } else if self.lookup(query).is_some() {
                let i=choose|i:int|self.exposes(i,query);
                assert(i!=id.0);assert(prior.exposes(i,query));prior.visible_at(i,query);
            }
        }
        if removed {assert(self.visible_table() =~= prior.visible_table().remove(key));}
        else {assert(self.visible_table() =~= prior.visible_table());}
    }

    /// Metadata-only lease steps and destruction of already revoked values
    /// preserve current lookup. The retained/leased observation can still change.
    pub proof fn visible_frame(&self,prior:&Self)
        requires self.wf(),prior.wf(),self.values().len()==prior.values().len(),
            forall|i:int| 0<=i<prior.values().len() ==> {
                &&& self.registry_view().publications()[i].visible==prior.registry_view().publications()[i].visible
                &&& self.registry_view().publications()[i].visible ==> self.registry_view().publications()[i].port==prior.registry_view().publications()[i].port && self.values()[i]==prior.values()[i]
            },
        ensures self.visible_table()==prior.visible_table(),
    {
        assert forall|key:Port| self.lookup(key)==prior.lookup(key) by {
            if self.lookup(key).is_some() {
                let i=choose|i:int|self.exposes(i,key);
                self.visible_at(i,key);prior.visible_at(i,key);
            } else if prior.lookup(key).is_some() {
                let i=choose|i:int|prior.exposes(i,key);
                self.visible_at(i,key);prior.visible_at(i,key);
            }
        }
        assert(self.visible_table() =~= prior.visible_table());
    }
}
}
