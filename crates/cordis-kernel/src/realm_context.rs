//! Immutable realm environments shared by registration and actual callbacks.
//! Allocation freshness is supplied by the host; resolution and map updates
//! are checked here and do not reinterpret an existing episode's environment.
use crate::lifecycle_state::registration::resolve;
#[cfg(verus_keep_ghost)]
use crate::lifecycle_state::registration::resolved;
use crate::Port;
use std::collections::BTreeMap;
use std::sync::Arc;
use vstd::prelude::*;

verus! {
#[derive(Debug)]
pub struct RealmContext {realms:Arc<BTreeMap<u64,u64>>}
impl Clone for RealmContext {
    fn clone(&self)->(out:Self) ensures out==*self, {Self {realms:self.realms.clone()}}
}
impl Default for RealmContext {
    fn default()->(out:Self) ensures out.mapping()==Map::<u64,u64>::empty(),
    {Self::from_map(BTreeMap::new())}
}
impl RealmContext {
    pub closed spec fn mapping(&self)->Map<u64,u64> {self.realms@}
    pub fn from_map(realms:BTreeMap<u64,u64>)->(out:Self)
        ensures out.mapping()==realms@,
    {Self {realms:Arc::new(realms)}}
    pub fn as_map(&self)->(out:&BTreeMap<u64,u64>) ensures out@==self.mapping(), {&self.realms}
    pub fn resolve(&self,key:u64)->(out:Port) ensures out==resolved(self.mapping(),key),
    {resolve(&self.realms,key)}
    pub fn with_realm(&self,key:u64,realm:u64)->(out:Self)
        ensures out.mapping()==self.mapping().insert(key,realm),
    {let mut realms=(*self.realms).clone();realms.insert(key,realm);Self::from_map(realms)}
    pub fn share(&self,key:u64,source:&Self)->(out:Self)
        ensures out.mapping()==self.mapping().insert(key,resolved(source.mapping(),key).realm),
            resolved(out.mapping(),key)==resolved(source.mapping(),key),
    {self.with_realm(key,source.resolve(key).realm)}
}
}
