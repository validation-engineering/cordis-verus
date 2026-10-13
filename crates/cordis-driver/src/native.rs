//! Ordinary Rust access to the checked native registration/lifecycle owner.
//! Domain allocation and scheduler policy are shared with the external adapter.
use super::{allocate_domain, coherent, decision, host_ticket, Decision, HostStatus};
use crate::{ActionTicket, DriverError};
use cordis_kernel::execution::Execution;
use cordis_kernel::lifecycle_actions::CleanupOutcome;
use cordis_kernel::lifecycle_state::native::runtime::NativeRuntime;
use cordis_kernel::lifecycle_state::native::NativeEntry;
use cordis_kernel::lifecycle_state::registration::shared_child::SharedChild;
use cordis_kernel::lifecycle_state::registration::{
    ChildIdentity, PluginDefinition, RegisteredInvocation, RegisteredPlugin,
};
use cordis_kernel::lifecycle_state::services::ReleasedNativeValues;
use cordis_kernel::setup_work::WorkReceipt;
use cordis_kernel::{Error, Kernel, Port};
use std::collections::BTreeMap;
use std::ops::Deref;
use std::sync::Arc;

pub struct NativeDriver<R, H, V> {
    state: NativeRuntime<R, H, V>,
}
impl<R, H, V> Deref for NativeDriver<R, H, V> {
    type Target = Kernel;
    fn deref(&self) -> &Kernel {
        self.state.kernel()
    }
}
impl<R, H, V> NativeDriver<R, H, V> {
    pub fn new() -> Result<Self, DriverError> {
        Ok(Self {
            state: NativeRuntime::new(allocate_domain()?),
        })
    }
    pub fn domain(&self) -> u64 {
        self.state.lifecycle().domain()
    }
    pub fn decision(&self, id: usize, status: HostStatus) -> Option<Decision> {
        decision(self.state.lifecycle(), id, status)
    }
    pub fn coherent(&self, id: usize, restart: bool) -> bool {
        coherent(self.state.kernel(), id, restart)
    }
    pub fn host(&self, id: usize) -> Option<&H> {
        self.state.host(id)
    }
    pub fn host_mut(&mut self, id: usize) -> Option<&mut H> {
        self.state.host_mut(id)
    }
    pub fn registration(&self, id: usize) -> Option<&RegisteredPlugin<R>> {
        self.state.registration(id)
    }
    pub fn ids(&self) -> Vec<usize> {
        self.state.ids()
    }
    pub fn len(&self) -> usize {
        self.state.len()
    }
    pub fn is_empty(&self) -> bool {
        self.state.is_empty()
    }
    pub fn register_plugin(
        &mut self,
        parent: Option<usize>,
        realms: &BTreeMap<u64, u64>,
        anchor: Port,
        definition: PluginDefinition<R>,
        host: H,
    ) -> Result<usize, (Error, PluginDefinition<R>, H)> {
        self.state
            .register(parent, realms, anchor, definition, host)
    }
    pub fn register_shared_child(
        &mut self,
        child: &SharedChild,
        realms: &BTreeMap<u64, u64>,
        anchor: Port,
        definition: PluginDefinition<R>,
        host: H,
    ) -> Result<usize, (Error, PluginDefinition<R>, H)> {
        self.state
            .register_shared_child(child, realms, anchor, definition, host)
            .result
    }
    pub fn retire_shared_child(
        &mut self,
        child: &SharedChild,
    ) -> Result<Option<ChildIdentity>, Error> {
        self.state.retire_shared_child(child).result
    }
    pub fn remove(&mut self, id: usize) -> Result<NativeEntry<R, H>, Error> {
        self.state.remove(id)
    }
    pub fn replace(&mut self, id: usize, payload: R) -> Result<R, (Error, R)> {
        self.state.replace(id, payload)
    }
    pub fn call_root<A, O>(
        &mut self,
        id: usize,
        invocation: RegisteredInvocation<A>,
    ) -> Result<WorkReceipt<O>, RegisteredInvocation<A>>
    where
        R: FnMut(A) -> O,
    {
        self.state.call(id, invocation)
    }
    pub fn native_value(&self, port: Port) -> Option<&Arc<V>> {
        self.state.native_value(port)
    }
    pub fn value_count(&self) -> usize {
        self.state.value_count()
    }
    pub fn begin_cleanup(&mut self, id: usize) -> Result<(), Error> {
        self.state.begin_cleanup(id).map(|_| ())
    }
    pub fn pending_action(&self, id: usize) -> Option<ActionTicket> {
        self.state.lifecycle().pending(id).map(host_ticket)
    }
    pub fn retire(&mut self, id: usize) -> Result<(), Error> {
        self.state.retire(id)
    }
    pub fn leave(&mut self, id: usize) -> Result<(), Error> {
        self.state.leave(id)
    }
    pub fn compact_bindings(&mut self) -> usize {
        self.state.compact_bindings()
    }
    pub fn compact_declarations(&mut self) -> usize {
        self.state.compact_declarations()
    }
    pub fn withdraw_managed_execution<C, G, I>(
        &mut self,
        id: usize,
        execution: &mut Execution<V, C, G, I>,
        retiring: bool,
    ) -> Result<(), Error> {
        self.state
            .withdraw_managed_execution(id, execution, retiring)
    }
    pub fn begin_managed_execution<C, G, I>(
        &mut self,
        id: usize,
        domain: u64,
    ) -> Result<Execution<V, C, G, I>, Error> {
        self.state.begin_managed_execution(id, domain)
    }
    pub fn finish_managed_execution<C, G, I>(
        &mut self,
        id: usize,
        execution: &mut Execution<V, C, G, I>,
    ) -> Result<(), Error> {
        self.state.finish_managed_execution(id, execution)
    }
    pub fn release_managed_execution<C, G, I>(
        &mut self,
        id: usize,
        execution: &mut Execution<V, C, G, I>,
    ) -> Result<(CleanupOutcome, ReleasedNativeValues<V>), Error> {
        self.state.release_managed_execution(id, execution)
    }
    pub fn admit_managed_root<C, G, I, A>(
        &self,
        id: usize,
        execution: &mut Execution<V, C, G, I>,
        argument: A,
    ) -> Result<RegisteredInvocation<A>, A> {
        self.state.admit_managed_root(id, execution, argument)
    }
    pub fn settle_managed_execution<C, G, I>(
        &mut self,
        id: usize,
        execution: &Execution<V, C, G, I>,
    ) -> Result<(), Error> {
        self.state.settle_managed_execution(id, execution)
    }
    pub fn fail_managed_execution<C, G, I>(
        &mut self,
        id: usize,
        execution: &Execution<V, C, G, I>,
    ) -> Result<(), Error> {
        self.state.fail_managed_execution(id, execution)
    }
    pub fn retry_managed_execution<C, G, I>(
        &mut self,
        id: usize,
        execution: &mut Execution<V, C, G, I>,
    ) -> Result<ActionTicket, Error> {
        self.state
            .retry_managed_execution(id, execution)
            .map(host_ticket)
    }
}
