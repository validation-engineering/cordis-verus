//! An ordinary Rust adapter over the actual recorded NativeRuntime APIs.
//! Expectations live in the independent campaign runner, never in this executor.
use cordis_kernel::{
    action_ledger::ActionTicket,
    cleanup_groups::payload::Dispatch,
    cleanup_journal::RestoreTicket,
    cleanup_queue::completion::{CleanupDispatch, CleanupPolicy},
    lifecycle_state::{
        native::runtime::NativeRuntime,
        registration::{
            shared_child::{ChildCleanup, ChildDispatch, SharedChild},
            PluginDefinition,
        },
    },
    reversible_value::{
        effect::Instruction,
        function::Body,
        managed::{
            interleaving::history::lifecycle::RecordedExecution, Call, Effect, Function, Owner,
            Slot,
        },
        Branch, Inverse, Operation, ReversibleValue,
    },
    Binding, Port,
};
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use std::{
    collections::BTreeMap,
    panic::{catch_unwind, AssertUnwindSafe},
    sync::Arc,
};

type World = NativeRuntime<Body<(), Function<Operation, ()>>, (), Slot<(), ()>>;
type Starting = Owner<ChildDispatch<(), ()>, (), (), (), (), (), ()>;
type Recorded = RecordedExecution<ChildDispatch<(), ()>, (), (), (), (), (), ()>;

#[derive(Clone, Copy, Debug, Deserialize, Serialize, PartialEq, Eq, PartialOrd, Ord)]
#[serde(rename_all = "snake_case")]
pub enum Actor {
    Provider,
    Consumer,
    Child,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(tag = "op", rename_all = "snake_case", deny_unknown_fields)]
pub enum Action {
    Register {
        actor: Actor,
    },
    Start {
        actor: Actor,
        #[serde(default)]
        revision: Option<usize>,
    },
    Spawn,
    Replace,
    Withdraw {
        actor: Actor,
    },
    Retire {
        actor: Actor,
    },
    RetireChild,
    BeginCleanup {
        actor: Actor,
    },
    Restore {
        actor: Actor,
        ticket: String,
    },
    Fail {
        actor: Actor,
    },
    Retry {
        actor: Actor,
    },
    Reply {
        actor: Actor,
        ticket: String,
    },
    Release {
        actor: Actor,
    },
    Remove {
        actor: Actor,
    },
    Write {
        revision: usize,
        amount: u64,
        inverse: String,
    },
    UndoWrite {
        inverse: String,
    },
    Observe,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Parameters {
    values: Vec<u64>,
    consumer_delta: u64,
    child_delta: u64,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Step {
    action: Action,
    expect: Value,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Scenario {
    schema: String,
    profile: String,
    id: String,
    seed: u64,
    generator: String,
    category: String,
    families: Vec<String>,
    purpose: String,
    parameters: Parameters,
    commands: Vec<Step>,
}

#[derive(Debug)]
enum Issue {
    Invalid(&'static str),
    Rejected(String),
}
fn rejected(error: impl std::fmt::Debug) -> Issue {
    Issue::Rejected(format!("{error:?}"))
}
fn port(key: u64) -> Port {
    Port { key, realm: 0 }
}
fn branch() -> Branch {
    Branch {
        matched: None,
        unmatched: None,
    }
}
fn body(add: Option<u64>) -> Body<(), Function<Operation, ()>> {
    Body::Managed(
        Function::new(
            add.map(|amount| {
                vec![Call {
                    key: 1,
                    effect: Effect::Kernel(Instruction::Operation(Operation::Add(amount))),
                    branch: branch(),
                }]
            })
            .unwrap_or_default(),
        )
        .ok()
        .unwrap(),
    )
}
fn action_ticket(ticket: ActionTicket) -> Value {
    json!({"domain":ticket.domain,"owner":ticket.id,"generation":ticket.generation,
        "action":ticket.action,"kind":format!("{:?}",ticket.kind)})
}
fn restore_ticket(ticket: RestoreTicket) -> Value {
    json!({"domain":ticket.domain,"attempt":ticket.attempt,"token":ticket.token})
}
fn bindings(items: Vec<Binding>) -> Value {
    json!(items
        .iter()
        .map(|b| json!({"key":b.key,"realm":b.realm,"provider":b.provider}))
        .collect::<Vec<_>>())
}
fn ok(data: Value) -> Value {
    json!({"status":"ok","data":data})
}

struct Machine {
    world: World,
    values: Vec<ReversibleValue>,
    marker: ReversibleValue,
    roles: BTreeMap<Actor, usize>,
    labels: BTreeMap<usize, Actor>,
    owners: BTreeMap<usize, Recorded>,
    children: Vec<SharedChild>,
    tickets: BTreeMap<String, RestoreTicket>,
    writes: BTreeMap<String, Inverse>,
    actions: Vec<ActionTicket>,
    next_work: u64,
    consumer_delta: u64,
    child_delta: u64,
}

impl Machine {
    fn new(parameters: &Parameters) -> Self {
        let world = World::new_recorded(790_000, 8192);
        let values = parameters
            .values
            .iter()
            .map(|value| ReversibleValue::new_in(&world.execution_journal(), *value))
            .collect();
        let marker = ReversibleValue::new_in(&world.execution_journal(), 0);
        Self {
            world,
            values,
            marker,
            roles: BTreeMap::new(),
            labels: BTreeMap::new(),
            owners: BTreeMap::new(),
            children: Vec::new(),
            tickets: BTreeMap::new(),
            writes: BTreeMap::new(),
            actions: Vec::new(),
            next_work: 790_001,
            consumer_delta: parameters.consumer_delta,
            child_delta: parameters.child_delta,
        }
    }
    fn id(&self, actor: Actor) -> Result<usize, Issue> {
        self.roles
            .get(&actor)
            .copied()
            .ok_or(Issue::Invalid("actor has not been registered"))
    }
    fn owner(&mut self, actor: Actor) -> Result<&mut Recorded, Issue> {
        let id = self.id(actor)?;
        self.owners
            .get_mut(&id)
            .ok_or(Issue::Invalid("actor has no execution"))
    }
    fn start(&mut self, actor: Actor, revision: Option<usize>) -> Result<Value, Issue> {
        let id = self.id(actor)?;
        let value = if actor == Actor::Provider {
            Some(
                self.values
                    .get(revision.ok_or(Issue::Invalid("provider needs a revision"))?)
                    .ok_or(Issue::Invalid("revision out of range"))?
                    .clone(),
            )
        } else if actor == Actor::Consumer {
            Some(self.marker.clone())
        } else {
            None
        };
        let execution: Starting = self
            .world
            .begin_managed_execution(id, self.next_work)
            .map_err(rejected)?;
        self.next_work += 1;
        let (mut execution, result) = self.world.run_recorded_root(id, execution);
        let result = result
            .map_err(rejected)
            .and_then(|r| r.result.map_err(rejected));
        if let Err(error) = result {
            self.owners.insert(id, execution);
            return Err(error);
        }
        if let Some(value) = value {
            let key = if actor == Actor::Provider { 1 } else { 2 };
            if execution
                .provide(
                    port(key),
                    Arc::new(Slot::new_reversible(Arc::new(value), ())),
                )
                .is_err()
            {
                self.owners.insert(id, execution);
                return Err(Issue::Rejected("publication rejected".into()));
            }
        }
        let result = execution.finish(&mut self.world, id);
        let ticket = execution.execution().lifecycle_ticket().map(action_ticket);
        self.owners.insert(id, execution);
        result.map_err(rejected)?;
        Ok(ok(json!({"id":id,"setup":ticket})))
    }
    fn spawn(&mut self) -> Result<Value, Issue> {
        let parent = self.id(Actor::Consumer)?;
        let owner = self
            .owners
            .get_mut(&parent)
            .ok_or(Issue::Invalid("parent has no execution"))?;
        let (handle, _) = owner.enqueue_native_child(0, ()).map_err(rejected)?;
        let item = owner
            .take_child()
            .ok_or(Issue::Invalid("no actual Child request"))?;
        let world = &mut self.world;
        let work = self.next_work;
        self.next_work += 1;
        let delta = self.child_delta;
        let reply = item.run(|request| -> Result<(usize, Recorded), Issue> {
            let ChildDispatch::Native(request) = request else {
                return Err(Issue::Invalid("non-native request"));
            };
            let (_, child) = request.into_parts();
            let id = world
                .register_shared_child(
                    &child,
                    &BTreeMap::new(),
                    port(102),
                    PluginDefinition::new(vec![1, 2], vec![], body(Some(delta))),
                    (),
                )
                .result
                .map_err(|e| rejected(e.0))?;
            let execution: Starting = world.begin_managed_execution(id, work).map_err(rejected)?;
            let (mut execution, report) = world.run_recorded_root(id, execution);
            report.map_err(rejected)?.result.map_err(rejected)?;
            execution.finish(world, id).map_err(rejected)?;
            Ok((id, execution))
        });
        let result = owner
            .complete_request(reply)
            .map_err(|_| Issue::Invalid("real request completion rejected"))?;
        self.children.push(handle);
        let (id, execution) = result?;
        self.roles.insert(Actor::Child, id);
        self.labels.insert(id, Actor::Child);
        self.owners.insert(id, execution);
        Ok(ok(json!({"id":id,"parent":parent})))
    }
    fn restore(&mut self, actor: Actor, label: &str) -> Result<Value, Issue> {
        if self.tickets.contains_key(label) {
            return Err(Issue::Invalid("duplicate ticket label"));
        }
        let id = self.id(actor)?;
        let owner = self
            .owners
            .get_mut(&id)
            .ok_or(Issue::Invalid("actor has no execution"))?;
        let dispatch = owner.dispatch(0).map_err(rejected)?;
        let dispatch = match dispatch {
            Some(Dispatch::Other(dispatch)) => dispatch,
            None => return Ok(json!({"status":"empty"})),
            Some(_) => return Err(Issue::Invalid("non-scalar dispatch outside this profile")),
        };
        match dispatch {
            CleanupDispatch::Value { ticket, completion } => {
                self.tickets.insert(label.to_owned(), ticket);
                Ok(
                    json!({"status":if completion.report.result.is_ok(){"restored"}else{"retained"},
                    "kind":"value","ticket":restore_ticket(ticket),
                    "error":completion.report.result.err().map(|e| format!("{e:?}"))}),
                )
            }
            CleanupDispatch::Host {
                ticket,
                action: ChildCleanup::Native(handle),
            } => {
                self.tickets.insert(label.to_owned(), ticket);
                let result = self.world.retire_shared_child(&handle).result;
                let retired = result
                    .as_ref()
                    .ok()
                    .and_then(|v| v.as_ref().map(|child| child.id()));
                let succeeded = result.is_ok();
                owner
                    .complete_result(
                        0,
                        ticket,
                        result.map(|_| ()),
                        None,
                        CleanupPolicy::RetainFailure,
                    )
                    .map_err(|_| Issue::Invalid("actual Child completion rejected"))?;
                Ok(
                    json!({"status":if succeeded{"restored"}else{"retained"},"kind":"child",
                    "child":retired,"ticket":restore_ticket(ticket)}),
                )
            }
            _ => Err(Issue::Invalid(
                "unsupported cleanup payload in native scalar profile",
            )),
        }
    }
    fn perform(&mut self, action: &Action) -> Result<Value, Issue> {
        match action {
            Action::Register { actor } => {
                if self.roles.contains_key(actor) {
                    return Err(Issue::Invalid("duplicate role"));
                }
                let (anchor, deps, provisions, add) = match actor {
                    Actor::Provider => (100, vec![], vec![1], None),
                    Actor::Consumer => (101, vec![1], vec![2], Some(self.consumer_delta)),
                    Actor::Child => return Err(Issue::Invalid("use the real Child request")),
                };
                let id = self
                    .world
                    .register(
                        None,
                        &BTreeMap::new(),
                        port(anchor),
                        PluginDefinition::new(deps, provisions, body(add)),
                        (),
                    )
                    .map_err(|e| rejected(e.0))?;
                self.roles.insert(*actor, id);
                self.labels.insert(id, *actor);
                Ok(ok(json!({"id":id})))
            }
            Action::Start { actor, revision } => self.start(*actor, *revision),
            Action::Spawn => self.spawn(),
            Action::Replace => {
                self.world
                    .replace(self.id(Actor::Provider)?, body(None))
                    .map_err(|e| rejected(e.0))?;
                Ok(ok(Value::Null))
            }
            Action::Withdraw { actor } => {
                let id = self.id(*actor)?;
                let owner = self
                    .owners
                    .get_mut(&id)
                    .ok_or(Issue::Invalid("actor has no execution"))?;
                owner
                    .withdraw(&mut self.world, id, false)
                    .map_err(rejected)?;
                self.world
                    .settle_managed_execution(id, owner.execution())
                    .map_err(rejected)?;
                Ok(ok(Value::Null))
            }
            Action::Retire { actor } => {
                self.world.retire(self.id(*actor)?).map_err(rejected)?;
                Ok(ok(Value::Null))
            }
            Action::RetireChild => {
                let handle = self
                    .children
                    .last()
                    .ok_or(Issue::Invalid("no Child handle"))?;
                let result = self
                    .world
                    .retire_shared_child(handle)
                    .result
                    .map_err(rejected)?;
                Ok(ok(json!({"id":result.map(|child|child.id())})))
            }
            Action::BeginCleanup { actor } => {
                let ticket = self
                    .world
                    .begin_cleanup(self.id(*actor)?)
                    .map_err(rejected)?;
                self.actions.push(ticket);
                Ok(ok(action_ticket(ticket)))
            }
            Action::Restore { actor, ticket } => self.restore(*actor, ticket),
            Action::Fail { actor } => {
                let id = self.id(*actor)?;
                let owner = self
                    .owners
                    .get(&id)
                    .ok_or(Issue::Invalid("actor has no execution"))?;
                self.world
                    .fail_managed_execution(id, owner.execution())
                    .map_err(rejected)?;
                Ok(ok(Value::Null))
            }
            Action::Retry { actor } => {
                let id = self.id(*actor)?;
                let owner = self
                    .owners
                    .get_mut(&id)
                    .ok_or(Issue::Invalid("actor has no execution"))?;
                let ticket = owner.retry_native(&mut self.world, id).map_err(rejected)?;
                self.actions.push(ticket);
                Ok(ok(action_ticket(ticket)))
            }
            Action::Reply { actor, ticket } => {
                let ticket = *self
                    .tickets
                    .get(ticket)
                    .ok_or(Issue::Invalid("ticket label has no receipt"))?;
                self.owner(*actor)?
                    .complete_result(
                        0,
                        ticket,
                        Ok::<(), ()>(()),
                        None,
                        CleanupPolicy::RetainFailure,
                    )
                    .map_err(|_| Issue::Rejected("stale or non-callback receipt".into()))?;
                Ok(ok(Value::Null))
            }
            Action::Release { actor } => {
                let id = self.id(*actor)?;
                let owner = self
                    .owners
                    .get_mut(&id)
                    .ok_or(Issue::Invalid("actor has no execution"))?;
                owner.release(&mut self.world, id).0.map_err(rejected)?;
                Ok(ok(Value::Null))
            }
            Action::Remove { actor } => {
                let id = self.id(*actor)?;
                self.world.remove(id).map_err(rejected)?;
                self.owners.remove(&id);
                Ok(ok(Value::Null))
            }
            Action::Write {
                revision,
                amount,
                inverse,
            } => {
                if self.writes.contains_key(inverse) {
                    return Err(Issue::Invalid("duplicate inverse label"));
                }
                let value = self
                    .values
                    .get(*revision)
                    .ok_or(Issue::Invalid("revision out of range"))?;
                let result = value
                    .apply(Operation::Add(*amount), branch())
                    .map_err(rejected)?;
                self.writes.insert(inverse.clone(), result.inverse);
                Ok(ok(Value::Null))
            }
            Action::UndoWrite { inverse } => {
                let item = self
                    .writes
                    .remove(inverse)
                    .ok_or(Issue::Invalid("inverse label has no write"))?;
                match item.restore() {
                    Ok(_) => Ok(ok(Value::Null)),
                    Err(retained) => {
                        self.writes.insert(inverse.clone(), retained);
                        Err(Issue::Rejected("raw inverse is blocked".into()))
                    }
                }
            }
            Action::Observe => Ok(ok(Value::Null)),
        }
    }
    fn snapshot(&self) -> Value {
        let plugins=self.world.ids().iter().map(|id| {
            let kernel=self.world.kernel();
            let execution=self.owners.get(id).map(|owner| {
                let execution=owner.execution();
                let queue=execution.get(0);
                json!({"ticket":execution.lifecycle_ticket().map(action_ticket),
                    "phase":format!("{:?}",execution.phase()),"belongs":self.world.matches_execution(*id,execution),
                    "failed":execution.has_failed(),"pending":execution.has_pending(),"issued":execution.has_issued(),
                    "canSeal":execution.can_seal(),"queues":execution.groups().len(),
                    "rootQueue":queue.map(|q|json!({"domain":q.domain(),"empty":q.is_empty(),
                        "failed":q.has_failed(),"canRetry":q.can_retry(),"issued":q.is_issued(),
                        "pending":q.is_pending(),"settled":q.is_settled()}))})
            });
            json!({"id":id,"role":self.labels[id],
                "parent":self.world.registration(*id).and_then(|r|r.parent()),
                "phase":format!("{:?}",kernel.phase(*id).unwrap()),"retired":kernel.retired(*id),
                "cleanupStarted":kernel.cleanup_started(*id),"blocked":self.world.lifecycle().blocked(*id),
                "pending":self.world.lifecycle().pending(*id).map(action_ticket),
                "target":kernel.target(*id).map(bindings),"committed":bindings(kernel.committed(*id)),"execution":execution})
        }).collect::<Vec<_>>();
        let values = self
            .values
            .iter()
            .map(|value| {
                let s = value.snapshot();
                json!({"value":s.value(),"depth":s.depth()})
            })
            .collect::<Vec<_>>();
        let children=self.children.iter().map(|handle|{let s=handle.snapshot();json!({
            "parent":handle.parent_id(),"generation":handle.generation(),"domain":handle.domain(),
            "id":s.identity().map(|id|id.id()),"pending":s.pending(),"cancelled":s.cancelled(),"failed":s.failed()})}).collect::<Vec<_>>();
        json!({"plugins":plugins,"values":values,"children":children,
            "publications":{"value":self.world.native_value(port(1)).is_some(),"marker":self.world.native_value(port(2)).is_some(),"retainedValues":self.world.value_count()},
            "actions":self.actions.iter().copied().map(action_ticket).collect::<Vec<_>>(),
            "tickets":self.tickets.iter().map(|(label,ticket)|(label,restore_ticket(*ticket))).collect::<BTreeMap<_,_>>(),
            "rawInverses":self.writes.keys().collect::<Vec<_>>()})
    }
}

pub fn run(input: Value) -> Value {
    let id = input.get("id").cloned().unwrap_or(Value::Null);
    let scenario: Scenario = match serde_json::from_value(input.clone()) {
        Ok(s) => s,
        Err(e) => return json!({"id":id,"status":"invalid","reason":e.to_string()}),
    };
    if scenario.schema != "cordis-verus.lifecycle-scenario/v1"
        || scenario.profile != "native-managed/v1"
        || scenario.commands.len() > 512
        || scenario.parameters.values.is_empty()
        || scenario.parameters.values.len() > 16
        || scenario.parameters.values.iter().any(|v| *v > 1_000_000)
        || scenario.parameters.consumer_delta > 1000
        || scenario.parameters.child_delta > 1000
    {
        return json!({"id":id,"status":"invalid","reason":"unsupported schema or bounded input limits"});
    }
    let mut machine = Machine::new(&scenario.parameters);
    let mut steps = Vec::new();
    let initial = machine.snapshot();
    for (index, step) in scenario.commands.iter().enumerate() {
        // Keep expectations in the input artifact, but never use them to
        // produce an outcome, resource snapshot or production history.
        let _ = &step.expect;
        let result = catch_unwind(AssertUnwindSafe(|| {
            let outcome = match machine.perform(&step.action) {
                Ok(outcome) => outcome,
                Err(Issue::Invalid(message)) => json!({"status":"invalid","reason":message}),
                Err(Issue::Rejected(message)) => json!({"status":"rejected","reason":message}),
            };
            json!({"index":index,"action":input["commands"][index]["action"],"outcome":outcome,"state":machine.snapshot()})
        }));
        match result {
            Ok(row) => steps.push(row),
            Err(_) => {
                return json!({"id":scenario.id,"status":"panicked","at":index,"initial":initial,"steps":steps})
            }
        }
    }
    json!({"id":scenario.id,"status":"executed","initial":initial,"steps":steps,
        "metadata":{"seed":scenario.seed,"generator":scenario.generator,"category":scenario.category,
            "families":scenario.families,"purpose":scenario.purpose,"observerHoldsValues":true}})
}
