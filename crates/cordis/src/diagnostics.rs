//! Payload-free lifecycle diagnostics. Snapshots do not drive the runtime.
use crate::{Binding, Phase, PluginId, Port};
use serde_json::{json, Value};

/// Record counts distinguish live work from retained identity tombstones.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct StorageStats {
    pub registered_plugins: usize,
    pub identity_slots: usize,
    pub declaration_records: usize,
    pub binding_records: usize,
    pub live_bindings: usize,
    /// Entries retained in the published-value table, including values kept
    /// during Unloading for committed consumers; not just resolvable services.
    pub published_values: usize,
}
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Compaction {
    pub removed_bindings: usize,
    pub removed_declarations: usize,
}
/// A reason progress may require another component or an external future.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Blocker {
    MissingDependencies(Vec<Port>),
    Failed(String),
    TargetChanged,
    SetupPending,
    EffectsPending(Vec<usize>),
    CommittedConsumers(Vec<PluginId>),
    CleanupPending,
    RetiringChildren(Vec<PluginId>),
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PluginSnapshot {
    pub id: PluginId,
    pub name: String,
    pub parent: Option<PluginId>,
    pub phase: Phase,
    pub retired: bool,
    pub restoring: bool,
    pub dependencies: Vec<Port>,
    pub provisions: Vec<Port>,
    pub committed: Vec<Binding>,
    pub target: Option<Vec<Binding>>,
    pub blockers: Vec<Blocker>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RuntimeSnapshot {
    pub plugins: Vec<PluginSnapshot>,
    pub storage: StorageStats,
}
fn ports(values: &[Port]) -> Value {
    json!(values
        .iter()
        .map(|p| json!({"key":p.key,"realm":p.realm}))
        .collect::<Vec<_>>())
}
fn bindings(values: &[Binding]) -> Value {
    json!(values
        .iter()
        .map(|b| json!({"key":b.key,"realm":b.realm,"provider":b.provider}))
        .collect::<Vec<_>>())
}
impl Blocker {
    fn json(&self) -> Value {
        match self {
            Self::MissingDependencies(p) => json!({"kind":"missing_dependencies","ports":ports(p)}),
            Self::Failed(message) => json!({"kind":"failed","message":message}),
            Self::TargetChanged => json!({"kind":"target_changed"}),
            Self::SetupPending => json!({"kind":"setup_pending"}),
            Self::EffectsPending(groups) => json!({"kind":"effects_pending","groups":groups}),
            Self::CommittedConsumers(ids) => json!({"kind":"committed_consumers","plugins":ids}),
            Self::CleanupPending => json!({"kind":"cleanup_pending"}),
            Self::RetiringChildren(ids) => json!({"kind":"retiring_children","plugins":ids}),
        }
    }
}
impl RuntimeSnapshot {
    /// A versioned diagnostic schema containing identities and status, never
    /// service payloads. Plugin names and failure messages are application text.
    pub fn to_json(&self) -> Value {
        let plugins: Vec<_> = self.plugins.iter().map(|p| json!({
            "id":p.id,"name":p.name,"parent":p.parent,"phase":format!("{:?}",p.phase),
            "retired":p.retired,"restoring":p.restoring,"dependencies":ports(&p.dependencies),
            "provisions":ports(&p.provisions),"committed":bindings(&p.committed),
            "target":p.target.as_deref().map(bindings),
            "blockers":p.blockers.iter().map(Blocker::json).collect::<Vec<_>>()
        })).collect();
        let s = &self.storage;
        json!({"schema":"cordis.runtime/v1","plugins":plugins,"storage":{
            "registered_plugins":s.registered_plugins,"identity_slots":s.identity_slots,
            "declaration_records":s.declaration_records,"binding_records":s.binding_records,
            "live_bindings":s.live_bindings,"published_values":s.published_values
        }})
    }
    /// Graphviz DOT: solid edges are committed service dependencies, dashed
    /// edges are ownership. Keeping them distinct avoids inventing dependencies.
    pub fn to_dot(&self) -> String {
        fn quote(s: &str) -> String {
            let mut out = String::new();
            for c in s.chars() {
                match c {
                    '\\' => out.push_str("\\\\"),
                    '"' => out.push_str("\\\""),
                    '\n' => out.push_str("\\n"),
                    '\r' => out.push_str("\\r"),
                    c if c.is_control() => out.push_str(&format!("\\\\u{{{:x}}}", c as u32)),
                    c => out.push(c),
                }
            }
            out
        }
        let mut dot = String::from("digraph cordis {\n");
        for p in &self.plugins {
            dot.push_str(&format!(
                "  n{} [label=\"{}: {}\\n{:?}\"];\n",
                p.id,
                p.id,
                quote(&p.name),
                p.phase
            ));
            if let Some(parent) = p.parent {
                dot.push_str(&format!(
                    "  n{} -> n{} [style=dashed,label=\"owns\"];\n",
                    parent, p.id
                ));
            }
            for b in &p.committed {
                dot.push_str(&format!(
                    "  n{} -> n{} [label=\"{}@{}\"];\n",
                    p.id, b.provider, b.key, b.realm
                ));
            }
        }
        dot.push_str("}\n");
        dot
    }
}
