# cordis-driver

Ordinary Rust adapters between the hosts and the verified state owners in
`cordis-kernel`. Shared scheduling policy chooses actions; the checked kernel
decides whether their state changes are admissible. The adapter itself is tested
ordinary Rust, not covered by a blanket Verus proof.

## Source entry points

| Path | Role |
| --- | --- |
| [shared.rs](src/shared.rs) | Shared scheduling decisions, domain allocation and lifecycle adapter |
| [shared/native.rs](src/shared/native.rs) | `shared::native::NativeDriver`, used by the Rust Runtime; owns the verified `NativeRuntime` |
| [node.rs](src/node.rs) | Internal Node adapter over the verified `NodeRuntime` |
| [lib.rs](src/lib.rs) | External command/action interface used by the Node binding |

The Native module's physical path matches its existing Rust module path. Moving
it does not introduce a second implementation or change its API.

## Protocol boundaries

The external interface uses decimal strings for identities and opaque handles
for host-owned values. Completion carries the emitted domain, episode and action
ticket. Failed retryable cleanup retains its dependencies; a later attempt needs
an explicit retry. A canceled setup is still awaited, and a timeout must not be
reported as successful restoration.

Provider identity, publication identity and value equality remain distinct.
Committed consumers retain their captured binding through the episode; publication
and lease guards control when old values can be released. The host executes the
actual callbacks and reports their results. Its payload associations and callback
effects remain explicit obligations.

Start review with the [cleanup protocol](../../docs/cleanup-protocol.md) and the
[provider/consumer/Child case](../../docs/cases/update-recovery.md). See
[architecture](../../docs/architecture.md) for the actual Rust and Node paths, and
[Node compatibility](../../docs/node-compatibility.md) for the supported external
interface and policy differences. The [verification plan](../../docs/verification-plan.md)
tracks structural cleanup and the retained paper-wide goals.
