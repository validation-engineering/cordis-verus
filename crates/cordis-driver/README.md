# cordis-driver

Value-independent command/action/completion driver over `cordis-kernel`. The
host executes callbacks only after the driver returns an action; it submits the
opaque domain, episode and action ticket when the callback has completed. The
driver never owns a JavaScript object or invokes user code.

This crate is ordinary Rust, with behavioral tests. Its scheduling adapter and
JSON boundary are not covered by the kernel's Verus proofs. Dynamic publication
uses the kernel publication ledger; availability filtering remains in this
adapter. In particular, a port remains declared by its owner until registry
removal, so replacing a revoked publication with a different still-registered
owner is not yet supported.

All protocol identities are decimal strings, including service and realm IDs.
The host owns value handles; a handle's payload never crosses the protocol.
Cleanup failure retains its episode and bindings, reporting a fault instead of
claiming successful resource restoration. An explicit cleanup retry is required.

The first ABI supports `mount`, `drive`, `complete`, `retire` (`dispose` alias),
`restart`, `retry_cleanup`, `validate`, `publish`, `set`, `revoke`, `resolve`
(`lookup` alias), and `snapshot`. `Drive` returns `actions` plus `released` value
handles that the executor may remove from its object table. Setup and cleanup
completions carry the exact emitted ticket. A canceled setup is still awaited;
there is no forced timeout pretending that an inverse has been recovered.

The logical epoch compares provider identities, not publication IDs. If one
provider revokes and republishes the same port before the next pump, an existing
consumer keeps its captured old slot without an unconditional restart. A new
consumer captures the new publication. `set` updates the existing slot and hence
is visible to its already committed consumers. All old leases must release
before the owner's restoration can finish. Availability changes observed by a
pump can still cause normal withdrawal and reactivation.

The current compatibility foundation intentionally does not implement profile
specific retry policies, reserve/seal child observers, check callback actions,
configuration transactions or module updates. An explicit `restart` clears a
setup failure latch. It does not silently retry a failed cleanup; failed cleanup
retains its dependency leases until the executor successfully completes a fresh
`retry_cleanup` action. Hosts must decide whether retrying their disposer is safe.
