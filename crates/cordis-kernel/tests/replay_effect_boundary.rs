//! Source success and a matching target input do not imply target success for
//! an extensible effect with hidden shared writes. No concurrent thread is used.
#[path = "support/replay_effect_boundary.rs"]
mod boundary;
use boundary::OnSecond;
use cordis_kernel::identity_issuer::IdentityIssuer;
use cordis_kernel::lifecycle_state::native::runtime::NativeRuntime;
use cordis_kernel::lifecycle_state::registration::PluginDefinition;
use cordis_kernel::reversible_value::{
    function::Body,
    managed::replay::Destination,
    managed::{Call, Effect, Function, Owner, Slot},
    Branch, ReversibleValue,
};
use cordis_kernel::Port;
use std::{collections::BTreeMap, sync::Arc};
type World<'a> = NativeRuntime<Body<(), Function<OnSecond<'a>, ()>>, (), Slot<(), ()>>;
type Episode = Owner<(), (), (), (), (), (), ()>;
fn port(key: u64) -> Port {
    Port { key, realm: 0 }
}
fn publish(world: &mut World<'_>, value: &ReversibleValue, work: u64) {
    let provider = world
        .register(
            None,
            &BTreeMap::new(),
            port(100),
            PluginDefinition::new(
                Vec::new(),
                vec![1],
                Body::Managed(Function::new(Vec::new()).ok().unwrap()),
            ),
            (),
        )
        .ok()
        .unwrap();
    let mut owner: Episode = world.begin_managed_execution(provider, work).unwrap();
    world.run_managed_root(provider, &mut owner).unwrap();
    owner
        .provide(
            port(1),
            Arc::new(Slot::new_reversible(Arc::new(value.clone()), ())),
        )
        .ok()
        .unwrap();
    world
        .finish_managed_execution(provider, &mut owner)
        .unwrap();
}
#[test]
fn verified_return_law_allows_source_success_and_target_interference() {
    let calls = IdentityIssuer::new();
    let source_value = ReversibleValue::new(5);
    let target_value = ReversibleValue::new(5);
    let effect = OnSecond {
        calls: &calls,
        target: &target_value,
    };
    let mut source = World::new(90_000);
    let mut target = World::new(91_000);
    publish(&mut source, &source_value, 90_001);
    publish(&mut target, &target_value, 91_001);
    let function = Function::new(vec![Call {
        key: 1,
        effect: Effect::Scalar(effect),
        branch: Branch {
            matched: None,
            unmatched: None,
        },
    }])
    .ok()
    .unwrap();
    let id = source
        .register(
            None,
            &BTreeMap::new(),
            port(101),
            PluginDefinition::new(vec![1], Vec::new(), Body::Managed(function)),
            (),
        )
        .ok()
        .unwrap();
    let owner: Episode = source.begin_managed_execution(id, 90_002).unwrap();
    let (_source_owner, captured) = source.run_replayable_root(id, owner);
    let captured = captured.unwrap();
    assert!(captured.report.result.as_ref().unwrap().failure.is_none());
    assert_eq!(
        (
            source_value.snapshot().value(),
            source_value.snapshot().depth()
        ),
        (6, 1)
    );
    assert_eq!(
        (
            target_value.snapshot().value(),
            target_value.snapshot().depth()
        ),
        (5, 0)
    );
    // The controlled entry rejects the same verified-but-effectful source
    // before registration or a second callback invocation. Reusing the anchor
    // below also checks that rejection left no inactive registration behind.
    assert!(!captured.source.is_controlled());
    let blocked: cordis_kernel::reversible_value::managed::replay::TargetOutcome<
        (),
        (),
        (),
        (),
        (),
        (),
        (),
        (),
        OnSecond<'_>,
    > = captured.source.instantiate_controlled(
        &mut target,
        Destination {
            parent: None,
            anchor: port(101),
            host: (),
            work_domain: 91_002,
        },
    );
    assert!(matches!(
        blocked,
        Err(cordis_kernel::reversible_value::managed::replay::StartError::ExternalEffect { .. })
    ));
    assert_eq!(
        (
            target_value.snapshot().value(),
            target_value.snapshot().depth()
        ),
        (5, 0)
    );
    let run: cordis_kernel::reversible_value::managed::replay::TargetRun<
        (),
        (),
        (),
        (),
        (),
        (),
        (),
        OnSecond<'_>,
    > = captured
        .source
        .instantiate(
            &mut target,
            Destination {
                parent: None,
                anchor: port(101),
                host: (),
                work_domain: 91_002,
            },
        )
        .ok()
        .unwrap();
    let report = run.report.as_ref().unwrap().result.as_ref().unwrap();
    assert!(report.steps.is_empty());
    assert!(matches!(
        report.failure.as_ref().unwrap().error,
        cordis_kernel::reversible_value::managed::Error::Scalar(
            cordis_kernel::reversible_value::effect::EffectError::Interference
        )
    ));
    assert_eq!(
        (
            target_value.snapshot().value(),
            target_value.snapshot().depth()
        ),
        (5, 1)
    );
    assert!(run.owner.execution().groups().get(0).unwrap().is_empty());
    // The model's decision is correct, but compute wrote the target before the
    // interpreter's guarded landing. Its unregistered inverse is not replayed.
}
