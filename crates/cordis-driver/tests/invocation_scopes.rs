use cordis_driver::{Command, Driver, HostAction, ScopeHandle};
use serde_json::{json, Value};

fn mount(driver: &mut Driver, parent: Option<usize>) -> (usize, u64) {
    let id = driver.mount(parent, vec![], vec![]).unwrap();
    let ticket = driver
        .drive()
        .unwrap()
        .into_iter()
        .find_map(|action| match action {
            HostAction::Setup { id: found, ticket } if found == id => Some(ticket),
            _ => None,
        })
        .unwrap();
    let generation = ticket.generation;
    driver.complete(ticket, true, None).unwrap();
    (id, generation)
}
fn begin(driver: &mut Driver, id: usize, generation: u64) -> ScopeHandle {
    serde_json::from_value(
        driver
            .execute(Command::BeginScope { id, generation })
            .unwrap()["scope"]
            .clone(),
    )
    .unwrap()
}
fn finish(driver: &mut Driver, scope: ScopeHandle) {
    driver.execute(Command::FinishScope { scope }).unwrap();
}
fn wait(driver: &mut Driver, scopes: Vec<ScopeHandle>, target: usize) -> Value {
    driver
        .execute(Command::CheckScopeWait { scopes, target })
        .unwrap()
}

#[test]
fn completed_nested_scope_does_not_hide_ancestor_or_consume_sibling() {
    let mut driver = Driver::new().unwrap();
    let (owner, generation) = mount(&mut driver, None);
    let (child, child_generation) = mount(&mut driver, Some(owner));
    let parent = begin(&mut driver, owner, generation);
    let nested = begin(&mut driver, child, child_generation);
    let sibling = begin(&mut driver, child, child_generation);
    let before = driver.snapshot();
    let block = wait(&mut driver, vec![nested, parent], owner);
    assert_eq!(block["blocked"], true);
    assert_eq!(block["owner"], child.to_string());
    assert_eq!(
        driver.snapshot(),
        before,
        "wait checks never withdraw a provider"
    );
    finish(&mut driver, nested);
    let block = wait(&mut driver, vec![nested, parent], owner);
    assert_eq!(block["owner"], owner.to_string());
    assert_eq!(block["scope"], serde_json::to_value(parent).unwrap());
    assert_eq!(
        driver
            .execute(Command::ScopesLive {
                scopes: vec![nested, sibling]
            })
            .unwrap(),
        json!({"live":true})
    );
    let before = driver.snapshot();
    assert_eq!(
        driver
            .execute(Command::FinishScope { scope: nested })
            .unwrap_err()
            .code,
        "StaleAuthority"
    );
    assert_eq!(driver.snapshot(), before);
    finish(&mut driver, parent);
    assert_eq!(
        wait(&mut driver, vec![nested, parent], owner),
        json!({"blocked":false})
    );
    assert_eq!(driver.snapshot()["storage"]["invocationScopes"], 1);
    finish(&mut driver, sibling);
    assert_eq!(driver.snapshot()["storage"]["invocationScopes"], 0);
}

#[test]
fn foreign_unknown_and_stale_admissions_do_not_change_live_ownership() {
    let mut a = Driver::new().unwrap();
    let mut b = Driver::new().unwrap();
    let (owner, generation) = mount(&mut a, None);
    let (other, other_generation) = mount(&mut b, None);
    let scope = begin(&mut a, owner, generation);
    let foreign = begin(&mut b, other, other_generation);
    assert_eq!(scope.scope, foreign.scope);
    assert_ne!(scope.domain, foreign.domain);
    let unknown = ScopeHandle {
        scope: scope.scope + 1,
        ..scope
    };
    let before = a.snapshot();
    for invalid in [foreign, unknown, ScopeHandle { scope: 0, ..scope }] {
        assert_eq!(
            a.execute(Command::FinishScope { scope: invalid })
                .unwrap_err()
                .code,
            "InvalidAuthority"
        );
        assert_eq!(
            a.execute(Command::ScopesLive {
                scopes: vec![scope, invalid]
            })
            .unwrap_err()
            .code,
            "InvalidAuthority"
        );
        assert_eq!(
            a.execute(Command::CheckScopeWait {
                scopes: vec![invalid],
                target: owner
            })
            .unwrap_err()
            .code,
            "InvalidAuthority"
        );
    }
    assert_eq!(
        a.execute(Command::BeginScope {
            id: owner,
            generation: generation + 1
        })
        .unwrap_err()
        .code,
        "StaleEpisode"
    );
    assert_eq!(a.snapshot(), before);
    assert_eq!(wait(&mut a, vec![scope], owner)["blocked"], true);
    finish(&mut a, scope);
    finish(&mut b, foreign);
}

#[test]
fn stale_live_scope_is_rejected_and_completion_never_reuses_identity() {
    let mut driver = Driver::new().unwrap();
    let (owner, generation) = mount(&mut driver, None);
    let old = begin(&mut driver, owner, generation);
    // The ordinary host owes a scope receipt before changing the episode; an
    // unbalanced host cannot use an old live record to obtain wait admission.
    driver.retire(owner).unwrap();
    for action in driver.drive().unwrap() {
        if let HostAction::Cleanup { ticket, .. } = action {
            driver.complete(ticket, true, None).unwrap();
        }
    }
    driver.drive().unwrap();
    assert_eq!(
        driver
            .execute(Command::CheckScopeWait {
                scopes: vec![old],
                target: owner
            })
            .unwrap_err()
            .code,
        "StaleEpisode"
    );
    finish(&mut driver, old);
    let (next_owner, next_generation) = mount(&mut driver, None);
    for _ in 0..512 {
        let next = begin(&mut driver, next_owner, next_generation);
        assert!(next.scope > old.scope);
        assert_eq!(
            driver
                .execute(Command::FinishScope { scope: old })
                .unwrap_err()
                .code,
            "StaleAuthority"
        );
        assert_eq!(driver.snapshot()["storage"]["invocationScopes"], 1);
        finish(&mut driver, next);
        assert_eq!(driver.snapshot()["storage"]["invocationScopes"], 0);
    }
}

#[test]
fn scope_wire_preserves_large_identities_and_rejects_metadata_or_holding_override() {
    let handle = ScopeHandle {
        domain: u64::MAX,
        scope: u64::MAX - 1,
    };
    let encoded = serde_json::to_string(&handle).unwrap();
    assert_eq!(
        serde_json::from_str::<ScopeHandle>(&encoded).unwrap(),
        handle
    );
    for invalid in [
        json!({"domain":1,"scope":"1"}),
        json!({"domain":"1","scope":"1","id":"2"}),
    ] {
        assert!(serde_json::from_value::<ScopeHandle>(invalid).is_err());
    }
    let mut driver = Driver::new().unwrap();
    let (owner, generation) = mount(&mut driver, None);
    let scope = begin(&mut driver, owner, generation);
    let encoded = json!({"op":"check_scope_wait","scopes":[scope],"target":owner.to_string(),"holding":false}).to_string();
    assert_eq!(driver.command(&encoded).unwrap_err().code, "InvalidCommand");
    assert_eq!(wait(&mut driver, vec![scope], owner)["blocked"], true);
    finish(&mut driver, scope);
}

#[test]
fn captured_path_retains_completed_ancestors_without_ledger_tombstones() {
    let mut driver = Driver::new().unwrap();
    let (owner, generation) = mount(&mut driver, None);
    let (child, child_generation) = mount(&mut driver, Some(owner));
    let root = driver.begin_invocation(owner, generation, None).unwrap();
    let nested = driver
        .begin_invocation(child, child_generation, Some(&root))
        .unwrap();
    let escaped = driver
        .begin_invocation(child, child_generation, Some(&nested))
        .unwrap();
    driver.finish_invocation(&nested).unwrap();
    driver.finish_invocation(&escaped).unwrap();
    assert!(!driver.invocation_own_live(&escaped).unwrap());
    assert!(driver.invocation_live(&escaped).unwrap());
    let before = driver.snapshot();
    let block = driver.check_invocation_wait(&escaped, owner).unwrap();
    assert_eq!(block["blocked"], true);
    assert_eq!(block["owner"], owner.to_string());
    assert_eq!(driver.snapshot(), before);
    driver.finish_invocation(&root).unwrap();
    assert_eq!(driver.snapshot()["storage"]["invocationScopes"], 0);
    // An escaped completed context is a valid parent. It cannot revive any of
    // its ancestors, consume another callback or grow the live-record table.
    for _ in 0..256 {
        let current = driver
            .begin_invocation(child, child_generation, Some(&escaped))
            .unwrap();
        assert_eq!(
            driver.finish_invocation(&escaped).unwrap_err().code,
            "StaleAuthority"
        );
        assert!(driver.invocation_own_live(&current).unwrap());
        assert!(!driver.invocation_live(&escaped).unwrap());
        assert_eq!(driver.snapshot()["storage"]["invocationScopes"], 1);
        driver.finish_invocation(&current).unwrap();
        assert_eq!(driver.snapshot()["storage"]["invocationScopes"], 0);
    }
    assert_eq!(
        driver.check_invocation_wait(&escaped, owner).unwrap(),
        json!({"blocked":false})
    );
}

#[test]
fn captured_paths_reject_foreign_parents_and_stale_live_generations() {
    let mut a = Driver::new().unwrap();
    let mut b = Driver::new().unwrap();
    let (owner, generation) = mount(&mut a, None);
    let (other, other_generation) = mount(&mut b, None);
    let parent = a.begin_invocation(owner, generation, None).unwrap();
    let foreign = b.begin_invocation(other, other_generation, None).unwrap();
    let before = a.snapshot();
    assert!(
        matches!(a.begin_invocation(owner,generation,Some(&foreign)),Err(e) if e.code=="InvalidAuthority")
    );
    assert!(
        matches!(a.begin_invocation(owner,generation+1,Some(&parent)),Err(e) if e.code=="StaleEpisode")
    );
    assert_eq!(
        a.check_invocation_wait(&foreign, owner).unwrap_err().code,
        "InvalidAuthority"
    );
    assert_eq!(a.snapshot(), before);
    a.retire(owner).unwrap();
    for action in a.drive().unwrap() {
        if let HostAction::Cleanup { ticket, .. } = action {
            a.complete(ticket, true, None).unwrap();
        }
    }
    a.drive().unwrap();
    assert_eq!(
        a.check_invocation_wait(&parent, owner).unwrap_err().code,
        "StaleEpisode"
    );
    a.finish_invocation(&parent).unwrap();
    assert!(!a.invocation_live(&parent).unwrap());
    b.finish_invocation(&foreign).unwrap();
}
