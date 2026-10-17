use cordis_kernel::configuration_batch::Action;
use cordis_kernel::configuration_recorded::{Load, Recorded};
use cordis_kernel::configuration_save::sources::Target;
use cordis_kernel::configuration_save::{Document, Stage, StepError};
use cordis_kernel::configuration_transaction::{Structure, StructureError, TransactionError};
use cordis_kernel::reversible_value::joint::Journal;
use std::collections::BTreeMap;
use std::task::Poll;

type Owner = Recorded<&'static str, u32, u8, u32, String, String>;

fn load(value: &str) -> Load<String, String> {
    Load {
        root: "root.json".into(),
        contents: BTreeMap::from([("root.json".into(), "loaded bytes".into())]),
        checkpoints: vec![("root.json".into(), value.into())],
        resolutions: BTreeMap::from([("alias.json".into(), "root.json".into())]),
    }
}

fn commit(owner: &mut Owner) {
    for expected in [
        Structure::Remove,
        Structure::SettleRemoved,
        Structure::Mount,
        Structure::SettleMounted,
    ] {
        assert_eq!(owner.structure(), Some(expected));
        assert!(owner
            .poll_structure::<(), _>(|_, _, _| Poll::Ready(Ok(())))
            .is_ready());
    }
    assert_eq!(
        owner.poll_update::<(), _>(|_, _| panic!("empty batch")),
        Poll::Ready(Ok(true))
    );
    assert_eq!(owner.structure(), Some(Structure::Adopt));
    assert_eq!(
        owner.poll_structure::<(), _>(|_, _, _| Poll::Ready(Ok(()))),
        Poll::Ready(Ok(true))
    );
    assert!(owner.commit().is_ok());
}

#[test]
fn shared_history_retains_sources_through_pending_failure_recovery_and_interleaving() {
    let journal = Journal::new();
    let mut owner = Owner::new_in(&journal, "accepted");
    let mut peer = Owner::new_in(&journal, "peer");
    owner.load_sources(load("base")).unwrap();
    peer.load_sources(load("peer base")).unwrap();
    let before = owner.source_snapshot();
    assert!(owner
        .begin_structural("candidate", 0, vec![Action::new(1, 0)])
        .is_ok());
    assert_eq!(
        owner.poll_structure::<&str, _>(|stage, accepted, pending| {
            assert_eq!((stage, *accepted), (Structure::Remove, "accepted"));
            pending.recovery += 1;
            // Same Journal, inside the real callback: no Journal lock may be held.
            peer.clear_sources().unwrap();
            assert_eq!(peer.refresh("peer refreshed"), Ok("peer"));
            Poll::Pending
        }),
        Poll::Pending
    );
    assert_eq!(owner.clear_sources(), Err(TransactionError::Pending));
    let rejected = owner.load_sources(load("rejected")).unwrap_err();
    assert_eq!(rejected.checkpoints, load("rejected").checkpoints);
    assert!(owner.save_stamp(7).is_none());
    assert_eq!(owner.sources().checkpoints()["root.json"].value, "base");
    assert_eq!(owner.pending().unwrap().recovery, 1);
    assert_eq!(
        owner.poll_structure(|_, _, pending| {
            pending.recovery += 1;
            Poll::Ready(Err("remove failed"))
        }),
        Poll::Ready(Err(StructureError::Callback("remove failed")))
    );
    assert_eq!(
        owner.poll_rollback::<(), _>(|_, _| panic!("unstarted action")),
        Poll::Ready(Ok(true))
    );
    assert!(owner.recover_with(|_| "too early").is_err());
    for expected in [
        Structure::RecoverRemove,
        Structure::RecoverSettleRemoved,
        Structure::RecoverMount,
        Structure::RecoverSettleMounted,
    ] {
        assert_eq!(owner.structure(), Some(expected));
        assert!(owner
            .poll_structure::<(), _>(|_, _, _| Poll::Ready(Ok(())))
            .is_ready());
    }
    assert!(owner
        .recover_with(|recovery| {
            assert_eq!(*recovery, 2);
            "reconstructed"
        })
        .is_ok());
    assert_eq!((*owner.current(), owner.revision()), ("reconstructed", 0));
    assert_eq!(owner.sources().checkpoints()["root.json"].value, "base");
    owner.load_sources(load("reloaded base")).unwrap();
    let after = owner.source_snapshot();
    // Both snapshots capture actual shared journal reads; their typed histories
    // and exact configuration associations are checked by the Verus contracts.
    drop((before, after, owner.snapshot(), peer.source_snapshot()));
    assert!(peer.sources().root().is_none());
    assert_eq!(peer.current(), &"peer refreshed");
    owner.clear_sources().unwrap();
    assert!(owner.sources().checkpoints().is_empty());
}

#[test]
fn save_failure_retry_and_old_revision_use_the_owned_source_checkpoint() {
    let journal = Journal::new();
    let mut owner = Owner::new_in(&journal, "accepted");
    let mut peer = Owner::new_in(&journal, "peer");
    owner.load_sources(load("base")).unwrap();
    peer.load_sources(load("peer base")).unwrap();
    let mut save = owner.save_stamp(7).unwrap().start(vec![Document::new(
        Target::new("root.json".into(), "saved intent".into(), ()),
        "before".into(),
        "after".into(),
        false,
        false,
    )]);
    loop {
        match save.step(|stage, _| {
            if stage == Stage::Sync {
                Err("directory sync failed")
            } else {
                Ok(())
            }
        }) {
            Ok(false) => {}
            Err(StepError::Callback("directory sync failed")) => break,
            result => panic!("unexpected save result: {result:?}"),
        }
    }
    let save = owner.accept_saved_sources(8, save).err().unwrap();
    assert_eq!(owner.sources().checkpoints()["root.json"].value, "base");
    assert!(owner.accept_saved_sources(7, save).is_ok());
    assert_eq!(
        owner.sources().checkpoints()["root.json"].value,
        "saved intent"
    );
    assert!(owner.sources().checkpoints()["root.json"].pending_sync);
    assert_eq!(peer.sources().checkpoints()["root.json"].value, "peer base");
    // A reload keeps the unresolved durability obligation for the actual key.
    owner.load_sources(load("saved intent")).unwrap();
    assert!(owner.sources().checkpoints()["root.json"].pending_sync);
    let checkpoint = &owner.sources().checkpoints()["root.json"];
    let mut retry = owner.save_stamp(7).unwrap().start(vec![Document::new(
        Target::new("root.json".into(), checkpoint.value.clone(), ()),
        "after".into(),
        "after".into(),
        checkpoint.pending_sync,
        false,
    )]);
    let mut stages = Vec::new();
    while !retry
        .step::<(), _>(|stage, _| {
            stages.push(stage);
            peer.clear_sources().unwrap();
            Ok(())
        })
        .unwrap()
    {}
    assert_eq!(stages, vec![Stage::Check, Stage::Sync]);
    assert!(owner.accept_saved_sources(7, retry).is_ok());
    assert!(!owner.sources().checkpoints()["root.json"].pending_sync);
    let stale = owner
        .save_stamp(7)
        .unwrap()
        .start::<Target<String, String, ()>>(vec![]);
    assert!(owner.begin_structural("next", 0, vec![]).is_ok());
    let stale = owner.accept_saved_sources(7, stale).err().unwrap();
    commit(&mut owner);
    assert!(owner.accept_saved_sources(7, stale).is_err());
    assert_eq!((*owner.current(), owner.revision()), ("next", 1));
    assert_eq!(
        owner.sources().checkpoints()["root.json"].value,
        "saved intent"
    );
    assert!(owner
        .accept_saved_sources(
            7,
            owner
                .save_stamp(7)
                .unwrap()
                .start::<Target<String, String, ()>>(vec![])
        )
        .is_ok());
    drop((owner.source_snapshot(), peer.source_snapshot()));
}
