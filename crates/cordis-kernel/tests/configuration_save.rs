use cordis_kernel::configuration_batch::Action;
use cordis_kernel::configuration_save::sources::{Source, Target};
use cordis_kernel::configuration_save::{Document, Save, Stage, StepError};
use cordis_kernel::configuration_transaction::Configuration;
use std::collections::BTreeMap;
use std::task::Poll;

fn changed(name: &str) -> Document<Target<String, String, ()>> {
    Document::new(
        Target::new(name.to_owned(), format!("saved:{name}"), ()),
        "old".into(),
        "new".into(),
        false,
        false,
    )
}

#[test]
fn io_failure_at_each_stage_preserves_the_processed_prefix_and_stops_dispatch() {
    let stages = [
        Stage::Check,
        Stage::Prepare,
        Stage::Recheck,
        Stage::Replace,
        Stage::Sync,
    ];
    for failed in stages {
        let config = Configuration::<(), (), (), ()>::new(());
        let mut save = config.save_stamp(7).unwrap().start(vec![
            changed("first"),
            changed("failed"),
            changed("last"),
        ]);
        let mut source = Source::new();
        let contents = BTreeMap::from([("root".into(), "loaded text".into())]);
        let resolutions = BTreeMap::from([("alias".into(), "root".into())]);
        source.load(
            "root".into(),
            contents.clone(),
            ["first", "failed", "last", "unmentioned"]
                .map(|name| (name.to_owned(), format!("base:{name}")))
                .into(),
            resolutions.clone(),
        );
        let mut calls = Vec::new();
        loop {
            match save.step(|stage, doc| {
                calls.push((doc.data().key.clone(), stage));
                if doc.data().key == "failed" && stage == failed {
                    Err("injected I/O error")
                } else {
                    Ok(())
                }
            }) {
                Ok(false) => {}
                Err(StepError::Callback(error)) => {
                    assert_eq!(error, "injected I/O error");
                    break;
                }
                other => panic!("unexpected progress: {other:?}"),
            }
        }
        assert_eq!(&calls[..5], &stages.map(|s| ("first".to_owned(), s)));
        assert_eq!(calls.last(), Some(&("failed".to_owned(), failed)));
        assert!(!calls.iter().any(|(name, _)| name == "last"));
        assert!(!save.complete());
        assert!(save.progress(0).unwrap().written);
        assert!(!save.progress(0).unwrap().durability_uncertain);
        let current = save.progress(1).unwrap();
        assert_eq!(current.written, failed == Stage::Sync);
        assert_eq!(current.remaining, failed != Stage::Sync);
        assert_eq!(current.durability_uncertain, failed == Stage::Sync);
        assert!(save.progress(2).unwrap().remaining);
        assert_eq!(
            save.step::<(), _>(|_, _| panic!("a halted save must not dispatch")),
            Err(StepError::Halted)
        );
        assert!(save.progress(3).is_none());
        assert!(config.accept_saved_sources(7, save, &mut source).is_ok());
        assert_eq!(source.root(), &Some("root".to_owned()));
        assert_eq!(source.contents(), &contents);
        assert_eq!(source.resolutions(), &resolutions);
        assert_eq!(source.checkpoints()["first"].value, "saved:first");
        assert!(!source.checkpoints()["first"].pending_sync);
        assert_eq!(
            source.checkpoints()["failed"].value,
            if failed == Stage::Sync {
                "saved:failed"
            } else {
                "base:failed"
            }
        );
        assert_eq!(
            source.checkpoints()["failed"].pending_sync,
            failed == Stage::Sync
        );
        assert_eq!(source.checkpoints()["last"].value, "base:last");
        assert_eq!(
            source.checkpoints()["unmentioned"].value,
            "base:unmentioned"
        );
    }
}

#[test]
fn unchanged_files_and_durability_retries_use_the_actual_stored_document() {
    let mut save = Save::new(vec![
        Document::new("unchanged", "same".into(), "same".into(), false, true),
        Document::new("retry", "same".into(), "same".into(), true, false),
        Document::new("write", "before".into(), "after".into(), false, true),
    ]);
    let mut calls = Vec::new();
    while !save
        .step::<(), _>(|stage, doc| {
            calls.push((*doc.data(), stage));
            if *doc.data() == "write" {
                assert_eq!(doc.observed(), "before");
                assert_eq!(doc.output(), "after");
            }
            Ok(())
        })
        .unwrap()
    {
        if calls.last() == Some(&("write", Stage::Replace)) {
            let state = save.progress(2).unwrap();
            assert!(state.written && state.durability_uncertain && !state.remaining);
        }
    }
    assert_eq!(
        calls,
        vec![
            ("unchanged", Stage::Check),
            ("retry", Stage::Check),
            ("retry", Stage::Sync),
            ("write", Stage::Check),
            ("write", Stage::Prepare),
            ("write", Stage::Recheck),
            ("write", Stage::Replace),
            ("write", Stage::Sync),
        ]
    );
    assert!(save.complete());
    for i in 0..3 {
        let progress = save.progress(i).unwrap();
        assert!(!progress.remaining && !progress.durability_uncertain);
        assert_eq!(progress.written, i == 2);
        assert_eq!(progress.unchanged, i != 2);
        assert_eq!(progress.merged_external, i != 1);
    }
    assert_eq!(
        save.step::<(), _>(|_, _| panic!("completed save must not dispatch")),
        Ok(true)
    );
    let mut empty = Save::<()>::new(vec![]);
    assert!(empty.complete());
    assert_eq!(
        empty.step::<(), _>(|_, _| panic!("empty save must not dispatch")),
        Ok(true)
    );
}

#[test]
fn save_stamp_rejects_pending_foreign_domain_and_revision_aba() {
    let mut config = Configuration::<u8, (), (), ()>::new(1);
    let stamp = config.save_stamp(10).unwrap();
    assert!(config.accepts_save(10, &stamp));
    assert!(!config.accepts_save(11, &stamp));
    for candidate in [2, 1] {
        assert!(config
            .begin(candidate, (), Vec::<Action<(), ()>>::new())
            .is_ok());
        assert!(config.save_stamp(10).is_none());
        assert!(!config.accepts_save(10, &stamp));
        assert!(config
            .poll_update::<(), _>(|_, _| Poll::Ready(Ok(())))
            .is_ready());
        assert!(config.commit().is_ok());
    }
    assert_eq!(*config.current(), 1);
    assert_eq!(config.revision(), 2);
    assert!(!config.accepts_save(10, &stamp));
    let fresh = config.save_stamp(10).unwrap();
    assert!(config.accepts_save(10, &fresh));
}

#[test]
fn source_acceptance_retains_the_review_and_last_processed_duplicate() {
    let mut config = Configuration::<u8, (), (), ()>::new(1);
    let mut source = Source::new();
    let document = |value| {
        Document::new(
            Target::new(1u8, value, ()),
            "same".into(),
            "same".into(),
            false,
            false,
        )
    };
    // Even successful I/O is insufficient without an original review stamp.
    let mut unreviewed = Save::new(vec![document("unreviewed")]);
    assert_eq!(unreviewed.step::<(), _>(|_, _| Ok(())), Ok(true));
    assert!(config
        .accept_saved_sources(10, unreviewed, &mut source)
        .is_err());
    assert!(source.checkpoints().is_empty());
    let mut save = config.save_stamp(10).unwrap().start(vec![
        document("first"),
        document("second"),
        document("not checked"),
    ]);
    assert_eq!(save.step::<(), _>(|_, _| Ok(())), Ok(false));
    assert_eq!(save.step::<(), _>(|_, _| Ok(())), Ok(false));
    assert_eq!(
        save.step(|_, _| Err("failed check")),
        Err(StepError::Callback("failed check"))
    );
    let save = config
        .accept_saved_sources(11, save, &mut source)
        .err()
        .unwrap();
    assert!(source.checkpoints().is_empty());
    assert!(config.accept_saved_sources(10, save, &mut source).is_ok());
    assert_eq!(source.checkpoints().len(), 1);
    assert_eq!(source.checkpoints()[&1].value, "second");
    assert!(!source.checkpoints()[&1].pending_sync);

    let mut save = config
        .save_stamp(10)
        .unwrap()
        .start(vec![document("old revision")]);
    assert_eq!(save.step::<(), _>(|_, _| Ok(())), Ok(true));
    assert!(config.begin(2, (), Vec::<Action<(), ()>>::new()).is_ok());
    let save = config
        .accept_saved_sources(10, save, &mut source)
        .err()
        .unwrap();
    assert_eq!(source.checkpoints()[&1].value, "second");
    assert!(config
        .poll_update::<(), _>(|_, _| Poll::Ready(Ok(())))
        .is_ready());
    assert!(config.commit().is_ok());
    let save = config
        .accept_saved_sources(10, save, &mut source)
        .err()
        .unwrap();
    assert_eq!(source.checkpoints()[&1].value, "second");
    assert!(save.complete());
    // A new revision must start new I/O, not re-stamp an executed cursor.
    let mut fresh = config
        .save_stamp(10)
        .unwrap()
        .start(vec![document("fresh revision")]);
    assert_eq!(fresh.step::<(), _>(|_, _| Ok(())), Ok(true));
    assert!(config.accept_saved_sources(10, fresh, &mut source).is_ok());
    assert_eq!(source.checkpoints()[&1].value, "fresh revision");
    source.clear();
    assert!(source.root().is_none() && source.checkpoints().is_empty());
}
