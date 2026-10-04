//! Owned transactions backed by the executable Verus resource store.
//! The verified primitives prove individual forward/inverse operations and
//! disjoint commutativity. Mutex synchronization and journal orchestration are
//! tested host code. Arbitrary I/O callbacks do not acquire these guarantees.
use crate::{AsyncSetup, Setup};
use cordis_kernel::resources::{Inverse, Store};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex};

#[derive(Clone)]
pub struct ReversibleStore {
    store: Arc<Mutex<Store>>,
    next_owner: Arc<AtomicU64>,
}
impl ReversibleStore {
    pub fn new(values: Vec<u64>) -> Self {
        Self {
            store: Arc::new(Mutex::new(Store::new(values))),
            next_owner: Arc::new(AtomicU64::new(1)),
        }
    }
    pub fn read(&self, index: usize) -> Option<u64> {
        self.store
            .lock()
            .expect("resource store poisoned")
            .read(index)
    }
    pub fn transaction(&self) -> Transaction {
        let owner = self
            .next_owner
            .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |n| n.checked_add(1))
            .expect("resource transaction identities exhausted");
        Transaction {
            inner: Arc::new(Mutex::new(Journal {
                store: self.store.clone(),
                owner,
                inverses: Vec::new(),
                closed: false,
            })),
        }
    }
}
struct Journal {
    store: Arc<Mutex<Store>>,
    owner: u64,
    inverses: Vec<Inverse>,
    closed: bool,
}
/// A shared transaction: writes serialize, rollback closes all clones and is
/// idempotent. Use Setup::reversible to attach rollback to a plugin episode.
/// Dropping a standalone transaction does not roll it back; rollback explicitly.
#[derive(Clone)]
pub struct Transaction {
    inner: Arc<Mutex<Journal>>,
}
impl Transaction {
    pub fn write(&self, index: usize, value: u64) -> Result<(), String> {
        let mut journal = self.inner.lock().map_err(|_| "resource journal poisoned")?;
        if journal.closed {
            return Err("resource transaction is closed".into());
        }
        let inverse = journal
            .store
            .lock()
            .map_err(|_| "resource store poisoned")?
            .write(journal.owner, index, value)
            .map_err(|e| format!("resource write: {e:?}"))?;
        journal.inverses.push(inverse);
        Ok(())
    }
    pub fn rollback(&self) -> Result<(), String> {
        let mut journal = self.inner.lock().map_err(|_| "resource journal poisoned")?;
        journal.closed = true;
        while let Some(inverse) = journal.inverses.pop() {
            let result = journal
                .store
                .lock()
                .map_err(|_| "resource store poisoned")?
                .undo(inverse);
            if let Err(inverse) = result {
                journal.inverses.push(inverse);
                return Err("resource inverse rejected: out-of-order or interfering write".into());
            }
        }
        Ok(())
    }
    pub fn is_closed(&self) -> bool {
        self.inner.lock().expect("resource journal poisoned").closed
    }
}
impl Setup<'_> {
    pub fn reversible(&mut self, store: &ReversibleStore) -> Transaction {
        let transaction = store.transaction();
        let cleanup = transaction.clone();
        self.on_cleanup(move || cleanup.rollback());
        transaction
    }
}
impl AsyncSetup {
    pub fn reversible(&self, store: &ReversibleStore) -> Result<Transaction, String> {
        let transaction = store.transaction();
        let cleanup = transaction.clone();
        self.on_cleanup(move || cleanup.rollback())?;
        Ok(transaction)
    }
}
