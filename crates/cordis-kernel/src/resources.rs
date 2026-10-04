//! A concrete reversible coeffect: exclusively owned integer cells.
//! Each write produces an opaque inverse; inverse application validates the
//! expected cell and preserves every other cell. No callback is assumed correct.
use vstd::prelude::*;

verus! {
#[derive(Copy, Clone, Debug, PartialEq, Eq, Structural)]
pub struct Cell { pub value: u64, pub owner: Option<u64>, pub depth: u64 }
#[derive(Copy, Clone, Debug, PartialEq, Eq, Structural)]
pub enum ResourceError { Unknown, Owned, Capacity, OutOfOrder }

// Intentionally neither Copy nor Clone: safe Rust cannot duplicate an inverse.
pub struct Inverse { index: usize, before: Cell, after: Cell }
impl Inverse {
    pub closed spec fn slot(&self) -> int { self.index as int }
    pub closed spec fn pre(&self) -> Cell { self.before }
    pub closed spec fn post(&self) -> Cell { self.after }
}
pub struct Store { cells: Vec<Cell> }

impl Store {
    pub closed spec fn view(&self) -> Seq<Cell> { self.cells@ }
    pub open spec fn valid_cell(cell: Cell) -> bool {
        (cell.owner.is_none() && cell.depth == 0) || (cell.owner.is_some() && cell.depth > 0)
    }
    pub closed spec fn wf(&self) -> bool {
        forall|i: int| 0 <= i < self.cells.len() ==> Self::valid_cell(self.cells[i])
    }
    pub fn new(values: Vec<u64>) -> (store: Self)
        ensures store.wf(), store.view().len() == values.len(),
            forall|i: int| 0 <= i < values.len() ==> store.view()[i] == (Cell { value: values[i], owner: None, depth: 0 }),
    {
        let mut cells = Vec::new();
        let mut i = 0;
        while i < values.len()
            invariant i <= values.len(), cells.len() == i,
                forall|j: int| 0 <= j < i ==> cells[j] == (Cell { value: values[j], owner: None, depth: 0 }),
            decreases values.len() - i,
        {
            cells.push(Cell { value: values[i], owner: None, depth: 0 });
            i += 1;
        }
        Store { cells }
    }
    pub fn read(&self, index: usize) -> (result: Option<u64>)
        ensures result == if index < self.view().len() { Some(self.view()[index as int].value) } else { None },
    {
        if index < self.cells.len() { Some(self.cells[index].value) } else { None }
    }
    pub fn resource_len(&self) -> (length:usize)
        ensures length == self.view().len(),
    { self.cells.len() }
    pub fn written(&self,index:usize) -> (yes:bool)
        ensures yes == (index < self.view().len() && self.view()[index as int].depth > 0),
    { index < self.cells.len() && self.cells[index].depth > 0 }
    pub fn write(&mut self, owner: u64, index: usize, value: u64) -> (result: Result<Inverse, ResourceError>)
        requires old(self).wf(),
        ensures final(self).wf(),
            result.is_err() ==> final(self).view() == old(self).view(),
            (index < old(self).view().len() && (old(self).view()[index as int].owner.is_none() || old(self).view()[index as int].owner == Some(owner))
                && old(self).view()[index as int].depth < u64::MAX) ==> result.is_ok(),
            result.is_ok() ==> {
                let inverse = result.unwrap();
                &&& inverse.slot() == index
                &&& 0 <= inverse.slot() < old(self).view().len()
                &&& inverse.pre() == old(self).view()[index as int]
                &&& inverse.post() == (Cell { value, owner: Some(owner), depth: (inverse.pre().depth + 1) as u64 })
                &&& final(self).view() == old(self).view().update(index as int, inverse.post())
                &&& Self::valid_cell(inverse.pre())
            },
    {
        if index >= self.cells.len() { return Err(ResourceError::Unknown); }
        let before = self.cells[index];
        if before.owner.is_some() && before.owner != Some(owner) { return Err(ResourceError::Owned); }
        if before.depth == u64::MAX { return Err(ResourceError::Capacity); }
        let after = Cell { value, owner: Some(owner), depth: before.depth + 1 };
        self.cells.set(index, after);
        Ok(Inverse { index, before, after })
    }
    /// Consume an inverse only if the current cell matches its post-state.
    /// Callers keep inverses with their originating store; no store ID is encoded.
    /// Rejection preserves both the store and the inverse for a later retry.
    pub fn undo(&mut self, inverse: Inverse) -> (result: Result<(), Inverse>)
        requires old(self).wf(), Self::valid_cell(inverse.pre()),
        ensures final(self).wf(),
            (0 <= inverse.slot() < old(self).view().len() && old(self).view()[inverse.slot()] == inverse.post()) ==> result.is_ok(),
            result.is_ok() ==> 0 <= inverse.slot() < old(self).view().len()
                && old(self).view()[inverse.slot()] == inverse.post()
                && final(self).view() == old(self).view().update(inverse.slot(), inverse.pre()),
            result.is_err() ==> final(self).view() == old(self).view()
                && result.unwrap_err().slot() == inverse.slot()
                && result.unwrap_err().pre() == inverse.pre() && result.unwrap_err().post() == inverse.post(),
    {
        if inverse.index >= self.cells.len() || self.cells[inverse.index] != inverse.after { return Err(inverse); }
        self.cells.set(inverse.index, inverse.before);
        Ok(())
    }
}

/// A witnessed write followed by its inverse restores exactly the prior cell,
/// while arbitrary independent changes to other cells remain untouched.
pub proof fn recovery(before: Seq<Cell>, intervened: Seq<Cell>, inverse: &Inverse)
    requires 0 <= inverse.slot() < before.len(), before.len() == intervened.len(),
        before[inverse.slot()] == inverse.pre(), intervened[inverse.slot()] == inverse.post(),
    ensures intervened.update(inverse.slot(), inverse.pre())[inverse.slot()] == before[inverse.slot()],
        forall|i: int| 0 <= i < before.len() && i != inverse.slot()
            ==> intervened.update(inverse.slot(), inverse.pre())[i] == intervened[i],
{ }

/// Disjoint forward writes commute. The same law applies to their inverses.
pub proof fn independent_updates(cells: Seq<Cell>, a: int, b: int, x: Cell, y: Cell)
    requires 0 <= a < cells.len(), 0 <= b < cells.len(), a != b,
    ensures cells.update(a, x).update(b, y) == cells.update(b, y).update(a, x),
{
    assert(cells.update(a, x).update(b, y) =~= cells.update(b, y).update(a, x));
}

/// No runtime checks or extra assumptions: prove and execute a complete episode.
pub fn round_trip(values: Vec<u64>, index: usize, owner: u64, value: u64) -> (store: Store)
    requires index < values.len(),
    ensures store.wf(), store.view().len() == values.len(),
        forall|i: int| 0 <= i < values.len() ==> store.view()[i] == (Cell { value: values[i], owner: None, depth: 0 }),
{
    let mut store = Store::new(values);
    let inverse = store.write(owner, index, value).unwrap();
    let _result = store.undo(inverse);
    assert(_result.is_ok());
    store
}
} // verus!
