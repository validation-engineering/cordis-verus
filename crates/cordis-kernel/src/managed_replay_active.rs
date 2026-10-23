//! A call locks only its actually visited payload allocations. The full Bank
//! and Archive remain the identity/history authority across calls and cleanup.
use super::{bank::Bank, inputs::Operand, mixed, Source};
use crate::reversible_value::effect::ScalarEffect;
use vstd::prelude::*;

verus! {
broadcast use vstd::seq_lib::group_seq_properties;
pub(crate) struct Selection<T:?Sized> {pub storage:mixed::Storage<T>,pub view:Bank<T>,pub indices:Vec<usize>}
pub(crate) fn select<E:ScalarEffect,T:?Sized>(bank:&Bank<T>,full:&Bank<T>,source:&Source<E,T>)->(out:Result<Selection<T>,mixed::Error>)
    requires bank.wf(),full.wf(),source.wf(),forall|i:int|0<=i<source.input_spec().len() ==> source.input_spec()[i].namespace(bank.namespace()),
        forall|storage:&mixed::Storage<T>|storage.matches(bank) && storage.canonical(bank) ==> storage.typed_view(bank,full),
    ensures out.is_ok() ==> out->Ok_0.storage.matches(bank) && out->Ok_0.view.wf() && out->Ok_0.storage.typed_view(bank,&out->Ok_0.view)
        && super::archive::projection::selected(full,&out->Ok_0.view,out->Ok_0.indices@),
{
    hide(crate::reversible_value::joint::valid);hide(crate::reversible_value::joint::step);
    let mut storage=mixed::Storage::new(bank);let ghost initial=storage;
    proof {assert(storage.typed_view(bank,full));}
    let mut indices:Vec<usize>=Vec::new();let mut i=0;
    while i<storage.payload_names.len()
        invariant storage.matches(bank),storage.typed_view(bank,full),i<=storage.payload_names.len(),indices.len()==i,forall|j:int|0<=j<i ==> (#[trigger] indices@[j])==j,
        decreases storage.payload_names.len()-i,
    {indices.push(i);i+=1;}
    let inputs=source.inputs();let mut i=0;
    while i<storage.payload_names.len()
        invariant bank.wf(),full.wf(),source.wf(),initial.matches(bank),initial.typed_view(bank,full),inputs@==source.input_spec(),
            forall|j:int|0<=j<inputs.len() ==> (#[trigger] inputs@[j]).wf() && inputs@[j].namespace(bank.namespace()),
            storage.matches(bank),i<=storage.payload_names.len(),indices.len()==storage.payload_names.len(),
            forall|j:int|0<=j<indices.len() ==> (#[trigger] indices@[j])<full.len_spec() && storage.payload_names@[j]==initial.payload_names@[indices@[j] as int],
            forall|j:int,k:int|0<=j<k<indices.len() ==> indices@[j]<indices@[k],
        decreases storage.payload_names.len()-i,
    {
        let entry=storage.payload_names[i];let mut j=0;let mut used=false;
        while j<inputs.len()
            invariant bank.wf(),source.wf(),inputs@==source.input_spec(),j<=inputs.len(),
                forall|k:int|0<=k<inputs.len() ==> (#[trigger] inputs@[k]).wf() && inputs@[k].namespace(bank.namespace()),
            decreases inputs.len()-j,
        {
            if matches!(inputs[j].operand(),Operand::Payload {..}) {
                let n=match bank.find(&inputs[j]) {Some(n)=>n,None=>return Err(mixed::Error::Input {step:j})};
                if n==entry {used=true;break;}
            }j+=1;
        }
        if used {i+=1;} else {
            let ghost before=storage;let ghost old_indices=indices@;
            storage.payload_names.remove(i);storage.payload_values.remove(i);storage.payload_slots.remove(i);indices.remove(i);
            proof {
                assert forall|j:int|0<=j<storage.scalar_names.len() implies #[trigger] storage.scalar_entry(bank,j) by {assert(before.scalar_entry(bank,j));}
                assert forall|j:int|0<=j<storage.payload_names.len() implies #[trigger] storage.payload_entry(bank,j) by {
                    let k=if j<i {j} else {j+1};assert(before.payload_entry(bank,k));
                }
                assert forall|j:int,k:int|0<=j<k<storage.payload_names.len() implies storage.payload_names@[j]<storage.payload_names@[k] by {
                    let a=if j<i {j} else {j+1};let b=if k<i {k} else {k+1};assert(before.payload_names@[a]<before.payload_names@[b]);
                }
                assert forall|j:int|0<=j<indices.len() implies (#[trigger] indices@[j])<full.len_spec() && storage.payload_names@[j]==initial.payload_names@[indices@[j] as int] by {
                    let k=if j<i {j} else {j+1};assert(indices@[j]==old_indices[k]);
                }
                assert forall|j:int,k:int|0<=j<k<indices.len() implies indices@[j]<indices@[k] by {
                    let a=if j<i {j} else {j+1};let b=if k<i {k} else {k+1};assert(old_indices[a]<old_indices[b]);
                }
                assert(storage.matches(bank));
            }
        }
    }
    let view=full.select(indices.as_slice());
    proof {
        assert forall|j:int|0<=j<view.len_spec() implies view.address(j)==bank.address(storage.payload_names@[j] as int)
            && (#[trigger] view.target(j))==bank.target(storage.payload_names@[j] as int) && view.service(j)==bank.service(storage.payload_names@[j] as int) by {
            assert(initial.payload_names@[indices@[j] as int]==storage.payload_names@[j]);
        }
    }
    Ok(Selection {storage,view,indices})
}
}
