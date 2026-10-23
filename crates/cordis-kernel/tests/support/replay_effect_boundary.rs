//! Executable counterexample: the ScalarEffect return law permits shared writes.
//! This fixture is also checked by scripts/check-r3-effect-boundary.py.
#[cfg(verus_keep_ghost)]
use crate as cordis_kernel;
use cordis_kernel::identity_issuer::IdentityIssuer;
use cordis_kernel::reversible_value::{
    effect::{Decision, ScalarEffect},
    Branch, Operation, ReversibleValue,
};
use vstd::prelude::*;

verus! {
#[derive(Copy,Clone)]
pub struct OnSecond<'a> {pub calls:&'a IdentityIssuer,pub target:&'a ReversibleValue}
impl ScalarEffect for OnSecond<'_> {
    open spec fn model(&self)->cordis_kernel::reversible_value::effect::Code {Operation::Add(1).model()}
    fn compute(self,input:u64)->(out:Option<Decision>) {
        if let Ok(call)=self.calls.issue() {
            if call.get()>1 {
                let _write=self.target.apply(Operation::Add(0),Branch {matched:None,unmatched:None});
            }
        }
        Operation::Add(1).compute(input)
    }
}
}
