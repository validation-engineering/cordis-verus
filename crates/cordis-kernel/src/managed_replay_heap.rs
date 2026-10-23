//! Full-domain scalar transport through the identity map constructed by Bank.
//! Recovery inputs are arbitrary related heaps. Correspondence at the next
//! real call remains a separate execution/ownership obligation.
#[cfg(verus_keep_ghost)]
use crate::reversible_value::{alias, effect, service_composition::Address, Branch, ValueState};
use vstd::prelude::*;

verus! {
pub open spec fn injective(names:Map<Address,Address>)->bool {
    forall|a:Address,b:Address|names.contains_key(a) && names.contains_key(b)
        && #[trigger] names[a]==#[trigger] names[b] ==> a==b
}
/// Missing entries are observable failures. Unmapped target infrastructure is
/// permitted, but every mapped address has exactly the source value and depth.
pub open spec fn corresponds(names:Map<Address,Address>,source:Map<Address,ValueState>,target:Map<Address,ValueState>)->bool {
    forall|key:Address|names.contains_key(key) ==> {
        &&& source.contains_key(key)==target.contains_key(#[trigger] names[key])
        &&& source.contains_key(key) ==> source[key]==target[names[key]]
    }
}
pub proof fn write(names:Map<Address,Address>,source:Map<Address,ValueState>,target:Map<Address,ValueState>,key:Address,value:ValueState)
    requires injective(names),corresponds(names,source,target),names.contains_key(key),
    ensures corresponds(names,source.insert(key,value),target.insert(names[key],value)),
{
    assert forall|other:Address|names.contains_key(other) implies {
        &&& source.insert(key,value).contains_key(other)==target.insert(names[key],value).contains_key(#[trigger] names[other])
        &&& source.insert(key,value).contains_key(other) ==> source.insert(key,value)[other]==target.insert(names[key],value)[names[other]]
    } by {if other!=key {assert(names[other]!=names[key]);}}
}
pub open spec fn contract(names:Map<Address,Address>,source:Map<Address,ValueState>,target:Map<Address,ValueState>,key:Address,code:effect::Code,branch:Branch)->bool {
    let left=crate::dependent_grammar::run(alias::library(),alias::node(key,code,branch),source);
    let right=crate::dependent_grammar::run(alias::library(),alias::node(names[key],code,branch),target);
    &&& left.is_some()==right.is_some()
    &&& left.is_some() ==> {
        &&& corresponds(names,left.unwrap().state,right.unwrap().state)
        &&& left.unwrap().next==right.unwrap().next
        &&& (effect::operation(code)(source[key]).unwrap().outcome==effect::operation(code)(target[names[key]]).unwrap().outcome)
        &&& forall|a:Map<Address,ValueState>,b:Map<Address,ValueState>|corresponds(names,a,b) ==> {
            let restored_left=#[trigger] (left.unwrap().undo)(a);
            let restored_right=#[trigger] (right.unwrap().undo)(b);
            &&& restored_left.is_some()==restored_right.is_some()
            &&& restored_left.is_some() ==> corresponds(names,restored_left.unwrap(),restored_right.unwrap())
        }
    }
}
/// Equal-domain transport includes missing objects, arithmetic failure, depth
/// exhaustion, branch results and the captured strict inverse on all inputs.
pub proof fn scalar(names:Map<Address,Address>,source:Map<Address,ValueState>,target:Map<Address,ValueState>,key:Address,code:effect::Code,branch:Branch)
    requires injective(names),corresponds(names,source,target),names.contains_key(key),
    ensures contract(names,source,target,key,code,branch),
{
    let left=crate::dependent_grammar::run(alias::library(),alias::node(key,code,branch),source);
    let right=crate::dependent_grammar::run(alias::library(),alias::node(names[key],code,branch),target);
    if left.is_some() {
        write(names,source,target,key,effect::operation(code)(source[key]).unwrap().value);
        assert forall|a:Map<Address,ValueState>,b:Map<Address,ValueState>|corresponds(names,a,b) implies {
            let restored_left=#[trigger] (left.unwrap().undo)(a);
            let restored_right=#[trigger] (right.unwrap().undo)(b);
            &&& restored_left.is_some()==restored_right.is_some()
            &&& restored_left.is_some() ==> corresponds(names,restored_left.unwrap(),restored_right.unwrap())
        } by {
            if (left.unwrap().undo)(a).is_some() {write(names,a,b,key,source[key]);}
        }
    }
}
impl<T:?Sized> super::Bank<T> {
    /// The real allocator establishes injectivity; callers supply only the
    /// state relation still needed at this cut, never an invented identity map.
    pub proof fn scalar_contract(&self,i:int,source:Map<Address,ValueState>,target:Map<Address,ValueState>,instruction:effect::Instruction,branch:Branch)
        requires self.wf(),0<=i<self.len_spec(),self.target(i) is Scalar,
            corresponds(self.mapping(),source,target),
        ensures contract(self.mapping(),source,target,self.address(i),instruction.model(),branch),
    {
        self.mapping_entry(i);self.mapping_injective();
        scalar(self.mapping(),source,target,self.address(i),instruction.model(),branch);
    }
}
impl<E:crate::reversible_value::effect::ScalarEffect,T:?Sized> super::super::Source<E,T> {
    /// Bind the transport law to the instruction and branch retained by an
    /// actual successful source step. No replacement code or expected output
    /// is supplied. Target heap correspondence remains the explicit cut premise.
    pub proof fn captured_scalar_contract(&self,bank:&super::Bank<T>,index:int,entry:int,source:Map<Address,ValueState>,target:Map<Address,ValueState>)
        requires self.wf(),bank.wf(),self.original().result.is_ok(),
            0<=index<self.original().result->Ok_0.steps.len(),0<=entry<bank.len_spec(),
            bank.target(entry) is Scalar,
            bank.address(entry)==self.original().result->Ok_0.steps@[index].address(),
            self.program().code()[self.original().result->Ok_0.steps@[index].pc as int].effect is Kernel,
            source.contains_pair(self.original().result->Ok_0.steps@[index].address(),self.original().result->Ok_0.steps@[index].before()->Scalar_0),
            corresponds(bank.mapping(),source,target),
        ensures {
            let step=self.original().result->Ok_0.steps@[index];let call=self.program().code()[step.pc as int];
            let instruction=call.effect->Kernel_0;
            let run=crate::dependent_grammar::run(alias::library(),alias::node(bank.mapping()[step.address()],instruction.model(),call.branch),target);
            &&& contract(bank.mapping(),source,target,step.address(),instruction.model(),call.branch)
            &&& run.is_some() && run.unwrap().state.contains_pair(bank.mapping()[step.address()],step.after()->Scalar_0)
            &&& run.unwrap().next==step.next
            &&& effect::operation(instruction.model())(target[bank.mapping()[step.address()]]).unwrap().outcome==step.outcome()->Scalar_0
        },
    {
        self.facts();let step=self.original().result->Ok_0.steps@[index];let call=self.program().code()[step.pc as int];
        assert(super::super::transport::step(self.program().code(),step));
        bank.mapping_entry(entry);bank.scalar_contract(entry,source,target,call.effect->Kernel_0,call.branch);
    }
}
}
