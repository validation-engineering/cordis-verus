//! Causal inclusion of every actual managed write in its native Begin interval.
use super::Report;
#[cfg(verus_keep_ghost)]
use super::Step;
#[cfg(verus_keep_ghost)]
use crate::reversible_value::joint;
use vstd::prelude::*;

verus! {
pub open spec fn same_cause(a:Option<joint::Receipt>,b:Option<joint::Receipt>)->bool {
    a.is_some()==b.is_some() && (a.is_some() ==> a.unwrap().same(&b.unwrap()))
}
#[verifier::opaque]
pub open spec fn writes_after<T:?Sized>(steps:Seq<Step<T>>,cause:Option<joint::Receipt>)->bool {
    cause.is_some() ==> forall|i:int|0<=i<steps.len() && (#[trigger] steps[i]).write().journal()==cause.unwrap().journal()
        ==> steps[i].write().follows(&cause.unwrap())
}
pub proof fn empty_after<T:?Sized>(cause:Option<joint::Receipt>)
    ensures writes_after(Seq::<Step<T>>::empty(),cause),
{reveal(writes_after);}
pub proof fn append_after<T:?Sized>(steps:Seq<Step<T>>,step:Step<T>,cause:Option<joint::Receipt>)
    requires writes_after(steps,cause),cause.is_some() && step.write().journal()==cause.unwrap().journal() ==> step.write().follows(&cause.unwrap()),
    ensures writes_after(steps.push(step),cause),
{
    reveal(writes_after);
    if cause.is_some() {
        assert forall|i:int|0<=i<steps.push(step).len() && (#[trigger] steps.push(step)[i]).write().journal()==cause.unwrap().journal()
            implies steps.push(step)[i].write().follows(&cause.unwrap()) by {
            if i<steps.len() {assert(steps.push(step)[i]==steps[i]);}
        }
    }
}
impl<T:?Sized> Report<T> {
    pub open spec fn predecessor(&self)->Option<joint::Receipt> {
        if self.receipts().contains_key((-1int,false)) {Some(self.receipts()[(-1int,false)])} else {None}
    }
    #[verifier::opaque]
    pub open spec fn after(&self,cause:Option<joint::Receipt>)->bool {
        same_cause(self.predecessor(),cause) && writes_after(self.steps@,cause)
    }
    pub proof fn establish_after(&self,cause:Option<joint::Receipt>)
        requires same_cause(self.predecessor(),cause),writes_after(self.steps@,cause),
        ensures self.after(cause),
    {reveal(Report::after);}
    pub proof fn equivalent_cause(&self,a:Option<joint::Receipt>,b:Option<joint::Receipt>)
        requires self.after(a),same_cause(a,b),ensures self.after(b),
    {reveal(Report::after);reveal(writes_after);}
    pub proof fn causal_return(&self,cause:joint::Receipt,completion:joint::Receipt)
        requires self.after(Some(cause)),crate::reversible_value::registration::before_return(self.receipts(),completion),
            completion.journal()==cause.journal(),
        ensures completion.follows(&cause),
    {
        reveal(Report::after);
        assert(self.receipts().contains_key((-1int,false)));
        assert(completion.follows(&self.receipts()[(-1int,false)]));
    }
}
}

pub mod endpoint;
