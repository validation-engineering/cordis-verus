//! Owned configuration-save execution. The actual document and returned I/O
//! result select progress; successful replacement and confirmed durability are
//! distinct states. Filesystem truth, serialization and external writers remain
//! adapter premises, not consequences of a successful callback result.
use vstd::prelude::*;
#[path = "configuration_source.rs"]
pub mod sources;

verus! {
broadcast use vstd::seq_lib::group_seq_properties;

#[derive(Debug)]
pub struct Document<T> {data:T,observed:String,output:String,retry_sync:bool,merged_external:bool}
impl<T> Document<T> {
    pub closed spec fn payload(&self)->T {self.data}
    pub closed spec fn before(&self)->Seq<char> {self.observed@}
    pub closed spec fn after(&self)->Seq<char> {self.output@}
    pub closed spec fn retry(&self)->bool {self.retry_sync}
    pub closed spec fn merged(&self)->bool {self.merged_external}
    pub open spec fn changes(&self)->bool {self.before()!=self.after()}
    pub fn new(data:T,observed:String,output:String,retry_sync:bool,merged_external:bool)->(out:Self)
        ensures out.payload()==data,out.before()==observed@,out.after()==output@,out.retry()==retry_sync,out.merged()==merged_external,
    {Self {data,observed,output,retry_sync,merged_external}}
    pub fn data(&self)->(out:&T) ensures *out==self.payload(), {&self.data}
    pub fn observed(&self)->(out:&str) ensures out@==self.before(), {self.observed.as_str()}
    pub fn output(&self)->(out:&str) ensures out@==self.after(), {self.output.as_str()}
    pub fn will_write(&self)->(out:bool) ensures out==self.changes(), {self.observed!=self.output}
    pub fn requires_sync(&self)->(out:bool) ensures out==(self.changes() || self.retry()), {self.will_write() || self.retry_sync}
    pub fn merged_external(&self)->(out:bool) ensures out==self.merged(), {self.merged_external}
}

#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub enum Stage {Check,Prepare,Recheck,Replace,Sync,Done}
#[derive(Copy,Clone,Debug,PartialEq,Eq)]
pub struct Progress {pub written:bool,pub unchanged:bool,pub remaining:bool,pub merged_external:bool,pub durability_uncertain:bool}
#[derive(Debug,PartialEq,Eq)]
pub enum StepError<E> {Halted,Callback(E)}

pub open spec fn stages<T>(document:Document<T>,phase:Stage)->Seq<Stage> {
    match phase {
        Stage::Check=>seq![],
        Stage::Prepare=>seq![Stage::Check],
        Stage::Recheck=>seq![Stage::Check,Stage::Prepare],
        Stage::Replace=>seq![Stage::Check,Stage::Prepare,Stage::Recheck],
        Stage::Sync=>if document.changes() {seq![Stage::Check,Stage::Prepare,Stage::Recheck,Stage::Replace]} else {seq![Stage::Check]},
        Stage::Done=>if document.changes() {seq![Stage::Check,Stage::Prepare,Stage::Recheck,Stage::Replace,Stage::Sync]}
            else if document.retry() {seq![Stage::Check,Stage::Sync]} else {seq![Stage::Check]},
    }
}
pub open spec fn allowed<T>(document:Document<T>,phase:Stage)->bool {
    match phase {Stage::Prepare|Stage::Recheck|Stage::Replace=>document.changes(),
        Stage::Sync=>document.changes() || document.retry(),_=>true}
}
pub open spec fn progress<T>(document:Document<T>,phase:Stage)->Progress {
    let processed=phase==Stage::Sync || phase==Stage::Done;
    Progress {written:document.changes() && processed,unchanged:!document.changes() && processed,
        remaining:!processed,merged_external:document.merged() && phase!=Stage::Check,
        durability_uncertain:phase==Stage::Sync}
}

#[verifier::opaque]
pub open spec fn called<T,E,C:FnOnce(Stage,&Document<T>)->Result<(),E>>(callback:C,phase:Stage,document:Document<T>,result:Result<(),E>)->bool {
    exists|d:&Document<T>| *d==document && callback.ensures((phase,d),result)
}
impl<T> Document<T> {
    fn call<E,C:FnOnce(Stage,&Self)->Result<(),E>>(&self,phase:Stage,callback:C)->(out:Result<(),E>)
        requires forall|s:Stage,d:&Self| callback.requires((s,d)),
        ensures called::<T,E,C>(callback,phase,*self,out),
    {reveal(called);callback(phase,self)}
}

/// No public acknowledgement or mutable document access can move this cursor.
/// A failed save is stopped; a new save plan rechecks its sources before retry.
#[allow(dead_code)]
pub struct Save<T> {origin:Option<crate::configuration_transaction::SaveStamp>,documents:Vec<Document<T>>,phases:Vec<Stage>,cursor:usize,halted:bool,history:Ghost<Seq<Seq<Stage>>>}
impl<T> Save<T> {
    pub closed spec fn review(&self)->Option<crate::configuration_transaction::SaveStamp> {self.origin}
    pub closed spec fn documents(&self)->Seq<Document<T>> {self.documents@}
    pub closed spec fn phases(&self)->Seq<Stage> {self.phases@}
    pub closed spec fn cursor(&self)->nat {self.cursor as nat}
    pub closed spec fn halted(&self)->bool {self.halted}
    pub closed spec fn history(&self)->Seq<Seq<Stage>> {self.history@}
    pub closed spec fn wf(&self)->bool {
        &&& self.cursor()<=self.documents().len()
        &&& self.phases().len()==self.documents().len() && self.history().len()==self.documents().len()
        &&& self.halted() ==> self.cursor()<self.documents().len()
        &&& forall|i:int| 0<=i<self.documents().len() ==> {
            &&& allowed(self.documents()[i],#[trigger] self.phases()[i])
            &&& self.history()[i]==stages(self.documents()[i],self.phases()[i])
            &&& (i<self.cursor() <==> self.phases()[i]==Stage::Done)
            &&& i>self.cursor() ==> self.phases()[i]==Stage::Check
        }
    }
    pub fn new(documents:Vec<Document<T>>)->(out:Self)
        ensures out.wf(),out.review().is_none(),out.documents()==documents@,out.cursor()==0,!out.halted(),
            forall|i:int| 0<=i<documents.len() ==> #[trigger] out.phases()[i]==Stage::Check && out.history()[i]==Seq::<Stage>::empty(),
    {
        let mut phases=Vec::new();let ghost history=Seq::new(documents.len() as nat,|_:int|Seq::<Stage>::empty());
        while phases.len()<documents.len()
            invariant phases.len()<=documents.len(),forall|i:int| 0<=i<phases.len() ==> #[trigger] phases@[i]==Stage::Check,
            decreases documents.len()-phases.len(),
        {phases.push(Stage::Check);}
        Self {origin:None,documents,phases,cursor:0,halted:false,history:Ghost(history)}
    }
    pub fn files(&self)->(out:&[Document<T>]) ensures out@==self.documents(), {self.documents.as_slice()}
    pub fn complete(&self)->(out:bool)
        requires self.wf(),ensures out==(self.cursor()==self.documents().len()),out ==> !self.halted(),
    {self.cursor==self.documents.len()}
    pub fn progress(&self,index:usize)->(out:Option<Progress>)
        requires self.wf(),
        ensures out.is_some()==(index<self.documents().len()),
            out.is_some() ==> out.unwrap()==progress(self.documents()[index as int],self.phases()[index as int]),
    {
        if index>=self.documents.len() {return None;}
        let d=&self.documents[index];let phase=self.phases[index];let processed=phase==Stage::Sync || phase==Stage::Done;
        Some(Progress {written:d.will_write() && processed,unchanged:!d.will_write() && processed,remaining:!processed,
            merged_external:d.merged_external() && phase!=Stage::Check,durability_uncertain:phase==Stage::Sync})
    }
    /// The callback receives the stored document at the current phase. Only its
    /// actual Ok advances; Err retains the completed prefix and closes the save.
    pub fn step<E,C:FnOnce(Stage,&Document<T>)->Result<(),E>>(&mut self,callback:C)->(out:Result<bool,StepError<E>>)
        requires old(self).wf(),forall|s:Stage,d:&Document<T>| callback.requires((s,d)),
        ensures final(self).wf(),final(self).documents()==old(self).documents(),final(self).review()==old(self).review(),
            old(self).halted() ==> out==Err(StepError::Halted) && *final(self)==*old(self),
            !old(self).halted() && old(self).cursor()==old(self).documents().len() ==> out==Ok(true) && *final(self)==*old(self),
            out.is_ok() ==> out->Ok_0==(final(self).cursor()==final(self).documents().len()),
            !old(self).halted() && old(self).cursor()<old(self).documents().len() ==> {
                let i=old(self).cursor() as int;let phase=old(self).phases()[i];let doc=old(self).documents()[i];
                &&& forall|j:int| 0<=j<old(self).documents().len() && j!=i ==> #[trigger] final(self).phases()[j]==old(self).phases()[j]
                    && final(self).history()[j]==old(self).history()[j]
                &&& match out {
                    Ok(_)=>!final(self).halted() && called::<T,E,C>(callback,phase,doc,Ok(()))
                        && final(self).history()[i]==old(self).history()[i].push(phase),
                    Err(StepError::Callback(error))=>final(self).halted() && final(self).phases()==old(self).phases()
                        && final(self).history()==old(self).history() && final(self).cursor()==old(self).cursor()
                        && called::<T,E,C>(callback,phase,doc,Err(error)),
                    _=>false,
                }
            },
    {
        if self.halted {return Err(StepError::Halted);}
        if self.cursor==self.documents.len() {return Ok(true);}
        let ghost before=*self;
        let i=self.cursor;let phase=self.phases[i];let doc=&self.documents[i];
        assert(phase!=Stage::Done);
        assert(self.history@[i as int]==stages(*doc,phase));
        let result=doc.call(phase,callback);
        assert(called::<T,E,C>(callback,phase,before.documents()[i as int],result));
        match result {
            Err(error)=>{
                self.halted=true;
                assert(self.history()==before.history() && self.phases()==before.phases() && self.cursor()==before.cursor());
                assert(called::<T,E,C>(callback,phase,before.documents()[i as int],Err(error)));
                Err(StepError::Callback(error))
            },
            Ok(_unit)=>{
                assert(_unit==());
                assert(Result::<(),E>::Ok(_unit)==Result::<(),E>::Ok(()));
                assert(result==Result::<(),E>::Ok(()));
                assert(called::<T,E,C>(callback,phase,before.documents()[i as int],Result::<(),E>::Ok(())));
                let next=match phase {
                    Stage::Check=>if doc.will_write() {Stage::Prepare} else if doc.requires_sync() {Stage::Sync} else {Stage::Done},
                    Stage::Prepare=>Stage::Recheck,Stage::Recheck=>Stage::Replace,Stage::Replace=>Stage::Sync,Stage::Sync=>Stage::Done,
                    Stage::Done=>Stage::Done,
                };
                proof {
                    assert(allowed(*doc,next));
                    assert(stages(*doc,next)==self.history@[i as int].push(phase));
                    self.history=Ghost(self.history@.update(i as int,self.history@[i as int].push(phase)));
                }
                self.phases.set(i,next);
                if next==Stage::Done {self.cursor+=1;}
                assert forall|j:int| 0<=j<self.documents().len() implies {
                    &&& allowed(self.documents()[j],#[trigger] self.phases()[j])
                    &&& self.history()[j]==stages(self.documents()[j],self.phases()[j])
                    &&& (j<self.cursor() <==> self.phases()[j]==Stage::Done)
                    &&& j>self.cursor() ==> self.phases()[j]==Stage::Check
                } by {
                    if j!=i {assert(before.phases()[j]==self.phases()[j]);}
                }
                assert forall|j:int| 0<=j<before.documents().len() && j!=i implies
                    #[trigger] self.phases()[j]==before.phases()[j] && self.history()[j]==before.history()[j] by { }
                assert(called::<T,E,C>(callback,phase,before.documents()[i as int],Ok(())));
                assert(self.history()[i as int]==before.history()[i as int].push(phase));
                Ok(self.cursor==self.documents.len())
            },
        }
    }
    /// A successful whole-save report entails a durability acknowledgement for
    /// every replacement and every explicitly requested barrier retry.
    pub proof fn complete_history(&self)
        requires self.wf(),self.cursor()==self.documents().len(),
        ensures !self.halted(),forall|i:int| 0<=i<self.documents().len() ==> #[trigger] self.phases()[i]==Stage::Done
            && self.history()[i]==stages(self.documents()[i],Stage::Done)
            && !progress(self.documents()[i],self.phases()[i]).remaining
            && !progress(self.documents()[i],self.phases()[i]).durability_uncertain,
    {}
}
impl crate::configuration_transaction::SaveStamp {
    /// Bind the actual reviewed stamp before any document is dispatched. There
    /// is no API for attaching a fresh stamp to an already progressed save.
    pub fn start<T>(self,documents:Vec<Document<T>>)->(out:Save<T>)
        ensures out.wf(),out.review()==Some(self),out.documents()==documents@,out.cursor()==0,!out.halted(),
            forall|i:int|0<=i<documents.len() ==> #[trigger] out.phases()[i]==Stage::Check && out.history()[i]==Seq::<Stage>::empty(),
    {
        let mut out=Save::new(documents);out.origin=Some(self);out
    }
}

}
