//! Declared native service calls shared by ordinary roots and Child roots.
//! Resolution, the actual object write and inverse registration form one checked
//! call. The proof observes the real journal position, including intervening
//! slot replacements; it does not assume that distinct ports are independent.
use super::slot::{ReadError, ServiceBinding, ServiceSlot};
use super::{joint, Branch, Operation, ValueError};
#[cfg(verus_keep_ghost)]
use super::{Applied, Outcome, ValueState};
use crate::execution::{Execution, ValueAdmission};
use crate::lifecycle_state::registration::shared_child::ChildCleanup;
use crate::lifecycle_state::services::NativeEpisode;
use crate::Port;
#[cfg(verus_keep_ghost)]
use crate::{dependent_grammar as d, lifecycle_state::services::slots};
use vstd::prelude::*;

verus! {
/// Cordis declarations authorize access to a service; they are not separate
/// read-only/write-only capabilities. Each call refines that service access to
/// the allocation actually captured by its slot.
pub open spec fn declared<T,M>(episode:NativeEpisode<ServiceSlot<T,M>>,port:Port)->bool {
    episode.provisions().contains(port) || exists|b:crate::Binding| episode.bindings().contains(b) && b.key==port.key && b.realm==port.realm
}
pub open spec fn selected<T,M>(episode:NativeEpisode<ServiceSlot<T,M>>,binding:ServiceBinding)->bool {
    episode.wf() && !episode.closed() && binding.wf() && declared(episode,binding.port_spec())
        && episode.selects_slot(binding.provider_spec(),binding.port_spec(),binding.capture_spec().slot())
}
pub proof fn selection_declared<T,M>(episode:NativeEpisode<ServiceSlot<T,M>>,binding:ServiceBinding)
    requires episode.wf(),!episode.closed(),binding.wf(),
        episode.selects_slot(binding.provider_spec(),binding.port_spec(),binding.capture_spec().slot()),
    ensures selected(episode,binding),
{
    if !episode.provisions().contains(binding.port_spec()) {
        let b=crate::Binding {provider:binding.provider_spec(),key:binding.port_spec().key,realm:binding.port_spec().realm};
        assert(episode.bindings().contains(b));
    }
}

#[derive(Debug)]
pub enum Error {NoNativeOwner,Read(ReadError),Value(ValueError)}
/// A rejected scalar attempt still identifies its declared capture and the
/// actual rejection commit; it is not a missing or fabricated successful step.
pub struct Rejection {pub binding:ServiceBinding,pub receipt:joint::Receipt}
impl Rejection {
    pub proof fn stutters(&self)
        requires self.receipt.wf(),self.receipt.event().change is Value,self.receipt.event().change->Value_event is Rejected,
        ensures joint::state_at(self.receipt.events(),self.receipt.at())==self.receipt.events().last().state,
            joint::pending_at(self.receipt.events(),self.receipt.at())==self.receipt.events().last().pending,
    {
        self.receipt.transition();reveal(joint::changes);
        assert(joint::state_at(self.receipt.events(),self.receipt.at()) =~= self.receipt.events().last().state);
    }
    pub open spec fn certified<T,M>(&self,episode:NativeEpisode<ServiceSlot<T,M>>,port:Port,operation:Operation,error:ValueError)->bool {
        selected(episode,self.binding) && self.binding.port_spec()==port && self.receipt.wf()
            && self.receipt.journal()==self.binding.capture_spec().value_spec().journal_spec()
            && self.receipt.event().key==self.binding.capture_spec().value_spec().object().key
            && self.receipt.event().change is Value
            && super::attempt::value_rejection(self.receipt.event().change->Value_event,operation,error)
    }
}
pub open spec fn failed<T,M,C,G,Cb,X>(before:Execution<ServiceSlot<T,M>,C,G,ChildCleanup<Cb,X>>,after:Execution<ServiceSlot<T,M>,C,G,ChildCleanup<Cb,X>>,id:usize,port:Port,operation:Operation,error:Error)->bool {
    match error {
        Error::NoNativeOwner=>before.value_state().is_none() && after.value_attempts()==before.value_attempts(),
        Error::Read(_)=>before.value_state().is_some() && after.value_attempts()==before.value_attempts(),
        Error::Value(error)=>before.value_state().is_some() && if error==ValueError::Closed {
            !(before.work_state().accepts() && before.cleanup_state().acquisition_open(id)) && after.value_attempts()==before.value_attempts()
        } else {exists|binding:ServiceBinding| {
            &&& after.value_attempts().appended(&before.value_attempts(),&binding.capture_spec().value_spec())
            &&& (Rejection {binding,receipt:after.value_attempts().events().last()}).certified(before.value_state().unwrap(),port,operation,error)
        }},
    }
}
pub proof fn failure_witness<T,M,C,G,Cb,X>(before:Execution<ServiceSlot<T,M>,C,G,ChildCleanup<Cb,X>>,after:Execution<ServiceSlot<T,M>,C,G,ChildCleanup<Cb,X>>,id:usize,port:Port,operation:Operation,error:Error)->(out:Option<Rejection>)
    requires failed(before,after,id,port,operation,error),
    ensures match error {
        Error::Value(e) if e!=ValueError::Closed=>out.is_some() && out.unwrap().certified(before.value_state().unwrap(),port,operation,e)
            && out.unwrap().receipt.same(&after.value_attempts().events().last()),
        _=>out.is_none(),
    },
{
    match error {
        Error::Value(e) if e!=ValueError::Closed=>{
            let binding=choose|binding:ServiceBinding| after.value_attempts().appended(&before.value_attempts(),&binding.capture_spec().value_spec())
                && (Rejection {binding,receipt:after.value_attempts().events().last()}).certified(before.value_state().unwrap(),port,operation,e);
            Some(Rejection {binding,receipt:after.value_attempts().events().last()})
        },
        _=>None,
    }
}
/// Explicit read/write ranges in allocation identities, not service names.
pub struct Footprint {pub read_slots:Set<joint::Object>,pub read_values:Set<joint::Object>,pub write_values:Set<joint::Object>}
pub open spec fn footprint(binding:ServiceBinding,writes:bool)->Footprint {
    let slot=binding.capture_spec().slot();let value=binding.capture_spec().value_spec().object();
    Footprint {read_slots:set![joint::Object {domain:slot.journal_spec().source(),key:slot.key()}],read_values:set![value],
        write_values:if writes {set![value]} else {Set::empty()}}
}
pub struct Read {pub binding:ServiceBinding,pub snapshot:super::Snapshot}
impl Read {
    pub open spec fn certified(&self)->bool {
        self.binding.wf() && self.snapshot.certified() && self.snapshot.object()==self.binding.capture_spec().value_spec().object()
            && self.snapshot.source()==self.binding.capture_spec().value_spec().source()
            && self.snapshot.journal_spec()==self.binding.capture_spec().value_spec().journal_spec()
            && (self.binding.capture_spec().commit().journal()==self.snapshot.journal_spec() ==>
                self.binding.capture_spec().commit().events().len()<=self.snapshot.joint_spec().events().len()
                && self.snapshot.joint_spec().events().take(self.binding.capture_spec().commit().events().len() as int)==self.binding.capture_spec().commit().events())
    }
    /// The read result is the captured allocation's actual production state.
    /// A concurrent slot replacement does not retarget the retained read.
    pub proof fn production(&self)
        requires self.certified(),
        ensures objects(self.snapshot.joint_spec().last()).contains_key(self.snapshot.object().key),
            objects(self.snapshot.joint_spec().last())[self.snapshot.object().key]==self.snapshot.state(),
            footprint(self.binding,false).write_values.is_empty(),
    {self.snapshot.production_state();}
}
impl<T,M> NativeEpisode<ServiceSlot<T,M>> {
    pub fn observe_reversible(&self,port:Port)->(out:Result<Read,ReadError>)
        requires self.wf(),
        ensures out.is_ok() ==> out->Ok_0.certified() && selected(*self,out->Ok_0.binding) && out->Ok_0.binding.port_spec()==port,
    {
        let binding=self.read_reversible(port)?;
        proof {selection_declared(*self,binding);}
        let snapshot=binding.capture().observe_value();
        let report=Read {binding,snapshot};proof {report.production();}Ok(report)
    }
}
pub struct Write {pub binding:ServiceBinding,pub admission:ValueAdmission}
impl Write {
    /// Both real write families instantiate the same allocation-key library.
    pub proof fn general_semantics(&self)
        requires self.certified(),
        ensures {
            let r=self.admission.registration().write();let event=r.event().change->Value_event;
            let run=d::run(super::alias::library(),super::alias::node(r.event().key,super::alias::event_code(event),super::alias::event_branch(event)),objects(joint::state_at(r.events(),r.at())));
            &&& run.is_some() && run.unwrap().state==objects(r.events().last().state)
            &&& run.unwrap().next==super::alias::event_branch(event).selected(super::alias::event_outcome(event))
            &&& forall|state:Map<nat,ValueState>| #[trigger] (run.unwrap().undo)(state)==
                if state.contains_key(r.event().key) && state[r.event().key]==event.after() {Some(state.insert(r.event().key,event.before()))} else {None}
        },
    {
        let r=self.admission.registration().write();
        super::alias::managed_step(joint::state_at(r.events(),r.at()),r.events().last().state,r.event());
    }
    pub proof fn disjoint_from(&self,other:&Self)
        requires self.certified(),other.certified(),
            self.admission.registration().write().journal()==other.admission.registration().write().journal(),
            self.admission.registration().write().event().key!=other.admission.registration().write().event().key,
        ensures crate::iterator_bridge::independent(crate::dependent_independence::equality(|_:nat,a:ValueState,b:ValueState|a==b),
            d::family(super::alias::library(),super::alias::terminal(self.admission.registration().write().event().key,super::alias::event_code(self.admission.registration().write().event().change->Value_event))),(),
            d::family(super::alias::library(),super::alias::terminal(other.admission.registration().write().event().key,super::alias::event_code(other.admission.registration().write().event().change->Value_event))),()),
    {
        super::alias::allocation_independence(self.admission.registration().write().event().key,other.admission.registration().write().event().key,
            super::alias::event_code(self.admission.registration().write().event().change->Value_event),super::alias::event_code(other.admission.registration().write().event().change->Value_event));
    }
    pub open spec fn corresponds(&self,operation:Operation,branch:Branch)->bool {
        let event=self.admission.registration().write().event().change;
        &&& self.certified() && event is Value && event->Value_event is Forward
        &&& event->Value_event->Forward_operation==operation && event->Value_event->Forward_branch==branch
        &&& event->Value_event->Forward_outcome==self.admission.outcome && event->Value_event->Forward_next==self.admission.next
        &&& self.admission.next==branch.selected(self.admission.outcome)
    }

    pub open spec fn certified(&self)->bool {
        self.binding.wf() && self.admission.registration().certified()
            && self.admission.registration().write().journal()==self.binding.capture_spec().value_spec().journal_spec()
            && self.admission.registration().write().event().key==self.binding.capture_spec().value_spec().object().key
            && (self.binding.capture_spec().commit().journal()==self.admission.registration().write().journal() ==>
                self.admission.registration().write().follows(&self.binding.capture_spec().commit()))
    }
    pub open spec fn recorded<T,M,C,G,Cb,X>(&self,execution:Execution<ServiceSlot<T,M>,C,G,ChildCleanup<Cb,X>>,id:usize)->bool {
        let queue=execution.cleanup_state().queues()[id];let token=self.admission.token;
        &&& execution.cleanup_state().live(id) && token<queue.slots().len()
        &&& queue.slots()[token as int].is_some() && queue.slots()[token as int].unwrap() is Value
        &&& self.admission.registration().records(queue.slots()[token as int].unwrap()->Value_0,queue.link(),queue.protocol().domain_id(),token)
        &&& queue.slots()[token as int].unwrap()->Value_0.target()==*self.binding.capture_spec().value_spec()
    }
    /// No synthetic initial table: the input and output come from the actual
    /// successful write's authenticated journal prefix.
    pub proof fn semantics(&self)
        requires self.certified(),self.admission.registration().write().event().change->Value_event is Forward,
        ensures {
            let receipt=self.admission.registration().write();let frames=receipt.events();let i=receipt.at();
            let event=receipt.event().change->Value_event;
            let run=d::run(library(),d::Node::Operation {operation:(receipt.event().key,event->Forward_operation),argument:(),
                select:|out:Outcome|event->Forward_branch.selected(out)},objects(joint::state_at(frames,i)));
            &&& run.is_some() && run.unwrap().state==objects(joint::state_at(frames,i+1)) && run.unwrap().next==event->Forward_next
            &&& objects(joint::state_at(frames,i)).contains_key(receipt.event().key)
            &&& forall|key:nat| objects(joint::state_at(frames,i)).contains_key(key) && key!=receipt.event().key ==>
                #[trigger] objects(joint::state_at(frames,i+1))[key]==objects(joint::state_at(frames,i))[key]
        },
    {
        let receipt=self.admission.registration().write();let frames=receipt.events();let i=receipt.at();
        assert(joint::step(joint::state_at(frames,i),frames[i as int].state,frames[i as int].event));
        interpret(joint::state_at(frames,i),joint::state_at(frames,i+1),receipt.event());
    }
    /// Use the actual owned/imported maps selected at the call boundary. Only
    /// aliases of the retained allocation can change at this write. Later slot
    /// replacements and other writers are separate events, not hidden stutters.
    pub proof fn service_frame<T,M>(&self,episode:NativeEpisode<ServiceSlot<T,M>>)
        requires self.certified(),selected(episode,self.binding),
        ensures {
            let receipt=self.admission.registration().write();let before=joint::state_at(receipt.events(),receipt.at());let after=receipt.events().last().state;
            &&& slots::value_frame(episode.owned(),receipt.journal(),before,after,receipt.event().key)
            &&& slots::value_frame(episode.imports(),receipt.journal(),before,after,receipt.event().key)
        },
    {
        let receipt=self.admission.registration().write();let before=joint::state_at(receipt.events(),receipt.at());let after=receipt.events().last().state;
        slots::project_value_step(episode.owned(),receipt.journal(),before,after,receipt.event());
        slots::project_value_step(episode.imports(),receipt.journal(),before,after,receipt.event());
    }
}

/// The whole local object carrier is extracted from actual production records.
pub open spec fn objects(state:Map<nat,joint::Record>)->Map<nat,ValueState> {
    Map::new(state.dom().filter(|key:nat|state[key] is Object),|key:nat|state[key]->Object_state)
}
pub open spec fn library()->d::Library<nat,(nat,Operation),(),ValueState,Outcome> {
    d::Library {values:|_:nat,_:ValueState|true,arguments:|_:(nat,Operation),_:()|true,
        outcomes:|_:(nat,Operation),_:Outcome|true,key:|a:(nat,Operation)|a.0,allowed:ISet::full(),
        apply:|a:(nat,Operation),_:()|super::operation(a.1)}
}
/// Full-carrier primitive law, independent of a particular observed execution.
pub proof fn primitive_theory()
    ensures d::primitive_theory(|_:nat,a:ValueState,b:ValueState|a==b,library()),
{}
pub proof fn interpret(before:Map<nat,joint::Record>,after:Map<nat,joint::Record>,step:joint::Step)
    requires joint::step(before,after,step),step.change is Value,step.change->Value_event is Forward,
    ensures objects(before).contains_key(step.key),objects(before)[step.key]==step.change->Value_event.before(),
        objects(after)==objects(before).insert(step.key,step.change->Value_event.after()),
        ({let event=step.change->Value_event;let run=d::run(library(),d::Node::Operation {operation:(step.key,event->Forward_operation),argument:(),
            select:|out:Outcome|event->Forward_branch.selected(out)},objects(before));
          run.is_some() && run.unwrap().state==objects(after) && run.unwrap().next==event->Forward_next}),
        forall|key:nat| objects(before).contains_key(key) && key!=step.key ==> #[trigger] objects(after)[key]==objects(before)[key],
{
    reveal(joint::changes);
    assert(objects(after) =~= objects(before).insert(step.key,step.change->Value_event.after()));
}
impl<T,M,C,G,Cb,X> Execution<ServiceSlot<T,M>,C,G,ChildCleanup<Cb,X>> {
    /// Ordinary root/Child callbacks reach the same checked resolution path.
    /// No provider, raw value pointer or expected output is supplied by the host.
    #[verifier::rlimit(20)]
    pub fn apply_native_value(&mut self,id:usize,port:Port,operation:Operation,branch:Branch)->(out:Result<Write,Error>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).capture()==old(self).capture(),final(self).work_state()==old(self).work_state(),
            final(self).value_state()==old(self).value_state(),final(self).phase_spec()==old(self).phase_spec(),
            final(self).execution_journal()==old(self).execution_journal(),
            out.is_err() ==> final(self).same_runtime(old(self)),
            out.is_err() ==> failed(*old(self),*final(self),id,port,operation,out->Err_0),
            out.is_ok() ==> {
                let report=out->Ok_0;
                &&& old(self).value_state().is_some() && selected(old(self).value_state().unwrap(),report.binding)
                &&& report.binding.port_spec()==port && report.certified() && report.recorded(*final(self),id)
                &&& report.corresponds(operation,branch)
                &&& final(self).cleanup_state().frame(&old(self).cleanup_state(),id)
                &&& final(self).cleanup_state().domain_ids()==old(self).cleanup_state().domain_ids()
                &&& final(self).cleanup_state().queues()[id].link()==old(self).cleanup_state().queues()[id].link()
                &&& final(self).cleanup_state().queues()[id].slots().take(old(self).cleanup_state().queues()[id].slots().len() as int)==old(self).cleanup_state().queues()[id].slots()
                &&& final(self).cleanup_state().queues()[id].protocol().waiting()==old(self).cleanup_state().queues()[id].protocol().waiting().push(report.admission.token)
                &&& report.admission.token==old(self).cleanup_state().queues()[id].slots().len()
                &&& final(self).cleanup_state().queues()[id].slots().len()==old(self).cleanup_state().queues()[id].slots().len()+1
                &&& final(self).value_attempts().appended(&old(self).value_attempts(),&report.binding.capture_spec().value_spec())
                &&& final(self).value_attempts().events().last().same(&report.admission.registration().write())
                &&& (Applied {outcome:report.admission.outcome,next:report.admission.next,pending:Tracked(None),
                    inverse:final(self).cleanup_state().queues()[id].slots()[report.admission.token as int].unwrap()->Value_0})
                    .corresponds(&report.binding.capture_spec().value_spec(),operation,branch)
            },
            final(self).status_links()==old(self).status_links(),
    {
        let ghost original=*self;
        let values=match self.native() {Some(values)=>values,None=>return Err(Error::NoNativeOwner)};
        let binding=match values.read_reversible(port) {Ok(binding)=>binding,Err(error)=>return Err(Error::Read(error))};
        proof {selection_declared(*values,binding);}
        let capture=binding.capture();let Tracked(cause)=capture.selection_receipt();
        let admission=match self.apply_value_following(id,binding.value(),operation,branch,Tracked(Some(cause))) {Ok(admission)=>admission,Err(error)=>{
            proof {
                if error!=ValueError::Closed {
                    assert((Rejection {binding,receipt:self.value_attempts().events().last()}).certified(original.value_state().unwrap(),port,operation,error));
                    assert(self.value_attempts().appended(&original.value_attempts(),&binding.capture_spec().value_spec()));
                }
            }
            return Err(Error::Value(error));
        }};
        let report=Write {binding,admission};
        proof {report.semantics();report.general_semantics();report.service_frame(self.value_state().unwrap());}
        Ok(report)
    }
    /// Ordered multi-service calls keep an actual prior write as a cause.
    #[verifier::rlimit(20)]
    pub fn apply_native_value_chained(&mut self,id:usize,port:Port,operation:Operation,branch:Branch,Tracked(previous):Tracked<Option<joint::Receipt>>)->(out:Result<Write,Error>)
        requires old(self).wf(),previous.is_some() ==> previous.unwrap().wf(),
        ensures final(self).wf(),final(self).capture()==old(self).capture(),final(self).work_state()==old(self).work_state(),
            final(self).value_state()==old(self).value_state(),final(self).phase_spec()==old(self).phase_spec(),
            final(self).execution_journal()==old(self).execution_journal(),
            out.is_err() ==> final(self).same_runtime(old(self)),
            out.is_err() ==> failed(*old(self),*final(self),id,port,operation,out->Err_0),
            out.is_err() && out->Err_0 is Value && out->Err_0->Value_0!=ValueError::Closed && previous.is_some()
                && previous.unwrap().journal()==final(self).value_attempts().events().last().journal()
                ==> final(self).value_attempts().events().last().follows(&previous.unwrap()),
            out.is_ok() ==> {
                let report = out->Ok_0;
                &&& old(self).value_state().is_some() && selected(old(self).value_state().unwrap(),report.binding)
                &&& report.certified() && report.recorded(*final(self),id) && report.binding.port_spec()==port
                &&& report.corresponds(operation,branch)
                &&& previous.is_some() && previous.unwrap().journal()==report.admission.registration().write().journal() ==> report.admission.registration().write().follows(&previous.unwrap())
                &&& final(self).cleanup_state().frame(&old(self).cleanup_state(),id)
                &&& final(self).cleanup_state().domain_ids()==old(self).cleanup_state().domain_ids()
                &&& final(self).cleanup_state().queues()[id].link()==old(self).cleanup_state().queues()[id].link()
                &&& final(self).cleanup_state().queues()[id].slots().take(old(self).cleanup_state().queues()[id].slots().len() as int)==old(self).cleanup_state().queues()[id].slots()
                &&& final(self).cleanup_state().queues()[id].protocol().waiting()==old(self).cleanup_state().queues()[id].protocol().waiting().push(report.admission.token)
                &&& report.admission.token==old(self).cleanup_state().queues()[id].slots().len()
                &&& final(self).cleanup_state().queues()[id].slots().len()==old(self).cleanup_state().queues()[id].slots().len()+1
                &&& final(self).value_attempts().appended(&old(self).value_attempts(),&report.binding.capture_spec().value_spec())
                &&& final(self).value_attempts().events().last().same(&report.admission.registration().write())
                &&& (Applied {outcome:report.admission.outcome,next:report.admission.next,pending:Tracked(None),
                    inverse:final(self).cleanup_state().queues()[id].slots()[report.admission.token as int].unwrap()->Value_0})
                    .corresponds(&report.binding.capture_spec().value_spec(),operation,branch)
            },
            final(self).status_links()==old(self).status_links(),
    {
        let ghost original=*self;
        let native=match self.native() {Some(native)=>native,None=>return Err(Error::NoNativeOwner)};
        let binding=match native.read_reversible(port) {Ok(binding)=>binding,Err(error)=>return Err(Error::Read(error))};
        proof {selection_declared(*native,binding);}
        let Tracked(selection)=binding.capture().selection_receipt();
        let (journal,Tracked(_object))=binding.value().reference();
        let Tracked(cause)=journal.join_causes(Tracked(Some(selection.duplicate())),Tracked(match &previous {Some(receipt)=>Some(receipt.duplicate()),None=>None}));
        let tracked forwarded=match &cause {Some(receipt)=>Some(receipt.duplicate()),None=>None};
        let admission=match self.apply_value_following(id,binding.value(),operation,branch,Tracked(forwarded)) {Ok(value)=>value,Err(error)=>{
            proof {
                if error!=ValueError::Closed {
                    assert((Rejection {binding,receipt:self.value_attempts().events().last()}).certified(original.value_state().unwrap(),port,operation,error));
                    assert(self.value_attempts().appended(&original.value_attempts(),&binding.capture_spec().value_spec()));
                }
                if error!=ValueError::Closed && previous.is_some() && previous.unwrap().journal()==journal {
                    self.value_attempts().events().last().after_cover(&cause.unwrap(),&previous.unwrap());
                }
            }
            return Err(Error::Value(error));
        }};
        proof {
            if selection.journal()==journal {admission.registration().write().after_cover(&cause.unwrap(),&selection);}
            if previous.is_some() && previous.unwrap().journal()==journal {admission.registration().write().after_cover(&cause.unwrap(),&previous.unwrap());}
        }
        let report=Write {binding,admission};
        proof {report.semantics();report.general_semantics();report.service_frame(self.value_state().unwrap());}
        Ok(report)
    }

}
}
