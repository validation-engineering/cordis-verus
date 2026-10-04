//! Finite scripts over an owning, single-admission machine.
//!
//! Admission and release change session metadata only. Checked calls and real
//! landings extend one source history under the original installed program.
use super::super::{Blueprint, Command, DriverError, FreshDriver, Transition};
use super::{Admission, AdmissionError, Landing};
#[cfg(verus_keep_ghost)]
use crate::{fresh_semantics as fs, mixed_driver as core, mixed_grammar as mx, Port};
use vstd::prelude::*;

verus! {

#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub enum ScriptAction {Call(Command),Admit {actor:usize},Land,Release}
pub open spec fn eventful(action:ScriptAction)->bool {matches!(action,ScriptAction::Call(_) | ScriptAction::Land)}
#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub enum ScriptError {NotReady,NotAdmitted,Driver(DriverError),Admission(AdmissionError)}
#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub enum Effect {Call(Transition),Land(Landing)}
impl Effect {
    pub open spec fn label(&self)->fs::Label {
        match *self {Self::Call(t)=>super::super::label(t),Self::Land(landed)=>landed.label()}
    }
    pub open spec fn matches(&self,action:ScriptAction)->bool {
        match *self {Self::Call(t)=>action==ScriptAction::Call(t.command),Self::Land(_)=>action==ScriptAction::Land}
    }
}
#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub struct ScriptEvent {pub action_index:usize,pub effect:Effect}
pub open spec fn labels(events:Seq<ScriptEvent>)->Seq<fs::Label> {
    events.map(|_:int,event:ScriptEvent|event.effect.label())
}

enum Session {Ready {machine:FreshDriver},Pending {admission:Admission}}
struct Acted {session:Session,event:Option<Effect>,error:Option<ScriptError>}
impl Session {
    closed spec fn machine(&self)->FreshDriver {match self {Self::Ready {machine}=>*machine,Self::Pending {admission}=>admission.machine()}}
    closed spec fn wf(&self)->bool {self.machine().wf()}
    fn into_driver(self)->(out:FreshDriver) ensures out==self.machine(), {
        match self {Self::Ready {machine}=>machine,Self::Pending {admission}=>admission.into_driver()}
    }
    /// The session owns every machine used here; there is no ticket rebinding.
    fn act(self,action:ScriptAction)->(out:Acted)
        requires self.wf(),
        ensures out.session.wf(),
            out.error.is_some() ==> out.event.is_none(),
            out.event.is_none() ==> out.session.machine().same(&self.machine()),
            out.event.is_some() ==> out.error.is_none() && out.event.unwrap().matches(action)
                && self.machine().ack(&out.session.machine(),out.event.unwrap().label().0,out.event.unwrap().label().1,out.event.unwrap().label().2),
            out.error.is_none() ==> out.event.is_some()==eventful(action),
    {
        match self {
            Self::Ready {machine}=>{
                match action {
                    ScriptAction::Call(command)=>{
                        let mut machine=machine;
                        match machine.apply(command) {
                            Ok(t)=>Acted {session:Self::Ready {machine},event:Some(Effect::Call(t)),error:None},
                            Err(error)=>Acted {session:Self::Ready {machine},event:None,error:Some(ScriptError::Driver(error))},
                        }
                    },
                    ScriptAction::Admit {actor}=>match machine.admit(actor) {
                        Ok(admission)=>Acted {session:Self::Pending {admission},event:None,error:None},
                        Err(rejected)=>Acted {session:Self::Ready {machine:rejected.machine},event:None,error:Some(ScriptError::Admission(rejected.error))},
                    },
                    ScriptAction::Land | ScriptAction::Release=>Acted {session:Self::Ready {machine},event:None,error:Some(ScriptError::NotAdmitted)},
                }
            },
            Self::Pending {admission}=>{
                match action {
                    ScriptAction::Call(command)=>{
                        let mut admission=admission;
                        match admission.apply(command) {
                            Ok(t)=>Acted {session:Self::Pending {admission},event:Some(Effect::Call(t)),error:None},
                            Err(error)=>Acted {session:Self::Pending {admission},event:None,error:Some(ScriptError::Driver(error))},
                        }
                    },
                    ScriptAction::Land=>{
                        let mut admission=admission;
                        match admission.land() {
                            Ok(landed)=>Acted {session:Self::Pending {admission},event:Some(Effect::Land(landed)),error:None},
                            Err(error)=>Acted {session:Self::Pending {admission},event:None,error:Some(ScriptError::Admission(error))},
                        }
                    },
                    ScriptAction::Release=>Acted {session:Self::Ready {machine:admission.into_driver()},event:None,error:None},
                    ScriptAction::Admit {..}=>Acted {session:Self::Pending {admission},event:None,error:Some(ScriptError::NotReady)},
                }
            },
        }
    }
}

/// `completed` counts successful script actions, including metadata actions.
/// `events` contains exactly the successful calls and landings in that prefix.
pub struct ScriptReport {pub machine:FreshDriver,pub events:Vec<ScriptEvent>,pub completed:usize,pub error:Option<ScriptError>}
impl ScriptReport {
    pub closed spec fn refines(&self,bank:Seq<core::Blueprint>)->bool {
        exists|states:Seq<mx::Configuration<u64,core::Index>>| {
            &&& fs::execution(core::library(),super::super::programs(bank),states,labels(self.events@)) && states.first()==mx::empty::<u64,core::Index>()
            &&& self.machine.represents(bank,states.last())
            &&& forall|i:int|0<=i<states.len() ==> fs::well_formed(core::library(),super::super::programs(bank),states[i]) && crate::preservation::resource_safe(states[i].state)
        }
    }
    proof fn establish(&self,bank:Seq<core::Blueprint>,states:Seq<mx::Configuration<u64,core::Index>>)
        requires fs::execution(core::library(),super::super::programs(bank),states,labels(self.events@)),states.first()==mx::empty::<u64,core::Index>(),self.machine.represents(bank,states.last()),
        ensures self.refines(bank),
    {
        super::super::weak_theory();
        fs::from_empty_safe(|_:Port,x:u64,y:u64|x==y,core::library(),super::super::programs(bank),states,labels(self.events@));
    }
}

/// Executes a finite script from a new machine, stopping at its first error.
/// Source configurations and the authentic history are constructed internally.
#[verifier::spinoff_prover]
pub fn run_script(blueprints:Vec<Blueprint>,actions:&[ScriptAction])->(out:ScriptReport)
    ensures out.machine.wf(),out.refines(blueprints@.map(|_:int,bp:Blueprint|bp.compiled())),
        out.completed<=actions.len(),out.events.len()<=out.completed,
        out.error.is_none() ==> out.completed==actions.len(),out.error.is_some() ==> out.completed<actions.len(),
        forall|i:int|0<=i<out.events.len() ==> out.events[i].action_index<out.completed && out.events[i].effect.matches(actions[out.events[i].action_index as int]),
        forall|j:int|0<=j<out.completed ==> eventful(actions[j]) == (exists|k:int|0<=k<out.events.len() && out.events[k].action_index==j),
        forall|j:int,k:int|0<=j<k<out.events.len() ==> out.events[j].action_index<out.events[k].action_index,
{
    let ghost bank=blueprints@.map(|_:int,bp:Blueprint|bp.compiled());
    let mut session=Session::Ready {machine:FreshDriver::new(blueprints)};
    let mut events:Vec<ScriptEvent>=Vec::new();let mut i=0;
    let ghost mut states=seq![mx::empty::<u64,core::Index>()];
    proof {fs::empty_well_formed(core::library(),super::super::programs(bank));}
    while i<actions.len()
        invariant i<=actions.len(),events.len()<=i,session.wf(),bank==blueprints@.map(|_:int,bp:Blueprint|bp.compiled()),
            forall|j:int|0<=j<events.len() ==> events[j].action_index<i && events[j].effect.matches(actions[events[j].action_index as int]),
            forall|j:int|0<=j<i ==> eventful(actions[j]) == (exists|k:int|0<=k<events.len() && events[k].action_index==j),
            forall|j:int,k:int|0<=j<k<events.len() ==> events[j].action_index<events[k].action_index,
            states.first()==mx::empty::<u64,core::Index>(),fs::execution(core::library(),super::super::programs(bank),states,labels(events@)),
            session.machine().represents(bank,states.last()),fs::well_formed(core::library(),super::super::programs(bank),states.last()),
        decreases actions.len()-i,
    {
        let ghost before=session.machine();
        let ghost previous=events@;
        let acted=session.act(actions[i]);
        let next=acted.session;let emitted=acted.event;let failure=acted.error;
        session=next;
        if let Some(effect)=emitted {
            events.push(ScriptEvent {action_index:i,effect});
            proof {
                let z=before.advance_source(&session.machine(),bank,states.last(),effect.label().0,effect.label().1,effect.label().2);
                assert(labels(events@)==labels(previous).push(effect.label()));
                super::super::append_source(bank,states,labels(previous),z,effect.label());
                states=states.push(z);
            }
        } else {
            proof {session.machine().same_representation(&before,bank,states.last());}
        }
        if failure.is_some() {
            let out=ScriptReport {machine:session.into_driver(),events,completed:i,error:failure};
            proof {out.establish(bank,states);}return out;
        }
        proof {
            assert forall|j:int,k:int|0<=j<k<events.len() implies events[j].action_index<events[k].action_index by {
                if k<previous.len() {assert(events[j]==previous[j] && events[k]==previous[k]);}
                else {assert(k==previous.len());assert(events[k].action_index==i);assert(j<previous.len());}
            }
            assert forall|j:int|0<=j<i+1 implies eventful(actions[j]) == (exists|k:int|0<=k<events.len() && events[k].action_index==j) by {
                if j<i {
                    if eventful(actions[j]) {
                        let k=choose|k:int|0<=k<previous.len() && previous[k].action_index==j;
                        assert(events[k]==previous[k]);
                    } else {
                        assert forall|k:int|0<=k<events.len() implies events[k].action_index!=j by {
                            if k<previous.len() {assert(events[k]==previous[k]);}else{assert(events[k].action_index==i);}
                        }
                    }
                } else {
                    assert(j==i);
                    if eventful(actions[j]) {assert(emitted.is_some());assert(events[previous.len() as int].action_index==j);}
                    else {assert(events@==previous);}
                }
            }
        }
        i+=1;
    }
    let out=ScriptReport {machine:session.into_driver(),events,completed:i,error:None};
    proof {out.establish(bank,states);}out
}

}
