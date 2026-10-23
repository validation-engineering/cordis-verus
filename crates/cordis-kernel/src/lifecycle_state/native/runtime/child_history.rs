//! Erased source collection at the actual native mutation boundaries. Birth,
//! retirement and Unload remain distinct events, including after parent release.
pub mod completion;
pub mod cut;
use super::{child_recovery::Retirement, episode::Unload, owner::EpisodeOwner, NativeRuntime};
#[cfg(verus_keep_ghost)]
use crate::lifecycle_state::registration::shared_child::ChildSnapshot;
use crate::lifecycle_state::registration::shared_child::{Decision, SharedChild};
use crate::reversible_value::joint;
#[cfg(verus_keep_ghost)]
use crate::{refinement as r, Phase};
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::resource::Loc;

verus! {
broadcast use vstd::seq_lib::group_seq_properties;
pub open spec fn prefix<T>(a:Seq<T>,b:Seq<T>)->bool {a.len()<=b.len() && b.take(a.len() as int)==a}
pub proof fn prefix_transitive<T>(a:Seq<T>,b:Seq<T>,c:Seq<T>)
    requires prefix(a,b),prefix(b,c),ensures prefix(a,c),
{assert(c.take(a.len() as int) =~= b.take(a.len() as int));}


/// Created only by the successful shared-slot registration path, with the
/// actual parent's current episode and the exact native Insert commit.
#[allow(dead_code)]
pub tracked struct Birth {
    decision:Decision,
    receipt:joint::Receipt,
    ghost handle:SharedChild,
    ghost native:nat,
    ghost parent:EpisodeOwner,
}
impl Birth {
    pub closed spec fn source(&self)->Loc {self.decision.source()}
    pub closed spec fn child(&self)->SharedChild {self.handle}
    pub closed spec fn id(&self)->usize {self.decision.state()->Assigned_0.child()}
    pub closed spec fn native(&self)->nat {self.native}
    pub closed spec fn parent(&self)->EpisodeOwner {self.parent}
    pub closed spec fn checkpoint(&self)->joint::Receipt {self.receipt}
    pub open spec fn before(&self)->joint::native::State {joint::native::at(self.checkpoint().events(),self.checkpoint().at(),self.native())}
    pub open spec fn after(&self)->joint::native::State {self.checkpoint().event().after->Native_state}
    pub open spec fn belongs_to(&self,child:&SharedChild)->bool {
        self.wf() && child.wf() && self.source()==child.source()
            && self.child().domain_id()==child.domain_id() && self.child().owner()==child.owner() && self.child().episode()==child.episode()
    }
    #[verifier::opaque]
    pub closed spec fn wf(&self)->bool {
        &&& self.decision.wf() && self.decision.state() is Assigned && self.child().wf() && self.source()==self.child().source()
        &&& self.checkpoint().wf() && self.checkpoint().event().key==self.native()
        &&& self.checkpoint().event().change==(joint::Change::Native {actor:self.id(),rule:r::Rule::Insert})
        &&& self.checkpoint().event().after is Native
        &&& joint::native::step(self.before(),self.after(),self.id(),r::Rule::Insert)
        &&& r::step(self.before().control,self.after().control,self.id(),r::Rule::Insert)
        &&& self.before().owners.contains_pair(self.child().owner(),self.parent())
        &&& self.parent().origin.id==self.child().owner() && self.parent().origin.domain==self.child().domain_id()
        &&& Some(self.parent().origin.generation)==self.child().episode()
        &&& self.after().control.fibers[self.id()].parent==Some(self.child().owner())
    }
    pub proof fn facts(&self)
        requires self.wf(),
        ensures self.checkpoint().wf(),self.checkpoint().event().key==self.native(),self.checkpoint().event().after is Native,self.child().wf(),self.source()==self.child().source(),
            !r::registered(self.before().control,self.id()),r::registered(self.after().control,self.id()),
            self.after().control.fibers[self.id()].parent==Some(self.child().owner()),
            self.after().control.fibers[self.id()].phase==Phase::Inactive,
            self.before().owners.contains_pair(self.child().owner(),self.parent()),
            self.parent().origin.id==self.child().owner(),self.parent().origin.domain==self.child().domain_id(),
            Some(self.parent().origin.generation)==self.child().episode(),
    {reveal(Birth::wf);}
    /// The persistent slot decision, rather than equal numeric IDs, links
    /// the observed retirement to this real successful registration.
    pub proof fn retirement_agrees(tracked &self,tracked retirement:&Retirement)
        requires self.wf(),retirement.wf(),retirement.source()==self.source(),
        ensures retirement.assigned(),retirement.child()==self.id(),
    {
        reveal(Birth::wf);
        self.decision.agrees_decision(retirement.decision_witness());
    }
    pub open spec fn matches_retirement(&self,retirement:&Retirement)->bool {
        self.belongs_to(&self.child()) && retirement.belongs_to(&self.child()) && retirement.assigned()
            && self.id()==retirement.child() && self.native()==retirement.native()
            && retirement.checkpoint().covers(&self.checkpoint())
    }
}

/// Three append-only sequences retain every successful operation in its category.
/// Indices are proof-only: no runtime allocation, traversal or payload clone.
#[allow(dead_code)]
pub tracked struct Ledger {
    ghost native:nat,
    ghost journal:joint::Journal,
    births:Seq<Birth>,
    retirements:Seq<Retirement>,
    unloads:Seq<Unload>,
}
impl Ledger {
    pub closed spec fn native(&self)->nat {self.native}
    pub closed spec fn journal(&self)->joint::Journal {self.journal}
    pub closed spec fn births(&self)->Seq<Birth> {self.births}
    pub closed spec fn retirements(&self)->Seq<Retirement> {self.retirements}
    pub closed spec fn unloads(&self)->Seq<Unload> {self.unloads}
    #[verifier::opaque]
    pub open spec fn wf(&self)->bool {
        &&& forall|i:int|0<=i<self.births().len() ==> (#[trigger] self.births()[i]).wf()
            && self.births()[i].native()==self.native() && self.births()[i].checkpoint().journal()==self.journal()
        &&& forall|i:int|0<=i<self.retirements().len() ==> (#[trigger] self.retirements()[i]).wf()
            && self.retirements()[i].native()==self.native() && self.retirements()[i].checkpoint().journal()==self.journal()
        &&& forall|i:int|0<=i<self.unloads().len() ==> (#[trigger] self.unloads()[i]).wf()
            && self.unloads()[i].native()==self.native() && self.unloads()[i].checkpoint().journal()==self.journal()
    }
    pub open spec fn covered(&self,cut:Seq<joint::Frame>)->bool {
        &&& forall|i:int|0<=i<self.births().len() ==> prefix((#[trigger] self.births()[i]).checkpoint().events(),cut)
        &&& forall|i:int|0<=i<self.retirements().len() ==> prefix((#[trigger] self.retirements()[i]).checkpoint().events(),cut)
        &&& forall|i:int|0<=i<self.unloads().len() ==> prefix((#[trigger] self.unloads()[i]).checkpoint().events(),cut)
    }
    pub proof fn extend_cut(&self,before:Seq<joint::Frame>,after:Seq<joint::Frame>)
        requires self.covered(before),prefix(before,after),ensures self.covered(after),
    {reveal(Ledger::wf);
        assert forall|i:int|0<=i<self.births().len() implies prefix((#[trigger] self.births()[i]).checkpoint().events(),after) by {
            prefix_transitive(self.births()[i].checkpoint().events(),before,after);
        }
        assert forall|i:int|0<=i<self.retirements().len() implies prefix((#[trigger] self.retirements()[i]).checkpoint().events(),after) by {
            prefix_transitive(self.retirements()[i].checkpoint().events(),before,after);
        }
        assert forall|i:int|0<=i<self.unloads().len() implies prefix((#[trigger] self.unloads()[i]).checkpoint().events(),after) by {
            prefix_transitive(self.unloads()[i].checkpoint().events(),before,after);
        }
    }
    pub proof fn source_order(&self,cut:&joint::Receipt)
        requires self.wf(),self.covered(cut.events()),cut.wf(),cut.journal()==self.journal(),
        ensures forall|b:int|0<=b<self.births().len() ==> cut.covers(&(#[trigger] self.births()[b]).checkpoint()),
    {reveal(Ledger::wf);}
    pub open spec fn extends(&self,earlier:&Self)->bool {
        self.native()==earlier.native() && self.journal()==earlier.journal()
            && prefix(earlier.births(),self.births()) && prefix(earlier.retirements(),self.retirements()) && prefix(earlier.unloads(),self.unloads())
    }
    pub proof fn transitive(&self,middle:&Self,earlier:&Self)
        requires self.extends(middle),middle.extends(earlier),ensures self.extends(earlier),
    {reveal(Ledger::wf);
        prefix_transitive(earlier.births(),middle.births(),self.births());
        prefix_transitive(earlier.retirements(),middle.retirements(),self.retirements());
        prefix_transitive(earlier.unloads(),middle.unloads(),self.unloads());
    }
    pub proof fn new(native:nat,journal:joint::Journal)->(tracked out:Self)
        ensures out.wf(),out.native()==native,out.journal()==journal,out.births()==Seq::empty(),out.retirements()==Seq::empty(),out.unloads()==Seq::empty(),
    {reveal(Ledger::wf);Self {native,journal,births:Seq::tracked_empty(),retirements:Seq::tracked_empty(),unloads:Seq::tracked_empty()}}
    pub(crate) proof fn birth(tracked &mut self,tracked birth:Birth,cut:Seq<joint::Frame>)
        requires old(self).covered(cut),prefix(birth.checkpoint().events(),cut),old(self).wf(),birth.wf(),birth.native()==old(self).native(),birth.checkpoint().journal()==old(self).journal(),
        ensures final(self).covered(cut),final(self).wf(),final(self).extends(old(self)),final(self).births()==old(self).births().push(birth),
            final(self).retirements()==old(self).retirements(),final(self).unloads()==old(self).unloads(),
    {reveal(Ledger::wf);
        let ghost prior=*self;
        self.births.tracked_push(birth);
        assert(self.births()==prior.births().push(birth));
        assert(self.native()==prior.native());assert(self.journal()==prior.journal());
        assert(self.retirements()==prior.retirements());
        assert forall|i:int|0<=i<self.retirements().len() implies (#[trigger] self.retirements()[i]).wf()
            && self.retirements()[i].native()==self.native() && self.retirements()[i].checkpoint().journal()==self.journal() by {
            assert(prior.retirements()[i].wf());
        }
        assert forall|i:int|0<=i<self.retirements().len() implies prefix((#[trigger] self.retirements()[i]).checkpoint().events(),cut) by {
            assert(prefix(prior.retirements()[i].checkpoint().events(),cut));
        }
        assert(self.unloads()==prior.unloads());
        assert forall|i:int|0<=i<self.unloads().len() implies (#[trigger] self.unloads()[i]).wf()
            && self.unloads()[i].native()==self.native() && self.unloads()[i].checkpoint().journal()==self.journal() by {
            assert(prior.unloads()[i].wf());
        }
        assert forall|i:int|0<=i<self.unloads().len() implies prefix((#[trigger] self.unloads()[i]).checkpoint().events(),cut) by {
            assert(prefix(prior.unloads()[i].checkpoint().events(),cut));
        }
        assert(self.births().take(prior.births().len() as int) =~= prior.births());
        assert forall|i:int|0<=i<self.births().len() implies prefix((#[trigger] self.births()[i]).checkpoint().events(),cut) by {
            if i<prior.births().len() {assert(self.births()[i]==prior.births()[i]);}
            else {assert(self.births()[i]==birth);}
        }
        assert forall|i:int|0<=i<self.births().len() implies (#[trigger] self.births()[i]).wf()
            && self.births()[i].native()==self.native() && self.births()[i].checkpoint().journal()==self.journal() by {
            if i<prior.births().len() {assert(self.births()[i]==prior.births()[i]);}
            else {assert(self.births()[i]==birth);}
        }
    }
    pub(crate) proof fn retire(tracked &mut self,tracked retirement:Retirement,cut:Seq<joint::Frame>)
        requires old(self).covered(cut),prefix(retirement.checkpoint().events(),cut),old(self).wf(),retirement.wf(),retirement.native()==old(self).native(),retirement.checkpoint().journal()==old(self).journal(),
        ensures final(self).covered(cut),final(self).wf(),final(self).extends(old(self)),final(self).retirements()==old(self).retirements().push(retirement),
            final(self).births()==old(self).births(),final(self).unloads()==old(self).unloads(),
    {reveal(Ledger::wf);
        let ghost prior=*self;
        self.retirements.tracked_push(retirement);
        assert(self.retirements()==prior.retirements().push(retirement));
        assert(self.native()==prior.native());assert(self.journal()==prior.journal());
        assert(self.births()==prior.births());
        assert forall|i:int|0<=i<self.births().len() implies (#[trigger] self.births()[i]).wf()
            && self.births()[i].native()==self.native() && self.births()[i].checkpoint().journal()==self.journal() by {
            assert(prior.births()[i].wf());
        }
        assert forall|i:int|0<=i<self.births().len() implies prefix((#[trigger] self.births()[i]).checkpoint().events(),cut) by {
            assert(prefix(prior.births()[i].checkpoint().events(),cut));
        }
        assert(self.unloads()==prior.unloads());
        assert forall|i:int|0<=i<self.unloads().len() implies (#[trigger] self.unloads()[i]).wf()
            && self.unloads()[i].native()==self.native() && self.unloads()[i].checkpoint().journal()==self.journal() by {
            assert(prior.unloads()[i].wf());
        }
        assert forall|i:int|0<=i<self.unloads().len() implies prefix((#[trigger] self.unloads()[i]).checkpoint().events(),cut) by {
            assert(prefix(prior.unloads()[i].checkpoint().events(),cut));
        }
        assert(self.retirements().take(prior.retirements().len() as int) =~= prior.retirements());
        assert forall|i:int|0<=i<self.retirements().len() implies prefix((#[trigger] self.retirements()[i]).checkpoint().events(),cut) by {
            if i<prior.retirements().len() {assert(self.retirements()[i]==prior.retirements()[i]);}
            else {assert(self.retirements()[i]==retirement);}
        }
        assert forall|i:int|0<=i<self.retirements().len() implies (#[trigger] self.retirements()[i]).wf()
            && self.retirements()[i].native()==self.native() && self.retirements()[i].checkpoint().journal()==self.journal() by {
            if i<prior.retirements().len() {assert(self.retirements()[i]==prior.retirements()[i]);}
            else {assert(self.retirements()[i]==retirement);}
        }
    }
    pub(crate) proof fn unload(tracked &mut self,tracked end:Unload,cut:Seq<joint::Frame>)
        requires old(self).covered(cut),prefix(end.checkpoint().events(),cut),old(self).wf(),end.wf(),end.native()==old(self).native(),end.checkpoint().journal()==old(self).journal(),
        ensures final(self).covered(cut),final(self).wf(),final(self).extends(old(self)),final(self).unloads()==old(self).unloads().push(end),
            final(self).births()==old(self).births(),final(self).retirements()==old(self).retirements(),
    {reveal(Ledger::wf);
        let ghost prior=*self;
        self.unloads.tracked_push(end);
        assert(self.unloads()==prior.unloads().push(end));
        assert(self.native()==prior.native());assert(self.journal()==prior.journal());
        assert(self.births()==prior.births());
        assert forall|i:int|0<=i<self.births().len() implies (#[trigger] self.births()[i]).wf()
            && self.births()[i].native()==self.native() && self.births()[i].checkpoint().journal()==self.journal() by {
            assert(prior.births()[i].wf());
        }
        assert forall|i:int|0<=i<self.births().len() implies prefix((#[trigger] self.births()[i]).checkpoint().events(),cut) by {
            assert(prefix(prior.births()[i].checkpoint().events(),cut));
        }
        assert(self.retirements()==prior.retirements());
        assert forall|i:int|0<=i<self.retirements().len() implies (#[trigger] self.retirements()[i]).wf()
            && self.retirements()[i].native()==self.native() && self.retirements()[i].checkpoint().journal()==self.journal() by {
            assert(prior.retirements()[i].wf());
        }
        assert forall|i:int|0<=i<self.retirements().len() implies prefix((#[trigger] self.retirements()[i]).checkpoint().events(),cut) by {
            assert(prefix(prior.retirements()[i].checkpoint().events(),cut));
        }
        assert(self.unloads().take(prior.unloads().len() as int) =~= prior.unloads());
        assert forall|i:int|0<=i<self.unloads().len() implies prefix((#[trigger] self.unloads()[i]).checkpoint().events(),cut) by {
            if i<prior.unloads().len() {assert(self.unloads()[i]==prior.unloads()[i]);}
            else {assert(self.unloads()[i]==end);}
        }
        assert forall|i:int|0<=i<self.unloads().len() implies (#[trigger] self.unloads()[i]).wf()
            && self.unloads()[i].native()==self.native() && self.unloads()[i].checkpoint().journal()==self.journal() by {
            if i<prior.unloads().len() {assert(self.unloads()[i]==prior.unloads()[i]);}
            else {assert(self.unloads()[i]==end);}
        }
    }
    pub proof fn birth_witness(tracked &self,index:int)->(tracked out:&Birth)
        requires self.wf(),0<=index<self.births().len(),ensures *out==self.births()[index],out.wf(),
    {reveal(Ledger::wf);self.births.tracked_borrow(index)}
    pub proof fn retirement_witness(tracked &self,index:int)->(tracked out:&Retirement)
        requires self.wf(),0<=index<self.retirements().len(),ensures *out==self.retirements()[index],out.wf(),
    {reveal(Ledger::wf);self.retirements.tracked_borrow(index)}
    pub proof fn unload_witness(tracked &self,index:int)->(tracked out:&Unload)
        requires self.wf(),0<=index<self.unloads().len(),ensures *out==self.unloads()[index],out.wf(),
    {reveal(Ledger::wf);self.unloads.tracked_borrow(index)}
}

impl<R,H,V> NativeRuntime<R,H,V> {
    pub open spec fn child_records_valid(&self)->bool {
        self.child_records().wf() && self.child_records().covered(self.joint_events()) && self.child_records().native()==self.joint_key() && self.child_records().journal()==self.journal_spec()
    }
    pub proof fn child_history(tracked &self)->(tracked out:&Ledger)
        requires self.wf(),ensures *out==self.child_records(),out.wf(),out.native()==self.joint_key(),out.journal()==self.journal_spec(),
    {self.children.borrow()}
    pub(crate) proof fn child_birth(tracked &self,child:&SharedChild,tracked snapshot:&ChildSnapshot)->(tracked out:Birth)
        requires self.wf(),child.wf(),snapshot.wf(),snapshot.source()==child.source(),snapshot.state() is Assigned,
            self.execution_history().labels.len()>0,
            self.execution_history().labels.last()==(snapshot.state()->Assigned_0.child(),r::Rule::Insert),
            self.history_positions().last()+1==self.joint_events().len(),
            r::registered(self.observation().control,snapshot.state()->Assigned_0.child()),
            self.observation().control.fibers[snapshot.state()->Assigned_0.child()].parent==Some(child.owner()),
            self.episode_owners().contains_key(child.owner()),
            self.episode_owners()[child.owner()].origin.id==child.owner(),self.episode_owners()[child.owner()].origin.domain==child.domain_id(),
            Some(self.episode_owners()[child.owner()].origin.generation)==child.episode(),
        ensures out.wf(),out.belongs_to(child),out.child()==*child,out.id()==snapshot.state()->Assigned_0.child(),
            out.native()==self.joint_key(),out.checkpoint().journal()==self.journal_spec(),out.checkpoint().events()==self.joint_events(),out.parent()==self.episode_owners()[child.owner()],
    {
        hide(joint::valid);hide(joint::step);reveal(Birth::wf);reveal(NativeRuntime::joint_valid);reveal(NativeRuntime::observation);reveal(NativeRuntime::joint_events);
        let history=self.execution_history();let last=history.labels.len()-1;let id=snapshot.state()->Assigned_0.child();
        let tracked receipt=self.joint.receipt();
        history.interval(self.history_positions(),receipt.events(),self.joint.key(),last);
        assert(super::history::step(history.states[last],history.states[last+1],id,r::Rule::Insert));
        super::history::project_step(history.states[last],history.states[last+1],id,r::Rule::Insert,last as nat);
        assert(self.history_positions()[last+1]==receipt.at());
        let tracked decision=snapshot.retain_decision();
        let tracked out=Birth {decision,receipt,handle:*child,native:self.joint_key(),parent:self.episode_owners()[child.owner()]};
        assert(out.before()==history.states[last].project(last as nat));
        assert(out.after()==history.states[last+1].project((last+1) as nat));
        assert(out.wf());out
    }
}
}
