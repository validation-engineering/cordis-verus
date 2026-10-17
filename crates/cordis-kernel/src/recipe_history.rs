//! Typed registration history produced at the actual native mutation boundary.
//! Cargo erases every old body and trace entry; only the shared journal handle
//! participates at runtime. A call event identifies a returned invocation, not
//! the completion of a Future or a proof of arbitrary callback effects.
#[cfg(verus_keep_ghost)]
use crate::lifecycle_state::native::NativeEntry;
use crate::lifecycle_state::registration::RegisteredPlugin;
use crate::reversible_value::joint::{self, recipes as r};
use vstd::prelude::*;
verus! {
broadcast use vstd::seq_lib::group_seq_properties;
pub open spec fn entries<R,H>(host:Map<usize,NativeEntry<R,H>>)->Map<usize,RegisteredPlugin<R>> {
    Map::new(host.dom(),|id:usize|host[id].recipe())
}
pub open spec fn shape<R>(recipe:RegisteredPlugin<R>)->r::Shape {
    r::Shape {domain:recipe.domain_id(),id:recipe.owner(),parent:recipe.parent_id(),anchor:recipe.anchor_port(),realms:recipe.realms(),
        dependencies:recipe.dependencies_spec(),provisions:recipe.provisions_spec(),version:recipe.version()}
}
pub open spec fn project<R>(entries:Map<usize,RegisteredPlugin<R>>)->Map<usize,r::Shape> {
    Map::new(entries.dom(),|id:usize|shape(entries[id]))
}
pub open spec fn step<R>(a:Map<usize,RegisteredPlugin<R>>,b:Map<usize,RegisteredPlugin<R>>,event:r::Event)->bool {
    let id=event.actor();
    match event {
        r::Event::Insert {..}=>!a.contains_key(id) && b.contains_key(id) && b==a.insert(id,b[id]) && b[id].version()==0,
        r::Event::Remove {..}=>a.contains_key(id) && b==a.remove(id),
        r::Event::Replace {..}=>a.contains_key(id) && b.contains_key(id) && b==a.insert(id,b[id])
            && b[id].same_identity(&a[id]) && a[id].version()<u64::MAX && b[id].version()==a[id].version()+1,
        r::Event::Call {version,..}=>a.contains_key(id) && b.contains_key(id) && b==a.insert(id,b[id])
            && b[id].same_identity(&a[id]) && b[id].version()==a[id].version() && a[id].version()==version,
    }
}
pub proof fn project_step<R>(a:Map<usize,RegisteredPlugin<R>>,b:Map<usize,RegisteredPlugin<R>>,event:r::Event,native:nat,revision:nat)
    requires step(a,b,event),
    ensures r::step(r::State {native,revision,entries:project(a)},r::State {native,revision:revision+1,entries:project(b)},event),
{
    reveal(r::step);let id=event.actor();
    if event is Remove {assert(project(b) =~= project(a).remove(id));}
    else if event is Call {assert(project(b) =~= project(a));}
    else {assert(project(b) =~= project(a).insert(id,shape(b[id])));}
}
pub struct History<R> {pub states:Seq<Map<usize,RegisteredPlugin<R>>>,pub events:Seq<r::Event>}
impl<R> History<R> {
    pub open spec fn valid(&self)->bool {
        self.states.len()==self.events.len()+1 && self.states[0]==Map::empty()
            && forall|i:int|0<=i<self.events.len() ==> step(self.states[i],self.states[i+1],#[trigger] self.events[i])
    }
    pub open spec fn indexed(&self,positions:Seq<nat>,frames:Seq<joint::Frame>,key:nat,native:nat)->bool {
        &&& positions.len()==self.states.len()
        &&& forall|i:int|0<=i<self.states.len() ==> #[trigger] positions[i]<frames.len()
            && frames[positions[i] as int].event.key==key
            && frames[positions[i] as int].event.after==(joint::Record::Recipes {state:r::State {native,revision:i as nat,entries:project(self.states[i])}})
            && frames[positions[i] as int].event.change==if i==0 {joint::Change::Allocate} else {joint::Change::Recipes {event:self.events[i-1]}}
        &&& forall|i:int,j:int|0<=i<j<self.states.len() ==> #[trigger] positions[i]<#[trigger] positions[j]
    }
    pub proof fn extend_indexed(&self,positions:Seq<nat>,before:Seq<joint::Frame>,after:Seq<joint::Frame>,key:nat,native:nat)
        requires self.indexed(positions,before,key,native),before.len()<=after.len(),after.take(before.len() as int)==before,
        ensures self.indexed(positions,after,key,native),
    {
        assert forall|i:int|0<=i<self.states.len() implies #[trigger] positions[i]<after.len()
            && after[positions[i] as int].event.key==key
            && after[positions[i] as int].event.after==(joint::Record::Recipes {state:r::State {native,revision:i as nat,entries:project(self.states[i])}})
            && after[positions[i] as int].event.change==if i==0 {joint::Change::Allocate} else {joint::Change::Recipes {event:self.events[i-1]}} by {
            assert(after[positions[i] as int]==before[positions[i] as int]);
        }
    }
    pub open spec fn append(&self,next:Map<usize,RegisteredPlugin<R>>,event:r::Event)->Self {Self {states:self.states.push(next),events:self.events.push(event)}}
    pub proof fn extended(&self,next:Map<usize,RegisteredPlugin<R>>,event:r::Event)
        requires self.valid(),step(self.states.last(),next,event),ensures self.append(next,event).valid(),
    {
        assert forall|i:int|0<=i<self.events.len()+1 implies step(self.states.push(next)[i],self.states.push(next)[i+1],#[trigger] self.events.push(event)[i]) by {
            if i<self.events.len() {assert(step(self.states[i],self.states[i+1],self.events[i]));}
        }
    }
    pub proof fn installed_origin(&self,index:int,id:usize)
        requires self.valid(),0<=index<self.states.len(),self.states[index].contains_key(id),
        ensures exists|at:int|0<=at<index && (self.events[at]==r::Event::Insert {id} || self.events[at]==r::Event::Replace {id})
            && self.states[at+1].contains_key(id) && self.states[at+1][id].same_identity(&self.states[index][id])
            && self.states[at+1][id].version()==self.states[index][id].version(),
        decreases index,
    {
        assert(index>0);let i=index-1;assert(step(self.states[i],self.states[index],self.events[i]));
        if self.events[i]!=(r::Event::Insert {id}) && self.events[i]!=(r::Event::Replace {id}) {
            assert(self.states[i].contains_key(id));
            self.installed_origin(i,id);
            let at=choose|at:int|0<=at<i && (self.events[at]==r::Event::Insert {id} || self.events[at]==r::Event::Replace {id})
                && self.states[at+1].contains_key(id) && self.states[at+1][id].same_identity(&self.states[i][id])
                && self.states[at+1][id].version()==self.states[i][id].version();
            assert(self.states[at+1][id].same_identity(&self.states[index][id]));
        }
    }
    pub proof fn append_indexed(&self,positions:Seq<nat>,before:Seq<joint::Frame>,after:Seq<joint::Frame>,key:nat,native:nat,next:Map<usize,RegisteredPlugin<R>>,event:r::Event)
        requires self.valid(),self.indexed(positions,before,key,native),before.len()<after.len(),after.take(before.len() as int)==before,
            after.last().event.key==key,after.last().event.change==(joint::Change::Recipes {event}),
            after.last().event.after==(joint::Record::Recipes {state:r::State {native,revision:self.states.len(),entries:project(next)}}),
        ensures self.append(next,event).indexed(positions.push((after.len()-1) as nat),after,key,native),
    {
        self.extend_indexed(positions,before,after,key,native);let updated=positions.push((after.len()-1) as nat);
        assert forall|i:int,j:int|0<=i<j<self.states.len()+1 implies #[trigger] updated[i]<#[trigger] updated[j] by {
            if j==self.states.len() {assert(positions[i]<before.len());}
        }
    }
}
#[allow(dead_code)]
pub(crate) struct Ledger<R> {history:Ghost<History<R>>,positions:Ghost<Seq<nat>>,native:Ghost<nat>,member:joint::Member}
impl<R> Ledger<R> {
    pub closed spec fn history(&self)->History<R> {self.history@}
    pub closed spec fn positions(&self)->Seq<nat> {self.positions@}
    pub closed spec fn frames(&self)->Seq<joint::Frame> {self.member.events()}
    pub closed spec fn journal(&self)->joint::Journal {self.member.journal()}
    pub closed spec fn key(&self)->nat {self.member.key()}
    pub closed spec fn native(&self)->nat {self.native@}
    pub open spec fn current(&self)->Map<usize,RegisteredPlugin<R>> {self.history().states.last()}
    pub open spec fn record(&self)->r::State {r::State {native:self.native(),revision:self.history().events.len(),entries:project(self.current())}}
    pub closed spec fn wf(&self)->bool {
        self.history().valid() && self.member.wf() && self.member.record()==(joint::Record::Recipes {state:self.record()})
            && self.history().indexed(self.positions(),self.member.events(),self.key(),self.native())
    }
    pub(crate) fn receipt(&self)->(out:Tracked<joint::Receipt>)
        requires self.wf(),
        ensures out@.wf(),out@.journal()==self.journal(),out@.events()==self.frames(),
            out@.event().key==self.key(),out@.event().after==(joint::Record::Recipes {state:self.record()}),
    {Tracked(self.member.receipt())}
    pub(crate) fn new(journal:&joint::Journal,Ghost(native):Ghost<nat>)->(out:Self)
        ensures out.wf(),out.journal()==*journal,out.native()==native,out.current()==Map::empty(),out.history().events.len()==0,
    {
        let member=journal.allocate(Ghost(joint::Record::Recipes {state:r::State {native,revision:0,entries:Map::empty()}}));
        let ghost positions=seq![(member.events().len()-1) as nat];
        proof {assert(project::<R>(Map::empty()) =~= Map::empty());}
        Self {history:Ghost(History {states:seq![Map::empty()],events:Seq::empty()}),positions:Ghost(positions),native:Ghost(native),member}
    }
    pub(crate) fn advance<'a>(&mut self,view:joint::WriteView<'a>,Ghost(next):Ghost<Map<usize,RegisteredPlugin<R>>>,Ghost(event):Ghost<r::Event>)->(out:joint::WriteView<'a>)
        requires old(self).wf(),view.wf(),view.journal_spec()==old(self).journal(),step(old(self).current(),next,event),
            r::guard(view.state(),old(self).record(),event),
        ensures final(self).wf(),final(self).journal()==old(self).journal(),final(self).key()==old(self).key(),final(self).native()==old(self).native(),
            final(self).history()==old(self).history().append(next,event),final(self).current()==next,
            out.wf(),out.journal_spec()==view.journal_spec(),out.events()==final(self).frames(),
            out.events().len()==view.events().len()+1,out.events().take(view.events().len() as int)==view.events(),
            out.events().last().event.change==(joint::Change::Recipes {event}),
    {
        let ghost prior=*self;
        proof {project_step(self.current(),next,event,self.native(),self.history().events.len());reveal(joint::changes);}
        let view=self.member.update_guarded(view,Ghost(joint::Record::Recipes {state:r::State {native:self.native(),revision:self.history().events.len()+1,entries:project(next)}}),Ghost(joint::Change::Recipes {event}));
        proof {
            prior.history().extended(next,event);
            prior.history().append_indexed(prior.positions(),prior.member.events(),self.member.events(),self.key(),self.native(),next,event);
            self.history=Ghost(prior.history().append(next,event));self.positions=Ghost(prior.positions().push((self.member.events().len()-1) as nat));
        }
        view
    }
    pub(crate) fn snapshot(&self,native:&joint::Member)->(out:Snapshot<R>)
        requires self.wf(),native.wf(),native.journal()==self.journal(),native.key()==self.native(),
        ensures out.certified(),out.history()==self.history(),out.key()==self.key(),out.native()==self.native(),out.joint_spec().journal_spec()==self.journal(),
            out.joint_spec().last().contains_pair(self.native(),native.record()),
    {
        let journal=self.member.domain();let view=journal.read();self.member.certify(&view);native.certify(&view);
        proof {self.history().extend_indexed(self.positions(),self.member.events(),view.events(),self.key(),self.native());}
        let snapshot=view.finish();
        Snapshot {joint:snapshot,history:Ghost(self.history()),positions:Ghost(self.positions()),key:Ghost(self.key()),native:Ghost(self.native())}
    }
}
#[allow(dead_code)]
pub struct Snapshot<R> {joint:joint::Snapshot,history:Ghost<History<R>>,positions:Ghost<Seq<nat>>,key:Ghost<nat>,native:Ghost<nat>}
impl<R> Snapshot<R> {
    pub closed spec fn history(&self)->History<R> {self.history@}
    pub closed spec fn key(&self)->nat {self.key@}
    pub closed spec fn native(&self)->nat {self.native@}
    pub closed spec fn positions(&self)->Seq<nat> {self.positions@}
    pub closed spec fn joint_spec(&self)->joint::Snapshot {self.joint}
    pub closed spec fn certified(&self)->bool {
        self.joint_spec().certified() && self.history().valid()
            && self.history().indexed(self.positions(),self.joint_spec().events(),self.key(),self.native())
            && self.joint_spec().last().contains_pair(self.key(),joint::Record::Recipes {state:r::State {native:self.native(),revision:self.history().events.len(),entries:project(self.history().states.last())}})
    }
    proof fn complete_at(&self,n:nat)->(index:int)
        requires self.certified(),n<self.joint_spec().events().len(),
            self.joint_spec().events()[n as int].event.key==self.key(),
        ensures 0<=index<self.history().states.len(),self.positions()[index]==n,
    {
        let frames=self.joint_spec().events();let key=self.key();let positions=self.positions();let h=self.history();
        self.joint.valid_history();
        if n<positions[0] {
            assert(joint::step(joint::state_at(frames,n),frames[n as int].state,frames[n as int].event));
            assert(joint::state_at(frames,n+1).contains_key(key));
            joint::key_persists(frames,n+1,positions[0],key);
            assert(frames[positions[0] as int].event.change==joint::Change::Allocate);
            assert(joint::step(joint::state_at(frames,positions[0]),frames[positions[0] as int].state,frames[positions[0] as int].event));
            assert(false);
        }
        if n==positions[0] {0} else {
            let start=positions[0];
            assert(0<h.states.len());assert(positions[0]<frames.len());
            assert(frames[start as int].event.after==(joint::Record::Recipes {state:r::State {native:self.native(),revision:0,entries:project(h.states[0])}}));
            assert(joint::step(joint::state_at(frames,start),frames[start as int].state,frames[start as int].event));
            assert(r::recorded(frames,start+1,key));
            r::monotone(frames,start+1,n,key);r::edge(frames,n,key);
            r::monotone(frames,n+1,frames.len(),key);
            assert(r::at(frames,frames.len(),key)==(r::State {native:self.native(),revision:h.events.len(),entries:project(h.states.last())}));
            let i=frames[n as int].event.after->Recipes_state.revision as int;
            assert(0<=i<h.states.len());
            assert(positions[i]<frames.len());
            assert(frames[positions[i] as int].event.after==(joint::Record::Recipes {state:r::State {native:self.native(),revision:i as nat,entries:project(h.states[i])}}));
            r::unique_revision(frames,n,positions[i],key);
            i
        }
    }
    /// Every mutation of this recipe owner in the complete checkpoint is an
    /// indexed typed state. Other records may interleave, but none is hidden.
    pub proof fn complete_projection(&self)
        requires self.certified(),
        ensures forall|n:int| 0<=n<self.joint_spec().events().len()
            && #[trigger] self.joint_spec().events()[n].event.key==self.key() ==>
                exists|i:int| 0<=i<self.history().states.len() && self.positions()[i]==n,
    {
        assert forall|n:int| 0<=n<self.joint_spec().events().len()
            && #[trigger] self.joint_spec().events()[n].event.key==self.key() implies
                exists|i:int| 0<=i<self.history().states.len() && self.positions()[i]==n by {
            let i=self.complete_at(n as nat);assert(self.positions()[i]==n);
        }
    }
    /// The actual call event names an installed version and the native Episode
    /// observed in the same journal epoch. A replacement does not forge Begin.
    pub proof fn invocation_origin(&self,index:int)
        requires self.certified(),0<=index<self.history().events.len(),self.history().events[index] is Call,
        ensures {
            let event=self.history().events[index];let id=event.actor();let pos=self.positions()[index+1];let frames=self.joint_spec().events();
            &&& self.history().states[index].contains_key(id)
            &&& self.history().states[index][id].version()==event->Call_version
            &&& exists|at:int|0<=at<index && (self.history().events[at]==r::Event::Insert {id} || self.history().events[at]==r::Event::Replace {id})
                && self.history().states[at+1].contains_key(id)
                && self.history().states[at+1][id].same_identity(&self.history().states[index][id])
                && self.history().states[at+1][id].version()==event->Call_version
            &&& joint::state_at(frames,pos).contains_key(self.native())
            &&& joint::state_at(frames,pos)[self.native()] is Native
            &&& r::native_guard(joint::state_at(frames,pos)[self.native()]->Native_state,event)
        },
    {
        let h=self.history();let event=h.events[index];let id=event.actor();let pos=self.positions()[index+1];let frames=self.joint_spec().events();
        self.joint.valid_history();assert(step(h.states[index],h.states[index+1],event));h.installed_origin(index,id);
        assert(joint::step(joint::state_at(frames,pos),frames[pos as int].state,frames[pos as int].event));
        assert(frames[pos as int].event.change==(joint::Change::Recipes {event}));
        reveal(joint::changes);reveal(r::step);
    }
    pub fn joint(&self)->(out:&joint::Snapshot) ensures *out==self.joint_spec(), {&self.joint}
}
}
