//! Constructive replay through the production Kernel, not a state installer.
//! Native source adapters establish the private execution preconditions. Values,
//! callback bodies and action-ledger tickets are not this control projection.
#[path = "kernel_replay_names.rs"]
pub mod names;
#[cfg(verus_keep_ghost)]
use crate::{alpha, Phase};
use crate::{refinement as r, Error, Kernel, Port};
use vstd::prelude::*;

verus! {
broadcast use vstd::seq_lib::group_seq_properties;
pub enum Command {
    Insert {actor:usize,parent:Option<usize>,dependencies:Vec<Port>,provisions:Vec<Port>},
    Step {actor:usize,rule:r::Rule},
}
impl Command {
    /// Preserve the resolved production inputs, including inherited dependencies
    /// and the private reservation anchor omitted from published service values.
    pub fn from_registration<R>(recipe:&crate::lifecycle_state::registration::RegisteredPlugin<R>)->(out:Self)
        ensures out is Insert,out.actor()==recipe.owner(),out->Insert_parent==recipe.parent_id(),
            out->Insert_dependencies@==recipe.dependencies_spec(),
            out->Insert_provisions@==recipe.provisions_spec().push(recipe.anchor_port()),
    {
        let dependencies=copy_slice(recipe.dependencies());let mut provisions=recipe.provisions_vec();provisions.push(recipe.anchor());
        Self::Insert {actor:recipe.id(),parent:recipe.parent(),dependencies,provisions}
    }
    pub open spec fn actor(&self)->usize {match self {Self::Insert {actor,..}|Self::Step {actor,..}=>*actor}}
    pub open spec fn rule(&self)->r::Rule {match self {Self::Insert {..}=>r::Rule::Insert,Self::Step {rule,..}=>*rule}}
    pub open spec fn shape(&self)->bool {match self {
        Self::Insert {dependencies,provisions,..}=>crate::distinct_ports(dependencies@) && crate::distinct_ports(provisions@),
        Self::Step {rule,..}=>*rule!=r::Rule::Insert,
    }}
    pub open spec fn payload(&self,z:r::State)->bool {match self {
        Self::Insert {actor,parent,dependencies,provisions}=>z.fibers[*actor].parent==*parent
            && z.fibers[*actor].dependencies==ports(dependencies@) && z.fibers[*actor].provisions==ports(provisions@),
        _=>true,
    }}
    pub open spec fn same(&self,other:Self)->bool {match (self,other) {
        (Self::Insert {actor:a,parent:p,dependencies:d,provisions:v},Self::Insert {actor:b,parent:q,dependencies:e,provisions:w})=>*a==b && *p==q && d@==e@ && v@==w@,
        (Self::Step {actor:a,rule:r},Self::Step {actor:b,rule:s})=>*a==b && *r==s,_=>false,
    }}
    pub open spec fn renamed(&self,rho:alpha::Renaming)->Self {match self {
        Self::Insert {actor,parent,dependencies,provisions}=>Self::Insert {actor:(rho.forward)(*actor),parent:alpha::parent(rho,*parent),dependencies:*dependencies,provisions:*provisions},
        Self::Step {actor,rule}=>Self::Step {actor:(rho.forward)(*actor),rule:*rule},
    }}
    /// The paper observes declaration sets. Canonicalization also accepts
    /// equivalent source representations without requiring a caller shape proof.
    pub fn canonical_registration<R>(recipe:&crate::lifecycle_state::registration::RegisteredPlugin<R>)->(out:Self)
        ensures out is Insert,out.shape(),out.actor()==recipe.owner(),out->Insert_parent==recipe.parent_id(),
            ports(out->Insert_dependencies@)==ports(recipe.dependencies_spec()),
            ports(out->Insert_provisions@)==ports(recipe.provisions_spec().push(recipe.anchor_port())),
    {
        let dependencies=unique_ports(recipe.dependencies());let mut provisions=recipe.provisions_vec();provisions.push(recipe.anchor());
        Self::Insert {actor:recipe.id(),parent:recipe.parent(),dependencies,provisions:unique_ports(provisions.as_slice())}
    }
    pub fn duplicate(&self)->(out:Self)
        ensures out.same(*self),
    {match self {
        Self::Insert {actor,parent,dependencies,provisions}=>Self::Insert {actor:*actor,parent:*parent,dependencies:copy_ports(dependencies),provisions:copy_ports(provisions)},
        Self::Step {actor,rule}=>Self::Step {actor:*actor,rule:*rule},
    }}
    pub fn rename(&self,names:&crate::mixed_driver::fresh::names::Names)->(out:Self)
        ensures out.same(self.renamed(names.renaming())),
    {
        match self {
            Self::Insert {actor,parent,dependencies,provisions}=>Self::Insert {actor:names.name(*actor),parent:(*parent).map(|p:usize| -> (out:usize) ensures out==names.name_spec(p), {names.name(p)}),dependencies:copy_ports(dependencies),provisions:copy_ports(provisions)},
            Self::Step {actor,rule}=>Self::Step {actor:names.name(*actor),rule:*rule},
        }
    }
}
fn contains_port(input:&[Port],p:Port)->(out:bool) ensures out==input@.contains(p), {
    let mut i=0;while i<input.len()
        invariant i<=input.len(),forall|j:int|0<=j<i ==> input@[j]!=p,
        decreases input.len()-i,
    {if input[i]==p {return true;}i+=1;}false
}
fn unique_ports(input:&[Port])->(out:Vec<Port>) ensures crate::distinct_ports(out@),ports(out@)==ports(input@), {
    let mut out=Vec::new();let mut i=0;
    while i<input.len()
        invariant i<=input.len(),crate::distinct_ports(out@),forall|q:Port| #[trigger] out@.contains(q)==input@.take(i as int).contains(q),
        decreases input.len()-i,
    {
        let ghost before=out@;let p=input[i];
        if !contains_port(out.as_slice(),p) {out.push(p);}
        proof {
            assert forall|a:int,b:int|0<=a<b<out.len() implies out@[a]!=out@[b] by {
                if b<before.len() {assert(out@[a]==before[a]);assert(out@[b]==before[b]);}
                else {assert(before.contains(before[a]));}
            }
            assert(input@.take(i as int+1)==input@.take(i as int).push(p));
            assert forall|q:Port|out@.contains(q)==input@.take(i as int+1).contains(q) by {
                assert(before.contains(q)==input@.take(i as int).contains(q));
            }
            assert(ports(out@) =~= ports(input@.take(i as int+1)));
        }
        i+=1;
    }
    proof {assert(ports(out@) =~= ports(input@));}
    out
}
fn copy_ports(input:&Vec<Port>)->(out:Vec<Port>) ensures out@==input@, {copy_slice(input.as_slice())}
fn copy_slice(input:&[Port])->(out:Vec<Port>) ensures out@==input@, {
    let mut out=Vec::new();let mut i=0;
    while i<input.len()
        invariant i<=input.len(),out@==input@.take(i as int),
        decreases input.len()-i,
    {out.push(input[i]);i+=1;assert(out@==input@.take(i as int));}out
}
pub open spec fn same_commands(a:Seq<Command>,b:Seq<Command>)->bool {
    a.len()==b.len() && forall|i:int|0<=i<a.len() ==> a[i].same(b[i])
}
pub proof fn allocation_equivalent(a:Seq<Command>,b:Seq<Command>)
    requires same_commands(a,b),ensures allocations(a)==allocations(b),decreases a.len(),
{
    if a.len()>0 {allocation_equivalent(a.drop_last(),b.drop_last());}
}
pub open spec fn ports(xs:Seq<Port>)->ISet<Port> {ISet::new(|p:Port|xs.contains(p))}
pub open spec fn allocations(commands:Seq<Command>)->nat decreases commands.len(), {
    if commands.len()==0 {0} else {allocations(commands.drop_last())+if commands.last() is Insert {1nat} else {0nat}}
}
/// Counts real retained Begin calls since each retained insertion. Removal
/// leaves the counter in the audit map; no public identity is reused.
pub proof fn allocation_push(commands:Seq<Command>,c:Command)
    ensures allocations(commands.push(c))==allocations(commands)+if c is Insert {1nat}else{0nat},
{assert(commands.push(c).drop_last()==commands);}
pub open spec fn generations(commands:Seq<Command>)->Map<usize,nat> decreases commands.len(), {
    if commands.len()==0 {Map::empty()} else {
        let prior=generations(commands.drop_last());let c=commands.last();
        if c is Insert {prior.insert(c.actor(),0nat)} else if c.rule()==r::Rule::Begin {prior.insert(c.actor(),prior[c.actor()]+1)} else {prior}
    }
}
pub open spec fn represented_generations(k:Kernel,g:Map<usize,nat>)->bool {
    forall|id:usize|#[trigger] k.registered(id) ==> g.contains_key(id) && k.generation_of(id).is_some() && k.generation_of(id).unwrap()==g[id]
}
pub open spec fn path(commands:Seq<Command>,states:Seq<r::State>)->bool {
    &&& states.len()==commands.len()+1 && states.first().fibers.dom().is_empty()
    &&& commands.len()<u64::MAX
    &&& forall|i:int|0<=i<commands.len() ==> commands[i].shape() && commands[i].payload(states[i+1])
        && r::step(states[i],states[i+1],commands[i].actor(),commands[i].rule())
        && (commands[i] is Insert ==> commands[i].actor()==allocations(commands.take(i)) && allocations(commands.take(i))<usize::MAX)
}
/// Only Insert needs a concrete payload beyond the paper label. Begin's
/// committed provider view is unique because the real Kernel owns reservations.
#[verifier::spinoff_prover]
pub proof fn unique(k:Kernel,z:r::State,other:r::State,c:Command)
    requires k.wf(),c.shape(),c.payload(z),c.payload(other),r::step(k.paper(),z,c.actor(),c.rule()),r::step(k.paper(),other,c.actor(),c.rule()),
    ensures z==other,
{
    k.refines_paper();let a=k.paper();let n=c.actor();
    if c.rule()==r::Rule::Begin {r::target_unique(a,n,z.fibers[n].committed,other.fibers[n].committed);}
    if c.rule()==r::Rule::Iter || c.rule()==r::Rule::Stutter { } else {
        assert(r::registered(z,n)==r::registered(other,n));
        if r::registered(z,n) {
            match c.rule() {r::Rule::Insert|r::Rule::Unload=>{assert(z.fibers[n].committed =~= other.fibers[n].committed);},_=>{}}
            assert(z.fibers[n].parent==other.fibers[n].parent);
            assert(z.fibers[n].dependencies==other.fibers[n].dependencies);assert(z.fibers[n].provisions==other.fibers[n].provisions);
            assert(z.fibers[n]==other.fibers[n]);
        }
        assert(z.fibers.dom() =~= other.fibers.dom()) by {
            assert forall|m:usize|z.fibers.dom().contains(m)==other.fibers.dom().contains(m) by {
                if m!=n {assert(r::registered(z,m)==r::registered(a,m));assert(r::registered(other,m)==r::registered(a,m));}
            }
        }
        assert(z.fibers =~= other.fibers) by {
            assert forall|m:usize|z.fibers.dom().contains(m)==other.fibers.dom().contains(m)
                && (z.fibers.dom().contains(m) ==> z.fibers[m]==other.fibers[m]) by {
                if m!=n {assert(r::registered(z,m)==r::registered(a,m));assert(r::registered(other,m)==r::registered(a,m));}
            }
        }
    }
}
impl Kernel {
    /// Completeness of real guards; no proposed successful result is assumed.
    #[verifier::spinoff_prover]
    proof fn replay_admission(&self,c:Command,z:r::State,steps:nat)
        requires self.wf(),self.metadata_bound(steps),steps<u64::MAX,c.shape(),c.payload(z),r::step(self.paper(),z,c.actor(),c.rule()),
            c is Insert ==> c.actor()==self.next_id() && self.next_id()<usize::MAX,
        ensures match c {
            Command::Insert {parent,dependencies,provisions,..}=>self.insert_enabled(parent,dependencies@,provisions@),
            Command::Step {actor,rule}=>match rule {
                r::Rule::Begin=>self.begin_enabled(actor),r::Rule::Finish|r::Rule::Iter=>self.iteration_enabled(actor),
                r::Rule::Unload=>self.cleanup_enabled(actor),r::Rule::Remove=>self.removal_enabled(actor),_=>true,
            },
        },
    {
        let n=c.actor();self.paper_observations(n);self.refines_paper();
        match c {
            Command::Insert {parent,dependencies,provisions,..}=>{self.paper_insert_domain(parent,dependencies@,provisions@);assert(self.insert_enabled(parent,dependencies@,provisions@));},
            Command::Step {rule,..}=>match rule {
                r::Rule::Begin=>{
                    reveal(Kernel::begin_enabled);reveal(Kernel::unavailable);reveal(Kernel::metadata_bound);
                    assert(self.nodes[n as int].generation< u64::MAX);
                    if self.unavailable(n) {
                        let j=choose|j:int|0<=j<self.declarations.len() && !self.declarations[j].provides && self.declarations[j].owner==n && !self.has_provider(self.declarations[j].port);
                        let p=self.declarations[j].port;
                        assert(self.paper().fibers[n].dependencies.contains(p));
                        let b=choose|b:crate::Binding|z.fibers[n].committed.contains(b) && b.key==p.key && b.realm==p.realm;
                        assert(r::publishes(self.paper(),p,b.provider));self.paper_observations(b.provider);
                        reveal(Kernel::active_provider);reveal(Kernel::has_provider);reveal(Kernel::resolves_to);reveal(Kernel::paper);reveal(Kernel::paper_fiber);
                        assert(Kernel::node_ok(self.nodes@,b.provider as int));assert(self.active_provider(b.provider));
                        let d=choose|d:int|0<=d<self.declarations.len() && self.declarations[d].provides && self.declarations[d].owner==b.provider && self.declarations[d].port==p;
                        assert(self.has_provider(p));
                    }
                    assert(self.begin_enabled(n));
                },
                r::Rule::Finish|r::Rule::Iter=>{self.paper_iteration_guard(n);assert(self.iteration_enabled(n));},
                r::Rule::Unload=>{
                    reveal(Kernel::cleanup_enabled);reveal(Kernel::metadata_bound);
                    assert forall|i:int|0<=i<self.links.len() implies !(self.links[i].live && self.links[i].binding.provider==n) by {
                        if self.links[i].live && self.links[i].binding.provider==n {
                            let link=self.links[i];assert(Kernel::link_ok(self.nodes@,link));self.paper_observations(link.consumer);
                            assert(self.binding_recorded(link.consumer,link.binding));assert(self.paper().fibers[link.consumer].committed.contains(link.binding));
                            assert(link.consumer!=n);assert(r::relied(self.paper(),n));
                        }
                    }
                    reveal(Kernel::is_restoring);reveal(Kernel::registered);reveal(Kernel::phase_of);
                    assert(self.registered(n));assert(self.nodes[n as int].phase==Phase::Unloading);
                    assert(!self.is_restoring(n));assert(!self.nodes[n as int].restoring);
                    assert(self.cleanup_enabled(n));
                },
                r::Rule::Remove=>{assert(self.removal_enabled(n));},_=>{},
            },
        }
    }
    /// Calls the same cleanup methods used by production; no state, generation
    /// or inverse acknowledgement is injected. This is only the control layer.
    fn replay_unload(&mut self,id:usize)->(out:Result<(),Error>)
        requires old(self).wf(),old(self).cleanup_enabled(id),old(self).metadata_bound(u64::MAX as nat),
        ensures out.is_ok(),final(self).wf(),final(self).next_id()==old(self).next_id(),final(self).generations_preserved(old(self)),
            final(self).synchronous_metadata(old(self),false),r::step(old(self).paper(),final(self).paper(),id,r::Rule::Unload),
    {
        let ghost prior=*self;
        self.begin_cleanup(id)?;self.finish_cleanup(id)?;
        proof {
            reveal(Kernel::synchronous_metadata);reveal(Kernel::generations_preserved);reveal(Kernel::metadata_bound);
            reveal(Kernel::is_restoring);reveal(Kernel::phase_of);
            assert forall|n:usize|!prior.is_restoring(n) implies !self.is_restoring(n) by {
                if n==id && n<self.nodes.len() {assert(Kernel::node_ok(self.nodes@,n as int));}
            }
        }
        Ok(())
    }
    fn replay_one(&mut self,c:&Command,Ghost(z):Ghost<r::State>,Ghost(steps):Ghost<nat>)->(out:Result<(),Error>)
        requires old(self).wf(),old(self).metadata_bound(steps),steps<u64::MAX,c.shape(),c.payload(z),r::step(old(self).paper(),z,c.actor(),c.rule()),
            c is Insert ==> c.actor()==old(self).next_id() && old(self).next_id()<usize::MAX,
        ensures out.is_ok(),final(self).wf(),final(self).paper()==z,final(self).metadata_bound(steps+1),
            final(self).next_id()==old(self).next_id()+if c is Insert {1nat}else{0nat},
            forall|g:Map<usize,nat>|represented_generations(*old(self),g) ==> represented_generations(*final(self),
                if c is Insert {g.insert(c.actor(),0nat)} else if c.rule()==r::Rule::Begin {g.insert(c.actor(),g[c.actor()]+1)} else {g}),
    {
        let ghost prior=*self;proof {self.replay_admission(*c,z,steps);}
        match c {
            Command::Insert {parent,dependencies,provisions,..}=>{
                let _id=self.insert(*parent,copy_ports(dependencies),copy_ports(provisions))?;
                assert(self.paper().fibers[_id].dependencies =~= ports(dependencies@));
                assert(self.paper().fibers[_id].provisions =~= ports(provisions@));
            },
            Command::Step {actor,rule}=>match rule {
                r::Rule::Begin=>{self.begin(*actor)?;},r::Rule::Finish=>{self.finish(*actor)?;},
                r::Rule::Unload=>{proof {reveal(Kernel::metadata_bound);}self.replay_unload(*actor)?;},
                r::Rule::Retire=>{self.retire(*actor)?;},r::Rule::Remove=>{self.remove(*actor)?;},
                r::Rule::Divert|r::Rule::Leave|r::Rule::Restart=>{proof {self.paper_observations(*actor);}self.leave(*actor)?;},
                r::Rule::Iter|r::Rule::Stutter=>{if *rule==r::Rule::Iter {self.check_iteration(*actor)?;}
                    proof {reveal(Kernel::synchronous_metadata);reveal(Kernel::generations_preserved);}},
                r::Rule::Insert=>{assert(false);return Err(Error::InvalidState);},
            },
        }
        proof {
            assert(r::step(prior.paper(),self.paper(),c.actor(),c.rule()));
            unique(prior,z,self.paper(),*c);self.metadata_progress(&prior,steps,true);
            assert forall|g:Map<usize,nat>|represented_generations(prior,g) implies represented_generations(*self,
                if c is Insert {g.insert(c.actor(),0nat)} else if c.rule()==r::Rule::Begin {g.insert(c.actor(),g[c.actor()]+1)} else {g}) by {
                let next=if c is Insert {g.insert(c.actor(),0nat)} else if c.rule()==r::Rule::Begin {g.insert(c.actor(),g[c.actor()]+1)} else {g};
                assert forall|n:usize|#[trigger] self.registered(n) implies next.contains_key(n) && self.generation_of(n).is_some() && self.generation_of(n).unwrap()==next[n] by {
                    self.paper_observations(n);prior.paper_observations(n);
                    if c is Insert && n==c.actor() {
                        reveal(Kernel::synchronous_metadata);reveal(Kernel::generation_of);reveal(Kernel::next_id);
                    } else if c.rule()!=r::Rule::Begin {self.generation_frame(&prior,n);}
                }
            }
        }
        Ok(())
    }
}
#[allow(dead_code)] // Intermediate execution evidence is erased by Cargo.
pub struct Execution {kernel:Kernel,history:Ghost<Seq<r::State>>}
impl Execution {
    pub closed spec fn states(&self)->Seq<r::State> {self.history@}
    pub closed spec fn control(&self)->Kernel {self.kernel}
    pub fn kernel(&self)->(out:&Kernel) ensures *out==self.control(), {&self.kernel}
}
/// Internal combinator. The native adapter constructs `states` from its source
/// snapshot, rather than requiring callers to prove a legal target execution.
pub(crate) fn execute(commands:&[Command],Ghost(states):Ghost<Seq<r::State>>)->(out:Result<Execution,Error>)
    requires path(commands@,states),
    ensures out.is_ok(),out.unwrap().states()==states,out.unwrap().control().wf(),out.unwrap().control().paper()==states.last(),
        out.unwrap().control().next_id()==allocations(commands@),out.unwrap().control().metadata_bound(commands.len() as nat),
        represented_generations(out.unwrap().control(),generations(commands@)),
{
    let mut kernel=Kernel::new();let mut i=0usize;let ghost history=seq![kernel.paper()];
    proof {reveal(Kernel::metadata_bound);reveal(Kernel::registered);reveal(Kernel::paper);assert(kernel.paper().fibers =~= states[0].fibers);}
    while i<commands.len()
        invariant i<=commands.len(),path(commands@,states),kernel.wf(),kernel.paper()==states[i as int],history==states.take(i as int+1),
            kernel.next_id()==allocations(commands@.take(i as int)),kernel.metadata_bound(i as nat),
            represented_generations(kernel,generations(commands@.take(i as int))),
        decreases commands.len()-i,
    {
        let ghost before=commands@.take(i as int);
        kernel.replay_one(&commands[i],Ghost(states[i as int+1]),Ghost(i as nat))?;
        proof {history=history.push(kernel.paper());}
        i+=1;
        assert(commands@.take(i as int).drop_last()==before);assert(commands@.take(i as int).last()==commands[i as int-1]);
    }
    assert(commands@.take(i as int)==commands@);assert(history==states);Ok(Execution {kernel,history:Ghost(history)})
}
}
