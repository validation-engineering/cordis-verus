//! Executable allocation compaction with retained source positions.
use super::Command;
use crate::mixed_driver::fresh::names::Names;
use vstd::prelude::*;
verus! {
broadcast use vstd::seq_lib::group_seq_properties;
pub open spec fn selected(source:Seq<Command>,keep:Seq<bool>)->Seq<Command> decreases source.len(), {
    if source.len()==0 {Seq::empty()} else {let p=selected(source.drop_last(),keep.drop_last());if keep.last() {p.push(source.last())} else {p}}
}
pub open spec fn births(source:Seq<Command>,keep:Seq<bool>,n:usize)->bool {
    exists|i:int|0<=i<source.len() && keep[i] && source[i] is Insert && source[i].actor()==n
}
pub open spec fn source_shape(source:Seq<Command>,keep:Seq<bool>,bound:usize)->bool {
    &&& source.len()==keep.len()
    &&& forall|i:int|0<=i<source.len() && source[i] is Insert ==> source[i].actor()<bound
    &&& forall|i:int,j:int|0<=i<j<source.len() && source[i] is Insert && source[j] is Insert ==> source[i].actor()!=source[j].actor()
}
pub open spec fn renamed(names:Names,source:Seq<Command>)->Seq<Command> {
    source.map(|_:int,c:Command|c.renamed(names.renaming()))
}
pub struct Plan {pub names:Names,pub commands:Vec<Command>}
impl Plan {
    pub open spec fn matches(&self,source:Seq<Command>,keep:Seq<bool>)->bool {
        &&& self.names.wf() && super::same_commands(self.commands@,renamed(self.names,selected(source,keep)))
        &&& forall|i:int|0<=i<source.len() && keep[i] && source[i] is Insert ==>
            self.names.name_spec(source[i].actor())==super::allocations(selected(source.take(i),keep.take(i)))
    }
}
pub proof fn prefix(source:Seq<Command>,keep:Seq<bool>,i:int)
    requires source.len()==keep.len(),0<=i<source.len(),
    ensures selected(source.take(i+1),keep.take(i+1))==if keep[i] {selected(source.take(i),keep.take(i)).push(source[i])} else {selected(source.take(i),keep.take(i))},
{
    assert(source.take(i+1).drop_last()==source.take(i));assert(keep.take(i+1).drop_last()==keep.take(i));
}
/// The native snapshot adapter supplies only source freshness and a source ID
/// bound. This pass neither receives nor checks a proposed successful target.
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub(crate) fn prepare(source:&[Command],keep:&[bool],bound:usize)->(out:Plan)
    requires source_shape(source@,keep@,bound),
    ensures out.matches(source@,keep@),out.names.size()==bound,
{
    let mut names=Names::identity(bound);let mut next=0usize;let mut i=0usize;
    while i<source.len()
        invariant i<=source.len(),source_shape(source@,keep@,bound),names.wf(),names.size()==bound,next<=bound,
            next==super::allocations(selected(source@.take(i as int),keep@.take(i as int))),
            forall|n:usize|#[trigger] names.name_spec(n)<next ==> births(source@.take(i as int),keep@.take(i as int),n),
            forall|j:int|0<=j<i && keep[j] && source[j] is Insert ==> names.name_spec(source[j].actor())==super::allocations(selected(source@.take(j),keep@.take(j))) && names.name_spec(source[j].actor())<next,
        decreases source.len()-i,
    {
        let ghost prior_next=next;let ghost prior_names=names;
        let ghost prefix_commands=selected(source@.take(i as int),keep@.take(i as int));
        proof {prefix(source@,keep@,i as int);super::allocation_push(prefix_commands,source[i as int]);}
        if keep[i] {
            if let Command::Insert {actor,..}=&source[i] {
                proof {
                    assert(!births(source@.take(i as int),keep@.take(i as int),*actor));
                    names.bijection();
                }
                let ghost prior=names;
                assert(names.name_spec(*actor)>=next);
                proof {names.name_bound(*actor);}
                names.pair(*actor,next);
                assert(names.name_spec(*actor)==prior_next);
                proof {
                    names.prefix_pairing(&prior,*actor,next);
                }
                next+=1;
                assert(next==prior_next+1);

            } else {
                assert(next==prior_next);assert(names==prior_names);
            }
        }
        proof {
            assert(next==prior_next+if keep[i as int] && source[i as int] is Insert {1nat}else{0nat});
            assert(next==super::allocations(selected(source@.take(i as int+1),keep@.take(i as int+1))));
            assert forall|n:usize|#[trigger] names.name_spec(n)<next implies births(source@.take(i as int+1),keep@.take(i as int+1),n) by {
                if keep[i as int] && source[i as int] is Insert && n==source[i as int].actor() {
                    assert(births(source@.take(i as int+1),keep@.take(i as int+1),n));
                } else {
                    assert(prior_names.name_spec(n)<prior_next);
                    assert(births(source@.take(i as int),keep@.take(i as int),n));
                    let j=choose|j:int|0<=j<i && keep[j] && source[j] is Insert && source[j].actor()==n;
                    assert(births(source@.take(i as int+1),keep@.take(i as int+1),n));
                }
            }
            assert forall|j:int|0<=j<i+1 && keep[j] && source[j] is Insert implies names.name_spec(source[j].actor())==super::allocations(selected(source@.take(j),keep@.take(j))) && names.name_spec(source[j].actor())<next by {
                if j<i {assert(prior_names.name_spec(source[j].actor())<prior_next);}
            }
        }
        i+=1;
    }
    let mut commands=Vec::new();let mut i=0usize;
    while i<source.len()
        invariant i<=source.len(),source.len()==keep.len(),super::same_commands(commands@,renamed(names,selected(source@.take(i as int),keep@.take(i as int)))),
        decreases source.len()-i,
    {
        proof {prefix(source@,keep@,i as int);}
        if keep[i] {commands.push(source[i].rename(&names));}
        i+=1;
        assert(super::same_commands(commands@,renamed(names,selected(source@.take(i as int),keep@.take(i as int)))));
    }
    Plan {names,commands}
}#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub enum Error {MaskLength,BirthBound {index:usize},DuplicateBirth {first:usize,second:usize}}
/// An ordinary Rust caller also receives a checked preparation result. These
/// are source-shape checks, not a trial run or target-success assumption.
pub fn compact(source:&[Command],keep:&[bool],bound:usize)->(out:Result<Plan,Error>)
    ensures out.is_ok()==source_shape(source@,keep@,bound),
        out.is_ok() ==> out.unwrap().matches(source@,keep@) && out.unwrap().names.size()==bound,
{
    if source.len()!=keep.len() {return Err(Error::MaskLength);}
    let mut seen=std::collections::BTreeMap::<usize,usize>::new();let mut i=0usize;
    while i<source.len()
        invariant i<=source.len(),source.len()==keep.len(),
            forall|j:int|0<=j<i && source[j] is Insert ==> source[j].actor()<bound && seen@.contains_pair(source[j].actor(),j as usize),
            forall|n:usize|#[trigger] seen@.contains_key(n) ==> seen@[n]<i && source[seen@[n] as int] is Insert && source[seen@[n] as int].actor()==n,
        decreases source.len()-i,
    {
        if let Command::Insert {actor,..}=&source[i] {
            if *actor>=bound {return Err(Error::BirthBound {index:i});}
            if let Some(first)=seen.get(actor) {return Err(Error::DuplicateBirth {first:*first,second:i});}
            seen.insert(*actor,i);
        }
        i+=1;
    }
    assert(source_shape(source@,keep@,bound)) by {
        assert forall|a:int,b:int|0<=a<b<source.len() && source[a] is Insert && source[b] is Insert implies source[a].actor()!=source[b].actor() by {
            assert(seen@.contains_pair(source[a].actor(),a as usize));assert(seen@.contains_pair(source[b].actor(),b as usize));
        }
    }
    Ok(prepare(source,keep,bound))
}

}
