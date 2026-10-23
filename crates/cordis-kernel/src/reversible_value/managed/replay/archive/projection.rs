//! Project only the payloads touched by the next real call, then merge the
//! authenticated histories back. Retired, untouched objects retain their name
//! history without being locked or represented by an invented current state.
use super::super::bank::Bank;
#[cfg(verus_keep_ghost)]
use super::super::{typed, typed_correspondence::epochs};
use super::{Archive, Entry, Head, Point};
#[cfg(verus_keep_ghost)]
use crate::reversible_value::service_composition::Address;
use vstd::prelude::*;

verus! {
broadcast use vstd::seq_lib::group_seq_properties;
pub(crate) open spec fn selected<T:?Sized>(whole:&Bank<T>,part:&Bank<T>,indices:Seq<usize>)->bool {
    part.namespace()==whole.namespace() && part.journal()==whole.journal() && part.len_spec()==indices.len()
        && (forall|i:int|0<=i<indices.len() ==> (#[trigger] indices[i])<whole.len_spec() && part.address(i)==whole.address(indices[i] as int)
            && part.target(i)==whole.target(indices[i] as int) && part.service(i)==whole.service(indices[i] as int))
        && forall|i:int,j:int|0<=i<j<indices.len() ==> indices[i]<indices[j]
}
impl<T:?Sized> Entry<T> {
    proof fn reindex(&self,a:&Bank<T>,i:int,b:&Bank<T>,j:int)
        requires self.wf(a,i),a.namespace()==b.namespace(),a.address(i)==b.address(j),a.target_address(i)==b.target_address(j),
        ensures self.wf(b,j),
    {
        assert forall|k:int|0<=k<self.history.len() implies (#[trigger] self.history@[k]).wf(b,j,self.names@) by {assert(self.history@[k].wf(a,i,self.names@));}
    }
    #[allow(unused_variables)] // Banks and indices anchor the erased provenance.
    fn duplicate(&self,bank:&Bank<T>,i:usize)->(out:Self)
        requires self.wf(bank,i as int),
        ensures out.wf(bank,i as int),out.names==self.names,out.source_clock==self.source_clock,out.target_clock==self.target_clock,
    {
        let mut history:Vec<Point<T>>=Vec::new();let mut j=0;
        while j<self.history.len()
            invariant self.wf(bank,i as int),j<=self.history.len(),forall|k:int|0<=k<history.len() ==> (#[trigger] history@[k]).wf(bank,i as int,self.names@),
            decreases self.history.len()-j,
        {
            let point=&self.history[j];let source=Head {input:point.source.input.duplicate(),initial:point.source.initial};let target=point.target.duplicate();
            history.push(Point {source,target});j+=1;
        }
        Self {history,source_clock:self.source_clock,target_clock:self.target_clock,names:self.names}
    }
}
impl<T:?Sized> Archive<T> {
    #[allow(unused_variables)] // Part carries the selected physical allocation interpretation.
    pub(crate) fn project(&self,bank:&Bank<T>,part:&Bank<T>,indices:&[usize])->(out:Self)
        requires self.wf(bank),bank.wf(),part.wf(),selected(bank,part,indices@),
        ensures out.wf(part),forall|i:int|0<=i<indices.len() ==> out.names()[i]==self.names()[indices@[i] as int]
            && out.source_clocks()[i]==self.source_clocks()[indices@[i] as int] && out.target_clocks()[i]==self.target_clocks()[indices@[i] as int],
    {
        let mut entries:Vec<Entry<T>>=Vec::new();let mut i=0;
        while i<indices.len()
            invariant self.wf(bank),bank.wf(),part.wf(),selected(bank,part,indices@),i<=indices.len(),entries.len()==i,
                forall|j:int|0<=j<i ==> (#[trigger] entries@[j]).wf(part,j) && entries@[j].names@==self.names()[indices@[j] as int]
                    && entries@[j].source_clock==self.source_clocks()[indices@[j] as int] && entries@[j].target_clock==self.target_clocks()[indices@[j] as int],
            decreases indices.len()-i,
        {
            let n=indices[i];let entry=self.entries[n].duplicate(bank,n);
            proof {entry.reindex(bank,n as int,part,i as int);}entries.push(entry);i+=1;
        }Self {entries}
    }
    #[allow(unused_variables)] // The banks identify the actual retained checkpoints.
    pub(crate) fn merge(&mut self,bank:&Bank<T>,part:&Bank<T>,indices:&[usize],mut selected_archive:Self)
        requires old(self).wf(bank),bank.wf(),part.wf(),selected(bank,part,indices@),selected_archive.wf(part),
            forall|i:int|0<=i<indices.len() ==> old(self).names()[indices@[i] as int].submap_of(#[trigger] selected_archive.names()[i]),
        ensures final(self).wf(bank),super::super::typed_correspondence::extends(final(self).names(),old(self).names()),
            forall|i:int|0<=i<indices.len() ==> final(self).names()[indices@[i] as int]==selected_archive.names()[i],
            forall|i:int|0<=i<bank.len_spec() && !indices@.contains(i as usize) ==> final(self).names()[i]==old(self).names()[i],
    {
        let ghost incoming=selected_archive.entries@;let mut n=indices.len();
        proof {
            assert forall|i:int|0<=i<indices.len() implies old(self).names()[indices@[i] as int].submap_of((#[trigger] incoming[i]).names@) by {
                assert(selected_archive.names()[i]==incoming[i].names@);
                assert(old(self).names()[indices@[i] as int].submap_of(selected_archive.names()[i]));
            }
        }
        while n>0
            invariant self.wf(bank),bank.wf(),part.wf(),selected(bank,part,indices@),n<=indices.len(),selected_archive.entries@==incoming.take(n as int),
                self.entries.len()==old(self).entries.len(),forall|i:int|0<=i<self.entries.len() ==> old(self).names()[i].submap_of(#[trigger] self.names()[i]),
                forall|i:int|0<=i<indices.len() ==> old(self).names()[indices@[i] as int].submap_of((#[trigger] incoming[i]).names@),
                incoming.len()==indices.len(),forall|i:int|0<=i<incoming.len() ==> (#[trigger] incoming[i]).wf(part,i),
                forall|i:int|n<=i<indices.len() ==> self.names()[indices@[i] as int]==incoming[i].names@,
                forall|i:int|0<=i<bank.len_spec() && !indices@.contains(i as usize) ==> self.names()[i]==old(self).names()[i],
            decreases n,
        {
            n-=1;let entry=selected_archive.entries.pop().unwrap();let k=indices[n];
            proof {entry.reindex(part,n as int,bank,k as int);}
            let ghost before=self.entries@;let ghost prior_names=self.names();
            proof {assert forall|i:int|0<=i<self.entries.len() implies old(self).names()[i].submap_of(#[trigger] prior_names[i]) by {assert(old(self).names()[i].submap_of(self.names()[i]));}}
            self.entries.set(k,entry);
            proof {
                assert forall|i:int|0<=i<self.entries.len() implies (#[trigger] self.entries@[i]).wf(bank,i) by {if i!=k {assert(self.entries@[i]==before[i]);}}
                assert forall|i:int|0<=i<self.entries.len() implies old(self).names()[i].submap_of(#[trigger] self.names()[i]) by {
                    if i==k {assert(entry.names@==incoming[n as int].names@);assert(self.names()[i]==entry.names@);assert(old(self).names()[indices@[n as int] as int].submap_of(incoming[n as int].names@));}
                    else {assert(self.entries@[i]==before[i]);assert(self.names()[i]==before[i].names@);assert(prior_names[i]==before[i].names@);assert(old(self).names()[i].submap_of(prior_names[i]));}
                }
                assert forall|i:int|n<=i<indices.len() implies self.names()[indices@[i] as int]==incoming[i].names@ by {if i>n {assert(indices@[i]!=k);}}
            }
        }
    }
}
/// This certificate covers all retained histories, including objects excluded
/// from a later call's live lock set. It makes no claim that they are still live.
pub ghost struct Names<T:?Sized> {pub bank:Bank<T>,pub heads:Seq<Map<u64,u64>>}
impl<T:?Sized> Names<T> {
    pub open spec fn wf(&self)->bool {self.bank.wf() && self.heads.len()==self.bank.len_spec() && forall|i:int|0<=i<self.heads.len() ==> typed::injective(#[trigger] self.heads[i]) && epochs::ordered(self.heads[i])}
    pub open spec fn at(&self,address:Address)->Map<u64,u64> {
        if exists|i:int|0<=i<self.bank.len_spec() && self.bank.address(i)==address {
            self.heads[choose|i:int|0<=i<self.bank.len_spec() && self.bank.address(i)==address]
        } else {Map::empty()}
    }
    pub proof fn entry(&self,i:int)
        requires self.wf(),0<=i<self.bank.len_spec(),ensures self.at(self.bank.address(i))==self.heads[i],
    {
        self.bank.mapping_entry(i);self.bank.mapping_domain();
        assert(exists|j:int|0<=j<self.bank.len_spec() && self.bank.address(j)==self.bank.address(i)) by {assert(self.bank.address(i)==self.bank.address(i));}
        let j=choose|j:int|0<=j<self.bank.len_spec() && self.bank.address(j)==self.bank.address(i);self.bank.aliases(i,j);
    }
    pub proof fn facts(&self,address:Address)
        requires self.wf(),ensures typed::injective(self.at(address)),epochs::ordered(self.at(address)),
    {
        if exists|i:int|0<=i<self.bank.len_spec() && self.bank.address(i)==address {
            let i=choose|i:int|0<=i<self.bank.len_spec() && self.bank.address(i)==address;self.entry(i);
        }
    }
}
impl<T:?Sized> Archive<T> {
    pub(crate) proof fn names_certificate(&self,bank:&Bank<T>)->(out:Names<T>)
        requires self.wf(bank),bank.wf(),ensures out.wf(),out.bank==*bank,out.heads==self.names(),
    {Names {bank:*bank,heads:self.names()}}
}
}
