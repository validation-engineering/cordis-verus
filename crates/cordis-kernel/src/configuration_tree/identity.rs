//! Parent-local configuration identities used by the production Loader.
//! Input parsing and module effects are external; key construction, inherited
//! administrative status and accepted tree placement execute here.
use super::*;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::iter::IteratorSpec;
verus! {
broadcast use vstd::seq_lib::group_seq_properties;
pub struct Origin {pub local:Seq<char>,pub enabled:bool}
pub open spec fn valid_local(id:Seq<char>)->bool {
    id.len()>0 && !id.contains('/') && !id.contains(':')
}
pub open spec fn parent_text(key:Option<String>)->Option<Seq<char>> {match key {Some(s)=>Some(s@),None=>None}}
pub open spec fn qualify(parent:Option<Seq<char>>,id:Seq<char>)->Seq<char> {
    match parent {Some(prefix)=>prefix+seq!['/']+id,None=>id}
}
#[allow(dead_code)]
pub struct PreparedEntry {
    domain:u64,root:Option<usize>,key:String,parent:Option<usize>,parent_key:Option<String>,
    enabled:bool,own_enabled:bool,origin:Ghost<Origin>,
}
impl PreparedEntry {
    pub closed spec fn origin(&self)->Origin {self.origin@}
    pub closed spec fn name(&self)->Seq<char> {self.key@}
    pub closed spec fn parent_index(&self)->Option<usize> {self.parent}
    pub closed spec fn enabled_spec(&self)->bool {self.enabled}
    pub closed spec fn wf(&self)->bool {
        valid_local(self.origin().local) && self.own_enabled==self.origin().enabled
            && self.name()==qualify(parent_text(self.parent_key),self.origin().local)
            && self.parent.is_some()==self.parent_key.is_some()
    }
    pub fn key(&self)->(out:&String) ensures out@==self.name(), {&self.key}
    pub fn enabled(&self)->(out:bool) ensures out==self.enabled_spec(), {self.enabled}
}
pub fn valid_id(id:&str)->(out:bool) ensures out==valid_local(id@),
{
    if id.is_empty() {return false;}
    let mut iter=id.chars();let ghost mut n:int=0;
    loop
        invariant 0<=n<=id@.len(),id@.len()>0,iter.remaining()==id@.skip(n),iter.decrease().is_some(),
            forall|j:int|0<=j<n ==> id@[j]!='/' && id@[j]!=':',
        decreases iter.decrease().unwrap(),
    {
        let ghost remaining=iter.remaining();
        match iter.next() {
            None=>{assert(n==id@.len());return true;},
            Some(c)=>{
                assert(c==id@[n]);
                if c=='/' || c==':' {return false;}
                proof {n=n+1;}
            },
        }
    }
}
impl<T> Tree<T> {
    pub open spec fn parent_name(&self,parent:Option<usize>)->Option<Seq<char>> {
        match parent {Some(p)=>Some(self@[p as int].name()),None=>None}
    }
    pub open spec fn effective(&self,parent:Option<usize>,enabled:bool)->bool {
        enabled && match parent {Some(p)=>self@[p as int].enabled_spec(),None=>true}
    }
    pub closed spec fn accepts_entry(&self,entry:PreparedEntry)->bool {
        entry.domain==self.domain_id() && entry.root==self.root_id()
            && (entry.parent.is_some() ==> entry.parent.unwrap()<self@.len())
            && parent_text(entry.parent_key)==self.parent_name(entry.parent)
            && entry.enabled==self.effective(entry.parent,entry.own_enabled)
    }
    /// Build the actual path from this tree's stored parent, never a caller's
    /// separately formatted prefix. Disabled ancestry propagates here.
    pub fn prepare_entry(&self,parent:Option<usize>,id:&str,enabled:bool)->(out:Result<PreparedEntry,TreeError>)
        requires self.wf(),
        ensures out.is_ok() ==> out->Ok_0.wf() && self.accepts_entry(out->Ok_0)
            && (parent.is_some() ==> parent.unwrap()<self@.len())
            && out->Ok_0.origin()==(Origin {local:id@,enabled}) && out->Ok_0.parent_index()==parent
            && out->Ok_0.name()==qualify(self.parent_name(parent),id@)
            && out->Ok_0.enabled_spec()==self.effective(parent,enabled),
    {
        if !valid_id(id) {return Err(TreeError::InvalidId);}
        let (mut key,parent_key,parent_enabled)=match parent {
            Some(p)=>{
                if p>=self.nodes.len() {return Err(TreeError::MissingParent);}
                let saved=self.nodes[p].key.clone();let mut prefix=saved.clone();prefix.push('/');
                assert(prefix@ =~= saved@+seq!['/']);
                (prefix,Some(saved),self.nodes[p].enabled)
            },
            None=>(String::new(),None,true),
        };
        key.push_str(id);
        let mut i=0;
        while i<self.nodes.len()
            invariant self.wf(),i<=self.nodes.len(),valid_local(id@),
                parent.is_some()==parent_key.is_some(),parent.is_some() ==> parent.unwrap()<self@.len(),
                parent_text(parent_key)==self.parent_name(parent),key@==qualify(self.parent_name(parent),id@),
                parent_enabled==match parent {Some(p)=>self@[p as int].enabled_spec(),None=>true},
            decreases self.nodes.len()-i,
        {if self.nodes[i].key==key {return Err(TreeError::Duplicate);}i+=1;}
        Ok(PreparedEntry {domain:self.domain,root:self.root,key,parent,parent_key,enabled:parent_enabled && enabled,
            own_enabled:enabled,origin:Ghost(Origin {local:id@,enabled})})
    }
    /// Stale/cross-tree preparations are checked again. Only a successful
    /// insertion assigns the source entry's local-ID/administrative evidence.
    pub fn insert_entry(&mut self,entry:PreparedEntry,allocation:Option<Allocation>,data:T)->(out:Result<usize,TreeError>)
        requires old(self).wf(),entry.wf(),allocation.is_some() ==> allocation.unwrap().wf(),
        ensures final(self).wf(),final(self).domain_id()==old(self).domain_id(),final(self).root_id()==old(self).root_id(),
            out.is_err() ==> *final(self)==*old(self),
            out.is_ok() ==> old(self).accepts_entry(entry) && out->Ok_0==old(self)@.len()
                && final(self)@.len()==old(self)@.len()+1 && final(self)@.take(old(self)@.len() as int)==old(self)@
                && final(self)@.last().name()==entry.name() && final(self)@.last().parent_index()==entry.parent_index()
                && final(self)@.last().enabled_spec()==entry.enabled_spec() && final(self)@.last().payload()==data
                && final(self)@.last().allocation_spec()==allocation && final(self)@.last().source()==Some(entry.origin()),
    {
        if entry.domain!=self.domain || entry.root!=self.root {return Err(TreeError::StaleEntry);}
        let parent_enabled=match entry.parent {
            Some(p)=>{
                if p>=self.nodes.len() {return Err(TreeError::MissingParent);}
                match &entry.parent_key {
                    Some(key)=>if key.as_str()!=self.nodes[p].key.as_str() {return Err(TreeError::StaleEntry);},
                    None=>return Err(TreeError::StaleEntry),
                }
                self.nodes[p].enabled
            },
            None=>true,
        };
        if entry.enabled!=(parent_enabled && entry.own_enabled) {return Err(TreeError::StaleEntry);}
        assert(self.accepts_entry(entry));
        let ghost origin=entry.origin();
        let index=self.insert(entry.key,entry.parent,entry.enabled,allocation,data)?;
        self.nodes[index].origin=Ghost(Some(origin));
        assert(self@.take(old(self)@.len() as int)==old(self)@);
        Ok(index)
    }
    /// The authoritative parent-before-child order for both apply and recovery.
    pub fn keys(&self)->(out:Vec<String>)
        ensures out.len()==self@.len(),forall|i:int|0<=i<out.len() ==> out[i]@==self@[i].name(),
    {
        let mut out:Vec<String>=Vec::new();let mut i=0;
        while i<self.nodes.len()
            invariant i<=self.nodes.len(),out.len()==i,forall|j:int|0<=j<i ==> out[j]@==self@[j].name(),
            decreases self.nodes.len()-i,
        {out.push(self.nodes[i].key.clone());i+=1;}
        out
    }
}
/// A slash-free nonempty local ID has an unambiguous final separator, even
/// when IDs contain non-ASCII characters. No string encoding assumption is used.
pub proof fn split_qualified(left:Seq<char>,id:Seq<char>,right:Seq<char>,other:Seq<char>)
    requires valid_local(id),valid_local(other),left+seq!['/']+id==right+seq!['/']+other,
    ensures left==right,id==other,
{
    let a=left+seq!['/']+id;let b=right+seq!['/']+other;
    assert(a.len()==left.len()+1+id.len());assert(b.len()==right.len()+1+other.len());
    assert(a.len()==b.len());
    if left.len()<right.len() {
        let k=right.len() as int;assert(b[k]=='/');assert(0<=k-left.len()-1<id.len());
        assert(id[k-left.len()-1]=='/');assert(id.contains('/'));
    }
    if right.len()<left.len() {
        let k=left.len() as int;assert(a[k]=='/');assert(0<=k-right.len()-1<other.len());
        assert(other[k-right.len()-1]=='/');assert(other.contains('/'));
    }
    assert(left.len()==right.len());
    assert forall|i:int|0<=i<left.len() implies left[i]==right[i] by {
        assert(left[i]==a[i]);assert(right[i]==b[i]);
    }
    assert(left =~= right);
    assert forall|i:int|0<=i<id.len() implies id[i]==other[i] by {
        assert(id[i]==a[left.len()+1+i]);assert(other[i]==b[right.len()+1+i]);
    }
    assert(id =~= other);
}
/// The implemented string name is an injective encoding of Definition 81's
/// (parent, local ID) reconciliation key, not a global ID interpretation.
pub proof fn qualified_key_identity(parent:Option<Seq<char>>,id:Seq<char>,other_parent:Option<Seq<char>>,other_id:Seq<char>)
    requires valid_local(id),valid_local(other_id),
    ensures (qualify(parent,id)==qualify(other_parent,other_id))==(parent==other_parent && id==other_id),
{
    if qualify(parent,id)==qualify(other_parent,other_id) {
        match (parent,other_parent) {
            (Some(a),Some(b))=>split_qualified(a,id,b,other_id),
            (Some(a),None)=>{assert(other_id[a.len() as int]=='/');assert(other_id.contains('/'));},
            (None,Some(b))=>{assert(id[b.len() as int]=='/');assert(id.contains('/'));},
            _=>{},
        }
    }
}
impl<T> Tree<T> {
    pub proof fn local_key_correspondence(&self,left:int,right:int)
        requires self.wf(),0<=left<self@.len(),0<=right<self@.len(),self@[left].source().is_some(),self@[right].source().is_some(),
        ensures (self@[left].name()==self@[right].name())==
            (self@[left].parent_index()==self@[right].parent_index() && self@[left].source().unwrap().local==self@[right].source().unwrap().local),
    {
        let a=self@[left];let b=self@[right];
        qualified_key_identity(self.parent_name(a.parent_index()),a.source().unwrap().local,self.parent_name(b.parent_index()),b.source().unwrap().local);
        if a.parent_index().is_some() && b.parent_index().is_some() && self.parent_name(a.parent_index())==self.parent_name(b.parent_index()) {
            let x=a.parent_index().unwrap() as int;let y=b.parent_index().unwrap() as int;
            if x<y {assert(self@[x].name()!=self@[y].name());}else if y<x {assert(self@[y].name()!=self@[x].name());}
        }
    }
}
}
