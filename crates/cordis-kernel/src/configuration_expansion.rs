//! Actual recursive group/include expansion. Parsing, canonical path identity
//! and file I/O are input adapters; this owner preserves every supplied payload,
//! records real reads and grafts their entries below the requesting node.
use vstd::prelude::*;
verus! {
broadcast use vstd::seq_lib::group_seq_properties;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::iter::IteratorSpec;
pub struct Entry<T,I> {pub payload:T,pub children:Vec<Entry<T,I>>,pub include:Option<I>}
impl<T,I> Entry<T,I> {
    pub fn new(payload:T,children:Vec<Self>,include:Option<I>)->(out:Self)
        ensures out.payload==payload,out.children==children,out.include==include,
    {Self {payload,children,include}}
}
pub struct Document<T,I,B> {pub identity:Vec<u8>,pub base:B,pub entries:Vec<Entry<T,I>>}
pub enum ExpandError<E> {Read(E),Cycle(Vec<Vec<u8>>),IncludeDepth(Vec<u8>),TreeDepth(Vec<u8>)}
pub open spec fn paths(stack:Seq<Vec<u8>>)->Seq<Seq<u8>> {Seq::new(stack.len(),|i:int|stack[i]@)}
pub open spec fn valid_cycle(cycle:Seq<Vec<u8>>)->bool {
    let keys=paths(cycle);
    keys.len()>1 && keys.drop_last().no_duplicates() && keys.drop_last().contains(keys.last())
}
pub open spec fn valid_error<E>(error:ExpandError<E>)->bool {
    match error {ExpandError::Cycle(cycle)=>valid_cycle(cycle@),_=>true}
}
pub struct Read<T,I,B,H,E> {pub base:B,pub request:I,pub before:H,pub after:H,pub result:Result<Document<T,I,B>,E>}
pub open spec fn failure_from<T,I,B,H,E>(error:ExpandError<E>,start:nat,reads:Seq<Read<T,I,B,H,E>>)->bool {
    valid_error(error) && match error {
        ExpandError::Read(error)=>start<reads.len() && reads.last().result==Err(error),
        _=>true,
    }
}
#[verifier::opaque]
#[verifier::prophetic]
pub open spec fn read_call<T,I,B,H,E,C:Fn(&mut H,&B,&I)->Result<Document<T,I,B>,E>>(
    callback:C,base:B,request:I,before:H,after:H,result:Result<Document<T,I,B>,E>)->bool {
    exists|h:&mut H,b:&B,i:&I| *h==before && *final(h)==after && *b==base && *i==request && callback.ensures((h,b,i),result)
}
fn invoke_read<T,I,B,H,E,C:Fn(&mut H,&B,&I)->Result<Document<T,I,B>,E>>(
    host:&mut H,base:&B,request:&I,reader:&C)->(out:Result<Document<T,I,B>,E>)
    requires forall|h:&mut H,b:&B,i:&I|(*reader).requires((h,b,i)),
    ensures read_call(*reader,*base,*request,*old(host),*final(host),out),
{reveal(read_call);(*reader)(host,base,request)}
pub struct Inclusion<T,I,B> {pub read:nat,pub forest:Seq<Forest<T,I,B>>}
pub struct Branch<T,I,B> {pub inline:Seq<Forest<T,I,B>>,pub included:Option<Inclusion<T,I,B>>,pub end:nat}
pub struct Forest<T,I,B> {
    pub before:Seq<Entry<T,I>>,pub after:Seq<Entry<T,I>>,pub base:B,pub ancestry:Seq<Seq<u8>>,pub depth:usize,pub start:nat,pub end:nat,pub branches:Seq<Branch<T,I,B>>,
}
impl<T,I,B> Branch<T,I,B> {
    #[verifier::opaque]
    pub open spec fn valid_for<H,E>(&self,a:Entry<T,I>,z:Entry<T,I>,base:B,ancestry:Seq<Seq<u8>>,depth:usize,start:nat,reads:Seq<Read<T,I,B,H,E>>)->bool
        decreases *self,
    {
        &&& z.payload==a.payload && z.include.is_none()
        &&& self.inline.len()==1 && self.inline[0].valid(reads)
        &&& self.inline[0].before==a.children@ && self.inline[0].base==base
        &&& self.inline[0].ancestry==ancestry && self.inline[0].depth==depth+1 && self.inline[0].start==start
        &&& match a.include {
            None=>self.included.is_none() && self.end==self.inline[0].end && z.children@==self.inline[0].after,
            Some(request)=>self.included.is_some() && {
                let inc=self.included.unwrap();
                &&& inc.read==self.inline[0].end && inc.read<reads.len()
                &&& reads[inc.read as int].base==base && reads[inc.read as int].request==request && reads[inc.read as int].result.is_ok()
                &&& inc.forest.len()==1 && inc.forest[0].valid(reads)
                &&& inc.forest[0].before==reads[inc.read as int].result->Ok_0.entries@
                &&& inc.forest[0].base==reads[inc.read as int].result->Ok_0.base
                &&& inc.forest[0].ancestry==ancestry.push(reads[inc.read as int].result->Ok_0.identity@) && inc.forest[0].depth==depth+1
                &&& inc.forest[0].start==inc.read+1 && self.end==inc.forest[0].end
                &&& z.children@==self.inline[0].after+inc.forest[0].after
            },
        }
    }
    #[verifier::spinoff_prover]
    pub proof fn extend<H,E>(&self,a:Entry<T,I>,z:Entry<T,I>,base:B,ancestry:Seq<Seq<u8>>,depth:usize,start:nat,
        before:Seq<Read<T,I,B,H,E>>,after:Seq<Read<T,I,B,H,E>>)
        requires self.valid_for(a,z,base,ancestry,depth,start,before),before.len()<=after.len(),after.take(before.len() as int)==before,
        ensures self.valid_for(a,z,base,ancestry,depth,start,after),decreases *self,
    {
        reveal(Branch::valid_for);
        self.inline[0].extend(before,after);
        if a.include.is_some() {
            let inc=self.included.unwrap();assert(after[inc.read as int]==before[inc.read as int]);
            inc.forest[0].extend(before,after);
        }
    }

}
impl<T,I,B> Forest<T,I,B> {
    /// Exactly one output per input; contiguous child/read intervals cover all
    /// actual reads. An included document extends the real acyclic file path.
    #[verifier::opaque]
    pub open spec fn valid<H,E>(&self,reads:Seq<Read<T,I,B,H,E>>)->bool
        decreases *self,
    {
        &&& self.start<=self.end<=reads.len()
        &&& 0<self.ancestry.len()<=128 && self.ancestry.no_duplicates() && self.depth<=128
        &&& self.before.len()==self.after.len() && self.branches.len()==self.before.len()
        &&& if self.before.len()==0 {self.end==self.start} else {self.end==self.branches.last().end}
        &&& forall|j:int|0<=j<self.before.len() ==> (#[trigger] self.branches[j]).valid_for(
            self.before[j],self.after[j],self.base,self.ancestry,self.depth,
            if j==0 {self.start} else {self.branches[j-1].end},reads)
    }
    #[verifier::spinoff_prover]
    pub proof fn extend<H,E>(&self,before:Seq<Read<T,I,B,H,E>>,after:Seq<Read<T,I,B,H,E>>)
        requires self.valid(before),before.len()<=after.len(),after.take(before.len() as int)==before,
        ensures self.valid(after),decreases *self,
    {
        reveal(Forest::valid);
        assert forall|j:int|0<=j<self.before.len() implies (#[trigger] self.branches[j]).valid_for(
            self.before[j],self.after[j],self.base,self.ancestry,self.depth,
            if j==0 {self.start} else {self.branches[j-1].end},after) by {
            self.branches[j].extend(self.before[j],self.after[j],self.base,self.ancestry,self.depth,
                if j==0 {self.start} else {self.branches[j-1].end},before,after);
        }
    }
    pub proof fn empty_valid<H,E>(base:B,ancestry:Seq<Seq<u8>>,depth:usize,start:nat,reads:Seq<Read<T,I,B,H,E>>)
        requires 0<ancestry.len()<=128,ancestry.no_duplicates(),depth<=128,start<=reads.len(),
        ensures (Self {before:Seq::empty(),after:Seq::empty(),base,ancestry,depth,start,end:start,branches:Seq::empty()}).valid(reads),
    {reveal(Forest::valid);}
    pub open spec fn push(&self,a:Entry<T,I>,z:Entry<T,I>,branch:Branch<T,I,B>)->Self {
        Self {before:self.before.push(a),after:self.after.push(z),base:self.base,ancestry:self.ancestry,
            depth:self.depth,start:self.start,end:branch.end,branches:self.branches.push(branch)}
    }
    #[verifier::spinoff_prover]
    pub proof fn append<H,E>(&self,a:Entry<T,I>,z:Entry<T,I>,branch:Branch<T,I,B>,reads:Seq<Read<T,I,B,H,E>>)
        requires self.valid(reads),branch.valid_for(a,z,self.base,self.ancestry,self.depth,self.end,reads),self.end<=branch.end<=reads.len(),
        ensures self.push(a,z,branch).valid(reads),
    {
        reveal(Forest::valid);

    }
}
fn close_cycle(stack:&[Vec<u8>],key:Vec<u8>,Ghost(at):Ghost<usize>)->(out:Vec<Vec<u8>>)
    requires paths(stack@).no_duplicates(),at<stack.len(),stack@[at as int]@==key@,
    ensures valid_cycle(out@),paths(out@)==paths(stack@).push(key@),
{
    let mut out:Vec<Vec<u8>>=Vec::new();let mut i=0;
    while i<stack.len()
        invariant i<=stack.len(),out.len()==i,paths(stack@).no_duplicates(),at<stack.len(),stack@[at as int]@==key@,
            forall|j:int|0<=j<i ==> out@[j]@==stack@[j]@,
        decreases stack.len()-i,
    {out.push(stack[i].clone());i+=1;}
    out.push(key);
    assert(paths(out@) =~= paths(stack@).push(key@));
    assert(paths(stack@)[at as int]==key@);assert(paths(stack@).contains(key@));
    assert(paths(out@).drop_last() =~= paths(stack@));assert(paths(out@).last()==key@);
    out
}
fn copy_bytes(input:&[u8])->(out:Vec<u8>) ensures out@==input@,
{
    let mut out=Vec::with_capacity(input.len());let mut i=0;
    while i<input.len()
        invariant i<=input.len(),out@==input@.take(i as int),decreases input.len()-i,
    {out.push(input[i]);i+=1;}
    out
}
fn check_path(stack:&[Vec<u8>],key:&[u8])->(out:Option<Vec<Vec<u8>>>)
    requires paths(stack@).no_duplicates(),
    ensures out.is_some()==paths(stack@).contains(key@),
        out.is_some() ==> valid_cycle(out.unwrap()@),
{
    let mut j=0;
    while j<stack.len()
        invariant j<=stack.len(),paths(stack@).no_duplicates(),forall|i:int|0<=i<j ==> stack@[i]@!=key@,
        decreases stack.len()-j,
    {
        if stack[j].as_slice()==key {
            assert(stack@[j as int]@ =~= key@);
            return Some(close_cycle(stack,copy_bytes(key),Ghost(j)));
        }
        j+=1;
    }
    None
}
#[allow(dead_code)]
struct One<T,I,B,E> {result:Result<Entry<T,I>,ExpandError<E>>,evidence:Ghost<Option<Branch<T,I,B>>>}
impl<T,I,B,E> One<T,I,B,E> {
    fn failed(error:ExpandError<E>)->(out:Self) requires valid_error(error),
        ensures out.result==Err(error),out.evidence@.is_none(),
    {Self {result:Err(error),evidence:Ghost(None)}}
}
#[allow(dead_code)]
pub struct Expanded<T,I,B,E> {pub result:Result<Vec<Entry<T,I>>,ExpandError<E>>,evidence:Ghost<Option<Forest<T,I,B>>>}
impl<T,I,B,E> Expanded<T,I,B,E> {
    pub closed spec fn outcome(&self)->Result<Vec<Entry<T,I>>,ExpandError<E>> {self.result}
    pub closed spec fn derivation(&self)->Option<Forest<T,I,B>> {self.evidence@}
    fn failed(error:ExpandError<E>)->(out:Self) requires valid_error(error),ensures out.outcome()==Err(error),out.derivation().is_none(),
    {Self {result:Err(error),evidence:Ghost(None)}}
}
pub type ReadHistory<T,I,B,H,E> = Seq<Read<T,I,B,H,E>>;
#[allow(dead_code)]
pub struct Expander<T,I,B,H,E,C> {host:H,reader:C,initial:Ghost<H>,reads:Ghost<ReadHistory<T,I,B,H,E>>}
impl<T,I,B,H,E,C:Fn(&mut H,&B,&I)->Result<Document<T,I,B>,E>> Expander<T,I,B,H,E,C> {
    pub closed spec fn host(&self)->H {self.host}
    pub closed spec fn reader(&self)->C {self.reader}
    pub closed spec fn reads(&self)->Seq<Read<T,I,B,H,E>> {self.reads@}
    #[verifier::prophetic]
    #[verifier::opaque]
    pub closed spec fn wf(&self)->bool {
        (if self.reads().len()==0 {self.host()==self.initial@} else {self.reads().first().before==self.initial@ && self.reads().last().after==self.host()})
            && forall|j:int|0<=j<self.reads().len() ==> {
                let r=#[trigger] self.reads()[j];
                read_call(self.reader(),r.base,r.request,r.before,r.after,r.result)
                    && (j>0 ==> self.reads()[j-1].after==r.before)
            }
    }
    pub fn new(host:H,reader:C)->(out:Self)
        ensures out.wf(),out.host()==host,out.reader()==reader,out.reads().len()==0,
    {reveal(Expander::wf);Self {host,reader,initial:Ghost(host),reads:Ghost(Seq::empty())}}
    pub fn into_host(self)->(out:H) ensures out==self.host(), {self.host}
    fn read(&mut self,base:&B,request:&I)->(out:Result<Document<T,I,B>,E>)
        requires old(self).wf(),forall|h:&mut H,b:&B,i:&I|old(self).reader().requires((h,b,i)),
        ensures final(self).wf(),final(self).reader()==old(self).reader(),
            final(self).reads()==old(self).reads().push(Read {base:*base,request:*request,before:old(self).host(),after:final(self).host(),result:out}),
    {
        let ghost before=self.host;
        assert(self.reader==old(self).reader());
        assert forall|h:&mut H,b:&B,i:&I| self.reader.requires((h,b,i)) by {}
        let result=invoke_read(&mut self.host,base,request,&self.reader);
        proof {reveal(read_call);reveal(Expander::wf);}
        self.reads=Ghost(self.reads@.push(Read {base:*base,request:*request,before,after:self.host,result}));result
    }
    pub fn expand(&mut self,document:Document<T,I,B>)->(out:Expanded<T,I,B,E>)
        requires old(self).wf(),forall|h:&mut H,b:&B,i:&I|old(self).reader().requires((h,b,i)),
        ensures final(self).wf(),final(self).reader()==old(self).reader(),
            old(self).reads().len()<=final(self).reads().len(),final(self).reads().take(old(self).reads().len() as int)==old(self).reads(),
            out.derivation().is_some()==out.outcome().is_ok(),
            out.outcome().is_err() ==> failure_from(out.outcome()->Err_0,old(self).reads().len(),final(self).reads()),
            out.derivation().is_some() ==> out.derivation().unwrap().valid(final(self).reads())
                && out.derivation().unwrap().before==document.entries@ && out.derivation().unwrap().after==out.outcome()->Ok_0@
                && out.derivation().unwrap().ancestry==seq![document.identity@] && out.derivation().unwrap().depth==0
                && out.derivation().unwrap().base==document.base && out.derivation().unwrap().start==old(self).reads().len()
                && out.derivation().unwrap().end==final(self).reads().len(),
    {self.expand_document(document,&mut Vec::new(),0)}
    fn expand_document(&mut self,document:Document<T,I,B>,stack:&mut Vec<Vec<u8>>,depth:usize)->(out:Expanded<T,I,B,E>)
        requires old(self).wf(),old(stack).len()<=128,paths(old(stack)@).no_duplicates(),depth<=129,forall|h:&mut H,b:&B,i:&I|old(self).reader().requires((h,b,i)),
        ensures final(self).wf(),final(self).reader()==old(self).reader(),final(stack)@==old(stack)@,
            old(self).reads().len()<=final(self).reads().len(),final(self).reads().take(old(self).reads().len() as int)==old(self).reads(),
            out.derivation().is_some()==out.outcome().is_ok(),
            out.outcome().is_err() ==> failure_from(out.outcome()->Err_0,old(self).reads().len(),final(self).reads()),
            out.derivation().is_some() ==> out.derivation().unwrap().valid(final(self).reads())
                && out.derivation().unwrap().before==document.entries@ && out.derivation().unwrap().after==out.outcome()->Ok_0@
                && out.derivation().unwrap().ancestry==paths(old(stack)@).push(document.identity@) && out.derivation().unwrap().depth==depth
                && out.derivation().unwrap().base==document.base && out.derivation().unwrap().start==old(self).reads().len()
                && out.derivation().unwrap().end==final(self).reads().len(),
        decreases 128-old(stack).len(),0nat,0nat,
    {
        if let Some(cycle)=check_path(stack.as_slice(),document.identity.as_slice()) {
            return Expanded::failed(ExpandError::Cycle(cycle));
        }
        if stack.len()>=128 {return Expanded::failed(ExpandError::IncludeDepth(document.identity));}
        let ghost prior=stack@;let ghost ancestry=paths(prior);
        stack.push(document.identity.clone());
        assert(paths(stack@) =~= ancestry.push(document.identity@));
        assert(paths(stack@).no_duplicates());
        let out=self.expand_forest(document.entries,&document.base,&document.identity,stack,depth);
        stack.pop();assert(stack@==prior);out
    }
    #[verifier::spinoff_prover]
    fn expand_forest(&mut self,entries:Vec<Entry<T,I>>,base:&B,source:&Vec<u8>,stack:&mut Vec<Vec<u8>>,depth:usize)->(out:Expanded<T,I,B,E>)
        requires old(self).wf(),0<old(stack).len()<=128,paths(old(stack)@).no_duplicates(),depth<=129,forall|h:&mut H,b:&B,i:&I|old(self).reader().requires((h,b,i)),
        ensures final(self).wf(),final(self).reader()==old(self).reader(),final(stack)@==old(stack)@,
            old(self).reads().len()<=final(self).reads().len(),final(self).reads().take(old(self).reads().len() as int)==old(self).reads(),
            out.derivation().is_some()==out.outcome().is_ok(),
            out.outcome().is_err() ==> failure_from(out.outcome()->Err_0,old(self).reads().len(),final(self).reads()),
            out.derivation().is_some() ==> out.derivation().unwrap().valid(final(self).reads())
                && out.derivation().unwrap().before==entries@ && out.derivation().unwrap().after==out.outcome()->Ok_0@
                && out.derivation().unwrap().ancestry==paths(old(stack)@) && out.derivation().unwrap().depth==depth
                && out.derivation().unwrap().base==*base && out.derivation().unwrap().start==old(self).reads().len()
                && out.derivation().unwrap().end==final(self).reads().len(),
        decreases 128-old(stack).len(),130-depth,1nat,
    {
        if depth>128 {return Expanded::failed(ExpandError::TreeDepth(source.clone()));}
        let ghost input=entries@;let ghost start=self.reads().len();
        let mut output:Vec<Entry<T,I>>=Vec::new();let ghost mut branches:Seq<Branch<T,I,B>>=Seq::empty();
        proof {Forest::<T,I,B>::empty_valid(*base,paths(stack@),depth,start,self.reads());}
        for entry in iter: entries
            invariant self.wf(),self.reader()==old(self).reader(),stack@==old(stack)@,0<stack.len()<=128,paths(stack@).no_duplicates(),depth<=128,
                start==old(self).reads().len(),input==entries@,iter.seq()==input,output.len()==iter.index(),branches.len()==iter.index(),
                old(self).reads().len()<=self.reads().len(),self.reads().take(old(self).reads().len() as int)==old(self).reads(),
                (Forest {before:input.take(iter.index()),after:output@,base:*base,ancestry:paths(stack@),depth,start,end:self.reads().len(),branches}).valid(self.reads()),
                forall|h:&mut H,b:&B,i:&I|self.reader().requires((h,b,i)),
        {
            let ghost reads_before=self.reads();let ghost prior=Forest {before:input.take(iter.index()),after:output@,base:*base,ancestry:paths(stack@),depth,start,end:self.reads().len(),branches};
            let ghost original=entry;
            let next=self.expand_one(entry,base,source,stack,depth);
            let value=match next.result {Ok(value)=>value,Err(error)=>return Expanded::failed(error)};
            output.push(value);
            proof {
                prior.extend(reads_before,self.reads());
                let branch=next.evidence@.unwrap();
                prior.append(original,value,branch,self.reads());
                assert(input.take(iter.index()+1) =~= prior.before.push(original));
                branches=branches.push(branch);
            }
        }
        let ghost forest=Forest {before:input,after:output@,base:*base,ancestry:paths(stack@),depth,start,end:self.reads().len(),branches};
        Expanded {result:Ok(output),evidence:Ghost(Some(forest))}
    }
    #[verifier::spinoff_prover]
    fn expand_one(&mut self,entry:Entry<T,I>,base:&B,source:&Vec<u8>,stack:&mut Vec<Vec<u8>>,depth:usize)->(out:One<T,I,B,E>)
        requires old(self).wf(),0<old(stack).len()<=128,paths(old(stack)@).no_duplicates(),depth<=128,
            forall|h:&mut H,b:&B,i:&I|old(self).reader().requires((h,b,i)),
        ensures final(self).wf(),final(self).reader()==old(self).reader(),final(stack)@==old(stack)@,
            old(self).reads().len()<=final(self).reads().len(),final(self).reads().take(old(self).reads().len() as int)==old(self).reads(),
            out.evidence@.is_some()==out.result.is_ok(),out.result.is_err() ==> failure_from(out.result->Err_0,old(self).reads().len(),final(self).reads()),
            out.evidence@.is_some() ==> out.evidence@.unwrap().valid_for(entry,out.result->Ok_0,*base,paths(old(stack)@),depth,old(self).reads().len(),final(self).reads())
                && out.evidence@.unwrap().end==final(self).reads().len(),
        decreases 128-old(stack).len(),130-depth,0nat,
    {
        let ghost original=entry;
        let inline=self.expand_forest(entry.children,base,source,stack,depth+1);
        let mut children=match inline.result {
            Ok(children)=>children,Err(error)=>return One::failed(error),
        };
        let ghost inline_proof=inline.derivation().unwrap();
        let ghost mut included:Option<Inclusion<T,I,B>>=None;
        if let Some(include)=entry.include {
            let ghost at=self.reads().len();let ghost before_read=self.reads();
            let document=match self.read(base,&include) {Ok(doc)=>doc,Err(error)=>return One::failed(ExpandError::Read(error))};
            let ghost landed=self.reads();
            assert(landed[at as int].result==Ok(document));
            let expanded=self.expand_document(document,stack,depth+1);
            let mut extra=match expanded.result {Ok(entries)=>entries,Err(error)=>return One::failed(error)};
            proof {
                assert(landed.take(before_read.len() as int) =~= before_read);
                assert(self.reads().take(before_read.len() as int) =~= before_read);
                assert(self.reads()[at as int]==landed[at as int]);
                inline_proof.extend(before_read,self.reads());
                included=Some(Inclusion {read:at,forest:seq![expanded.derivation().unwrap()]});
            }
            children.append(&mut extra);
        }
        let value=Entry {payload:entry.payload,children,include:None};
        let ghost branch=Branch {inline:seq![inline_proof],included,end:self.reads().len()};
        proof {reveal(Branch::valid_for);}
        assert(branch.valid_for(original,value,*base,paths(stack@),depth,old(self).reads().len(),self.reads()));
        One {result:Ok(value),evidence:Ghost(Some(branch))}
    }

}
}
