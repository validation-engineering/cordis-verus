//! Actual loaded-source and logical checkpoint ownership. A checkpoint is the
//! last successfully saved local intent, not a claim that merged disk text equals
//! that intent. Only the real Save cursor can advance it after I/O acknowledgements.
use super::*;
use std::collections::BTreeMap;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::btree::key_obeys_cmp_spec;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::iter::IteratorSpec;

verus! {
broadcast use vstd::seq_lib::group_seq_properties;
#[derive(Debug)]
pub struct Checkpoint<V> {pub value:V,pub pending_sync:bool}
#[derive(Debug)]
pub struct Target<K,V,M> {pub key:K,pub value:V,pub metadata:M}
impl<K,V,M> Target<K,V,M> {
    pub fn new(key:K,value:V,metadata:M)->(out:Self)
        ensures out.key==key,out.value==value,out.metadata==metadata,
    {Self {key,value,metadata}}
}
pub struct Observation<K,V> {
    pub root:Option<K>,pub contents:Map<K,String>,pub checkpoints:Map<K,Checkpoint<V>>,pub resolutions:Map<K,K>,
}
impl<K,V> Observation<K,V> {
    pub open spec fn empty()->Self {Self {root:None,contents:Map::empty(),checkpoints:Map::empty(),resolutions:Map::empty()}}
}
pub struct Saved<K,V> {
    pub key:K,pub value:V,pub observed:String,pub output:String,pub retry:bool,pub merged:bool,pub phase:Stage,pub acknowledged:Seq<Stage>,
}
impl<K,V> Saved<K,V> {
    pub closed spec fn document(&self)->Document<(K,V)> {
        Document {data:(self.key,self.value),observed:self.observed,output:self.output,retry_sync:self.retry,merged_external:self.merged}
    }
    pub open spec fn valid(&self)->bool {
        allowed(self.document(),self.phase) && self.acknowledged==stages(self.document(),self.phase)
    }
    pub open spec fn processed(&self)->bool {self.phase==Stage::Sync || self.phase==Stage::Done}
}
pub closed spec fn saved<K,V,M>(s:Save<Target<K,V,M>>)->Seq<Saved<K,V>> {
    Seq::new(s.documents().len(),|i:int|Saved {
        key:s.documents()[i].payload().key,value:s.documents()[i].payload().value,
        observed:s.documents()[i].observed,output:s.documents()[i].output,
        retry:s.documents()[i].retry(),merged:s.documents()[i].merged(),phase:s.phases()[i],acknowledged:s.history()[i],
    })
}
pub open spec fn saved_valid<K,V>(items:Seq<Saved<K,V>>)->bool {
    forall|i:int|0<=i<items.len() ==> (#[trigger] items[i]).valid()
}
pub open spec fn advance<K,V>(checkpoints:Map<K,Checkpoint<V>>,entry:Saved<K,V>)->Map<K,Checkpoint<V>> {
    if entry.processed() {checkpoints.insert(entry.key,Checkpoint {value:entry.value,pending_sync:entry.phase==Stage::Sync})} else {checkpoints}
}
pub open spec fn advanced<K,V>(checkpoints:Map<K,Checkpoint<V>>,entries:Seq<Saved<K,V>>)->Map<K,Checkpoint<V>>
    decreases entries.len(),
{
    if entries.len()==0 {checkpoints} else {advance(advanced(checkpoints,entries.drop_last()),entries.last())}
}
pub open spec fn loaded<K,V>(previous:Map<K,Checkpoint<V>>,entries:Seq<(K,V)>)->Map<K,Checkpoint<V>>
    decreases entries.len(),
{
    if entries.len()==0 {Map::empty()} else {
        let entry=entries.last();
        loaded(previous,entries.drop_last()).insert(entry.0,Checkpoint {value:entry.1,pending_sync:previous.contains_key(entry.0) && previous[entry.0].pending_sync})
    }
}
pub enum Event<K,V> {
    Clear,
    Load {root:K,contents:Map<K,String>,checkpoints:Seq<(K,V)>,resolutions:Map<K,K>},
    Save {domain:u64,revision:u64,entries:Seq<Saved<K,V>>},
}
pub open spec fn step<K,V>(a:Observation<K,V>,b:Observation<K,V>,event:Event<K,V>)->bool {
    match event {
        Event::Clear=>b==Observation::empty(),
        Event::Load {root,contents,checkpoints,resolutions}=>b==(Observation {root:Some(root),contents,checkpoints:loaded(a.checkpoints,checkpoints),resolutions}),
        Event::Save {entries,..}=>saved_valid(entries) && b==(Observation {checkpoints:advanced(a.checkpoints,entries),..a}),
    }
}
pub struct History<K,V> {pub states:Seq<Observation<K,V>>,pub events:Seq<Event<K,V>>}
impl<K,V> History<K,V> {
    pub open spec fn valid(&self)->bool {
        self.states.len()==self.events.len()+1 && self.states[0]==Observation::empty()
            && forall|i:int|0<=i<self.events.len() ==> #[trigger] step(self.states[i],self.states[i+1],self.events[i])
    }
    pub open spec fn append(&self,after:Observation<K,V>,event:Event<K,V>)->Self {
        Self {states:self.states.push(after),events:self.events.push(event)}
    }
    pub proof fn extend(&self,after:Observation<K,V>,event:Event<K,V>)
        requires self.valid(),step(self.states.last(),after,event),ensures self.append(after,event).valid(),
    {
        let next=self.append(after,event);
        assert forall|i:int|0<=i<next.events.len() implies #[trigger] step(next.states[i],next.states[i+1],next.events[i]) by {
            if i<self.events.len() {assert(step(self.states[i],self.states[i+1],self.events[i]));}
        }
    }
}
/// Read-only access is available to JSON/filesystem adapters. Mutation is owned
/// here; reports do not grant authority to update a logical merge checkpoint.
#[allow(dead_code)]
pub struct Source<K,V> {
    root:Option<K>,contents:BTreeMap<K,String>,checkpoints:BTreeMap<K,Checkpoint<V>>,resolutions:BTreeMap<K,K>,history:Ghost<History<K,V>>,
}
impl<K:Ord,V> Source<K,V> {
    pub closed spec fn observation(&self)->Observation<K,V> {
        Observation {root:self.root,contents:self.contents@,checkpoints:self.checkpoints@,resolutions:self.resolutions@}
    }
    pub closed spec fn history(&self)->History<K,V> {self.history@}
    pub open spec fn wf(&self)->bool {self.history().valid() && self.history().states.last()==self.observation()}
    pub fn new()->(out:Self)
        ensures out.wf(),out.observation()==Observation::empty(),out.history().events.len()==0,
    {
        Self {root:None,contents:BTreeMap::new(),checkpoints:BTreeMap::new(),resolutions:BTreeMap::new(),
            history:Ghost(History {states:seq![Observation::empty()],events:Seq::empty()})}
    }
    pub fn root(&self)->(out:&Option<K>) ensures *out==self.observation().root, {&self.root}
    pub fn contents(&self)->(out:&BTreeMap<K,String>) ensures out@==self.observation().contents, {&self.contents}
    pub fn checkpoints(&self)->(out:&BTreeMap<K,Checkpoint<V>>) ensures out@==self.observation().checkpoints, {&self.checkpoints}
    pub fn resolutions(&self)->(out:&BTreeMap<K,K>) ensures out@==self.observation().resolutions, {&self.resolutions}
    proof fn record(tracked &mut self,before:Observation<K,V>,event:Event<K,V>)
        requires old(self).history().valid(),old(self).history().states.last()==before,step(before,old(self).observation(),event),
        ensures final(self).wf(),final(self).observation()==old(self).observation(),
            final(self).history()==old(self).history().append(old(self).observation(),event),
    {
        self.history@.extend(self.observation(),event);
        self.history=Ghost(self.history@.append(self.observation(),event));
    }
    pub fn clear(&mut self)
        requires old(self).wf(),ensures final(self).wf(),final(self).observation()==Observation::empty(),
            final(self).history()==old(self).history().append(final(self).observation(),Event::Clear),
    {
        let ghost before=self.observation();
        self.root=None;self.contents=BTreeMap::new();self.checkpoints=BTreeMap::new();self.resolutions=BTreeMap::new();
        proof {self.record(before,Event::Clear);}
    }
    pub fn load(&mut self,root:K,contents:BTreeMap<K,String>,checkpoints:Vec<(K,V)>,resolutions:BTreeMap<K,K>)
        requires old(self).wf(),key_obeys_cmp_spec::<K>(),
        ensures final(self).wf(),final(self).observation()==(Observation {root:Some(root),contents:contents@,checkpoints:loaded(old(self).observation().checkpoints,checkpoints@),resolutions:resolutions@}),
            final(self).history()==old(self).history().append(final(self).observation(),Event::Load {root,contents:contents@,checkpoints:checkpoints@,resolutions:resolutions@}),
    {
        let ghost before=self.observation();let ghost input=checkpoints@;let ghost saved_root=root;let ghost text=contents@;let ghost paths=resolutions@;
        let mut next=BTreeMap::new();
        for (key,value) in iter:checkpoints
            invariant key_obeys_cmp_spec::<K>(),self.observation()==before,iter.seq()==input,
                next@==loaded(before.checkpoints,input.take(iter.index())),
        {
            let pending_sync=match self.checkpoints.get(&key) {Some(old)=>old.pending_sync,None=>false};
            next.insert(key,Checkpoint {value,pending_sync});
            proof {
                assert(input.take(iter.index()+1).drop_last() =~= input.take(iter.index()));
                assert(input.take(iter.index()+1).last()==(key,value));
            }
        }
        assert(input.take(input.len() as int)==input);
        self.root=Some(root);self.contents=contents;self.checkpoints=next;self.resolutions=resolutions;
        proof {self.record(before,Event::Load {root:saved_root,contents:text,checkpoints:input,resolutions:paths});}
    }
}
impl<K:Ord,V> Default for Source<K,V> {
    fn default()->(out:Self)
        ensures out.wf(),out.observation()==Observation::empty(),out.history().events.len()==0,
    {Self::new()}
}
impl<K:Ord,V,M> Save<Target<K,V,M>> {
    /// Consume this actual save's documents and phases. A report assembled by
    /// an adapter is never an input to checkpoint or durability bookkeeping.
    // Keep an explicit phase index: the pinned vstd specifies Vec's owning
    // iterator, but does not specify Iterator::enumerate.
    #[allow(clippy::explicit_counter_loop)]
    fn apply_sources(self,source:&mut Source<K,V>,Ghost(authority):Ghost<(u64,u64)>)
        requires self.wf(),old(source).wf(),key_obeys_cmp_spec::<K>(),
        ensures final(source).wf(),final(source).observation()==(Observation {checkpoints:advanced(old(source).observation().checkpoints,saved(self)),..old(source).observation()}),
            final(source).history()==old(source).history().append(final(source).observation(),Event::Save {domain:authority.0,revision:authority.1,entries:saved(self)}),
    {
        let ghost before=source.observation();let ghost initial=self;let ghost records=saved(self);let mut i=0;
        assert(saved_valid(records)) by {
            assert forall|j:int|0<=j<records.len() implies (#[trigger] records[j]).valid() by {
                assert(initial.history()[j]==stages(initial.documents()[j],initial.phases()[j]));
            }
        }
        for document in iter:self.documents
            invariant key_obeys_cmp_spec::<K>(),i==iter.index(),iter.seq()==initial.documents(),self.phases@==initial.phases(),
                records==saved(initial),saved_valid(records),initial.wf(),source.history()==old(source).history(),
                source.observation()==(Observation {checkpoints:advanced(before.checkpoints,records.take(i as int)),..before}),
        {
            let phase=self.phases[i];
            if phase==Stage::Sync || phase==Stage::Done {
                let target=document.data;
                source.checkpoints.insert(target.key,Checkpoint {value:target.value,pending_sync:phase==Stage::Sync});
            }
            proof {
                assert(records.take(i+1).drop_last() =~= records.take(i as int));
                assert(records.take(i+1).last()==records[i as int]);
            }
            i+=1;
        }
        assert(records.take(i as int)==records);
        proof {source.record(before,Event::Save {domain:authority.0,revision:authority.1,entries:records});}
    }
}

impl<K,V> Saved<K,V> {
    /// Progress only reaches a checkpoint after its actual check, and after
    /// replacement when bytes changed. Sync acknowledgement is a separate fact.
    pub proof fn acknowledgement(&self)
        requires self.valid(),self.processed(),
        ensures self.acknowledged.contains(Stage::Check),
            self.document().changes() ==> self.acknowledged.contains(Stage::Replace),
            self.phase==Stage::Sync ==> !self.acknowledged.contains(Stage::Sync),
            self.phase==Stage::Done && (self.document().changes() || self.retry) ==> self.acknowledged.contains(Stage::Sync),
    {}
}
pub open spec fn targets<K,V>(entries:Seq<Saved<K,V>>,key:K)->bool {
    exists|i:int|0<=i<entries.len() && entries[i].processed() && entries[i].key==key
}
pub proof fn advance_frame<K,V>(before:Map<K,Checkpoint<V>>,entries:Seq<Saved<K,V>>,key:K)
    requires !targets(entries,key),
    ensures advanced(before,entries).contains_key(key)==before.contains_key(key),
        before.contains_key(key) ==> advanced(before,entries)[key]==before[key],
    decreases entries.len(),
{
    if entries.len()>0 {
        assert(!targets(entries.drop_last(),key)) by {
            assert forall|i:int|0<=i<entries.drop_last().len() implies !(entries.drop_last()[i].processed() && entries.drop_last()[i].key==key) by {
                assert(entries.drop_last()[i]==entries[i]);
            }
        }
        advance_frame(before,entries.drop_last(),key);
        assert(!entries.last().processed() || entries.last().key!=key);
    }
}
/// Includes overwritten/duplicate keys: the final checkpoint comes from the
/// last actual processed document for that key, not from an arbitrary report.
pub proof fn advance_origin<K,V>(before:Map<K,Checkpoint<V>>,entries:Seq<Saved<K,V>>,key:K)
    requires targets(entries,key),
    ensures advanced(before,entries).contains_key(key),exists|i:int|0<=i<entries.len()
        && entries[i].processed() && entries[i].key==key
        && advanced(before,entries)[key]==(Checkpoint {value:entries[i].value,pending_sync:entries[i].phase==Stage::Sync})
        && (forall|j:int|i<j<entries.len() ==> !entries[j].processed() || entries[j].key!=key),
    decreases entries.len(),
{
    assert(entries.len()>0);
    if entries.last().processed() && entries.last().key==key {
        let i=entries.len()-1;
        assert(advanced(before,entries)[key]==(Checkpoint {value:entries[i].value,pending_sync:entries[i].phase==Stage::Sync}));
    } else {
        assert(targets(entries.drop_last(),key)) by {
            let i=choose|i:int|0<=i<entries.len() && entries[i].processed() && entries[i].key==key;
            assert(i<entries.len()-1);assert(entries.drop_last()[i]==entries[i]);
        }
        advance_origin(before,entries.drop_last(),key);
        let i=choose|i:int|0<=i<entries.drop_last().len() && entries.drop_last()[i].processed() && entries.drop_last()[i].key==key
            && advanced(before,entries.drop_last())[key]==(Checkpoint {value:entries.drop_last()[i].value,pending_sync:entries.drop_last()[i].phase==Stage::Sync})
            && (forall|j:int|i<j<entries.drop_last().len() ==> !entries.drop_last()[j].processed() || entries.drop_last()[j].key!=key);
        assert(entries[i]==entries.drop_last()[i]);
        assert forall|j:int|i<j<entries.len() implies !entries[j].processed() || entries[j].key!=key by {
            if j<entries.len()-1 {assert(entries[j]==entries.drop_last()[j]);}
        }
        assert(advanced(before,entries)[key]==(Checkpoint {value:entries[i].value,pending_sync:entries[i].phase==Stage::Sync}));
    }
}
pub proof fn loaded_origin<K,V>(previous:Map<K,Checkpoint<V>>,entries:Seq<(K,V)>,key:K)
    requires loaded(previous,entries).contains_key(key),
    ensures exists|i:int|0<=i<entries.len() && entries[i].0==key && entries[i].1==loaded(previous,entries)[key].value,
    decreases entries.len(),
{
    assert(entries.len()>0);
    if entries.last().0==key {assert(entries[entries.len()-1].1==loaded(previous,entries)[key].value);}
    else {
        loaded_origin(previous,entries.drop_last(),key);
        let i=choose|i:int|0<=i<entries.drop_last().len() && entries.drop_last()[i].0==key && entries.drop_last()[i].1==loaded(previous,entries.drop_last())[key].value;
        assert(entries[i]==entries.drop_last()[i]);
    }
}
impl<K,V> History<K,V> {
    pub open spec fn introduces(&self,index:int,key:K,value:V)->bool {
        match self.events[index] {
            Event::Load {checkpoints,..}=>exists|j:int|0<=j<checkpoints.len() && checkpoints[j]==(key,value),
            Event::Save {entries,..}=>exists|j:int|0<=j<entries.len() && entries[j].processed() && entries[j].key==key && entries[j].value==value,
            Event::Clear=>false,
        }
    }
    /// Every retained base comes from a real load or a processed document in
    /// the same source history; failure cannot invent a replacement checkpoint.
    pub proof fn checkpoint_origin(&self,end:int,key:K)
        requires self.valid(),0<=end<self.states.len(),self.states[end].checkpoints.contains_key(key),
        ensures exists|i:int|0<=i<end && self.introduces(i,key,self.states[end].checkpoints[key].value),
        decreases end,
    {
        assert(end>0);let i=end-1;
        assert(step(self.states[i],self.states[i+1],self.events[i]));
        match self.events[i] {
            Event::Load {checkpoints,..}=>{
                loaded_origin(self.states[i].checkpoints,checkpoints,key);
                assert(self.introduces(i,key,self.states[end].checkpoints[key].value));
            },
            Event::Save {entries,..}=>{
                if targets(entries,key) {
                    advance_origin(self.states[i].checkpoints,entries,key);
                    assert(self.introduces(i,key,self.states[end].checkpoints[key].value));
                } else {
                    advance_frame(self.states[i].checkpoints,entries,key);
                    self.checkpoint_origin(i,key);
                }
            },
            Event::Clear=>{},
        }
    }
    pub proof fn save_frame(&self,index:int,key:K)
        requires self.valid(),0<=index<self.events.len(),self.events[index] is Save,
            !targets(self.events[index]->Save_entries,key),
        ensures self.states[index+1].root==self.states[index].root,
            self.states[index+1].contents==self.states[index].contents,
            self.states[index+1].resolutions==self.states[index].resolutions,
            self.states[index+1].checkpoints.contains_key(key)==self.states[index].checkpoints.contains_key(key),
            self.states[index].checkpoints.contains_key(key) ==> self.states[index+1].checkpoints[key]==self.states[index].checkpoints[key],
    {
        assert(step(self.states[index],self.states[index+1],self.events[index]));
        advance_frame(self.states[index].checkpoints,self.events[index]->Save_entries,key);
    }
}

#[allow(dead_code)]
pub struct Snapshot<K,V> {history:Ghost<History<K,V>>}
impl<K,V> Snapshot<K,V> {
    pub closed spec fn history(&self)->History<K,V> {self.history@}
    pub open spec fn certified(&self)->bool {self.history().valid()}
}
impl<K:Ord,V> Source<K,V> {
    pub fn snapshot(&self)->(out:Snapshot<K,V>)
        requires self.wf(),ensures out.certified(),out.history()==self.history(),
    {Snapshot {history:Ghost(self.history())}}
}

impl<S,R,U,W> crate::configuration_transaction::Configuration<S,R,U,W> {
    /// The real accepted configuration gates checkpoint publication. Neither
    /// an old revision nor an outstanding recovery can acknowledge this save.
    pub fn accept_saved_sources<K:Ord,V,M>(&self,domain:u64,
        save:Save<Target<K,V,M>>,source:&mut Source<K,V>)->(out:Result<(),Save<Target<K,V,M>>>)
        requires self.wf(),save.wf(),old(source).wf(),key_obeys_cmp_spec::<K>(),
        ensures final(source).wf(),
            out.is_ok()==(self.staged().is_none() && save.review().is_some() && domain==save.review().unwrap().domain() && self.version()==save.review().unwrap().revision()),
            out.is_err() ==> out->Err_0==save && *final(source)==*old(source),
            out.is_ok() ==> final(source).observation()==(Observation {checkpoints:advanced(old(source).observation().checkpoints,saved(save)),..old(source).observation()})
                && final(source).history()==old(source).history().append(final(source).observation(),Event::Save {domain,revision:self.version(),entries:saved(save)}),
    {
        match save.origin.as_ref() {
            Some(stamp)=>if !self.accepts_save(domain,stamp) {return Err(save);},
            None=>return Err(save),
        }
        save.apply_sources(source,Ghost((domain,self.version())));Ok(())
    }
}
}
