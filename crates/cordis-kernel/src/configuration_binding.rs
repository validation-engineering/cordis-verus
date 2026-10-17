//! Actual module selection and immutable configuration binding. Factories are
//! retained by reference, so later re-registration cannot rewrite old recipes.
use std::sync::Arc;
use vstd::prelude::*;
verus! {
broadcast use vstd::seq_lib::group_seq_properties;
#[derive(Debug)]
pub struct Modules<T> {names:Vec<String>,values:Vec<Arc<T>>}
impl<T> Default for Modules<T> {fn default()->(out:Self) ensures out.wf(),out.keys().len()==0, {Self::new()}}
impl<T> Clone for Modules<T> {
    fn clone(&self)->(out:Self) ensures out.keys()==self.keys(),out.values()==self.values(),
    {
        let mut values=Vec::new();let mut i=0;
        while i<self.values.len()
            invariant i<=self.values.len(),values@==self.values@.take(i as int),
            decreases self.values.len()-i,
        {values.push(self.values[i].clone());i+=1;}
        Self {names:self.names.clone(),values}
    }
}
impl<T> Modules<T> {
    pub closed spec fn keys(&self)->Seq<Seq<char>> {self.names@.map(|i:int,name:String|name@)}
    pub closed spec fn values(&self)->Seq<Arc<T>> {self.values@}
    pub closed spec fn wf(&self)->bool {self.names.len()==self.values.len() && self.keys().no_duplicates()}
    pub closed spec fn mapping(&self)->IMap<Seq<char>,Arc<T>> {
        IMap::new(|key:Seq<char>|self.keys().contains(key),|key:Seq<char>|self.values()[choose|i:int|0<=i<self.keys().len() && self.keys()[i]==key])
    }
    pub proof fn entry_mapping(&self,index:int)
        requires self.wf(),0<=index<self.keys().len(),
        ensures self.mapping().dom().contains(self.keys()[index]),self.mapping()[self.keys()[index]]==self.values()[index],
    {
        let key=self.keys()[index];let at=choose|i:int|0<=i<self.keys().len() && self.keys()[i]==key;
        assert(at==index);
    }
    pub fn new()->(out:Self) ensures out.wf(),out.keys().len()==0, {Self {names:Vec::new(),values:Vec::new()}}
    pub fn names(&self)->(out:&[String]) ensures out@.map(|i:int,name:String|name@)==self.keys(), {&self.names}
    fn index(&self,name:&str)->(out:Option<usize>)
        requires self.wf(),
        ensures out.is_none()==!self.keys().contains(name@),out.is_some() ==> out.unwrap()<self.keys().len() && self.keys()[out.unwrap() as int]==name@,
    {
        let mut i=0;
        while i<self.names.len()
            invariant self.wf(),i<=self.names.len(),forall|j:int|0<=j<i ==> self.keys()[j]!=name@,
            decreases self.names.len()-i,
        {if self.names[i].as_str()==name {assert(self.keys()[i as int]==name@);return Some(i);}i+=1;}
        None
    }
    pub fn insert(&mut self,name:String,value:Arc<T>)
        requires old(self).wf(),ensures final(self).wf(),final(self).keys().contains(name@),final(self).mapping()==old(self).mapping().insert(name@,value),
            forall|i:int|0<=i<final(self).keys().len() ==> {
                let key=#[trigger] final(self).keys()[i];
                if key==name@ {final(self).values()[i]==value}
                else {exists|j:int|0<=j<old(self).keys().len() && old(self).keys()[j]==key && final(self).values()[i]==old(self).values()[j]}},
            forall|i:int|0<=i<old(self).keys().len() ==> final(self).keys().contains(#[trigger] old(self).keys()[i]),
    {
        match self.index(name.as_str()) {
            Some(i)=>{self.values.set(i,value);},
            None=>{let ghost old_keys=self.keys();self.names.push(name);self.values.push(value);assert(self.keys() =~= old_keys.push(name@));},
        }
        proof {
            assert(self.mapping() =~= old(self).mapping().insert(name@,value)) by {
                assert forall|key:Seq<char>|self.mapping().dom().contains(key) || old(self).mapping().dom().contains(key) || key==name@ implies
                    self.mapping().dom().contains(key) == old(self).mapping().insert(name@,value).dom().contains(key)
                    && (self.mapping().dom().contains(key) ==> self.mapping()[key]==old(self).mapping().insert(name@,value)[key]) by {
                    if self.keys().contains(key) {let i=choose|i:int|0<=i<self.keys().len() && self.keys()[i]==key;self.entry_mapping(i);}
                    if old(self).keys().contains(key) {let i=choose|i:int|0<=i<old(self).keys().len() && old(self).keys()[i]==key;old(self).entry_mapping(i);}
                }
            }
        }
    }
    pub fn extend(&mut self,entries:Vec<(String,Arc<T>)>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).mapping()==extended(old(self).mapping(),entries@),
    {
        let ghost original=self.mapping();let ghost input=entries@;let ghost mut rest=input;
        for entry in iter: entries
            invariant self.wf(),iter.seq()==input,rest==input.skip(iter.index()),
                extended(self.mapping(),rest)==extended(original,input),
        {
            assert(rest.first()==entry);reveal(extended);
            self.insert(entry.0,entry.1);
            proof {rest=rest.skip(1);}
        }
        assert(rest.len()==0);reveal(extended);
    }
    pub fn get(&self,name:&str)->(out:Option<&Arc<T>>)
        requires self.wf(),ensures out.is_none()==!self.keys().contains(name@),
            out.is_some() ==> exists|i:int|0<=i<self.keys().len() && self.keys()[i]==name@ && *out.unwrap()==self.values()[i],
    {match self.index(name) {Some(i)=>Some(&self.values[i]),None=>None}}
    pub fn bind<C,S>(&self,name:Option<&str>,raw:C,effective:C,scope:S)->(out:Option<Binding<T,C,S>>)
        requires self.wf(),
        ensures out.is_some()==(name.is_none() || self.keys().contains(name.unwrap()@)),
            out.is_some() ==> out.unwrap().raw_value()==raw && out.unwrap().value()==effective && out.unwrap().context()==scope
                && (name.is_none() ==> out.unwrap().module().is_none())
                && (name.is_some() ==> out.unwrap().module().is_some() && exists|i:int|0<=i<self.keys().len() && self.keys()[i]==name.unwrap()@ && out.unwrap().module()==Some(self.values()[i])),
    {
        let module=match name {None=>None,Some(name)=>Some(self.get(name)?.clone())};
        Some(Binding {module,raw:Arc::new(raw),effective:Arc::new(effective),scope:Arc::new(scope)})
    }
}
pub open spec fn extended<T>(before:IMap<Seq<char>,Arc<T>>,entries:Seq<(String,Arc<T>)>)->IMap<Seq<char>,Arc<T>> decreases entries.len(), {
    if entries.len()==0 {before} else {extended(before.insert(entries.first().0@,entries.first().1),entries.skip(1))}
}
pub struct Binding<M,C,S> {module:Option<Arc<M>>,raw:Arc<C>,effective:Arc<C>,scope:Arc<S>}
impl<M,C,S> Clone for Binding<M,C,S> {
    fn clone(&self)->(out:Self) ensures out==*self,
    {Self {module:self.module.as_ref().map(|m:&Arc<M>| -> (out:Arc<M>) ensures out==*m, {m.clone()}),raw:self.raw.clone(),effective:self.effective.clone(),scope:self.scope.clone()}}
}
impl<M,C,S> Binding<M,C,S> {
    pub closed spec fn module(&self)->Option<Arc<M>> {self.module}
    pub closed spec fn raw_value(&self)->C {*self.raw}
    pub closed spec fn value(&self)->C {*self.effective}
    pub closed spec fn context(&self)->S {*self.scope}
    pub fn selected(&self)->(out:Option<&Arc<M>>) ensures match out {None=>self.module().is_none(),Some(m)=>self.module()==Some(*m)}, {self.module.as_ref()}
    pub fn config(&self)->(out:&C) ensures *out==self.value(), {&self.effective}
    pub fn raw(&self)->(out:&C) ensures *out==self.raw_value(), {&self.raw}
    pub fn scope(&self)->(out:&S) ensures *out==self.context(), {&self.scope}
}
}
