//! Structured configuration values. Parsing is an adapter; recursive data
//! operations below execute in the verified kernel on the supplied values.
use vstd::prelude::*;
verus! {
broadcast use vstd::seq_lib::group_seq_properties;
#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub enum Class {Null,Boolean,String,Number {signed:Option<i64>,rank:u64}}
#[derive(Debug)]
pub enum Value {Atom(String,Class),Array(Vec<Value>),Object(Vec<(String,Value)>)}
pub ghost enum Data {Atom(Seq<char>,Class),Array(Seq<Data>),Object(Seq<(Seq<char>,Data)>)}
pub open spec fn elements(items:Seq<Value>)->Seq<Data> decreases items, {Seq::new(items.len(),|i:int|if 0<=i<items.len() {items[i].model()} else {Data::Atom(Seq::empty(),Class::Null)})}
pub open spec fn fields(items:Seq<(String,Value)>)->Seq<(Seq<char>,Data)> decreases items, {Seq::new(items.len(),|i:int|if 0<=i<items.len() {(items[i].0@,items[i].1.model())} else {(Seq::empty(),Data::Atom(Seq::empty(),Class::Null))})}
impl Value {
    pub open spec fn model(&self)->Data decreases *self, {
        match self {Self::Atom(text,class)=>Data::Atom(text@,*class),Self::Array(items)=>Data::Array(Seq::new(items.len() as nat,|i:int|if 0<=i<items.len() {items[i].model()} else {Data::Atom(Seq::empty(),Class::Null)})),Self::Object(items)=>Data::Object(Seq::new(items.len() as nat,|i:int|if 0<=i<items.len() {(items[i].0@,items[i].1.model())} else {(Seq::empty(),Data::Atom(Seq::empty(),Class::Null))}))}
    }
    pub proof fn shape(&self)
        ensures match self {Self::Atom(text,class)=>self.model()==Data::Atom(text@,*class),Self::Array(items)=>self.model()==Data::Array(elements(items@)),Self::Object(items)=>self.model()==Data::Object(fields(items@))},
    {
        reveal(Value::model);
        match self {
            Self::Atom(..)=>{},
            Self::Array(items)=>{assert(self.model()->Array_0 =~= elements(items@));},
            Self::Object(items)=>{assert(self.model()->Object_0 =~= fields(items@));},
        }
    }
    pub fn copy(&self)->(out:Self) ensures out.model()==self.model(), decreases *self,
    {
        proof {self.shape();}
        match self {
            Self::Atom(text,class)=>Self::Atom(text.clone(),*class),
            Self::Array(items)=>{
                let mut result:Vec<Value>=Vec::new();let mut i=0;
                while i<items.len()
                    invariant self.model()==Data::Array(elements(items@)),self is Array,self->Array_0==*items,i<=items.len(),result.len()==i,forall|j:int|0<=j<i ==> result@[j].model()==items@[j].model(),
                    decreases items.len()-i,
                {reveal(elements);reveal(fields);result.push(items[i].copy());i+=1;}
                assert(elements(result@) =~= elements(items@));
                let out=Self::Array(result);proof {out.shape();}out
            },
            Self::Object(items)=>{
                let mut result:Vec<(String,Value)>=Vec::new();let mut i=0;
                while i<items.len()
                    invariant self.model()==Data::Object(fields(items@)),self is Object,self->Object_0==*items,i<=items.len(),result.len()==i,forall|j:int|0<=j<i ==> result@[j].0@==items@[j].0@ && result@[j].1.model()==items@[j].1.model(),
                    decreases items.len()-i,
                {reveal(elements);reveal(fields);result.push((items[i].0.clone(),items[i].1.copy()));i+=1;}
                assert(fields(result@) =~= fields(items@));
                let out=Self::Object(result);proof {out.shape();}out
            },
        }
    }
    pub fn equals(&self,other:&Self)->(out:bool) ensures out==(self.model()==other.model()), decreases *self,
    {
        proof {self.shape();}
        proof {other.shape();}
        match (self,other) {
            (Self::Atom(a,ak),Self::Atom(b,bk))=>{let out=a.as_str()==b.as_str() && ak==bk;assert(out==(self.model()==other.model()));out},
            (Self::Array(a),Self::Array(b))=>{
                assert(elements(a@).len()==a.len());assert(elements(b@).len()==b.len());
                assert(self.model()==other.model() ==> a.len()==b.len());
                if a.len()!=b.len() {return false;}
                let mut i=0;
                while i<a.len()
                    invariant self is Array,self->Array_0==*a,other is Array,other->Array_0==*b,
                        self.model()==Data::Array(elements(a@)),other.model()==Data::Array(elements(b@)),
                        i<=a.len(),a.len()==b.len(),forall|j:int|0<=j<i ==> a@[j].model()==b@[j].model(),
                    decreases a.len()-i,
                {reveal(elements);if !a[i].equals(&b[i]) {assert(elements(a@)[i as int]!=elements(b@)[i as int]);return false;}i+=1;}
                assert(elements(a@) =~= elements(b@));assert(self.model()==other.model());true
            },
            (Self::Object(a),Self::Object(b))=>{
                assert(fields(a@).len()==a.len());assert(fields(b@).len()==b.len());
                assert(self.model()==other.model() ==> a.len()==b.len());
                if a.len()!=b.len() {return false;}
                let mut i=0;
                while i<a.len()
                    invariant self is Object,self->Object_0==*a,other is Object,other->Object_0==*b,
                        self.model()==Data::Object(fields(a@)),other.model()==Data::Object(fields(b@)),
                        i<=a.len(),a.len()==b.len(),forall|j:int|0<=j<i ==> a@[j].0@==b@[j].0@ && a@[j].1.model()==b@[j].1.model(),
                    decreases a.len()-i,
                {reveal(fields);if a[i].0.as_str()!=b[i].0.as_str() || !a[i].1.equals(&b[i].1) {assert(fields(a@)[i as int]!=fields(b@)[i as int]);return false;}i+=1;}
                assert(fields(a@) =~= fields(b@));assert(self.model()==other.model());true
            },
            _=>{assert(self.model()!=other.model());false},
        }
    }
}
#[verifier::opaque]
pub open spec fn find(items:Seq<(Seq<char>,Data)>,key:Seq<char>)->Option<nat> {
    if exists|i:int|0<=i<items.len() && items[i].0==key {Some((choose|i:int|0<=i<items.len() && items[i].0==key && forall|j:int|0<=j<i ==> items[j].0!=key) as nat)} else {None}
}
pub open spec fn lookup(items:Seq<(Seq<char>,Data)>,key:Seq<char>)->Option<Data> {match find(items,key) {Some(i)=>Some(items[i as int].1),None=>None}}
pub open spec fn replaced(items:Seq<(Seq<char>,Data)>,key:Seq<char>,value:Data)->Seq<(Seq<char>,Data)> {
    match find(items,key) {Some(i)=>items.update(i as int,(key,value)),None=>items.push((key,value))}
}
pub fn position(items:&[(String,Value)],key:&str)->(out:Option<usize>)
    ensures (match out {Some(i)=>Some(i as nat),None=>None})==find(fields(items@),key@),out.is_some() ==> out.unwrap()<items.len() && items@[out.unwrap() as int].0@==key@,
{
    reveal(find);
    let mut i=0;
    while i<items.len()
        invariant i<=items.len(),forall|j:int|0<=j<i ==> items@[j].0@!=key@,
        decreases items.len()-i,
    {
        if items[i].0.as_str()==key {
            proof {
                reveal(find);let list=fields(items@);
                assert(list[i as int].0==key@);
                assert forall|j:int|0<=j<i implies list[j].0!=key@ by {}
                assert(exists|j:int|0<=j<list.len() && list[j].0==key@);
                assert(exists|j:int|0<=j<list.len() && list[j].0==key@ && forall|k:int|0<=k<j ==> list[k].0!=key@) by {assert(0<=i<list.len() && list[i as int].0==key@ && forall|k:int|0<=k<i ==> list[k].0!=key@);}
                let at=choose|j:int|0<=j<list.len() && list[j].0==key@ && forall|k:int|0<=k<j ==> list[k].0!=key@;
                if at<i {assert(list[at].0!=key@);}if at>i {assert(list[i as int].0!=key@);}
                assert(find(list,key@)==Some(i as nat));
            }
            return Some(i);
        }
        i+=1;
    }
    assert(find(fields(items@),key@).is_none());None
}
pub fn get<'a>(items:&'a [(String,Value)],key:&str)->(out:Option<&'a Value>)
    ensures (match out {Some(v)=>Some(v.model()),None=>None})==lookup(fields(items@),key@),
        out.is_some() ==> exists|i:int|0<=i<items.len() && *out.unwrap()==items@[i].1 && items@[i].0@==key@,
{
    match position(items,key) {Some(i)=>Some(&items[i].1),None=>None}
}
pub fn put(items:&mut Vec<(String,Value)>,key:String,value:Value)
    ensures fields(final(items)@)==replaced(fields(old(items)@),key@,value.model()),
{
    let ghost before=fields(items@);let ghost key_text=key@;let ghost data=value.model();
    match position(items,key.as_str()) {Some(i)=>{items.set(i,(key,value));},None=>items.push((key,value))}
    assert(fields(items@) =~= replaced(before,key_text,data));
}
pub open spec fn overlay(base:Data,patch:Data)->Data decreases patch, {
    match (base,patch) {(Data::Object(a),Data::Object(b))=>Data::Object(overlays(a,b)),(_,b)=>b}
}
pub open spec fn overlays(base:Seq<(Seq<char>,Data)>,patch:Seq<(Seq<char>,Data)>)->Seq<(Seq<char>,Data)> decreases patch, {
    if patch.len()==0 {base} else {
        let (key,value)=patch.first();
        let next=match lookup(base,key) {None=>value,Some(old)=>overlay(old,value)};
        overlays(replaced(base,key,next),patch.skip(1))
    }
}
pub fn apply(base:&Value,patch:&Value)->(out:Value)
    ensures out.model()==overlay(base.model(),patch.model()),decreases *patch,
{
    proof {base.shape();patch.shape();}
    match (base,patch) {
        (Value::Object(_a),Value::Object(b))=>{
            let copied=base.copy();proof {copied.shape();}let mut items=match copied {Value::Object(v)=>v,_=>unreachable!()};
            let mut i=0;let ghost original=fields(_a@);let ghost patches=fields(b@);
            while i<b.len()
                invariant patch is Object,patch->Object_0==*b,i<=b.len(),patches==fields(b@),
                    base.model()==Data::Object(original),patch.model()==Data::Object(patches),
                    overlays(fields(items@),patches.skip(i as int))==overlays(original,patches),
                decreases b.len()-i,
            {
                let next=match get(&items,b[i].0.as_str()) {Some(old)=>apply(old,&b[i].1),None=>b[i].1.copy()};
                let ghost prior=fields(items@);
                put(&mut items,b[i].0.clone(),next);
                proof {
                    assert(patches.skip(i as int).first()==patches[i as int]);
                    assert(patches.skip(i as int).skip(1)==patches.skip(i as int+1));
                    reveal(overlays);
                }
                i+=1;
            }
            assert(patches.skip(i as int)==Seq::<(Seq<char>,Data)>::empty());reveal(overlays);
            let out=Value::Object(items);proof {out.shape();}out
        },
        _=>patch.copy(),
    }
}
/// A successful round trip compares complete structured values, not their
/// revision, entry count, or a caller-provided fingerprint.
#[allow(dead_code)]
pub struct RoundTrip<T> {payload:T,expected:Ghost<Data>,expanded:Ghost<Data>}
impl<T> RoundTrip<T> {
    pub closed spec fn payload(&self)->T {self.payload}
    pub closed spec fn expected(&self)->Data {self.expected@}
    pub closed spec fn expanded(&self)->Data {self.expanded@}
    pub fn check(payload:T,expected:&Value,expanded:&Value)->(out:Result<Self,T>)
        ensures out.is_ok()==(expected.model()==expanded.model()),
            out.is_ok() ==> out->Ok_0.payload()==payload && out->Ok_0.expected()==expected.model()
                && out->Ok_0.expanded()==expanded.model() && out->Ok_0.expected()==out->Ok_0.expanded(),
            out.is_err() ==> out->Err_0==payload,
    {
        if !expected.equals(expanded) {return Err(payload);}
        Ok(Self {payload,expected:Ghost(expected.model()),expanded:Ghost(expanded.model())})
    }
    pub fn into_inner(self)->(out:T) ensures out==self.payload(), {self.payload}
}
pub open spec fn optional(value:Option<&Value>)->Option<Data> {match value {Some(v)=>Some(v.model()),None=>None}}
pub fn copy_optional(value:Option<&Value>)->(out:Option<Value>)
    ensures (match out {Some(v)=>Some(v.model()),None=>None})==optional(value),
{value.map(|v:&Value| -> (out:Value) ensures out.model()==v.model(), {v.copy()})}
pub fn equal_optional(a:Option<&Value>,b:Option<&Value>)->(out:bool) ensures out==option_equal(optional(a),optional(b)),
{match (a,b) {(Some(a),Some(b))=>a.json_equals(b),(None,None)=>true,_=>false}}
pub open spec fn names(values:Seq<String>)->Seq<Seq<char>> {values.map(|i:int,v:String|v@)}
pub open spec fn keys(values:Seq<(Seq<char>,Data)>)->Set<Seq<char>> {values.map(|i:int,p:(Seq<char>,Data)|p.0).to_set()}
pub fn contains_name(values:&[String],key:&str)->(out:bool) ensures out==names(values@).contains(key@),
{
    let mut i=0;
    while i<values.len()
        invariant i<=values.len(),forall|j:int|0<=j<i ==> values@[j]@!=key@,
        decreases values.len()-i,
    {if values[i].as_str()==key {assert(names(values@)[i as int]==key@);return true;}i+=1;}
    false
}
fn add_keys(out:&mut Vec<String>,input:&[(String,Value)])
    requires names(old(out)@).no_duplicates(),
    ensures names(final(out)@).no_duplicates(),names(final(out)@).to_set()==names(old(out)@).to_set().union(keys(fields(input@))),
{
    let ghost initial=names(out@).to_set();let mut i=0;
    while i<input.len()
        invariant i<=input.len(),names(out@).no_duplicates(),names(out@).to_set()==initial.union(keys(fields(input@.take(i as int)))),
        decreases input.len()-i,
    {
        let ghost prior=names(out@);let ghost pref=fields(input@.take(i as int));
        if !contains_name(out,input[i].0.as_str()) {out.push(input[i].0.clone());assert(names(out@) =~= prior.push(input[i as int].0@));proof {prior.lemma_push_to_set_commute(input[i as int].0@);}}
        proof {
            assert(fields(input@.take(i as int+1)) =~= pref.push((input[i as int].0@,input[i as int].1.model())));
            let ns=pref.map(|j:int,p:(Seq<char>,Data)|p.0);
            assert(pref.push((input[i as int].0@,input[i as int].1.model())).map(|j:int,p:(Seq<char>,Data)|p.0) =~= ns.push(input[i as int].0@));
            ns.lemma_push_to_set_commute(input[i as int].0@);
        }
        i+=1;
    }
}
pub fn union_keys(a:&[(String,Value)],b:&[(String,Value)],c:&[(String,Value)])->(out:Vec<String>)
    ensures names(out@).no_duplicates(),names(out@).to_set()==keys(fields(a@)).union(keys(fields(b@))).union(keys(fields(c@))),
{
    let mut out=Vec::new();add_keys(&mut out,a);add_keys(&mut out,b);add_keys(&mut out,c);out
}
/// Evidence is derived from the recursive execution. It covers every key in
/// all three inputs, including deletions; no caller supplies a desired result.
pub ghost struct MergeProof {pub base:Option<Data>,pub ours:Option<Data>,pub theirs:Option<Data>,pub output:Option<Data>,pub children:Seq<(Seq<char>,MergeProof)>}
pub open spec fn results(children:Seq<(Seq<char>,MergeProof)>)->Seq<(Seq<char>,Data)> decreases children.len(), {
    if children.len()==0 {Seq::empty()} else {let head=children.first();let tail=results(children.skip(1));
        match head.1.output {None=>tail,Some(value)=>seq![(head.0,value)]+tail}}
}
impl MergeProof {
    #[verifier::opaque]
    pub open spec fn valid(&self)->bool decreases *self, {
        if option_equal(self.ours,self.base) {self.output==self.theirs}
        else if option_equal(self.theirs,self.base) || option_equal(self.ours,self.theirs) {self.output==self.ours}
        else {match (self.base,self.ours,self.theirs) {
            (Some(Data::Object(a)),Some(Data::Object(b)),Some(Data::Object(c)))=>{
                &&& self.output==Some(Data::Object(results(self.children)))
                &&& self.children.map(|i:int,p:(Seq<char>,MergeProof)|p.0).no_duplicates()
                &&& self.children.map(|i:int,p:(Seq<char>,MergeProof)|p.0).to_set()==keys(a).union(keys(b)).union(keys(c))
                &&& forall|i:int|0<=i<self.children.len() ==> {let (key,child)=#[trigger] self.children[i];
                    child.valid() && child.base==lookup(a,key) && child.ours==lookup(b,key) && child.theirs==lookup(c,key)}
            },_=>false}}
    }
}
proof fn push_results(children:Seq<(Seq<char>,MergeProof)>,key:Seq<char>,proof:MergeProof)
    ensures results(children.push((key,proof)))==results(children)+(match proof.output {Some(v)=>seq![(key,v)],None=>Seq::empty()}),
    decreases children.len(),
{
    reveal_with_fuel(results,2);
    if children.len()>0 {push_results(children.skip(1),key,proof);assert(children.push((key,proof)).skip(1)==children.skip(1).push((key,proof)));}
}
#[allow(dead_code)]
pub struct Merged {pub value:Option<Value>,proof:Ghost<MergeProof>}
impl Merged {
    pub closed spec fn evidence(&self)->MergeProof {self.proof@}
    pub closed spec fn model(&self)->Option<Data> {match self.value {Some(v)=>Some(v.model()),None=>None}}
}
pub fn merge(base:Option<&Value>,ours:Option<&Value>,theirs:Option<&Value>)->(out:Result<Merged,Vec<String>>)
    ensures out.is_ok() ==> out->Ok_0.evidence().valid() && out->Ok_0.evidence().base==optional(base)
        && out->Ok_0.evidence().ours==optional(ours) && out->Ok_0.evidence().theirs==optional(theirs)
        && out->Ok_0.evidence().output==out->Ok_0.model(),
    decreases if ours.is_some() {1int} else {0int},ours.unwrap(),
{
    let ghost b=optional(base);let ghost o=optional(ours);let ghost t=optional(theirs);
    if equal_optional(ours,base) {
        let proof=Ghost(MergeProof {base:b,ours:o,theirs:t,output:t,children:Seq::empty()});
        proof {reveal(MergeProof::valid);}return Ok(Merged {value:copy_optional(theirs),proof});
    }
    if equal_optional(theirs,base) || equal_optional(ours,theirs) {
        let proof=Ghost(MergeProof {base:b,ours:o,theirs:t,output:o,children:Seq::empty()});
        proof {reveal(MergeProof::valid);}return Ok(Merged {value:copy_optional(ours),proof});
    }
    match (base,ours,theirs) {
        (Some(a),Some(bv),Some(c))=>{
            proof {a.shape();bv.shape();c.shape();}
            match (a,bv,c) {
                (Value::Object(ba),Value::Object(ou),Value::Object(th))=>{
                    let all_keys=union_keys(ba,ou,th);let mut output:Vec<(String,Value)>=Vec::new();let ghost mut children:Seq<(Seq<char>,MergeProof)>=Seq::empty();let mut i=0;
                    while i<all_keys.len()
                        invariant i<=all_keys.len(),children.len()==i,ours==Some(bv),bv is Object,bv->Object_0==*ou,
                            b==Some(Data::Object(fields(ba@))),o==Some(Data::Object(fields(ou@))),t==Some(Data::Object(fields(th@))),!option_equal(o,b),!option_equal(t,b),!option_equal(o,t),
                            names(all_keys@).no_duplicates(),names(all_keys@).to_set()==keys(fields(ba@)).union(keys(fields(ou@))).union(keys(fields(th@))),
                            children.map(|j:int,p:(Seq<char>,MergeProof)|p.0)==names(all_keys@).take(i as int),fields(output@)==results(children),
                            forall|j:int|0<=j<i ==> {let (key,child)=#[trigger] children[j];child.valid() && child.base==lookup(fields(ba@),key) && child.ours==lookup(fields(ou@),key) && child.theirs==lookup(fields(th@),key)},
                        decreases all_keys.len()-i,
                    {
                        let result=merge(get(ba,all_keys[i].as_str()),get(ou,all_keys[i].as_str()),get(th,all_keys[i].as_str()));
                        let child=match result {Ok(value)=>value,Err(mut path)=>{path.insert(0,all_keys[i].clone());return Err(path);}};
                        proof {push_results(children,all_keys[i as int]@,child.evidence());}
                        let ghost before=fields(output@);let ghost entry=child.evidence();
                        if let Some(value)=child.value {output.push((all_keys[i].clone(),value));assert(fields(output@) =~= before.push((all_keys[i as int]@,entry.output.unwrap())));}
                        proof {children=children.push((all_keys[i as int]@,entry));assert(children.map(|j:int,p:(Seq<char>,MergeProof)|p.0) =~= names(all_keys@).take(i as int+1));}
                        i+=1;
                    }
                    let value=Value::Object(output);proof {value.shape();}
                    let proof=Ghost(MergeProof {base:b,ours:o,theirs:t,output:Some(value.model()),children});
                    proof {reveal(MergeProof::valid);assert(names(all_keys@).take(i as int)==names(all_keys@));}
                    Ok(Merged {value:Some(value),proof})
                },_=>Err(Vec::new()),
            }
        },_=>Err(Vec::new()),
    }
}
/// Decode an ordered keyed collection only when the order covers every live
/// member once. This prevents a merge from silently dropping a new sibling.
#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub enum OrderError {Unlisted,Duplicate,Missing}
pub fn ordered(items:&[(String,Value)],order:&[String])->(out:Result<Vec<Value>,OrderError>)
    ensures out.is_ok() ==> out->Ok_0.len()==order.len() && names(order@).no_duplicates()
        && names(order@).to_set()==keys(fields(items@))
        && forall|i:int|0<=i<order.len() ==> lookup(fields(items@),order@[i as int]@)==Some(out->Ok_0@[i].model()),
{
    let mut i=0;
    while i<items.len()
        invariant i<=items.len(),forall|j:int|0<=j<i ==> names(order@).contains(items@[j].0@),
        decreases items.len()-i,
    {if !contains_name(order,items[i].0.as_str()) {return Err(OrderError::Unlisted);}i+=1;}
    let mut result:Vec<Value>=Vec::new();let mut i=0;
    while i<order.len()
        invariant i<=order.len(),result.len()==i,
            forall|j:int|0<=j<items.len() ==> names(order@).contains(items@[j].0@),
            forall|j:int|0<=j<i ==> lookup(fields(items@),order@[j]@)==Some(result@[j].model()) && keys(fields(items@)).contains(order@[j]@),
            forall|j:int,k:int|0<=j<k<i ==> order@[j]@!=order@[k]@,
        decreases order.len()-i,
    {
        let mut j=0;
        while j<i
            invariant j<=i,i<order.len(),forall|k:int|0<=k<j ==> order@[k]@!=order@[i as int]@,
            decreases i-j,
        {if order[j].as_str()==order[i].as_str() {return Err(OrderError::Duplicate);}j+=1;}
        let value=match get(items,order[i].as_str()) {Some(value)=>value,None=>return Err(OrderError::Missing)};
        proof {
            let at=choose|j:int|0<=j<items.len() && *value==items@[j].1 && items@[j].0@==order@[i as int]@;
            assert(fields(items@).map(|j:int,p:(Seq<char>,Data)|p.0)[at]==order@[i as int]@);
            assert(keys(fields(items@)).contains(order@[i as int]@));
        }
        result.push(value.copy());i+=1;
    }
    proof {
        assert(names(order@).to_set() =~= keys(fields(items@))) by {
            assert forall|key:Seq<char>|names(order@).to_set().contains(key) implies keys(fields(items@)).contains(key) by {
                let j=choose|j:int|0<=j<order.len() && order@[j]@==key;
                assert(keys(fields(items@)).contains(order@[j]@));
            }
            assert forall|key:Seq<char>|keys(fields(items@)).contains(key) implies names(order@).to_set().contains(key) by {
                let j=choose|j:int|0<=j<items.len() && items@[j].0@==key;
                assert(names(order@).contains(items@[j].0@));
            }
        }
    }
    Ok(result)
}
pub open spec fn json_equal(a:Data,b:Data)->bool decreases a, {
    match (a,b) {
        (Data::Atom(x,k),Data::Atom(y,l))=>k==l && (x==y || k==Class::Number {signed:None,rank:0x8000000000000000}),
        (Data::Array(x),Data::Array(y))=>x.len()==y.len() && forall|i:int|0<=i<x.len() ==> json_equal(x[i],y[i]),
        (Data::Object(x),Data::Object(y))=>x.len()==y.len() && forall|i:int|0<=i<x.len() ==> match #[trigger] lookup(y,x[i].0) {Some(v)=>json_equal(x[i].1,v),None=>false},
        _=>false,
    }
}
impl Value {
    /// JSON objects compare fields by key, including after overlay appends keys.
    /// Numeric equality treats both floating zero signs alike. Selected values
    /// retain their original encoding; exact round-trip equality remains separate.
    pub fn json_equals(&self,other:&Self)->(out:bool)
        ensures out==json_equal(self.model(),other.model()),decreases *self,
    {
        proof {self.shape();other.shape();}
        match (self,other) {
            (Self::Atom(a,ak),Self::Atom(b,bk))=>ak==bk && (a.as_str()==b.as_str() || *ak==Class::Number {signed:None,rank:0x8000000000000000}),
            (Self::Array(a),Self::Array(b))=>{
                assert(elements(a@).len()==a.len());assert(elements(b@).len()==b.len());
                if a.len()!=b.len() {return false;}
                let mut i=0;
                while i<a.len()
                    invariant self is Array,self->Array_0==*a,self.model()==Data::Array(elements(a@)),other.model()==Data::Array(elements(b@)),
                        i<=a.len(),a.len()==b.len(),forall|j:int|0<=j<i ==> json_equal(a@[j].model(),b@[j].model()),
                    decreases a.len()-i,
                {
                    if !a[i].json_equals(&b[i]) {
                        assert(elements(a@)[i as int]==a@[i as int].model());assert(elements(b@)[i as int]==b@[i as int].model());return false;
                    }i+=1;
                }
                assert forall|j:int|0<=j<elements(a@).len() implies json_equal(elements(a@)[j],elements(b@)[j]) by {}
                true
            },
            (Self::Object(a),Self::Object(b))=>{
                assert(fields(a@).len()==a.len());assert(fields(b@).len()==b.len());
                if a.len()!=b.len() {return false;}
                let mut i=0;
                while i<a.len()
                    invariant self is Object,self->Object_0==*a,self.model()==Data::Object(fields(a@)),other.model()==Data::Object(fields(b@)),
                        i<=a.len(),a.len()==b.len(),forall|j:int|0<=j<i ==> match #[trigger] lookup(fields(b@),a@[j].0@) {Some(v)=>json_equal(a@[j].1.model(),v),None=>false},
                    decreases a.len()-i,
                {
                    let value=match get(b,a[i].0.as_str()) {
                        Some(value)=>value,
                        None=>{
                            assert(fields(a@)[i as int]==(a@[i as int].0@,a@[i as int].1.model()));
                        assert(!(match lookup(fields(b@),fields(a@)[i as int].0) {Some(v)=>json_equal(fields(a@)[i as int].1,v),None=>false}));
                        reveal(json_equal);
                        assert(!json_equal(self.model(),other.model()));return false;
                        },
                    };
                    if !a[i].1.json_equals(value) {
                        assert(fields(a@)[i as int]==(a@[i as int].0@,a@[i as int].1.model()));
                        assert(!(match lookup(fields(b@),fields(a@)[i as int].0) {Some(v)=>json_equal(fields(a@)[i as int].1,v),None=>false}));
                        reveal(json_equal);
                        assert(!json_equal(self.model(),other.model()));return false;
                    }i+=1;
                }
                assert forall|j:int|0<=j<fields(a@).len() implies match #[trigger] lookup(fields(b@),fields(a@)[j].0) {Some(v)=>json_equal(fields(a@)[j].1,v),None=>false} by {}
                true
            },_=>false,
        }
    }
}
pub open spec fn option_equal(a:Option<Data>,b:Option<Data>)->bool {
    match (a,b) {(Some(a),Some(b))=>json_equal(a,b),(None,None)=>true,_=>false}
}
}
