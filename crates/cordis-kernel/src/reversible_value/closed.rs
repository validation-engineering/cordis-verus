//! Closed native data. Object references are names in an explicit object table,
//! never arbitrary Rust handles. Collections use a finite immutable DAG, so the
//! kernel can visit every reference without invoking user code or destructors.
use vstd::prelude::*;

verus! {
broadcast use vstd::seq_lib::group_seq_properties;
#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub enum Kind {Scalar,Payload}
#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub struct Reference {pub index:usize,pub kind:Kind,pub name:u64}
/// Child indices precede their collection node. Repeated indices preserve DAG
/// sharing; reference aliases are independently checked by the object table.
pub enum Node {Null,Bool(bool),Integer(i64),Unsigned(u64),Bytes(Vec<u8>),Reference(Reference),Sequence(Vec<usize>),Record(Vec<(Vec<u8>,usize)>)}
pub enum Atom {Null,Bool(bool),Integer(i64),Unsigned(u64),Bytes(Seq<u8>),Reference(Reference),Sequence(Seq<usize>),Record(Seq<(Seq<u8>,usize)>)}
impl View for Node {
    type V=Atom;
    open spec fn view(&self)->Atom {
        match self {
            Self::Null=>Atom::Null,Self::Bool(b)=>Atom::Bool(*b),Self::Integer(n)=>Atom::Integer(*n),Self::Unsigned(n)=>Atom::Unsigned(*n),
            Self::Bytes(b)=>Atom::Bytes(b@),Self::Reference(r)=>Atom::Reference(*r),Self::Sequence(c)=>Atom::Sequence(c@),
            Self::Record(c)=>Atom::Record(c@.map(|_:int,p:(Vec<u8>,usize)|(p.0@,p.1))),
        }
    }
}
pub open spec fn before(node:Atom,at:int)->bool {
    match node {Atom::Sequence(c)=>forall|j:int|0<=j<c.len() ==> #[trigger] c[j]<at,
        Atom::Record(c)=>forall|j:int|0<=j<c.len() ==> (#[trigger] c[j]).1<at,_=>true}
}
pub open spec fn admitted(node:Atom,schema:Seq<Reference>)->bool {
    match node {Atom::Reference(r)=>r.index<schema.len() && schema[r.index as int]==r,_=>true}
}
impl Node {
    fn ordered(&self,at:usize)->(out:bool)
        ensures out==before(self@,at as int),
    {
        match self {
            Node::Sequence(c)=>{
                let mut i=0;
                while i<c.len()
                    invariant self@==Atom::Sequence(c@),i<=c.len(),forall|j:int|0<=j<i ==> #[trigger] c@[j]<at,
                    decreases c.len()-i,
                {if c[i]>=at {proof {assert(c@[i as int]>=at);assert(!before(self@,at as int)) by {if before(self@,at as int) {assert((self@)->Sequence_0[i as int]<(at as int));}}}return false;}i+=1;}true
            },
            Node::Record(c)=>{
                let mut i=0;
                while i<c.len()
                    invariant self@==Atom::Record(c@.map(|_:int,p:(Vec<u8>,usize)|(p.0@,p.1))),i<=c.len(),forall|j:int|0<=j<i ==> (#[trigger] c@[j]).1<at,
                    decreases c.len()-i,
                {if c[i].1>=at {proof {assert(c@[i as int].1>=at);assert(!before(self@,at as int)) by {if before(self@,at as int) {assert(((self@)->Record_0[i as int]).1<(at as int));}}}return false;}i+=1;}true
            },_=>true,
        }
    }
}
pub struct Value {nodes:Vec<Node>,root:usize}
impl Value {
    #[verifier::type_invariant]
    closed spec fn invariant(&self)->bool {self.wf()}
    pub fn null()->(out:Self) ensures out.wf(),out.nodes()==seq![Atom::Null],out.root()==0, {Self {nodes:vec![Node::Null],root:0}}
    pub fn representation(&self) ensures self.wf(), {proof {use_type_invariant(self);}}
    pub closed spec fn nodes(&self)->Seq<Atom> {self.nodes@.map(|_:int,n:Node|n@)}
    pub closed spec fn root(&self)->usize {self.root}
    pub closed spec fn wf(&self)->bool {self.root<self.nodes.len() && forall|i:int|0<=i<self.nodes.len() ==> before(#[trigger] self.nodes@[i]@,i)}
    pub open spec fn admissible(&self,schema:Seq<Reference>)->bool {self.wf() && forall|i:int|0<=i<self.nodes().len() ==> admitted(#[trigger] self.nodes()[i],schema)}
    /// Returns the original input on malformed collection edges or root.
    pub fn new(nodes:Vec<Node>,root:usize)->(out:Result<Self,(Vec<Node>,usize)>)
        ensures out.is_ok() ==> out->Ok_0.wf() && out->Ok_0.nodes()==nodes@.map(|_:int,n:Node|n@) && out->Ok_0.root()==root,
            out.is_err() ==> out->Err_0==(nodes,root),
    {
        if root>=nodes.len() {return Err((nodes,root));}
        let mut i=0;
        while i<nodes.len()
            invariant root<nodes.len(),i<=nodes.len(),forall|j:int|0<=j<i ==> before(#[trigger] nodes@[j]@,j),
            decreases nodes.len()-i,
        {
            if !nodes[i].ordered(i) {return Err((nodes,root));}i+=1;        }Ok(Self {nodes,root})
    }
    /// Exhaustive object-table admission. Unused nodes are checked too, so a
    /// later root or continuation cannot reveal an unchecked hidden reference.
    pub fn check(&self,schema:&[Reference])->(out:bool)
        requires self.wf(),ensures out==self.admissible(schema@),
    {
        let mut i=0;
        while i<self.nodes.len()
            invariant self.wf(),i<=self.nodes.len(),forall|j:int|0<=j<i ==> admitted(#[trigger] self.nodes()[j],schema@),
            decreases self.nodes.len()-i,
        {
            if let Node::Reference(r)=&self.nodes[i] {if r.index>=schema.len() || schema[r.index]!=*r {proof {assert(!admitted(self.nodes()[i as int],schema@));}return false;}}
            i+=1;
        }true
    }
    pub fn node(&self,index:usize)->(out:Option<&Node>)
        ensures out.is_some()==(index<self.nodes().len()),out.is_some() ==> out.unwrap()@==self.nodes()[index as int],
    {if index<self.nodes.len() {Some(&self.nodes[index])} else {None}}
    pub fn root_index(&self)->(out:usize) ensures out==self.root(), {self.root}
    pub fn len(&self)->(out:usize) ensures out==self.nodes().len(), {self.nodes.len()}
    pub fn is_empty(&self)->(out:bool) ensures out==(self.nodes().len()==0), {self.nodes.is_empty()}
}
/// A complete schema includes the authentic allocation name, not just its type.
pub open spec fn layout(schema:Seq<Reference>)->bool {
    forall|i:int|0<=i<schema.len() ==> (#[trigger] schema[i]).index==i
}
fn check_layout(schema:&[Reference])->(out:bool)
    ensures out==layout(schema@),
{
    let mut i=0;
    while i<schema.len()
        invariant i<=schema.len(),forall|j:int|0<=j<i ==> (#[trigger] schema@[j]).index==j,
        decreases schema.len()-i,
    {if schema[i].index!=i {proof {assert(!layout(schema@));}return false;}i+=1;}true
}
/// A checked injection from all source object names into a target object table.
/// It is a concrete input transformer for stored values, retained history and
/// future arguments; unrelated target objects need not be in its image.
pub struct Transport {source:Vec<Reference>,target:Vec<Reference>,names:Vec<usize>}
impl Transport {
    pub fn target_schema(&self)->(out:&[Reference]) ensures out@==self.target(), {self.target.as_slice()}
    pub closed spec fn source(&self)->Seq<Reference> {self.source@}
    pub closed spec fn target(&self)->Seq<Reference> {self.target@}
    pub closed spec fn names(&self)->Seq<usize> {self.names@}
    pub closed spec fn wf(&self)->bool {
        self.names.len()==self.source.len() && layout(self.source@) && layout(self.target@)
            && (forall|i:int|0<=i<self.names.len() ==> (#[trigger] self.names@[i])<self.target.len() && self.source@[i].kind==self.target@[self.names@[i] as int].kind)
            && forall|i:int,j:int|0<=i<j<self.names.len() ==> self.names@[i]!=self.names@[j]
    }
    pub fn new(source:Vec<Reference>,target:Vec<Reference>,names:Vec<usize>)->(out:Option<Self>)
        ensures out.is_some() ==> out.unwrap().wf() && out.unwrap().source()==source@ && out.unwrap().target()==target@ && out.unwrap().names()==names@,
    {
        if !check_layout(source.as_slice()) || !check_layout(target.as_slice()) || source.len()!=names.len() {return None;}
        let mut i=0;
        while i<names.len()
            invariant layout(source@),layout(target@),names.len()==source.len(),i<=names.len(),
                forall|j:int|0<=j<i ==> (#[trigger] names@[j])<target.len() && source@[j].kind==target@[names@[j] as int].kind,
                forall|j:int,k:int|0<=j<k<i ==> names@[j]!=names@[k],
            decreases names.len()-i,
        {
            if names[i]>=target.len() || source[i].kind!=target[names[i]].kind {return None;}
            let mut j=0;
            while j<i
                invariant j<=i,i<names.len(),forall|k:int|0<=k<j ==> names@[k]!=names@[i as int],
                decreases i-j,
            {if names[j]==names[i] {return None;}j+=1;}
            i+=1;
        }Some(Self {source,target,names})
    }
    pub open spec fn reference(&self,r:Reference)->Reference {self.target()[self.names()[r.index as int] as int]}
    pub proof fn aliases(&self,a:Reference,b:Reference)
        requires self.wf(),a.index<self.source().len(),b.index<self.source().len(),self.source()[a.index as int]==a,self.source()[b.index as int]==b,
        ensures (a==b)==(self.reference(a)==self.reference(b)),
    {if a.index<b.index {} else if b.index<a.index {}}
    pub open spec fn atom(&self,node:Atom)->Atom {match node {Atom::Reference(r)=>Atom::Reference(self.reference(r)),_=>node}}
    /// All topology, bytes and scalar data are copied unchanged. Only explicit
    /// object names move; no user-supplied Clone/Eq/Drop implementation runs.
    pub fn apply(&self,value:&Value)->(out:Option<Value>)
        requires self.wf(),value.wf(),
        ensures out.is_some()==value.admissible(self.source()),
            out.is_some() ==> out.unwrap().admissible(self.target()) && out.unwrap().root()==value.root()
                && out.unwrap().nodes()==value.nodes().map(|_:int,n:Atom|self.atom(n)),
    {
        if !value.check(self.source.as_slice()) {return None;}
        let mut nodes:Vec<Node>=Vec::new();let mut i=0;
        while i<value.nodes.len()
            invariant self.wf(),value.admissible(self.source()),i<=value.nodes.len(),nodes.len()==i,
                forall|j:int|0<=j<i ==> (#[trigger] nodes@[j])@==self.atom(value.nodes()[j]) && before(nodes@[j]@,j) && admitted(nodes@[j]@,self.target()),
            decreases value.nodes.len()-i,
        {
            let node=match &value.nodes[i] {
                Node::Null=>Node::Null,Node::Bool(b)=>Node::Bool(*b),Node::Integer(n)=>Node::Integer(*n),Node::Unsigned(n)=>Node::Unsigned(*n),
                Node::Bytes(bytes)=>Node::Bytes(bytes.clone()),
                Node::Reference(r)=>Node::Reference(self.target[self.names[r.index]]),
                Node::Sequence(children)=>Node::Sequence(children.clone()),
                Node::Record(children)=>{
                    let mut copied:Vec<(Vec<u8>,usize)>=Vec::new();let mut j=0;
                    while j<children.len()
                        invariant j<=children.len(),copied.len()==j,forall|k:int|0<=k<j ==> (#[trigger] copied@[k]).0@==children@[k].0@ && copied@[k].1==children@[k].1,
                        decreases children.len()-j,
                    {copied.push((children[j].0.clone(),children[j].1));j+=1;}
                    proof {assert(copied@.map(|_:int,p:(Vec<u8>,usize)|(p.0@,p.1)) =~= children@.map(|_:int,p:(Vec<u8>,usize)|(p.0@,p.1)));}
                    Node::Record(copied)
                },
            };
            proof {assert(node@==self.atom(value.nodes()[i as int]));}
            nodes.push(node);i+=1;
        }
        let out=Value {nodes,root:value.root};
        proof {assert(out.nodes() =~= value.nodes().map(|_:int,n:Atom|self.atom(n)));}
        Some(out)
    }
}
}

pub mod objects;

pub mod replay;

pub mod semantics;

pub mod recovery;

pub(crate) mod slots;

pub mod fresh;

pub mod context;

pub mod contract;

pub mod component;
