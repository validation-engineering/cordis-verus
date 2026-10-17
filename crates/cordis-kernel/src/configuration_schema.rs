//! Structural schema normalization used by the real Loader. The JSON adapter
//! classifies scalar tokens; this interpreter owns ranges, defaults, unknown
//! fields, complete array/object traversal and the actual normalized result.
#[cfg(verus_keep_ghost)]
use crate::configuration_data::Data;
use crate::configuration_data::{self as data, Class, Value};
use vstd::prelude::*;
verus! {
broadcast use vstd::seq_lib::group_seq_properties;
pub enum Schema {Any,Boolean,String,Integer {min:Option<i64>,max:Option<i64>},Number {low:Option<u64>,high:Option<u64>},Enum(Vec<Value>),Array(Box<Schema>),Object {fields:Vec<Field>,allow_unknown:bool},Nullable(Box<Schema>)}
pub struct Field {pub name:String,pub schema:Schema,pub required:bool,pub default:Option<Value>}
#[derive(Debug)]
pub enum Part {Field(String),Index(usize)}
#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub enum Reason {Boolean,String,Integer,Number,Range,Enum,Array,Object,Unknown,Required}
#[derive(Debug)]
pub struct Failure {pub path:Vec<Part>,pub reason:Reason}
fn fail(reason:Reason)->Failure {Failure {path:Vec::new(),reason}}
impl Failure {
    fn at(self,part:Part)->Self {let mut next=self;next.path.insert(0,part);next}
}
pub open spec fn field_names(fields:Seq<Field>)->Seq<Seq<char>> {fields.map(|i:int,f:Field|f.name@)}
pub open spec fn null(value:Data)->bool {matches!(value,Data::Atom(_,Class::Null))}
pub open spec fn scalar(schema:Schema,value:Data)->bool {
    match schema {
        Schema::Any=>true,
        Schema::Boolean=>matches!(value,Data::Atom(_,Class::Boolean)),
        Schema::String=>matches!(value,Data::Atom(_,Class::String)),
        Schema::Integer {min,max}=>match value {Data::Atom(_,Class::Number {signed:Some(n),rank:_})=>(min.is_none() || min.unwrap()<=n) && (max.is_none() || n<=max.unwrap()),_=>false},
        Schema::Number {low:min,high:max}=>match value {Data::Atom(_,Class::Number {signed:_,rank:n})=>(min.is_none() || min.unwrap()<=n) && (max.is_none() || n<=max.unwrap()),_=>false},
        Schema::Enum(values)=>exists|i:int|0<=i<values.len() && data::json_equal(values@[i].model(),value),
        _=>false,
    }
}
pub open spec fn defaults(value:Option<Value>)->Option<Data> {match value {Some(v)=>Some(v.model()),None=>None}}
#[verifier::opaque]
pub open spec fn normalized(schema:Schema,value:Data)->Option<Data> decreases schema, {
    match schema {
        Schema::Nullable(inner)=>if null(value) {Some(value)} else {normalized(*inner,value)},
        Schema::Array(inner)=>match value {
            Data::Array(items)=>if forall|i:int|0<=i<items.len() ==> normalized(*inner,items[i]).is_some() {
                Some(Data::Array(Seq::new(items.len(),|i:int|normalized(*inner,items[i]).unwrap())))
            } else {None},_=>None},
        Schema::Object {fields,allow_unknown}=>match value {
            Data::Object(items)=>if allow_unknown || forall|i:int|0<=i<items.len() ==> field_names(fields@).contains(items[i].0) {
                normalize_fields(fields@,items,items)
            } else {None},_=>None},
        _=>if scalar(schema,value) {Some(value)} else {None},
    }
}
#[verifier::opaque]
pub open spec fn normalize_fields(fields:Seq<Field>,input:Seq<(Seq<char>,Data)>,output:Seq<(Seq<char>,Data)>)->Option<Data> decreases fields, {
    if fields.len()==0 {Some(Data::Object(output))} else {
        let field=fields.first();let chosen=match data::lookup(input,field.name@) {Some(v)=>Some(v),None=>defaults(field.default)};
        match chosen {
            Some(value)=>match normalized(field.schema,value) {
                Some(value)=>normalize_fields(fields.skip(1),input,data::replaced(output,field.name@,value)),None=>None},
            None=>if field.required {None} else {normalize_fields(fields.skip(1),input,output)},
        }
    }
}
proof fn array_result(inner:Box<Schema>,input:Seq<Data>,output:Seq<Data>)
    requires input.len()==output.len(),forall|i:int|0<=i<input.len() ==> normalized(*inner,input[i])==Some(output[i]),
    ensures normalized(Schema::Array(inner),Data::Array(input))==Some(Data::Array(output)),
{
    reveal_with_fuel(normalized,2);reveal(normalize_fields);
    assert forall|i:int|0<=i<input.len() implies normalized(*inner,input[i]).is_some() by {}
    let result=normalized(Schema::Array(inner),Data::Array(input));
    assert(result.is_some());assert(result.unwrap() is Array);
    assert(result.unwrap()->Array_0.len()==input.len());
    assert(result.unwrap()->Array_0 =~= output) by {
        assert forall|i:int|0<=i<input.len() implies result.unwrap()->Array_0[i]==output[i] by {
            assert(result.unwrap()->Array_0[i]==normalized(*inner,input[i]).unwrap());
        }
    }
}
proof fn object_start(fields:Vec<Field>,allow:bool,input:Seq<(Seq<char>,Data)>)
    requires allow || forall|i:int|0<=i<input.len() ==> field_names(fields@).contains(input[i].0),
    ensures normalized(Schema::Object {fields,allow_unknown:allow},Data::Object(input))==normalize_fields(fields@,input,input),
{reveal_with_fuel(normalized,2);reveal(normalize_fields);}
proof fn field_step(fields:Seq<Field>,input:Seq<(Seq<char>,Data)>,output:Seq<(Seq<char>,Data)>)
    requires fields.len()>0,
    ensures normalize_fields(fields,input,output)=={
        let field=fields.first();let chosen=match data::lookup(input,field.name@) {Some(v)=>Some(v),None=>defaults(field.default)};
        match chosen {
            Some(value)=>match normalized(field.schema,value) {Some(value)=>normalize_fields(fields.skip(1),input,data::replaced(output,field.name@,value)),None=>None},
            None=>if field.required {None} else {normalize_fields(fields.skip(1),input,output)},
        }
    },
{reveal_with_fuel(normalize_fields,2);reveal(normalized);}
fn declared(fields:&[Field],key:&str)->(out:bool) ensures out==field_names(fields@).contains(key@),
{
    let mut i=0;
    while i<fields.len()
        invariant i<=fields.len(),forall|j:int|0<=j<i ==> fields@[j].name@!=key@,
        decreases fields.len()-i,
    {if fields[i].name.as_str()==key {assert(field_names(fields@)[i as int]==key@);return true;}i+=1;}
    false
}
impl Schema {
    pub fn validate(&self,value:&Value)->(out:Result<Value,Failure>)
        ensures match out {Ok(v)=>normalized(*self,value.model())==Some(v.model()),Err(_)=>normalized(*self,value.model()).is_none()},
        decreases *self,
    {
        reveal_with_fuel(normalized,2);reveal(normalize_fields);proof {value.shape();}
        match self {
            Self::Any=>Ok(value.copy()),
            Self::Boolean=>match value {Value::Atom(_,Class::Boolean)=>Ok(value.copy()),_=>Err(fail(Reason::Boolean))},
            Self::String=>match value {Value::Atom(_,Class::String)=>Ok(value.copy()),_=>Err(fail(Reason::String))},
            Self::Integer {min,max}=>match value {
                Value::Atom(_,Class::Number {signed:Some(n),rank:_})=>{
                    if let Some(min)=min {if n<min {return Err(fail(Reason::Range));}}
                    if let Some(max)=max {if n>max {return Err(fail(Reason::Range));}}
                    Ok(value.copy())
                },_=>Err(fail(Reason::Integer))},
            Self::Number {low:min,high:max}=>match value {
                Value::Atom(_,Class::Number {signed:_,rank:n})=>{
                    if let Some(min)=min {if n<min {return Err(fail(Reason::Range));}}
                    if let Some(max)=max {if n>max {return Err(fail(Reason::Range));}}
                    Ok(value.copy())
                },_=>Err(fail(Reason::Number))},
            Self::Enum(values)=>{
                let mut i=0;
                while i<values.len()
                    invariant self is Enum,self->Enum_0==*values,i<=values.len(),forall|j:int|0<=j<i ==> !data::json_equal(values@[j].model(),value.model()),
                    decreases values.len()-i,
                {if values[i].json_equals(value) {reveal(normalized);return Ok(value.copy());}i+=1;}
                reveal(normalized);Err(fail(Reason::Enum))
            },
            Self::Nullable(inner)=>{
                if let Value::Atom(_,Class::Null)=value {Ok(value.copy())} else {
                    let out=inner.validate(value);
                    assert(match out {Ok(v)=>normalized(*self,value.model())==Some(v.model()),Err(_)=>normalized(*self,value.model()).is_none()});out
                }
            },
            Self::Array(inner)=>match value {
                Value::Array(items)=>{
                    let mut result:Vec<Value>=Vec::new();let mut i=0;
                    while i<items.len()
                        invariant self is Array,self->Array_0==*inner,value.model()==Data::Array(data::elements(items@)),
                            i<=items.len(),result.len()==i,forall|j:int|0<=j<i ==> normalized(**inner,items@[j].model())==Some(result@[j].model()),
                        decreases items.len()-i,
                    {
                        let next=match inner.validate(&items[i]) {Ok(v)=>v,Err(error)=>{
                            reveal(normalized);assert(data::elements(items@)[i as int]==items@[i as int].model());return Err(error.at(Part::Index(i)));}};
                        result.push(next);i+=1;
                    }
                    let output=Value::Array(result);proof {output.shape();reveal(normalized);
                        assert(data::elements(output->Array_0@) =~= Seq::new(items.len() as nat,|j:int|normalized(**inner,data::elements(items@)[j]).unwrap()));}
                    reveal_with_fuel(normalized,2);
                    assert forall|j:int|0<=j<data::elements(items@).len() implies normalized(**inner,data::elements(items@)[j]).is_some() by {
                        assert(data::elements(items@)[j]==items@[j].model());
                        assert(normalized(**inner,items@[j].model())==Some(output->Array_0@[j].model()));
                    }
                    proof {array_result(*inner,data::elements(items@),data::elements(output->Array_0@));}
                    assert(normalized(*self,value.model())==Some(output.model()));Ok(output)
                },_=>Err(fail(Reason::Array))},
            Self::Object {fields,allow_unknown}=>match value {
                Value::Object(items)=>{
                    let mut i=0;
                    while i<items.len()
                        invariant self is Object,self->Object_fields==*fields,self->Object_allow_unknown==*allow_unknown,
                            value.model()==Data::Object(data::fields(items@)),i<=items.len(),
                            forall|j:int|0<=j<i ==> *allow_unknown || field_names(fields@).contains(items@[j].0@),
                        decreases items.len()-i,
                    {if !*allow_unknown && !declared(fields,items[i].0.as_str()) {reveal(normalized);assert(data::fields(items@)[i as int].0==items@[i as int].0@);return Err(fail(Reason::Unknown).at(Part::Field(items[i].0.clone())));}i+=1;}
                    let copied=value.copy();proof {copied.shape();}let mut result=match copied {Value::Object(items)=>items,_=>unreachable!()};
                    let ghost input=data::fields(items@);let mut i=0;
                    reveal(normalized);proof {assert forall|j:int|0<=j<input.len() implies *allow_unknown || field_names(fields@).contains(input[j].0) by {assert(input[j].0==items@[j].0@);} }
                    proof {object_start(*fields,*allow_unknown,input);}
                    assert(normalized(*self,value.model())==normalize_fields(fields@,input,input));
                    while i<fields.len()
                        invariant self is Object,self->Object_fields==*fields,self->Object_allow_unknown==*allow_unknown,
                            i<=fields.len(),input==data::fields(items@),value.model()==Data::Object(input),
                            normalized(*self,value.model())==normalize_fields(fields@.skip(i as int),input,data::fields(result@)),
                        decreases fields.len()-i,
                    {
                        let field=&fields[i];let chosen=match data::get(items,field.name.as_str()) {Some(v)=>Some(v),None=>field.default.as_ref()};
                        assert(data::optional(chosen)==match data::lookup(input,field.name@) {Some(v)=>Some(v),None=>defaults(field.default)});
                        let ghost prior=data::fields(result@);
                        let ghost tail=fields@.skip(i as int+1);
                        proof {field_step(fields@.skip(i as int),input,prior);assert(fields@.skip(i as int).first()==*field);assert(fields@.skip(i as int).skip(1)==tail);}
                        match chosen {
                            Some(v)=>{
                                let next=match field.schema.validate(v) {Ok(v)=>v,Err(error)=>{reveal(normalize_fields);return Err(error.at(Part::Field(field.name.clone())))}};
                                assert(normalize_fields(fields@.skip(i as int),input,prior)==normalize_fields(tail,input,data::replaced(prior,field.name@,next.model())));
                                data::put(&mut result,field.name.clone(),next);
                            },
                            None=>{reveal(normalize_fields);if field.required {return Err(fail(Reason::Required).at(Part::Field(field.name.clone())));}},
                        }
                        i+=1;
                    }
                    reveal(normalize_fields);assert(fields@.skip(i as int)==Seq::<Field>::empty());
                    let output=Value::Object(result);proof {output.shape();}assert(normalized(*self,value.model())==Some(output.model()));Ok(output)
                },_=>Err(fail(Reason::Object))},
        }
    }
}
}
