//! Definition 81: the six fields of a declarative configuration entry.
//!
//! Identifiers, module URLs, annotations and configuration values are opaque
//! parameters. The module does not parse URLs/JSON, resolve modules, interpret
//! annotations, or prove reconciliation converges. Parent membership belongs
//! to the surrounding tree; it is not a seventh field of an entry.
use vstd::prelude::*;

verus! {

pub struct Entry<Id, Url, Isolation, Interception, Config> {
    pub id: Id,
    pub url: Url,
    pub isolate: Isolation,
    pub intercept: Interception,
    pub config: Config,
    pub disabled: bool,
}

impl<Id, Url, Isolation, Interception, Config> Entry<Id, Url, Isolation, Interception, Config> {
    pub fn new(id:Id,url:Url,isolate:Isolation,intercept:Interception,config:Config,disabled:bool)->(entry:Self)
        ensures entry.id==id,entry.url==url,entry.isolate==isolate,entry.intercept==intercept,
            entry.config==config,entry.disabled==disabled,
    {
        Self {id,url,isolate,intercept,config,disabled}
    }

    pub fn enabled(&self)->(enabled:bool)
        ensures enabled==!self.disabled,
    {
        !self.disabled
    }

    /// Administrative status changes preserve the reconciliation key and recipe.
    pub fn set_disabled(&mut self,disabled:bool)
        ensures final(self).disabled==disabled,final(self).id==old(self).id,final(self).url==old(self).url,
            final(self).isolate==old(self).isolate,final(self).intercept==old(self).intercept,final(self).config==old(self).config,
    {
        self.disabled=disabled;
    }

    /// Replace the bound configuration without changing module or annotations.
    pub fn set_config(&mut self,config:Config)
        ensures final(self).config==config,final(self).id==old(self).id,final(self).url==old(self).url,
            final(self).isolate==old(self).isolate,final(self).intercept==old(self).intercept,final(self).disabled==old(self).disabled,
    {
        self.config=config;
    }
}

/// The stable reconciliation key is parent-local. Changing only the parent
/// changes the key even when every field of the record is identical.
pub open spec fn reconciliation_key<Parent,Id,Url,Isolation,Interception,Config>(
    parent:Parent,entry:Entry<Id,Url,Isolation,Interception,Config>)->(Parent,Id) {
    (parent,entry.id)
}

/// Binding selects the named module and supplies exactly this entry's config.
/// This denotes binding only; no arbitrary module callback is executed here.
pub open spec fn bound_effect<Id,Url,Isolation,Interception,Config,Effect>(
    modules:spec_fn(Url,Config)->Effect,entry:Entry<Id,Url,Isolation,Interception,Config>)->Effect {
    modules(entry.url,entry.config)
}

pub proof fn binding_ignores_administration<Id,Url,Isolation,Interception,Config,Effect>(
    modules:spec_fn(Url,Config)->Effect,a:Entry<Id,Url,Isolation,Interception,Config>,b:Entry<Id,Url,Isolation,Interception,Config>)
    requires a.url==b.url,a.config==b.config,
    ensures bound_effect(modules,a)==bound_effect(modules,b),
{}

pub proof fn sibling_keys<Parent,Id,Url,Isolation,Interception,Config>(parent:Parent,
    a:Entry<Id,Url,Isolation,Interception,Config>,b:Entry<Id,Url,Isolation,Interception,Config>)
    ensures (reconciliation_key(parent,a)==reconciliation_key(parent,b))==(a.id==b.id),
{}

pub proof fn different_parent_keys<Parent,Id,Url,Isolation,Interception,Config>(left:Parent,right:Parent,
    entry:Entry<Id,Url,Isolation,Interception,Config>)
    requires left!=right,
    ensures reconciliation_key(left,entry)!=reconciliation_key(right,entry),
{}

} // verus!
