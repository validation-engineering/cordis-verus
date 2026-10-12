//! A full-carrier Unit Component input to the strict typed Child primitive.
//!
//! Equal all-table observations do not determine insertion's reservation domain.
//! The final bridge relates this exact domain to the executable Kernel checker.
//! It does not construct recursive Gamma or a full witness for the spawning
//! parent, and the registration bridge does not interpret runtime service values.
use crate::paper_instantiation as i;
#[cfg(verus_keep_ghost)]
use crate::{paper_observations as p, paper_typed_context as t, refinement as r};
use crate::{Error, Kernel, Port};
use vstd::prelude::*;

verus! {

pub open spec fn equal()->spec_fn(bool,int,int)->bool { |_:bool,a:int,b:int|a==b }
/// Each key's fiber is int. Every value in every SmallState is interpreted,
/// including absent, inactive, retired and overlapping registry inputs.
pub open spec fn types()->spec_fn(bool,int)->bool { |_:bool,_:int|true }
pub open spec fn installs()->spec_fn(usize,bool,i::SmallState)->ISet<bool> {
    |n:usize,id:bool,a:i::SmallState|i::no_installs(n,id,a)
}
pub open spec fn child(a:i::SmallState,parent:usize,name:usize)->Option<i::Landing<i::SmallState,usize,bool>> {
    i::typed_instantiate(types(),equal(),i::small_view(),i::small_editors(),installs(),
        a,parent,name,i::child_component(),|n:usize|Some(n==2))
}
pub open spec fn reserved()->i::SmallState {
    (i::small_editors().insert)(i::before(),0,1,i::child_component()).unwrap()
}

pub proof fn interpretation(name:usize)
    ensures i::editor_laws(i::small_view(),i::small_editors()),
        t::projection_typed(types(),|a:i::SmallState|p::project(i::small_view(),a,ISet::full())),
        i::typed_component(equal(),i::small_view(),installs(),name,i::child_component()),
{
    i::small_editors_satisfy_laws();i::small_component_has_full_witness(name);
}

pub proof fn exact_domain(a:i::SmallState,parent:usize,name:usize)
    ensures child(a,parent,name).is_some()==i::enabled(i::small_view(),a,parent,name,i::child_component()),
{
    interpretation(name);
    if i::enabled(i::small_view(),a,parent,name,i::child_component()) {
        i::dependent_typed_instantiation(types(),equal(),i::small_view(),i::small_editors(),installs(),
            a,parent,name,i::child_component(),|n:usize|Some(n==2));
    }
}

/// This strengthens the grammar-only boundary with the same actual Component,
/// a full-carrier typed witness, concrete editors, and a returned inverse.
pub proof fn equal_observations_different_domains(keys:ISet<bool>)
    ensures {
        let a=i::before();let b=reserved();let view=i::small_view();let edit=i::small_editors();
        &&& i::editor_laws(view,edit)
        &&& t::projection_typed(types(),|s:i::SmallState|p::project(view,s,ISet::full()))
        &&& i::typed_component(equal(),view,installs(),2,i::child_component())
        &&& (edit.insert)(a,0,1,i::child_component())==Some(b)
        &&& p::unambiguous(view,a) && p::unambiguous(view,b)
        &&& p::lookup(view,a,0,true)==Some(7) && p::lookup(view,b,0,true)==Some(7)
        &&& p::project(view,a,keys)==p::project(view,b,keys)
        &&& !p::registered(view,a,2) && !p::registered(view,b,2)
        &&& (view.registry)(a)[0].component==(view.registry)(b)[0].component
        &&& (view.registry)(a)[0].theta==(view.registry)(b)[0].theta
        &&& (view.registry)(b)[1].table.is_empty()
        &&& (view.registry)(b)[1].theta==p::Theta::Inactive
        &&& child(a,0,2).is_some() && child(b,0,2).is_none()
        &&& child(a,0,2).unwrap().name==2 && child(a,0,2).unwrap().next==Some(true)
        &&& child(a,0,2).unwrap().inverse.child==2
        &&& i::undo(edit,child(a,0,2).unwrap().inverse,child(a,0,2).unwrap().state).is_some()
        &&& p::project(view,i::undo(edit,child(a,0,2).unwrap().inverse,child(a,0,2).unwrap().state).unwrap(),keys)
            ==p::project(view,a,keys)
    },
{
    interpretation(1);interpretation(2);
    let a=i::before();let b=reserved();let view=i::small_view();let edit=i::small_editors();
    assert(i::enabled(view,a,0,1,i::child_component()));
    assert(p::unambiguous(view,a));
    i::immediate_table_recovery(equal(),view,edit,installs(),a,0,1,i::child_component(),|n:usize|Some(n==2),keys);
    assert forall|n:usize,k:bool| p::lookup(view,a,n,k)==p::lookup(view,b,n,k) by { }
    i::unchanged_bindings_projection(view,a,b,keys);
    exact_domain(a,0,2);exact_domain(b,0,2);
    assert(!i::enabled(view,b,0,2,i::child_component())) by {
        assert(p::registered(view,b,1));
        assert((view.registry)(b)[1].component.provisions.contains(false));
    }
    i::immediate_retirement(equal(),view,edit,installs(),a,0,2,i::child_component(),|n:usize|Some(n==2));
    i::immediate_table_recovery(equal(),view,edit,installs(),a,0,2,i::child_component(),|n:usize|Some(n==2),keys);
}

/// A successful creation followed by its actual inverse restores every
/// service observation, but reserves the child's provision even for a fresh
/// subsequent name. No identity reuse or allocator exhaustion is involved.
pub open spec fn recovered()->i::SmallState {
    let out=child(i::before(),0,2).unwrap();
    i::undo(i::small_editors(),out.inverse,out.state).unwrap()
}
pub proof fn recovery_changes_admission()
    ensures child(i::before(),0,2).is_some(),
        i::undo(i::small_editors(),child(i::before(),0,2).unwrap().inverse,child(i::before(),0,2).unwrap().state).is_some(),
        p::project(i::small_view(),recovered(),ISet::full())==p::project(i::small_view(),i::before(),ISet::full()),
        !p::registered(i::small_view(),i::before(),3),!p::registered(i::small_view(),recovered(),3),
        child(i::before(),0,3).is_some(),child(recovered(),0,3).is_none(),
        recovered().rows[2].retired && recovered().rows[2].table.is_empty(),
{
    equal_observations_different_domains(ISet::full());
    exact_domain(i::before(),0,3);exact_domain(recovered(),0,3);
    assert(!i::enabled(i::small_view(),recovered(),0,3,i::child_component())) by {
        assert(recovered().rows.dom().contains(2));
        assert(recovered().rows[2].component.provisions.contains(false));
        assert(p::registered(i::small_view(),recovered(),2));
        assert((i::small_view().registry)(recovered())[2].component.provisions.contains(false));
    }
}

/// Any relation that calls this real inverse a recovery cannot also preserve
/// all strict Child domains. Strengthening table equality with control fields
/// therefore does not repair the original single-relation witness.
pub proof fn no_single_recovery_and_admission_relation(relation:spec_fn(i::SmallState,i::SmallState)->bool)
    requires relation(recovered(),i::before()),
        forall|a:i::SmallState,b:i::SmallState| #[trigger] relation(a,b)
            ==> child(a,0,3).is_some()==child(b,0,3).is_some(),
    ensures false,
{
    recovery_changes_admission();
}

pub open spec fn port(key:bool)->Port {Port{key:if key {1}else{0},realm:0}}

/// Only the observations needed for this registration decision are related.
/// Other ports, table values, iterator bodies and phases are not identified.
pub open spec fn registration_matches(kernel:&Kernel,a:i::SmallState)->bool {
    &&& kernel.paper().fibers.dom()==a.rows.dom()
    &&& forall|n:usize| a.rows.dom().contains(n) ==>
        kernel.paper().fibers[n].provisions.contains(port(false))==a.rows[n].component.provisions.contains(false)
}

pub proof fn kernel_domain(kernel:&Kernel,a:i::SmallState,parent:usize,name:usize)
    requires kernel.wf(),kernel.next_id()<usize::MAX,registration_matches(kernel,a),
        !a.rows.dom().contains(name),
    ensures kernel.insert_enabled(Some(parent),seq![port(true)],seq![port(false)])==child(a,parent,name).is_some(),
{
    exact_domain(a,parent,name);
    let deps=seq![port(true)];let provisions=seq![port(false)];
    kernel.paper_insert_domain(Some(parent),deps,provisions);
    let reserved_ports=ISet::new(|p:Port|provisions.contains(p));
    assert forall|p:Port| provisions.contains(p)==(p==port(false)) by {
        if provisions.contains(p) {
            let j=choose|j:int| 0<=j<provisions.len() && provisions[j]==p;
            assert(j==0);
        } else if p==port(false) {assert(provisions[0]==p);}
    }
    assert(reserved_ports =~= ISet::empty().insert(port(false)));
    assert(r::insertion_domain(kernel.paper(),Some(parent),reserved_ports)
        == i::enabled(i::small_view(),a,parent,name,i::child_component())) by {
        if r::insertion_domain(kernel.paper(),Some(parent),reserved_ports) {
            assert forall|n:usize| p::registered(i::small_view(),a,n) implies
                i::child_component().provisions.disjoint((i::small_view().registry)(a)[n].component.provisions) by {
                assert(r::registered(kernel.paper(),n));
                assert(!kernel.paper().fibers[n].provisions.contains(port(false)));
            }
        }
        if i::enabled(i::small_view(),a,parent,name,i::child_component()) {
            assert forall|n:usize,p:Port| r::registered(kernel.paper(),n)
                && kernel.paper().fibers[n].provisions.contains(p) implies !reserved_ports.contains(p) by {
                assert(a.rows.dom().contains(n));
                assert(p::registered(i::small_view(),a,n));
                assert((i::small_view().registry)(a)[n]==i::row_view(a.rows[n]));
                assert(i::child_component().provisions.disjoint(a.rows[n].component.provisions));
                if reserved_ports.contains(p) {assert(p==port(false));}
            }
        }
    }
}

/// An executable review client of the production checker. Ghost arguments are
/// erased; they establish a correspondence, never supply a runtime answer.
pub fn check_instantiation(kernel:&Kernel,parent:usize,Ghost(a):Ghost<i::SmallState>,Ghost(name):Ghost<usize>)
    ->(out:Result<(),Error>)
    requires kernel.wf(),kernel.next_id()<usize::MAX,registration_matches(kernel,a),
        !a.rows.dom().contains(name),
    ensures out.is_ok()==child(a,parent,name).is_some(),
{
    let dependencies=vec![Port{key:1,realm:0}];
    let provisions=vec![Port{key:0,realm:0}];
    proof {
        assert(dependencies@ =~= seq![port(true)]);
        assert(provisions@ =~= seq![port(false)]);
        kernel_domain(kernel,a,parent,name);
    }
    kernel.check_insert(Some(parent),dependencies.as_slice(),provisions.as_slice())
}

/// Construct the registration relation from real calls, without a caller-
/// supplied Kernel invariant or representation premise. The native allocator
/// chooses reservation 1; name 2 stays fresh in both compared checks.
pub fn exercise_domain_gap()->(out:(Result<(),Error>,Result<(),Error>))
    ensures out.0==Ok(()),out.1.is_err(),
{
    let mut kernel=Kernel::new();
    let p=vec![Port{key:1,realm:0}];
    let ghost root_ports=p@;
    let parent=kernel.insert(None,Vec::new(),p).unwrap();
    proof {
        assert(parent==0);
        assert(kernel.paper().fibers.dom() =~= i::before().rows.dom());
        assert forall|n:usize| i::before().rows.dom().contains(n) implies
            kernel.paper().fibers[n].provisions.contains(port(false))==i::before().rows[n].component.provisions.contains(false) by {
            assert(n==0);
            assert(!root_ports.contains(port(false))) by {
                if root_ports.contains(port(false)) {let j=choose|j:int| 0<=j<root_ports.len() && root_ports[j]==port(false);assert(j==0);}
            }
        }
        assert(registration_matches(&kernel,i::before()));
    }
    proof {equal_observations_different_domains(ISet::full());}
    let first=check_instantiation(&kernel,parent,Ghost(i::before()),Ghost(2usize));
    proof {
        assert(parent==0);
        assert(child(i::before(),parent,2usize).is_some());
        assert(first.is_ok());
        assert(first.unwrap()==());
        assert(first==Ok(()));
    }
    let d=vec![Port{key:1,realm:0}];
    let p=vec![Port{key:0,realm:0}];
    proof {kernel_domain(&kernel,i::before(),0,2);exact_domain(i::before(),0,2);}
    let ghost prior=kernel.paper();
    let ghost reservation_ports=p@;
    let _reservation=kernel.insert(Some(parent),d,p).unwrap();
    proof {
        assert(_reservation==1);
        assert(kernel.paper().fibers.dom() =~= reserved().rows.dom());
        assert forall|n:usize| reserved().rows.dom().contains(n) implies
            kernel.paper().fibers[n].provisions.contains(port(false))==reserved().rows[n].component.provisions.contains(false) by {
            if n==0 {assert(kernel.paper().fibers[n]==prior.fibers[n]);}
            else {assert(n==1);assert(reservation_ports[0]==port(false));assert(reservation_ports.contains(port(false)));}
        }
        assert(registration_matches(&kernel,reserved()));
        equal_observations_different_domains(ISet::full());
    }
    let second=check_instantiation(&kernel,parent,Ghost(reserved()),Ghost(2usize));
    (first,second)
}

} // verus!
