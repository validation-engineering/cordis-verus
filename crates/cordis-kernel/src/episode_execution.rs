//! Erased observations of the actual work owner and cleanup queue. Payload
//! meanings remain in their typed owners; ticket identity and occupancy do not.
use crate::action_ledger::ActionTicket;
use crate::cleanup_journal::{RestoreOutcome, RestoreTicket};
use crate::setup_work::{RootStatus, WorkKind, WorkTicket};
use crate::Binding;
use vstd::prelude::*;

verus! {
pub struct WorkState {
    pub domain:u64,pub origin:Option<ActionTicket>,pub next:u64,
    pub root:RootStatus,pub failed:bool,pub accepting:bool,pub closed:bool,
    pub children:Seq<WorkTicket>,pub groups:Seq<WorkTicket>,pub issued:Map<u64,WorkKind>,
}
pub enum WorkChange {
    Withdraw,IssueRoot,StartRoot {ticket:WorkTicket},CancelRoot {ticket:WorkTicket},
    CompleteRoot {ticket:WorkTicket,failed:bool},FailRoot {ticket:WorkTicket},Abandon,
    Enqueue {kind:WorkKind},Take {kind:WorkKind},Complete {ticket:WorkTicket},Seal,
}
pub open spec fn root_ticket(state:WorkState,ticket:WorkTicket)->bool {
    ticket.domain()==state.domain && ticket.id()==0 && ticket.kind()==WorkKind::Root
}
pub open spec fn root_open(state:WorkState,ticket:WorkTicket)->bool {
    root_ticket(state,ticket) && (state.root==RootStatus::Queued || state.root==RootStatus::Running)
}
pub open spec fn work_step(a:WorkState,b:WorkState,change:WorkChange)->bool {
    match change {
        WorkChange::Withdraw=>b==(WorkState {accepting:false,..a}),
        WorkChange::IssueRoot=>a.root==RootStatus::Unissued && !a.closed
            && b==(WorkState {root:RootStatus::Queued,..a}),
        WorkChange::StartRoot {ticket}=>root_open(a,ticket) && b==(WorkState {root:RootStatus::Running,..a}),
        WorkChange::CancelRoot {ticket}=>root_ticket(a,ticket) && a.root==RootStatus::Queued && !a.accepting
            && b==(WorkState {root:RootStatus::Settled,failed:true,..a}),
        WorkChange::CompleteRoot {ticket,failed}=>root_open(a,ticket)
            && b==(WorkState {root:RootStatus::Settled,failed,..a}),
        WorkChange::FailRoot {ticket}=>root_open(a,ticket)
            && b==(WorkState {root:RootStatus::Settled,failed:true,..a}),
        WorkChange::Abandon=>b==if a.root==RootStatus::Settled {WorkState {accepting:false,..a}}
            else {WorkState {accepting:false,root:RootStatus::Abandoned,failed:true,..a}},
        WorkChange::Enqueue {kind}=>a.accepting && a.next<u64::MAX && match kind {
            WorkKind::Child=>b.next==a.next+1 && b.children.len()==a.children.len()+1
                && b.children.drop_last()==a.children && b.children.last().domain()==a.domain
                && b.children.last().id()==a.next && b.children.last().kind()==kind
                && b==(WorkState {next:b.next,children:b.children,..a}),
            WorkKind::Group=>b.next==a.next+1 && b.groups.len()==a.groups.len()+1
                && b.groups.drop_last()==a.groups && b.groups.last().domain()==a.domain
                && b.groups.last().id()==a.next && b.groups.last().kind()==kind
                && b==(WorkState {next:b.next,groups:b.groups,..a}),
            _=>false,
        },
        WorkChange::Take {kind}=>match kind {
            WorkKind::Child=>a.children.len()>0 && !a.issued.contains_key(a.children.first().id())
                && b==(WorkState {children:a.children.skip(1),issued:a.issued.insert(a.children.first().id(),kind),..a}),
            WorkKind::Group=>a.groups.len()>0 && !a.issued.contains_key(a.groups.first().id())
                && b==(WorkState {groups:a.groups.skip(1),issued:a.issued.insert(a.groups.first().id(),kind),..a}),
            _=>false,
        },
        WorkChange::Complete {ticket}=>ticket.domain()==a.domain && a.issued.contains_key(ticket.id())
            && a.issued[ticket.id()]==ticket.kind() && b==(WorkState {issued:a.issued.remove(ticket.id()),..a}),
        // Queue drain is established by SetupWork::seal's typed cleanup owner.
        WorkChange::Seal=>a.root==RootStatus::Settled && a.children.len()==0 && a.groups.len()==0 && a.issued.len()==0
            && b==(WorkState {accepting:false,closed:true,..a}),
    }
}

pub struct CleanupState {
    pub domain:u64,pub next:u64,pub selected:Option<RestoreTicket>,pub failed:bool,
    pub committed:Seq<Binding>,pub waiting:Seq<usize>,pub pending:bool,pub settled:bool,pub cancelled:bool,
    pub occupied:Seq<bool>,pub issued:bool,
}
pub enum CleanupChange {
    Register,Land,Pop {ticket:RestoreTicket},Complete {ticket:RestoreTicket,outcome:RestoreOutcome,retained:bool},
    Retry {ticket:RestoreTicket},Admit {matches:bool},End,Cancel,
}
pub open spec fn cleanup_step(a:CleanupState,b:CleanupState,change:CleanupChange)->bool {
    match change {
        CleanupChange::Register=>b==(CleanupState {occupied:a.occupied.push(true),waiting:a.waiting.push(a.occupied.len() as usize),..a}),
        CleanupChange::Land=>a.pending && b==(CleanupState {occupied:a.occupied.push(true),
            waiting:a.waiting.push(a.occupied.len() as usize),pending:false,settled:a.cancelled,..a}),
        CleanupChange::Pop {ticket}=>!a.issued && !a.failed && ticket.token<a.occupied.len() && a.occupied[ticket.token as int]
            && if a.selected.is_some() {ticket==a.selected.unwrap()
                && b==(CleanupState {occupied:a.occupied.update(ticket.token as int,false),issued:true,..a})}
            else {a.settled && !a.pending && a.waiting.len()>0 && a.next<u64::MAX
                && ticket==(RestoreTicket {domain:a.domain,attempt:a.next,token:a.waiting.last()})
                && b==(CleanupState {next:(a.next+1) as u64,selected:Some(ticket),waiting:a.waiting.drop_last(),
                    occupied:a.occupied.update(ticket.token as int,false),issued:true,..a})},
        CleanupChange::Complete {ticket,outcome,retained}=>a.issued && !a.failed && a.selected==Some(ticket)
            && (outcome==RestoreOutcome::Failed || !retained)
            && b==(CleanupState {issued:false,occupied:a.occupied.update(ticket.token as int,retained),
                failed:outcome==RestoreOutcome::Failed,selected:if outcome==RestoreOutcome::Failed {Some(ticket)} else {None},..a}),
        CleanupChange::Retry {ticket}=>a.failed && a.selected.is_some() && a.next<u64::MAX && !a.issued
            && a.selected.unwrap().token<a.occupied.len() && a.occupied[a.selected.unwrap().token as int]
            && ticket==(RestoreTicket {domain:a.domain,attempt:a.next,token:a.selected.unwrap().token})
            && ticket.attempt>a.selected.unwrap().attempt
            && b==(CleanupState {next:(a.next+1) as u64,selected:Some(ticket),failed:false,..a}),
        CleanupChange::Admit {matches}=>{
            let poll=a.pending || (!a.settled && !a.cancelled && matches);
            b==(CleanupState {pending:poll,settled:!poll,cancelled:a.cancelled || !matches,..a})
        },
        CleanupChange::End=>b==if a.pending {CleanupState {pending:false,settled:true,..a}} else {a},
        CleanupChange::Cancel=>b==(CleanupState {cancelled:true,settled:!a.pending,..a}),
    }
}
}

#[path = "cleanup_interval.rs"]
pub mod interval;
