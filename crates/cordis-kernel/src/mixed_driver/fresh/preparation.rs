//! Exact input domains for the Insert/Begin/Step preparation command profile.
//!
//! Other commands remain accepted by the dispatcher; this profile does not
//! characterize their success or failure. All predicates are proof-only.
#[cfg(verus_keep_ghost)]
use super::Command;
use super::FreshDriver;
use vstd::prelude::*;

verus! {

/// Commands whose acceptance is connected to an independent input predicate.
pub open spec fn preparation_command(command:Command)->bool {
    matches!(command,Command::Insert {..} | Command::Begin {..} | Command::Step {..})
}

impl FreshDriver {
    /// Evaluate in the current machine, immediately before the selected call.
    /// A false result outside `preparation_command` is not a rejection claim.
    pub open spec fn preparation_enabled(&self,command:Command)->bool {
        match command {
            Command::Insert {parent,blueprint}=>self.insertion_enabled(parent,blueprint),
            Command::Begin {actor}=>self.begin_enabled(actor),
            Command::Step {actor}=>self.step_enabled(actor),
            _=>false,
        }
    }
    pub proof fn same_preparation_domain(&self,other:&Self,command:Command)
        requires self.wf(),other.wf(),self.same(other),
        ensures self.preparation_enabled(command)==other.preparation_enabled(command),
    {
        match command {
            Command::Insert {parent,blueprint}=>self.same_start_domains(other,parent,blueprint,0),
            Command::Begin {actor}=>self.same_start_domains(other,None,0,actor),
            Command::Step {actor}=>self.same_step_domain(other,actor),
            _=>{},
        }
    }
}

}
