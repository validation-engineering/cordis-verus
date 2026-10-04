//! Executable cleanup-token stack, shared by Verus verification and the host.
//!
//! Tokens identify host-owned callbacks. This module proves the exact token
//! order and one-entry removal per pop; it does not prove callback inverses.
use vstd::prelude::*;

verus! {

pub struct EffectStack {
    tokens: Vec<usize>,
}

impl Default for EffectStack {
    fn default() -> Self { Self::new() }
}

impl EffectStack {
    pub closed spec fn view(&self) -> Seq<usize> {
        self.tokens@
    }

    pub fn new() -> (stack: Self)
        ensures stack.view() == Seq::<usize>::empty(),
    {
        Self { tokens: Vec::new() }
    }

    /// Register one cleanup token after every previously registered token.
    /// Duplicate tokens are allowed: each registration is a distinct entry.
    pub fn push(&mut self, token: usize)
        ensures final(self).view() == old(self).view().push(token),
            final(self).view().len() == old(self).view().len() + 1,
    {
        self.tokens.push(token);
    }

    /// Remove exactly the last registered entry, preserving the entire prefix.
    /// Empty stacks remain empty and return None.
    pub fn pop(&mut self) -> (token: Option<usize>)
        ensures
            old(self).view().len() == 0 ==> token.is_none()
                && final(self).view() == old(self).view(),
            old(self).view().len() > 0 ==> token == Some(old(self).view().last())
                && final(self).view() == old(self).view().drop_last()
                && final(self).view().len() + 1 == old(self).view().len(),
    {
        self.tokens.pop()
    }

    pub fn len(&self) -> (len: usize)
        ensures len == self.view().len(),
    {
        self.tokens.len()
    }

    pub fn is_empty(&self) -> (empty: bool)
        ensures empty == (self.view().len() == 0),
    {
        self.tokens.len() == 0
    }
}

} // verus!
