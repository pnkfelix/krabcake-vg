use alloc::vec;
use alloc::vec::Vec;

use crate::{vg_addr, COUNTER, CTX, STACKS};

#[derive(Copy, Clone, PartialEq, Eq)]
pub struct Tag(pub u64);

impl Tag {
    pub fn next(self) -> Tag {
        Tag(self.0 + 1)
    }
}

#[derive(Copy, Clone, PartialEq, Eq)]
pub enum Item {
    Unique(Tag),
}

impl Item {
    pub fn num(&self) -> u64 {
        match *self {
            Item::Unique(Tag(val)) => val,
        }
    }
}

pub struct Stack {
    pub addr: vg_addr,
    // A unique ID, used in lieu of the address when printing
    // Should only be used when opted into with `--normalize-output`
    pub id: u64,
    pub items: Vec<Item>,
}

impl Stack {
    pub fn dbg_id(&self) -> u64 {
        unsafe {
            if CTX.normalize_output {
                self.id
            } else {
                self.addr
            }
        }
    }
}

pub struct Stacks(pub Vec<Stack>);

impl Stacks {
    // Add a new stack and return its index
    fn add_new_stack(&mut self, addr: vg_addr, items: Vec<Item>) -> usize {
        let id = self.next_id();
        let stack = Stack { addr, id, items };
        self.0.push(stack);
        self.0.len() - 1
    }

    /// Pushes an address into a new or existing stack, returning the index of that stack
    pub fn push(&mut self, addr: vg_addr) -> usize {
        unsafe {
            for (idx, stack) in &mut self.0.iter_mut().enumerate() {
                if stack.addr == addr {
                    stack.items.push(Item::Unique(COUNTER));
                    return idx;
                }
            }

            let items = vec![Item::Unique(COUNTER)];
            self.add_new_stack(addr, items)
        }
    }

    // Get the next ID (currently, it is just monotonically increasing)
    fn next_id(&self) -> u64 {
        self.0.last().map(|stack| stack.id + 1).unwrap_or_default()
    }

    // To reserve each dbg id, add an empty `Vec` into Stacks
    // FIXME: Optimize this in the future
    fn reserve_dbg_id(&mut self, addr: vg_addr) -> u64 {
        let id = self.next_id();
        let stack = Stack { addr, id, items: Vec::new() };
        self.0.push(stack);
        id
    }

    pub fn if_addr_has_stack_then<T>(
        &mut self,
        addr: vg_addr,
        process_stack: impl FnOnce(&mut Stack) -> T,
    ) -> Option<T> {
        for stack in &mut self.0 {
            if stack.addr == addr {
                return Some(process_stack(stack));
            }
        }
        None
    }

    pub fn get_stack_dbg_id_or_assign(&mut self, addr: vg_addr) -> u64 {
        unsafe {
            if CTX.normalize_output {
                self.if_addr_has_stack_then(addr, |stack| stack.dbg_id())
                    .unwrap_or_else(|| self.reserve_dbg_id(addr))
            } else {
                addr
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use alloc::vec;

    use crate::Context;

    use super::*;

    const STARTING_DBG_ID: u64 = 8080;

    // Utility to create a `Stacks` with one item, with an arbitrary ID.
    // Just using this so that the IDs don't align with the indices, otherwise
    // the assertions become confusing to read.
    fn new_stacks(addr: vg_addr) -> Stacks {
        unsafe {
            let items = vec![Item::Unique(COUNTER)];
            let stack = Stack { addr, id: STARTING_DBG_ID, items };
            Stacks(vec![stack])
        }
    }

    #[test]
    fn push_to_stack() {
        let mut stacks = new_stacks(0xdeadbeef);
        assert_eq!(1, stacks.push(101));
        assert_eq!(2, stacks.push(102));
        assert_eq!(3, stacks.push(103));
    }

    #[test]
    fn get_dbg_ids() {
        unsafe {
            CTX = Context { normalize_output: false };
        }
        let mut stacks = new_stacks(0xdeadbeef);
        stacks.push(101);
        stacks.push(102);
        stacks.push(103);
        // We always just get the addr back
        assert_eq!(101, stacks.get_stack_dbg_id_or_assign(101));
        assert_eq!(102, stacks.get_stack_dbg_id_or_assign(102));
        assert_eq!(103, stacks.get_stack_dbg_id_or_assign(103));
        assert_eq!(104, stacks.get_stack_dbg_id_or_assign(104));
        assert_eq!(105, stacks.get_stack_dbg_id_or_assign(105));
        assert_eq!(4, stacks.0.len());
    }

    #[test]
    fn get_dbg_ids_normalized() {
        unsafe {
            CTX = Context { normalize_output: true };
        }
        let mut stacks = new_stacks(0xdeadbeef);
        stacks.push(101);
        stacks.push(102);
        stacks.push(103);
        // Here we actually use the `id` field in whatever is the last Stack
        assert_eq!(STARTING_DBG_ID + 1, stacks.get_stack_dbg_id_or_assign(101));
        assert_eq!(STARTING_DBG_ID + 2, stacks.get_stack_dbg_id_or_assign(102));
        assert_eq!(STARTING_DBG_ID + 3, stacks.get_stack_dbg_id_or_assign(103));
        assert_eq!(STARTING_DBG_ID + 4, stacks.get_stack_dbg_id_or_assign(104));
        assert_eq!(STARTING_DBG_ID + 5, stacks.get_stack_dbg_id_or_assign(105));
        // This is because currently, the above 2 lines each add a new empty `Vec` into Stacks
        // (Because `normalize_output` is true)
        assert_eq!(6, stacks.0.len());
        // (Should be the 4th item
        // Before this line, the `Vec` was already there, but until now, it was empty
        assert_eq!(4, stacks.push(104));
        // Same index because we just add to existing Stack
        assert_eq!(4, stacks.push(104));
        // Adds at the end
        assert_eq!(6, stacks.push(106));
        assert_eq!(STARTING_DBG_ID + 6, stacks.get_stack_dbg_id_or_assign(106));
    }
}
