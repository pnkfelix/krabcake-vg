use alloc::{string::String, vec::Vec};
use core::{ffi::c_char, fmt, fmt::Write, writeln};

use crate::{vgPlain_dmsg, vg_addr, vg_long, vg_ulong, VgPlainUmsgWriter, COUNTER, CTX, STACKS};

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct Counter(u64);

impl Counter {
    pub const fn new() -> Counter {
        Counter(0)
    }

    pub fn next(self) -> Counter {
        Counter(self.0 + 1)
    }

    pub fn get(self) -> u64 {
        // FIXME: Replace with assert when panics have stacktraces
        if self.0 == 0 {
            let mut w = VgPlainUmsgWriter;
            writeln!(
                w,
                "Counter::get - Attempted to access counter with value of zero! This is a bug."
            );
            panic!("Counter::get - Attempted to access counter with value of zero! This is a bug.");
        }
        self.0
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Tag {
    Counter(Counter),
    Bottom,
}

impl fmt::Display for Tag {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Tag::Counter(c) => write!(f, "{}", c.0),
            Tag::Bottom => write!(f, "bot"),
        }
    }
}

impl Tag {
    pub fn s(&self) -> String {
        alloc::format!("{self}\0")
    }

    pub fn to_shadow_state(self) -> vg_ulong {
        let res = match self {
            Tag::Counter(ctr) => (ctr.0 << 4) as vg_ulong,
            Tag::Bottom => 1,
        };
        // let mut w = VgPlainUmsgWriter;
        // core::writeln!(w, "to_shadow_state: {self:?} -> {res:#0x}, {res:#0b}");
        res
    }

    pub fn from_shadow_state(ctr: vg_ulong) -> Tag {
        let res = if ctr == 1 {
            Tag::Bottom
        } else {
            Tag::Counter(Counter(ctr >> 4))
        };
        // let mut w = VgPlainUmsgWriter;
        // core::writeln!(w, "from_shadow_state: {ctr:#0x}, {ctr:#0b} -> {res:?}");
        res
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Item {
    Unique(Tag),
    SharedRW,
}
impl Item {
    pub(crate) fn from_tag(tag: Tag) -> Item {
        match tag {
            Tag::Counter(ctr) => Item::Unique(tag),
            Tag::Bottom => Item::SharedRW,
        }
    }
}

impl fmt::Display for Item {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            // FIXME: we probably can just print the number without
            // including the "Unique(...)" here. (What will be best
            // for our customers to understand?)
            Item::Unique(t) => write!(f, "Unique({})", t),
            Item::SharedRW => write!(f, "SharedRW"),
        }
    }
}

#[derive(Debug)]
pub struct Stack {
    pub addr: vg_addr,
    // A unique ID, used in lieu of the address when printing
    // Should only be used when opted into with `--normalize-output`
    pub id: u64,
    pub items: Vec<Item>,
}

impl fmt::Display for Stack {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[")?;
        let mut seen_any = false;
        for item in &self.items {
            if seen_any {
                write!(f, ", ")?;
            }
            write!(f, "{}", item)?;
            seen_any = true;
        }
        write!(f, "]")
    }
}

impl Stack {
    pub fn dbg_id(&self) -> u64 {
        unsafe {
            if CTX.normalize_output {
                self.id
            } else {
                self.addr as u64
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
                    stack.items.push(Item::Unique(Tag::Counter(COUNTER)));
                    return idx;
                }
            }

            let mut items = Vec::new();
            items.push(Item::Unique(Tag::Counter(COUNTER)));
            self.add_new_stack(addr, items)
        }
    }

    // Get the next ID (currently, it's just monotonically increasing)
    fn next_id(&self) -> u64 {
        const INIT_NORM: u64 = 0x10000000;
        self.0.last().map(|stack| stack.id + 1).unwrap_or(INIT_NORM)
    }

    // To reserve each dbg id, add an empty `Vec` into Stacks
    // FIXME: Optimize this in the future
    fn reserve_dbg_id(&mut self, addr: vg_addr) -> u64 {
        let id = self.next_id();
        let stack = Stack {
            addr,
            id,
            items: Vec::new(),
        };
        self.0.push(stack);
        id
    }

    pub fn if_addr_has_stack_then<T>(
        &mut self,
        addr: vg_addr,
        process_stack: impl FnOnce(&mut Stack) -> T,
    ) -> Option<T> {
        for mut stack in &mut self.0 {
            if stack.addr == addr {
                return Some(process_stack(&mut stack));
            }
        }
        None
    }

    pub fn assume_addr_has_stack_then<T>(
        &mut self,
        addr: vg_addr,
        process_stack: impl FnOnce(&mut Stack) -> T,
    ) -> T {
        for mut stack in &mut self.0 {
            if stack.addr == addr {
                return process_stack(&mut stack);
            }
        }
        panic!("Expected addr {addr:x} to have a Stack but it does not!");
    }

    pub fn get_stack_dbg_id_or_assign(&mut self, addr: vg_addr) -> u64 {
        unsafe {
            if CTX.normalize_output {
                self.if_addr_has_stack_then(addr, |stack| stack.dbg_id())
                    .unwrap_or_else(|| self.reserve_dbg_id(addr))
            } else {
                addr as u64
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
            let mut items = Vec::new();
            items.push(Item::Unique(Tag::Counter(COUNTER)));
            let stack = Stack {
                addr,
                id: STARTING_DBG_ID,
                items,
            };
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
            CTX = Context {
                normalize_output: false,
            };
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
            CTX = Context {
                normalize_output: true,
            };
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
