//! Validation/Verification logic for rkyv

use std::cmp::Ordering;

use crate::{
    rkyv::{ArchiveError::*, ArchivedPrefixMap},
    table::K,
    Prefix,
};
use rkyv::{
    bytecheck::Verify,
    rancor::{Fallible, Source},
    Archive,
};

unsafe impl<P, T, C> Verify<C> for ArchivedPrefixMap<P, T>
where
    P: Prefix,
    T: Archive,
    C: Fallible + ?Sized,
    C::Error: Source,
{
    fn verify(&self, _context: &mut C) -> Result<(), C::Error> {
        if self.nodes.len() > 1 << 32 {
            Err(C::Error::new(NodeIndexOverflow))?
        }
        if self.data.len() > 1 << 32 {
            Err(C::Error::new(DataIndexOverflow))?
        }
        if self.nodes.is_empty() {
            Err(C::Error::new(MissingRootNode))?
        }

        let mut child_cursor = 1;
        let mut data_cursor = 0;
        let mut cur_depth = 0;
        let mut next_depth = 1u32;

        let max_depth = P::num_bits();

        for i in 0..self.nodes.len() {
            let node = &self.nodes[i];
            // check non-empty (allow empty roots though)
            if i > 0 && node.data_bitmap == 0 && node.child_bitmap == 0 {
                Err(C::Error::new(ContainsEmptyNode))?
            }

            // check the depth count
            if i as u32 == next_depth {
                cur_depth += K;
                next_depth = node.children_idx.to_native();
                if cur_depth > max_depth {
                    Err(C::Error::new(DepthExceedsPrefixRepr))?
                }
            }

            // check max depth
            let max_allowed = u32::min(K - 1, max_depth - cur_depth);
            let denied_mask = DENIED_DEPTH_MASK[max_allowed as usize];
            if node.data_bitmap & denied_mask != 0 {
                Err(C::Error::new(DepthExceedsPrefixRepr))?
            }

            if node.data_idx != data_cursor {
                Err(C::Error::new(DataListInconsistent))?
            }
            data_cursor += node.data_bitmap.to_native().count_ones();
            if node.children_idx != child_cursor {
                Err(C::Error::new(NodeListInconsistent))?
            }
            child_cursor += node.child_bitmap.to_native().count_ones();
        }

        match child_cursor.cmp(&(self.nodes.len() as u32)) {
            Ordering::Less => Err(C::Error::new(NodeListTooShort))?,
            Ordering::Equal => {}
            Ordering::Greater => Err(C::Error::new(NodeListTooLong))?,
        }
        match data_cursor.cmp(&(self.data.len() as u32)) {
            Ordering::Less => Err(C::Error::new(DataListTooShort))?,
            Ordering::Equal => {}
            Ordering::Greater => Err(C::Error::new(DataListTooLong))?,
        }

        Ok(())
    }
}

const DENIED_DEPTH_MASK: [u32; K as usize] = [
    !((1u32 << 1) - 1),  // m = 0: allow bit 0
    !((1u32 << 3) - 1),  // m = 1: allow bits 0..=2
    !((1u32 << 7) - 1),  // m = 2: allow bits 0..=6
    !((1u32 << 15) - 1), // m = 3: allow bits 0..=14
    !((1u32 << 31) - 1), // m = 4: allow bits 0..=30 (bit 31 denied = stray-bit check)
];
