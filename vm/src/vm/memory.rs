use types::*;
use program::Program;
use errors::MemoryError;

pub type Result<T> = ::std::result::Result<T, MemoryError>;

#[derive(Debug)]
pub struct Memory {
    size: usize,
    spaces: Vec<(usize, usize)>,
    mem: Box<[StackVal]>,
    free_size: usize,
}

impl Memory {
    pub fn invariant(&self) -> bool {
        let are_blocks_valid = self.spaces
            .iter()
            .all(|&(a, b)| a < b && b <= self.size);

        let are_blocks_ordered_and_disjoint = self.spaces
            .iter()
            .zip(self.spaces.iter().skip(1))
            .all(|(&(_, p), &(n, _))| p < n);

        let is_free_size_consistent = self.free_size ==
                                      self.spaces.iter().fold(0, |sum, &(a, b)| sum + (b - a));

        are_blocks_valid && are_blocks_ordered_and_disjoint && is_free_size_consistent
    }

    pub fn new(mem_size: usize, prog: &Program) -> Result<Memory> {
        let mut mem_block = vec![0; mem_size].into_boxed_slice();

        let mem = Memory {
            size: mem_size,
            spaces: vec![(0, mem_size)],
            mem: mem_block,
            free_size: mem_size,
        };

        assert!(mem.invariant());
        Ok(mem)
    }

    pub fn alloc(&mut self, size: usize) -> Result<usize> {
        match self.spaces
                  .iter()
                  .enumerate()
                  .find(|&(_, &(a, b))| b - a >= size) {
            Some((n, &(a, b))) => {
                if b - a == size {
                    self.spaces.remove(n);
                } else {
                    self.spaces[n] = (a + size, b);
                }
                self.free_size -= size;
                assert!(self.invariant());
                Ok(a)
            }
            None => Err(MemoryError::OutOfMemory),
        }
    }

    pub fn free(&mut self, start: usize, length: usize) {

        // A zero-size free does nothing
        if length == 0 {
            return;
        }

        // check that this space doesn't overlap with existing free spaces
        let double_free = self.spaces
            .iter()
            .any(|&(lower, upper)| start < upper && start + length > lower);

        if start + length > self.size || double_free {
            panic!()
        }

        // Find the free slices on either side, if they exist.
        // We use the final map to dereference (copy) the values
        // so that self.spaces doesnt remain 'borrowed'

        let prev = self.spaces
            .iter()  // Iter<&(usize, usize)>
            .enumerate() // Iter<(usize, &(usize, usize))>
            .take_while(|&(_,&(_, upper))| upper <= start)
            .last()  // Option<(usize, &(usize, usize))>
            .map(|(n, bounds)| (n, *bounds)); // Option<(usize, (usize, usize))>

        let next = self.spaces
            .iter()  // Iter<&(usize, usize)>
            .enumerate() // Iter<(usize, &(usize, usize))>
            .find(|&(_, &(lower, _))| lower == start + length) // Option<(usize, &(usize, usize))>
            .map(|(n, bounds)| (n, *bounds)); // Option<(usize, (usize, usize))>

        match (prev, next) {
            (None, None) => self.spaces.insert(0, (start, start + length)),
            (None, Some((n_n, (_, n_end)))) => self.spaces[n_n] = (start, n_end),
            (Some((p_pos, (p_start, p_end))), None) => {
                if p_end == start {
                    self.spaces[p_pos] = (p_start, p_end + length)
                } else {
                    self.spaces.insert(p_pos + 1, (start, start + length))
                }
            }
            (Some((p_n, (p_start, p_end))), Some((n_n, (_, n_end)))) => {
                if p_end == start {
                    self.spaces[p_n] = (p_start, n_end);
                    self.spaces.remove(n_n);
                } else {
                    self.spaces.insert(n_n, (start, start + length));
                }
            }
        }

        self.free_size += length;
        assert!(self.invariant());
    }

    pub fn get(&self, pos: usize) -> Result<StackVal> {
        self.mem
            .get(pos)
            .cloned()
            .ok_or(MemoryError::OutOfBoundsAccess)
    }

    pub fn put(&mut self, pos: usize, v: StackVal) -> Result<()> {
        if pos < self.size {
            self.mem[pos] = v;
            Ok(())
        } else {
            Err(MemoryError::OutOfBoundsAccess)
        }
    }
}
