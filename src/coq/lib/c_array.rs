use ocaml::de::{Array};
use std::borrow::{Borrow};
use std::sync::{Arc};

impl<T> Array<T> {
    /// If none of the elements is changed by f we return ar itself.
    /// The while loop looks for the first such an element.
    /// If found, we break here and the new array is produced,
    /// but f is not re-applied to elements that are already checked
    ///
    /// Different from OCaml in that it takes a PER (E) instead of always using pointer equality,
    /// since things in the array aren't necessarily boxed, and it doesn't require the map to
    /// produce element of exactly type T, only of type U (as long as you can get a borrowed T back
    /// out of U).  This allows you to, e.g., have F go from &T to Cow<T>, and then have
    /// equivalence as pointer equality so you can determine whether it's really the same
    /// reference.  Note that you also must be able to go from a U to a T.
    ///
    /// Also differs from the OCaml implementation because it allows for an Err option for its map
    /// elements.  If the thing you're mapping can't actually return an error, you can pass ! in
    /// its stead.
    /// ! in its stead.
    pub fn smart_map<U, E, F, Equiv>(&self, mut f: F, eq: Equiv) -> Result<Array<T>, E>
        where
            T: Clone,
            U: Borrow<T>,
            F: FnMut(&T) -> Result<U, E>,
            U: Into<T>,
            Equiv: Fn(&T, &T) -> bool,
    {
        // Don't even bother allocating until we detect a difference.
        // NOTE: This might not be a useful microoptimization in Rust...
        // in fact, it might not be an optimization at all!
        for (i, v) in (&self).iter().enumerate() {
            let v_ = f(v)?;
            if !eq(v, v_.borrow()) {
                // The array had at least one new element, so we do have to allocate.
                let mut vec = Vec::with_capacity(self.len());
                // The below is safe because i < self.len().
                vec.extend_from_slice(&self[..i]);
                vec.push(v_.into());
                // Observe that unlike the OCaml implementation, we don't repeat the check
                // for whether we can reuse v in these cases, because either way we have to
                // perform a Clone (since we don't actually own T in the first place).
                // The below is safe because i + 1 ≤ self.len()
                for v in &self[i + 1..] {
                    vec.push(f(v)?.into());
                }
                return Ok(Array(Arc::new(vec)));
            }
        }
        // There were no changes, so just clone this Arc.  We could also use a Cow if we didn't
        // always have an Arc around anyway...
        return Ok(self.clone());
    }
}
