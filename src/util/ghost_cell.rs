use std::cell::{UnsafeCell};
use std::marker::{PhantomData};

/// Unsafe: tread carefully!

/// GhostCell: A Cell with ghost ownership.
///
/// Often, interior mutability in Rust is full of unsatisfying tradeoffs: thread safety,
/// generality of types, runtime overhead (both time and space) or even runtime failure, and so on.
/// Cell::get_mut shows that interior mutability can be made much nicer when you can take advantage
/// Rust's ownership information to avoid these issues, but the trick is unfortunately limited to
/// Cells where you have direct ownership.  Here, we extend this trick to Cells where you have
/// *logical* ownership, using the following techniques:
///
/// - Invariant lifetimes (to generate unforgeable, compile-time unique lifetime tokens).
/// - Higher rank lifetimes (to ensure code is parametric with respect to the chosen token).
/// - Ghost ownership (to allow ownership to be held by the token owner, rather than the value
///   itself).
///
/// The API works as follows: first, you create a ghost owner (within an appropriate scope).  Then,
/// you create cells that reference the ghost owner (they must reference exactly one ghost owner,
/// due to lifetime invariance, and no two ghost owners can be the same, due to lifetime
/// parametricity).  Finally, to access values at a given lifetime and mutability, you must first
/// borrow the owner with the same lifetime and mutability.  As a result, all of Rust's guarantees
/// about ownership and lifetimes flow from the owner to cells owned by the owner.

/// An invariant lifetime--required in order to make sure that a Cell can only belong to a single
/// ghost set.
#[derive(Clone,Copy)]
struct InvariantLifetime<'id>(
    PhantomData<*mut &'id ()>);

impl<'id> InvariantLifetime<'id> {
    #[inline]
    fn new() -> InvariantLifetime<'id> {
        InvariantLifetime(PhantomData)
    }
}

/// A ghost set.
///
/// Once created, a Set can neither be cloned nor copied.
///
/// Note that Set does not need to know which types it is protecting.  The reason for this is that
/// in order to do anything with a Cell<T>, both the owner *and* a reference to the Cell are
/// required.  Since a Cell inherits its trait markers (and other information) from the type of
/// data it is protecting, Set does not need to know about it; it only needs to carry around
/// ownership information about the entire set.  For example, one could create a Cell<'id, Rc<T>>
/// and then send the owning Set<'id> to another thread, but since one cannot actually send the
/// Cell to another thread, it is not possible to observe a race condition in this way.  Similarly,
/// one could not send a reference to a Cell<'id, Cell<T>> to another thread, so it wouldn't be
/// possible to observe races through its owning Set<'id> even if the Set<'id> were borrowed
/// immutably.
///
/// Observe that 'id is totally disjoint from T itself--it is only used as a unique compile-time
/// identifier for a set of Ts, and otherwise has no relationship to T.  This means that one can
/// create sets of Ts where T does not outlive the 'id--since you need a reference to a T *and* the
/// owning set in order to gain access to its interior, this should not cause unsoundness.
pub struct Set<'id> {
    _marker: InvariantLifetime<'id>,
}

/// A ghost cell.
///
/// A ghost cell acts exactly like a T, except that its contents are inaccessible except through
/// its owning Set.
pub struct Cell<'id, T> {
    _marker: InvariantLifetime<'id>,
    value: UnsafeCell<T>,
}

/// Cell<'id, T> implements Send iff T does.  This is safe because in order to access the T
/// mutably within a Cell<T>, you need both a mutable reference to its owning set and an immutable
/// reference to T, and both references must have the same lifetime.
unsafe impl<'id, T> Sync for Cell<'id, T> where T: Sync {}

/// Cell<'id, T> implements Sync iff T does.  This is safe because in order to access the T
/// immutably within a Cell<T>, you need both an immutable reference to its owning set and an
/// immutable reference to T, and both references must have the same lifetime.
unsafe impl<'id, T> Send for Cell<'id, T> where T: Send {}

impl<'id> Set<'id> {
    /// Create a new `Set` with a particular lifetime identifier, `'id`.
    ///
    /// The passed function must be parametric with respect to its lifetime parameter; this
    /// guarantees that 'id is chosen by the scope function, not the user.  Because 'id is
    /// invariant with respect to Set, and can't be chosen by the user to replicate an existing
    /// Set, we know that 'id is unique per function call.
    pub fn new<F, R>(f: F) -> R where F: for <'new_id> FnOnce(Set<'new_id>) -> R {
        // We choose the lifetime; it is definitely unique for each new instance of Set.
        let set = Set {
            _marker: InvariantLifetime::new(),
        };
        // Return the result of running f.  Note that the Set itself can't be returned, because R
        // can't mention the lifetime 'id, so the Set really does only exist within its scope.
        f(set)
    }

    /// Get an immutable reference to the item that lives for as long as the owning set is
    /// immutably borrowed.
    pub fn get<'a, T>(&'a self, item: &'a Cell<'id, T>) -> &'a T {
        unsafe {
            // We know the set and lifetime are both borrowed at 'a, and the set is borrowed
            // immutably; therefore, nobody has a mutable reference to this set.  Therefore, any
            // items in the set that are currently aliased would have been legal to alias at &'a T
            // as well, so we can take out an immutable reference to any of them, as long as we
            // make sure that nobody else can take a mutable reference to any item in the set until
            // we're done.
            &*item.value.get()
        }
    }

    /// Get a mutable reference to the item that lives for as long as the owning set is mutably
    /// borrowed.
    pub fn get_mut<'a, T>(&'a mut self, item: &'a Cell<'id, T>) -> &'a mut T {
        unsafe {
            // We know the set and lifetime are both borrowed at 'a, and the set is borrowed
            // mutably; therefore, nobody else has a mutable reference to this set.  As a result,
            // all items in the set are currently unaliased, so we can take out a mutable referecne
            // to any one of them, as lon as we make sure that nobody else can take a mutable
            // reference to any other item in the set until we're done.
            &mut *item.value.get()
        }
    }
}

impl<'id, T> Cell<'id, T> {
    /// Creates a new cell that belongs to the set at lifetime 'id.  This consumes its value.  From
    /// this point on, the only way to access the inner value is by using a Set with scope 'id.
    /// Since 'id is always chosen parametrically for Sets, and 'id is invariant for both the Cell
    /// and the Set, if one chooses 'id to actually correspond to an existing Set<'id>, that is the
    /// only Set<'id> to which the Cell belongs.  Therefore, there is no way to access the value
    /// through more than one set at a time.
    ///
    /// As with Set itself, note that 'id has no relationship to T--it is only used as a unique
    /// marker.
    ///
    /// A subtle point to make is around Drop.  If T's Drop implementation is run, and T has a
    /// reference to a Set<'id>, it seems that since the invariant that Set<'id> must be accessed
    /// mutably to get a mutable reference to the T inside a Cell<'id, T> is being bypassed, there
    /// could be a soundness bug here.  Fortunately, thanks to dropck, such pathological cases
    /// appear to be ruled out.  For example, this code will not compile:
    ///
    /// ```compile_fail
    /// use util::ghost_cell::{Set, Cell};
    ///
    /// struct Foo<'a, 'id>(&'a Set<'id>,
    ///                         Cell<'id,
    ///                              ::std::cell::Cell<Option<&'a Foo<'a, 'id>>>>)
    ///                              where 'id: 'a;
    ///
    /// impl<'a, 'id> Drop for Foo<'a, 'id> {
    ///     fn drop(&mut self) {
    ///         match self.0.get(&self.1).get() {
    ///             Some(ref foo) => {
    ///                 println!("Oops, have aliasing.");
    ///             },
    ///             None => {
    ///                 println!("Okay")
    ///             }
    ///         }
    ///     }
    /// }
    ///
    /// Set::new(|set| {
    ///     let foo = Foo(&set, Cell::new(::std::cell::Cell::new(None)));
    ///     set.get(&foo.1).set(Some(&foo));
    /// });
    /// ```
    ///
    /// It will compile if the manual Drop implementation is removed, but only pathological Drop
    /// implementations are an issue here.  I believe there are two factors at work: one, in order
    /// to have a reference to a value, the set must outlive the reference.  Two, types must
    /// *strictly* outlive the lifetimes of things they reference if they have a nontrivial Drop
    /// implementation.  As a result, if there is any reference to a `Cell` containing the type
    /// being dropped from within the type being dropped, and it has a nontrivial Drop
    /// implementation, it will not be possible to complete the cycle.  To illustrate more clearly,
    /// this fails, too:
    ///
    /// ```compile_fail
    /// fn foo() {
    ///     struct Foo<'a>(::std::cell::Cell<Option<&'a Foo<'a>>>);
    ///
    ///     impl<'a> Drop for Foo<'a> {
    ///         fn drop(&mut self) {}
    ///     }
    ///
    ///     let foo = Foo(::std::cell::Cell::new(None));
    ///     foo.0.set(Some(&foo));
    /// }
    /// ```
    ///
    /// So any conceivable way to peek at a self-reference within a Drop implementation is probably
    /// covered.
    pub fn new(value: T) -> Self {
        Cell {
            _marker: InvariantLifetime::new(),
            value: UnsafeCell::new(value),
        }
    }

    /// Convenience method to clone the Cell when T is Clone, as long as the set is available.
    pub fn clone(&self, set: &Set<'id>) -> Self where T: Clone {
        Cell::new(set.get(self).clone())
    }
}
