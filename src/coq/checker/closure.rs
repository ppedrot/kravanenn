use coq::checker::environ::{EnvError, Globals};
use coq::kernel::esubst::{Expr, Idx, IdxError, IdxResult, Lift, SubsV as Subs};
use coq::kernel::names::{
    KnUser,
};
use core::convert::{TryFrom};
use core::nonzero::{NonZero};
use core::ops::Deref;
use ocaml::de::{Array, ORef};
use ocaml::values::{
    CaseInfo,
    Cast,
    CoFix,
    Cons,
    Constr,
    Cst,
    Name,
    Finite,
    Fix,
    Fix2,
    Ind,
    PRec,
    Proj,
    PUniverses,
    RDecl,
    RecordBody,
};
use std::borrow::{Cow};
use std::cell::{Cell as RustCell};
use std::collections::{HashMap};
use std::collections::hash_map;
use std::hash::{Hash, Hasher};
use std::mem;
use std::option::{NoneError};
use std::sync::{Arc};
use typed_arena::{Arena};
use util::ghost_cell::{Cell, Set};
use vec_map::{self, VecMap};

pub type MRef<'b, T> = &'b ORef<T>;

/*
 * Five kinds of reductions:
 *
 * β - lambda application
 * δ - constant expansion
 * ι - case analysis
 * ζ - let substitution
 * η - function extensionality
 *
 * Of these, only the first four occur during normal reduction (the fifth is invoked
 * opportunistically during conversion).  The first four are configured on or off by flags passed
 * to the reduction function.  In Rust, as an optimization, these flags are set as compile time
 * constants.
 */

#[derive(Copy,Clone,Debug,Hash)]
pub enum TableKey<T> {
    ConstKey(T),
    // should not occur
    // VarKey(Id),
    RelKey(Idx),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RedError {
    Idx(IdxError),
    Env(EnvError),
    NotFound,
}

// We box the Error to shrink the Result size.
pub type RedResult<T> = Result<T, Box<RedError>>;

/// Specification of the reduction function.

/// Flags of reduction and cache of constants: 'a is a type that may be
/// mapped to constr. 'a infos implements a cache for constants and
/// abstractions, storing a representation (of type 'a) of the body of
/// this constant or abstraction.
///  * i_tab is the cache table of the results
///  * i_repr is the function to get the representation from the current
///         state of the cache and the body of the constant. The result
///         is stored in the table.
///  * i_rels = (4,[(1,c);(3,d)]) means there are 4 free rel variables
///    and only those with index 1 and 3 have bodies which are c and d resp.
///
/// ref_value_cache searchs in the tab, otherwise uses i_repr to
/// compute the result and store it in the table. If the constant can't
/// be unfolded, returns None, but does not store this failure.  * This
/// doesn't take the RESET into account. You mustn't keep such a table
/// after a Reset.  * This type is not exported. Only its two
/// instantiations (cbv or lazy) are.

bitflags! {
    pub struct Reds : u8 {
        const BETA  = 0b0001;
        const DELTA = 0b0010;
        const IOTA  = 0b0100;
        const ZETA  = 0b1000;

        const BETADELTAIOTA = Self::BETA.bits | Self::DELTA.bits | Self::ZETA.bits |
                              Self::IOTA.bits;
        const BETADELTAIOTANOLET = Self::BETA.bits | Self::DELTA.bits | Self::IOTA.bits;
        const BETAIOTAZETA = Self::BETA.bits | Self::IOTA.bits | Self::ZETA.bits;
    }
}

#[derive(Copy, Clone)]
pub struct Context<'id, 'a, 'b> where 'b: 'a, 'id: 'a {
    /// The term arena; this is really a poor substitute for garbage collection, since it can't
    /// free, but my suspicion is that it will still have better performance characteristics than
    /// Arc.
    term_arena: &'a Arena<FTerm<'id, 'a, 'b>>,
    /// We need this arena for a kind of silly reason.   We need essentially all Constrs we
    /// reference to have lifetime 'b, and if we get a Constr from a global we indeed have a
    /// reference with lifetime 'b; so far, so good, right?  Unfortunately, in some cases (namely,
    /// those with universe polymorphism) we actually need to modify the Constr in a way that we
    /// don't want to share mutably with everyone each time, since it depends on the particular
    /// universe with which it was instantiated.
    ///
    /// Note that this could be shared a la Globals, if we so chose.
    ///
    /// At first, I was sad about this, because it seemed to make the distinction between 'a and 'b
    /// meaningless; but on further reflection, it actually makes it *meaningful* since before this
    /// point there was not much reason for 'b to be different from 'a.  Now, it is clear where we
    /// can't get away without an arena at all (constr_arena, which is actually a perfect use case
    /// for an arena in the sense that we'd never deallocate these Constrs until we were done with
    /// the reduction anyway), and where we might want to start looking for other means of GC
    /// (term_arena).  However, it might be useful to use a structure other than an arena (like a
    /// Vec with size "number of inds in the environment", combined with a sendable iterator over
    /// the vector).  That would make it Sendable, but at the cost of some complexity.
    constr_arena: &'b Arena<Constr>,
    // constr_arena: Arena<FConstr<'id, 'a, 'b>>
    // Not clear to me if this would actually be an optimization (at least, not with the current
    // substitution structure).  The reason being that the amount of sharing we can actually get
    // out of it seems limited, since the interesting reduction steps usually require mutating
    // the substitution environment in some way, and we normally only construct closures to a
    // relatively short depth unless we can strip away their environments.  So far, we only seem
    // to really gain sharing during mk_clos_deep, which is called just once(ish) per Constr node;
    // so we probably don't get *too* much sharing out of that (if the reduction steps are actually
    // doing something).  In other places, we gain sharing automatically by sharing terms that
    // contain substitutions within them; in those cases, *also* sharing the substitutions wouldn't
    // buy a whole lot.
    //
    // If we change our minds, it's not that hard to fix, we just need to change &Subs (or Subs) to
    // &'a Subs in a bunch of places.
    //
    // subs_arena: Arena<Subs<T>>,
}

pub type TableKeyC<'b> = TableKey<MRef<'b, PUniverses<Cst>>>;

// TODO: Use custom KeyHash algorithm.
struct KeyTable<'b, T>(HashMap<TableKeyC<'b>, T>);

pub struct Infos<'id, 'b, T> {
  flags : Reds,
  // i_repr : 'a infos -> constr -> 'a;
  // globals: &'a mut Globals<'g>,
  // i_rels : int * (int * constr) list;
  rels: (u32, VecMap<&'b mut Constr>),
  tab: KeyTable<'b, T>,
  /// The owning set: if you want to do pretty much anything with an FConstr<'id, 'a, 'b>, you
  /// need this in order to do it.
  pub set: Set<'id>,
}

#[derive(Copy,Clone,Debug,PartialEq)]
pub enum RedState {
    /// Norm means the term is fully normalized and cannot create a redex
    /// when substituted
    Norm,
    /// Cstr means the term is in head normal form and that it can
    /// create a redex when substituted (i.e. constructor, fix, lambda)
    Cstr,
    /// Whnf means we reached the head normal form and that it cannot
    /// create a redex when substituted
    Whnf,
    /// Red is used for terms that might be reduced
    Red,
}

/// type of shared terms. fconstr and frterm are mutually recursive.
/// Clone of the constr structure, but completely mutable, and
/// annotated with reduction state (reducible or not).
pub struct FConstr<'id, 'a, 'b> where 'b: 'a, 'id: 'a {
    norm: Cell<'id, RedState>,
    term: Cell<'id, Option<&'a FTerm<'id, 'a, 'b>>>,
}

pub enum FTerm<'id, 'a, 'b> where 'b: 'a, 'id: 'a {
  Rel(Idx),
  /// Metas and sorts; but metas shouldn't occur in a .vo...
  Atom(&'b Constr),
  Cast(FConstr<'id, 'a, 'b>, MRef<'b, (Constr, Cast, Constr)>, FConstr<'id, 'a, 'b>),
  Flex(TableKeyC<'b>),
  Ind(MRef<'b, PUniverses<Ind>>),
  Construct(MRef<'b, PUniverses<Cons>>),
  App(FConstr<'id, 'a, 'b>, Vec<FConstr<'id, 'a, 'b>>),
  Proj(&'b Cst, bool, FConstr<'id, 'a, 'b>),
  Fix(MRef<'b, Fix>, usize, Subs<FConstr<'id, 'a, 'b>>),
  CoFix(MRef<'b, CoFix>, usize, Subs<FConstr<'id, 'a, 'b>>),
  Case(MRef<'b, (CaseInfo, Constr, Constr, Array<Constr>)>, FConstr<'id, 'a, 'b>,
       FConstr<'id, 'a, 'b>, Vec<FConstr<'id, 'a, 'b>>),
  /// predicate and branches are closures
  CaseT(MRef<'b, (CaseInfo, Constr, Constr, Array<Constr>)>, FConstr<'id, 'a, 'b>,
        Subs<FConstr<'id, 'a, 'b>>),
  Lambda(Vec</*(Name, Constr)*/MRef<'b, (Name, Constr, Constr)>>,
         &'b Constr, Subs<FConstr<'id, 'a, 'b>>),
  Prod(MRef<'b, (Name, Constr, Constr)>, FConstr<'id, 'a, 'b>, FConstr<'id, 'a, 'b>),
  LetIn(MRef<'b, (Name, Constr, Constr, Constr)>,
        FConstr<'id, 'a, 'b>, FConstr<'id, 'a, 'b>, Subs<FConstr<'id, 'a, 'b>>),
  // should not occur
  // | FEvar of existential_key * fconstr array (* why diff from kernel/closure? *)
  /// FLIFT is a delayed shift; allows sharing between 2 lifted copies
  /// of a given term.
  Lift(Idx, FConstr<'id, 'a, 'b>),
  /// FCLOS is a delayed substitution applied to a constr
  Clos(&'b Constr, Subs<FConstr<'id, 'a, 'b>>),
  // /// FLOCKED is used to erase the content of a reference that must
  // /// be updated. This is to allow the garbage collector to work
  // /// before the term is computed.
  // Locked,
}

/// The type of (machine) stacks (= lambda-bar-calculus' contexts)
/// Inst ≡ ! allows us to type-safely represent stacks which have no instructions;
/// Shift ≡ ! allows us to type-safely represent stacks which have no shifts.
/// Inst ≡ ! and Shift ≡ ! means the stack is purely applicative.
/// (NOTE: This might become harder if / when we move away from Vecs, so it's a bit risky to add
/// this at this stage).
pub enum StackMember<'id, 'a, 'b, Inst, Shft> where 'b: 'a, 'id: 'a {
    App(Vec<FConstr<'id, 'a, 'b>>),
    Case(MRef<'b, (CaseInfo, Constr, Constr, Array<Constr>)>, FConstr<'id, 'a, 'b>,
         Vec<FConstr<'id, 'a, 'b>>, Inst),
    CaseT(MRef<'b, (CaseInfo, Constr, Constr, Array<Constr>)>, Subs<FConstr<'id, 'a, 'b>>, Inst),
    Proj(usize, usize, &'b Cst, bool, Inst),
    Fix(FConstr<'id, 'a, 'b>, Stack<'id, 'a, 'b, Inst, Shft>, Inst),
    Shift(Idx, Shft),
    Update(&'a FConstr<'id, 'a, 'b>, Inst),
}

/// A dumbed-down version of Cow that has no requirements on its type parameter.
/// Used for implementig the immutable version of zip.
enum SCow<'a, B> where B: 'a {
    Borrowed(&'a B),
    Owned(B),
}

/// A [stack] is a context of arguments, arguments are pushed by
/// [append_stack] one array at a time but popped with [decomp_stack]
/// one by one
pub struct Stack<'id, 'a, 'b, Inst, Shft>(Vec<StackMember<'id, 'a, 'b, Inst, Shft>>)
    where 'b: 'a, 'id: 'a;

/// Full stack (all operations are allowed).
pub type FStack<'id, 'a, 'b> = Stack<'id, 'a, 'b, (), ()>;

/// Purely applicative stack (only Apps are allowed).
pub type AStack<'id, 'a, 'b> = Stack<'id, 'a, 'b, !, !>;

/// Applicative + shifts (only Shift and App are allowed).
pub type SStack<'id, 'a, 'b> = Stack<'id, 'a, 'b, !, ()>;

/// The result of trying to perform beta reduction.
enum Application<T> {
    /// Arguments are fully applied; this is the corresponding substitution.
    Full(Subs<T>),
    /// Arguments are partially applied; this is the corresponding thunk.
    Partial(T),
}

/// cache of constants: the body is computed only when needed.
pub type ClosInfos<'id, 'a, 'b> = Infos<'id, 'b, FConstr<'id, 'a, 'b>>;

pub trait IRepr<'id, 'a, 'b> {
    fn i_repr<T>(set: &Set<'id>, c: T, ctx: Context<'id, 'a, 'b>) -> Result<Self, (IdxError, T)>
        where T: Into<&'b Constr> + 'b,
              T: Deref<Target=Constr>,
              Self: Sized;
}

impl ::std::convert::From<IdxError> for Box<RedError> {
    fn from(e: IdxError) -> Self {
        Box::new(RedError::Idx(e))
    }
}

impl ::std::convert::From<EnvError> for Box<RedError> {
    fn from(e: EnvError) -> Self {
        Box::new(RedError::Env(e))
    }
}

impl<'id, 'a, 'b> Context<'id, 'a, 'b> {
    pub fn new(term_arena: &'a Arena<FTerm<'id, 'a, 'b>>,
               constr_arena: &'b Arena<Constr>) -> Self {
        Context {
            term_arena: term_arena,
            constr_arena: constr_arena,
        }
    }
}

impl<'b, T> ::std::ops::Deref for KeyTable<'b, T> {
    type Target = HashMap<TableKeyC<'b>, T>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<'b, T> ::std::ops::DerefMut for KeyTable<'b, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<'a, B> Deref for SCow<'a, B>
{
    type Target = B;

    fn deref(&self) -> &B {
        match *self {
            SCow::Borrowed(borrowed) => borrowed,
            SCow::Owned(ref owned) => owned,
        }
    }
}

impl<'b> Into<&'b Constr> for &'b mut Constr {
    fn into(self) -> &'b Constr {
        &*self
    }
}

impl<'b> PartialEq for TableKeyC<'b> {
    fn eq(&self, o: &Self) -> bool {
        match (*self, *o) {
            (TableKey::ConstKey(o1), TableKey::ConstKey(o2)) => {
                let PUniverses(ref c1, ref u1) = **o1;
                let PUniverses(ref c2, ref u2) = **o2;
                KnUser(c1) == KnUser(c2) && u1.equal(u2)
            },
            (TableKey::RelKey(i1), TableKey::RelKey(i2)) => i1 == i2,
            (_, _) => false,
        }
    }
}

impl<'b> Eq for TableKeyC<'b>  {}

impl<'b> Hash for TableKeyC<'b> {
    fn hash<H>(&self, state: &mut H) where H: Hasher {
        match *self {
            TableKey::ConstKey(o) => {
                let PUniverses(ref c, ref u) = **o;
                state.write_u64(1);
                KnUser(c).hash(state);
                u.hash(state);
            },
            TableKey::RelKey(i) => {
                state.write_u64(2);
                i.hash(state);
            }
        }
    }
}

impl<'id, 'a, 'b> IRepr<'id, 'a, 'b> for FConstr<'id, 'a, 'b> {
    fn i_repr<T>(set: &Set<'id>, c: T, ctx: Context<'id, 'a, 'b>) -> Result<Self, (IdxError, T)>
        where T: Into<&'b Constr> + 'b,
              T: Deref<Target=Constr>,
    {
        let env = Subs::id(None);
        env.mk_clos_raw(set, c, ctx)
    }
}

impl<'id, 'a, 'b, T> Infos<'id, 'b, T> where T: IRepr<'id, 'a, 'b> {
    fn ref_value_cache<'r, 'g>(set: &Set<'id>,
                               rels: &'r mut (u32, VecMap<&'b mut Constr>),
                               tab: &'r mut KeyTable<'b, T>,
                               globals: &'r Globals<'g>, rf: TableKeyC<'b>,
                               ctx: Context<'id, 'a, 'b>) -> IdxResult<Option<&'r T>>
            where 'g: 'b
    {
        Ok(Some(match tab.entry(rf) {
            hash_map::Entry::Occupied(o) => o.into_mut(),
            hash_map::Entry::Vacant(v) => {
                match rf {
                    TableKey::RelKey(n) => {
                        let (s, ref mut l) = *rels;
                        if let Some(i) = s.checked_sub(u32::from(n)) {
                            // i is potentially valid, meaning u32 (note that n is a length, not an
                            // Idx, so 0 is a valid index; also note that since n was a positive
                            // u32, we know i < s).
                            // FIXME: Verify that u32 to usize is always a valid cast.
                            let i = i as usize;
                            let (mut body, old) = if let vec_map::Entry::Occupied(mut o) =
                                                         l.entry(i) {
                                let c = o.get().lift(n)?;
                                // One weird trick to keep your lifetimes in order!
                                // We remove body from rels; if there's a panic here and we catch
                                // it before rels goes away, it will be incorrect (proper
                                // UnwindSafe usage will make this a nonissue, but if we care, we
                                // can either use take_mut or add a catch_panic here to fix body
                                // back up).  In the absence of panics, once this block ends nobody
                                // will ever try to look up this entry directly in i_rels again,
                                // since ref_value_cache is the only thing that does so and it will
                                // always take the entry in the outer hash table if it's present;
                                // therefore, the removal here is fine.
                                let mut body: &'b mut Constr = o.remove();
                                let mut old = mem::replace(body, c);
                                (body, old)
                            } else {
                                // Rel is a free variable without a body.
                                return Ok(None);
                            };

                            // We do this dance to ensure that we keep rels the same if there
                            // was a (non-panic) error.  Obviously if there's a panic during
                            // VecMap insertion, this will not work out, but that shouldn't be
                            // an issue given how VecMap is implemented (in particular, it
                            // shouldn't shrink after remove is run, so it should still have
                            // space for i).
                            //
                            // Note that unlike inserting into a vacant HashMap entry or
                            // reinserting the old VecMap entry (neither of which should panic
                            // in practice), there is actually a chance that i_repr panics
                            // here.  To be on the safe side, maybe we should catch_panic
                            // here (which take_mut would also do for safety reasons).
                            match T::i_repr(&set, body, ctx) {
                                Ok(c) => v.insert(c),
                                Err((e, body)) => {
                                    mem::replace(body, old);
                                    l.insert(i, body);
                                    return Err(e)
                                },
                            }
                            // As mentioned above, this insert shouldn't panic in practice,
                            // because space for the entry was already reserved.
                        } else {
                            // n would definitely be invalid if it were negative, (it wasn't
                            // actually a free variable at all), so we know it can't have a body.
                            return Ok(None);
                        }
                    },
                    // | VarKey(id) => raise Not_found
                    TableKey::ConstKey(cst) => {
                        if let Some(Ok(body)) = globals.constant_value(cst) {
                            let body = match body {
                                Cow::Borrowed(b) => b,
                                Cow::Owned(b) => {
                                    // Sometimes we get an owned value back (due to, e.g., universe
                                    // polymorphism), so we need to allocate it in our constr arena.
                                    // This is very unfortunate, but I'm not sure I see a good way
                                    // around something like this; it seems like making *all*
                                    // Constr references be Cow would be overkill, for example.
                                    // We could also share the Constr arena and cache further, since
                                    // the values in it only depend on the input parameters, but that
                                    // would probably limit parallelism.
                                    ctx.constr_arena.alloc(b)
                                },
                            };
                            v.insert(T::i_repr(&set, body, ctx).map_err( |(e, _)| e)?)
                        } else {
                            // We either encountered a lookup error, or cst was not an
                            // evaluable constant; in either case, we can't return a body.
                            return Ok(None);
                        }
                    },
                }
            },
        }))
    }

    pub fn unfold_reference<'r, 'g>(&'r mut self,
                                    globals: &'r Globals<'g>, rf: TableKeyC<'b>,
                                    ctx: Context<'id, 'a, 'b>) ->
        IdxResult<Option<(&'r mut Set<'id>, &'r T)>>
        where 'g: 'b,
    {
        let Infos { ref mut set, ref mut rels, ref mut tab, .. } = *self;
        let res = Self::ref_value_cache(set, rels, tab, globals, rf, ctx)?;
        Ok(res.map( |res| (set, res) ))
    }
}


impl RedState {
    fn neutr(&self) -> Self {
        match *self {
            RedState::Whnf => RedState::Whnf,
            RedState::Norm => RedState::Whnf,
            RedState::Red => RedState::Red,
            RedState::Cstr => RedState::Red,
        }
    }
}

pub fn clone_vec<'id, 'a, 'b>(v: &[FConstr<'id, 'a, 'b>],
                              set: &Set<'id>) -> Vec<FConstr<'id, 'a, 'b>> {
    v.iter().map( |x| x.clone(set) ).collect()
}

impl<'id, 'a, 'b> FConstr<'id, 'a, 'b> {
    pub fn clone(&self, set: &Set<'id>) -> Self {
        FConstr {
            norm: self.norm.clone(set),
            term: self.term.clone(set),
        }
    }

    pub fn fterm(&self, set: &Set<'id>) -> Option<&'a FTerm<'id, 'a, 'b>> {
        *set.get(&self.term)
    }

    fn set_norm(&self, set: &mut Set<'id>) {
        *set.get_mut(&self.norm) = RedState::Norm;
    }

    fn update(&self, set: &mut Set<'id>, no: RedState, term: Option<&'a FTerm<'id, 'a, 'b>>) {
        // Could issue a warning if no is still Red, pointing out that we lose sharing.
        *set.get_mut(&self.norm) = no;
        *set.get_mut(&self.term) = term;
    }

    fn lft(&self, set: &Set<'id>, mut n: Idx, ctx: Context<'id, 'a, 'b>) -> IdxResult<Self> {
        let mut ft = self;
        loop {
            match *ft.fterm(set).expect("Tried to lift a locked term") {
                FTerm::Ind(_) | FTerm::Construct(_)
                | FTerm::Flex(TableKey::ConstKey(_)/* | VarKey _*/) => return Ok(ft.clone(set)),
                FTerm::Rel(i) => return Ok(FConstr {
                    norm: Cell::new(RedState::Norm),
                    term: Cell::new(Some(ctx.term_arena.alloc(FTerm::Rel(i.checked_add(n)?)))),
                }),
                FTerm::Lambda(ref tys, f, ref e) => {
                    let mut e = e.clone(set); // expensive
                    e.shift(n)?;
                    return Ok(FConstr {
                        norm: Cell::new(RedState::Cstr),
                        term: Cell::new(Some(
                                ctx.term_arena.alloc(FTerm::Lambda(tys.clone(), // expensive
                                                                   f, e)))),
                    })
                },
                FTerm::Fix(fx, i, ref e) => {
                    let mut e = e.clone(set); // expensive
                    e.shift(n)?;
                    return Ok(FConstr {
                        norm: Cell::new(RedState::Cstr),
                        term: Cell::new(Some(ctx.term_arena.alloc(FTerm::Fix(fx, i, e)))),
                    })
                },
                FTerm::CoFix(cfx, i, ref e) => {
                    let mut e = e.clone(set); // expensive
                    e.shift(n)?;
                    return Ok(FConstr {
                        norm: Cell::new(RedState::Cstr),
                        term: Cell::new(Some(ctx.term_arena.alloc(FTerm::CoFix(cfx, i, e)))),
                    })
                },
                FTerm::Lift(k, ref m) => {
                    n = n.checked_add(k)?;
                    ft = m;
                },
                _ => return Ok(FConstr {
                    norm: ft.norm.clone(set),
                    term: Cell::new(Some(ctx.term_arena.alloc(FTerm::Lift(n, ft.clone(set))))),
                })
            }
        }
    }

    /// Lifting specialized to the case where n = 0.
    fn lft0(&self, set: &Set<'id>, ctx: Context<'id, 'a, 'b>) -> IdxResult<Self> {
        match *self.fterm(set).expect("Tried to lift a locked term") {
            FTerm::Ind(_) | FTerm::Construct(_)
            | FTerm::Flex(TableKey::ConstKey(_)/* | VarKey _*/) => Ok(self.clone(set)),
            FTerm::Rel(_) => Ok(FConstr {
                norm: Cell::new(RedState::Norm),
                term: self.term.clone(set),
            }),
            FTerm::Lambda(_, _, _) | FTerm::Fix(_, _, _) | FTerm::CoFix(_, _, _) => Ok(FConstr {
                norm: Cell::new(RedState::Cstr),
                term: self.term.clone(set),
            }),
            FTerm::Lift(k, ref m) => m.lft(set, k, ctx),
            _ => Ok(self.clone(set))
        }
    }

    /// The inverse of mk_clos_deep: move back to constr
    /// Note: self must be typechecked beforehand!
    fn to_constr<F>(&self, set: &mut Set<'id>, constr_fun: F, lfts: &Lift,
                    ctx: Context<'id, 'a, 'b>) -> IdxResult<Constr>
        where F: Fn(&FConstr<'id, 'a, 'b>, &mut Set<'id>,
                    &Lift, Context<'id, 'a, 'b>) -> IdxResult<Constr>,
    {
        // FIXME: The constant cloning of lfts can likely be replaced by a slightly different API
        // where lfts is taken mutably, and added shifts or lifts can be pushed for a scope, then
        // popped automatically.  There are several cute ways to do this (including a wrapper
        // around a lift with a custom destructor, and using a closure).  The destructor route is
        // somewhat appealing because it probably makes it easier to convert this into something
        // that doesn't require mutual recursion.
        /* let mut norm_ = self.norm.get();
        let mut term_ = Cow::Borrowed(self.fterm().expect("Tried to lift a locked term!"));*/
        let mut lfts = Cow::Borrowed(lfts);
        let mut v = self;
        loop {
            match *v.fterm(set).expect("Tried to lift a locked term!") {
                FTerm::Rel(i) => return Ok(Constr::Rel(i32::from(lfts.reloc_rel(i)?) as i64)),
                FTerm::Flex(TableKey::RelKey(i)) =>
                    return Ok(Constr::Rel(i32::from(lfts.reloc_rel(i)?) as i64)),
                // | FFlex (VarKey x) -> Var x
                FTerm::Atom(c) => {
                    // Unless something weird is happening, this should be a cheap operation,
                    // because atoms should only contain sorts in our implementation (so this just
                    // becomes a clone()).  Really, this could probably just be replaced by a
                    // c.clone(), for more clarity.
                    return c.exliftn(&lfts)
                },
                FTerm::Cast(ref a, k, ref b) => {
                    let a = constr_fun(a, set, &lfts, ctx)?;
                    let b = constr_fun(b, set, &lfts, ctx)?;
                    return Ok(Constr::Cast(ORef(Arc::from((a, k.1, b)))))
                },
                FTerm::Flex(TableKey::ConstKey(c)) => return Ok(Constr::Const(c.clone())),
                FTerm::Ind(op) => return Ok(Constr::Ind(op.clone())),
                FTerm::Construct(op) => return Ok(Constr::Construct(op.clone())),
                FTerm::Case(ci, ref p, ref c, ref ve) => {
                    let (ref ci, _, _, _) = **ci;
                    let p = constr_fun(p, set, &lfts, ctx)?;
                    let c = constr_fun(c, set, &lfts, ctx)?;
                    // expensive -- allocates a Vec
                    let ve: Result<Vec<_>, _> = ve.iter()
                        .map( |v| constr_fun(v, set, &lfts, ctx) )
                        .collect();
                    return Ok(Constr::Case(ORef(Arc::from((ci.clone(), p, c,
                                                           Array(Arc::from(ve?)))))))
                },
                FTerm::CaseT(ci, ref c, ref e) => {
                    /*
                    // FIXME: Do we really need to create a new FTerm here?  Aren't we just going
                    // to immediately turn it back into a Term?  It seems like it would be better
                    // to just go directly to the logic in FTerm::Case above.
                    let (_, ref p, _, ref ve) = **ci;
                    norm = RedState::Red;
                    term = Cow::Owned(FTerm::Case(ci.clone(), e.mk_clos2(p, ctx)?,
                                                  c.clone(),
                                                  e.mk_clos_vect(&ve, ctx)? /* expensive */));
                    */
                    let (ref ci, ref p, _, ref ve) = **ci;
                    let p = e.mk_clos2(set, p, ctx)?;
                    let p = constr_fun(&p, set, &lfts, ctx)?;
                    let c = constr_fun(c, set, &lfts, ctx)?;
                    // expensive -- allocates a Vec
                    let ve: Result<Vec<_>, _> = ve.iter()
                        .map( |t: &'b Constr| {
                            let v = e.mk_clos(set, t, ctx);
                            constr_fun(&v?, set, &lfts, ctx)
                        })
                        .collect();
                    return Ok(Constr::Case(ORef(Arc::from((ci.clone(), p, c,
                                                           Array(Arc::from(ve?)))))))
                },
                FTerm::Fix(o, i, ref e) => {
                    // FIXME: The recursion here seems like it potentially wastes a lot of work
                    // converting Constrs to FTerms and back... same with CoFix below, and possibly
                    // CaseT above to some extent.  Also, we probably prematurely allocate a few
                    // times, since this is one of the cases where we only need references to
                    // FTerms and FConstrs rather than full-fledged FTerms / FConstrs.
                    let Fix(Fix2(ref reci, _), PRec(ref lna, ref tys, ref bds)) = **o;
                    // expensive, makes a Vec
                    let ftys: Result<Vec<_>, _> = tys.iter()
                        .map( |t| {
                            let t = e.mk_clos(set, t, ctx);
                            constr_fun(&t?, set, &lfts, ctx)
                        })
                        .collect();
                    // Note: I believe the length should always be nonzero here, but I'm not 100%
                    // sure.  For now, we separate the two cases to avoid failing outright in the
                    // zero case (it would also save useless work, but our implementation won't
                    // let you try to lift by zero so this is an academic point).  This also
                    // applies to CoFix below.

                    // expensive, makes a Vec
                    let fbds: Result<Vec<_>, _> = if let Some(n) = NonZero::new(bds.len()) {
                        let n = Idx::new(n)?;
                        let mut e = e.clone(set); // expensive, but shouldn't outlive this block.
                        e.liftn(n)?;
                        // expensive, but shouldn't outlive this block.
                        let mut lfts = lfts.into_owned();
                        lfts.liftn(n)?;
                        bds.iter()
                           .map( |t| {
                                let t = e.mk_clos(set, t, ctx);
                                constr_fun(&t?, set, &lfts, ctx)
                           })
                           .collect()
                    } else {
                        // expensive, makes a Vec
                        bds.iter()
                           .map( |t| {
                               let t = e.mk_clos(set, t, ctx);
                               constr_fun(&t?, set, &lfts, ctx)
                           })
                           .collect()
                    };
                    // FIXME: We know (assuming reasonable FTerm construction) that i fits in an
                    // i64 if it was created directly from a Constr.  We also know that i fits in
                    // an isize if it was created by unfolding a Fix, since all the FTerm::Fix
                    // terms we derive have i < reci.len(), and reci is a vector; Rust guarantees
                    // that vector lengths (in bytes, actually!) fit in an isize.  What remains to
                    // be determined is whether isize is always guaranteed to fit in an i64.  If
                    // that's true, this cast necessarily succeeds.
                    return Ok(Constr::Fix(ORef(Arc::from(Fix(Fix2(reci.clone(), i as i64),
                                                             PRec(lna.clone(),
                                                                  Array(Arc::new(ftys?)),
                                                                  Array(Arc::new(fbds?))))))))
                },
                FTerm::CoFix(o, i, ref e) => {
                    let CoFix(_, PRec(ref lna, ref tys, ref bds)) = **o;
                    // expensive, makes a Vec
                    let ftys: Result<Vec<_>, _> = tys.iter()
                        .map( |t| {
                            let t = e.mk_clos(set, t, ctx);
                            constr_fun(&t?, set, &lfts, ctx)
                        })
                        .collect();
                    // expensive, makes a Vec
                    let fbds: Result<Vec<_>, _> = if let Some(n) = NonZero::new(bds.len()) {
                        let n = Idx::new(n)?;
                        let mut e = e.clone(set); // expensive, but shouldn't outlive this block.
                        e.liftn(n)?;
                        // expensive, but shouldn't outlive this block.
                        let mut lfts = lfts.into_owned();
                        lfts.liftn(n)?;
                        bds.iter()
                           .map( |t| {
                               let t = e.mk_clos(set, t, ctx);
                                constr_fun(&t?, set, &lfts, ctx)
                           })
                           .collect()
                    } else {
                        // expensive, makes a Vec
                        bds.iter()
                           .map( |t| {
                               let t = e.mk_clos(set, t, ctx);
                               constr_fun(&t?, set, &lfts, ctx)
                           })
                           .collect()
                    };
                    // FIXME: We know (assuming reasonable FTerm construction) that i fits in an
                    // i64 if it was created directly from a Constr.  We also know that i fits in
                    // an isize if it was created by unfolding a CoFix, since all the FTerm::CoFix
                    // terms we derive have i < reci.len(), and reci is a vector; Rust guarantees
                    // that vector lengths (in bytes, actually!) fit in an isize.  What remains to
                    // be determined is whether isize is always guaranteed to fit in an i64.  If
                    // that's true, this cast necessarily succeeds.
                    return Ok(Constr::CoFix(ORef(Arc::from(CoFix(i as i64,
                                                                 PRec(lna.clone(),
                                                                      Array(Arc::new(ftys?)),
                                                                      Array(Arc::new(fbds?))))))))
                },
                FTerm::App(ref f, ref ve) => {
                    let f = constr_fun(f, set, &lfts, ctx)?;
                    // expensive -- allocates a Vec
                    let ve: Result<Vec<_>, _> = ve.iter()
                        .map( |v| constr_fun(v, set, &lfts, ctx) )
                        .collect();
                    return Ok(Constr::App(ORef(Arc::from((f, Array(Arc::from(ve?)))))))
                },
                FTerm::Proj(p, b, ref c) => {
                    let c = constr_fun(c, set, &lfts, ctx)?;
                    return Ok(Constr::Proj(ORef(Arc::from((Proj(p.clone(), b), c)))))
                },
                FTerm::Lambda(ref tys, b, ref e) => {
                    // We should know v is nonzero, if Lambda was created properly.
                    // TODO: Enforce this by construction with a Lambda newtype in this file.
                    // FIXME: Is converting to dest_flambda only to convert back to a Lambda really
                    // worthwhile?  It seems like we just keep recurively allocating smaller
                    // FTerms, then turning them back into smaller Lambdas, when we could just skip
                    // allocating the FTerm in the first place.
                    // FIXME: Based on the above, maybe consider having dest_flambda not actually
                    // allocate new FTerms, and instead just return references?  Dunno if this
                    // would work, since we'd need to make new ones at some point anyway.
                    // FIXME: Consider switching FTerm::Lambda to take slices so we don't have to
                    // clone here.  This optimization may also apply for other FTerms but Lambda is
                    // the most obvious, since dest_flambda only needs to slice into the array (of
                    // course, because of this maybe dest_flambda isn't even needed here).
                    let (na, ty, bd) =
                        FTerm::dest_flambda(set, Subs::mk_clos2, tys, b, e, ctx)?;
                    let ty = constr_fun(&ty, set, &lfts, ctx)?;
                    // expensive, but shouldn't outlive this block.
                    let mut lfts = lfts.into_owned();
                    lfts.lift()?;
                    let bd = constr_fun(&bd, set, &lfts, ctx)?;
                    return Ok(Constr::Lambda(ORef(Arc::from((na, ty, bd)))))
                },
                FTerm::Prod(o, ref t, ref c) => {
                    let (ref n, _, _) = **o;
                    let t = constr_fun(t, set, &lfts, ctx)?;
                    // expensive, but shouldn't outlive this block.
                    let mut lfts = lfts.into_owned();
                    lfts.lift()?;
                    let c = constr_fun(c, set, &lfts, ctx)?;
                    return Ok(Constr::Prod(ORef(Arc::from((n.clone(), t, c)))))
                },
                FTerm::LetIn(o, ref b, ref t, ref e) => {
                    let (ref n, _, _, ref f) = **o;
                    let b = constr_fun(b, set, &lfts, ctx)?;
                    let t = constr_fun(t, set, &lfts, ctx)?;
                    let mut e = e.clone(set); // expensive, but shouldn't outlive this block.
                    e.lift()?;
                    let fc = e.mk_clos2(set, f, ctx)?;
                    // expensive, but shouldn't outlive this block.
                    let mut lfts = lfts.into_owned();
                    lfts.lift()?;
                    let fc = constr_fun(&fc, set, &lfts, ctx)?;
                    return Ok(Constr::LetIn(ORef(Arc::from((n.clone(), b, t, fc)))))
                },
                // | FEvar (ev,args) -> Evar(ev,Array.map (constr_fun lfts) args)
                FTerm::Lift(k, ref a) => {
                    // expensive
                    let mut lfts_ = lfts.into_owned();
                    lfts_.shift(k)?;
                    lfts = Cow::Owned(lfts_);
                    // norm_ = a.norm.get();
                    // term_ = Cow::Borrowed(a.fterm().expect("Tried to lift a locked term!"));
                    v = a;
                },
                FTerm::Clos(t, ref env) => {
                    let fr = env.mk_clos2(set, t, ctx)?;
                    // TODO: check whether the update here is useful.  If so, we should
                    // slightly change the function definition.
                    // norm_ = ...
                    // let a = constr_fun(a, set, &lfts, ctx)?;
                    let norm = *set.get(&fr.norm);
                    let term = *set.get(&fr.term);
                    v.update(set, norm, term);
                }
            }
        }
    }

    /// Zip a single item; shared between zip and zip_mut.
    ///
    /// f is the function used to perform the append in the App case.
    fn zip_item_mut<'r, I, S, F>(m: SCow<'r, Self>, set: &mut Set<'id>,
                                 s: StackMember<'id, 'a, 'b, I, S>,
                                 ctx: Context<'id, 'a, 'b>,
                                 f: F) -> IdxResult<SCow<'r, Self>>
        where F: FnOnce(&Set<'id>, Vec<Self>, Stack<'id, 'a, 'b, I, S>),
    {
        match s {
            StackMember::App(args) => {
                let norm = set.get(&m.norm).neutr();
                let t = FTerm::App(m.clone(set), args);
                Ok(SCow::Owned(FConstr {
                    norm: Cell::new(norm),
                    term: Cell::new(Some(ctx.term_arena.alloc(t))),
                }))
            },
            StackMember::Case(o, p, br, _) => {
                let norm = set.get(&m.norm).neutr();
                let t = FTerm::Case(o, p, m.clone(set), br);
                Ok(SCow::Owned(FConstr {
                    norm: Cell::new(norm),
                    term: Cell::new(Some(ctx.term_arena.alloc(t))),
                }))
            },
            StackMember::CaseT(o, e, _) => {
                let norm = set.get(&m.norm).neutr();
                let t = FTerm::CaseT(o, m.clone(set), e);
                Ok(SCow::Owned(FConstr {
                    norm: Cell::new(norm),
                    term: Cell::new(Some(ctx.term_arena.alloc(t))),
                }))
            },
            StackMember::Proj(_, _, p, b, _) => {
                let norm = set.get(&m.norm).neutr();
                let t = FTerm::Proj(p, b, m.clone(set));
                Ok(SCow::Owned(FConstr {
                    norm: Cell::new(norm),
                    term: Cell::new(Some(ctx.term_arena.alloc(t))),
                }))
            },
            StackMember::Fix(fx, par, _) => {
                // FIXME: This seems like a very weird and convoluted way to do this.
                let mut v = vec![m.clone(set)];
                f(set, v, par);
                Ok(SCow::Owned(fx))
            },
            StackMember::Shift(n, _) => {
                Ok(SCow::Owned(m.lft(set, n, ctx)?))
            },
            StackMember::Update(rf, _) => {
                let norm = *set.get(&m.norm);
                let term = *set.get(&m.term);
                rf.update(set, norm, term);
                // TODO: The below is closer to the OCaml implementation, but it doesn't seem
                // like there's any point in doing it, since we never update m anyway (we do
                // return it at the end, but we're currently returning an owned FTerm rather
                // than a shared reference).
                // *m = Cow::Borrowed(rf);
                Ok(m)
            },
        }
    }

    /// This differs from the OCaml because it acutally mutates its stk argument.  Fortunately,
    /// this only matters in one place (whd_stack)--see below.
    fn zip_mut<I, S>(&self, set: &mut Set<'id>, stk: &mut Stack<'id, 'a, 'b, I, S>,
                     ctx: Context<'id, 'a, 'b>) -> IdxResult<FConstr<'id, 'a, 'b>> {
        let mut m = SCow::Borrowed(self);
        while let Some(s) = stk.pop() {
            m = Self::zip_item_mut(m, set, s, ctx, |_, v, par| {
                stk.append(v);
                // mem::swap(stk, &mut par);
                // NOTE: Since we use a Vec rather than a list, the "head" of our stack is
                // actually at the end of the Vec.  Therefore, where in the OCaml we perform
                // par @ stk, here we have reversed par and reversed stk, and perform
                // stk ++ par (or kst ++ rap).
                stk.extend(par.0.into_iter());
            })?;
        }
        Ok(m.clone(set))
    }

    /// This differs from the OCaml because it actually mutates its stk argument.  Fortunately, in
    /// all but one place, this doesn't matter, because we end up not using the stack afterwards
    /// anyway.  The one place, sadly, is whd_stack, which is called all the time, so optimizing
    /// that case separately might be a good idea.
    fn fapp_stack_mut<I, S>(&self, set: &mut Set<'id>, stk: &mut Stack<'id, 'a, 'b, I, S>,
                            ctx: Context<'id, 'a, 'b>) -> IdxResult<FConstr<'id, 'a, 'b>> {
        self.zip_mut(set, stk, ctx)
    }

    /// The immutable version of zip.  Doesn't return a value, since it's only used by whd_stack to
    /// apply update marks.
    fn zip<I, S>(&self, set: &mut Set<'id>, stk: &Stack<'id, 'a, 'b, I, S>,
                 ctx: Context<'id, 'a, 'b>) -> IdxResult<()> {
        let stk = stk.iter();
        let mut bstk = Vec::new(); // the stack, m, and s outlive bstk
        let mut m = SCow::Borrowed(self); // the stack and s outlive m
        // We use a Vec of SCows of StackMembers rather than a normal stack.  The reason is that
        // normal stacks own their items, and some operations (like append) require mutability
        // in order to function.  Rather than write a specialized version of Stack that works
        // within these restrictions, we just use the Vec directly and inline specialized versions
        // of the methods we need (currently, just append).
        //
        // So what's the upside to this over cloning the stack up front?  Well, we avoid tracing
        // the stack again, and not being allowed to clone stacks normally is a nice lint, but
        // that honestly might be less work; maybe we should just do that instead.
        //
        // Also note that we use SCow over regular Cow because regular Cow requires there to be an
        // easy way to turn an immutable version into an owned one, which we don't actually have in
        // general (we only sort of provide an implementation for Apps).
        for s_ in stk {
            let mut s_ = SCow::Borrowed(s_);
            loop {
                // Manual copy of append designed for our weird Cow stacks.
                let append = |set: &Set<'id>, bstk: &mut Vec<_>, mut v: Vec<_>| {
                    if let Some(o) = bstk.last_mut() {
                        match *o {
                            SCow::Borrowed(&StackMember::App(ref l)) => {
                                v.extend(l.iter().map( |v| v.clone(set) ));
                                *o = SCow::Owned(StackMember::App(v));
                                return;
                            },
                            SCow::Owned(StackMember::App(ref mut l)) => {
                                mem::swap(&mut v, l);
                                l.extend(v.into_iter());
                                return;
                            },
                            _ => {},
                        }
                    }
                    bstk.push(SCow::Owned(StackMember::App(v)))
                };
                // First, check whether we can get away (almost) with the mutable case.
                let s = match s_ {
                    SCow::Borrowed(s) => s,
                    SCow::Owned(s) => {
                        // In the owned case, we can just treat this like we do for regular mutable
                        // stacks, except for the append case (which needs to be different to deal
                        // with our weird Cow stack).  Actually, the append case is the only case
                        // we should ever see here, but it might be annoying to convince Rust's
                        // type system of that, and anyway it wouldn't save us much code.
                        m = Self::zip_item_mut(m, set, s, ctx, |set, v, par| {
                            append(set, &mut bstk, v);
                            // mem::swap(stk, &mut par);
                            // NOTE: Since we use a Vec rather than a list, the "head" of our
                            // stack is actually at the end of the Vec.  Therefore, where in the
                            // OCaml we perform par @ stk, here we have reversed par and reversed
                            // stk, and perform stk ++ par (or kst ++ rap).
                            bstk.extend(par.0.into_iter().map(SCow::Owned));
                        })?;
                        // Continue the loop only if we added some elements to the head of the
                        // stack (a fixpoint does this).
                        if let Some(s) = bstk.pop() { s_ = s; continue } else { break }
                    },
                };
                // Now we have to deal with the immutable case.  This is basically identical to the
                // mutable case, except that we clone instead of moving.
                match *s {
                    StackMember::App(ref args) => {
                        let norm = set.get(&m.norm).neutr();
                        let t = FTerm::App(m.clone(set), clone_vec(args, set) /* expensive */);
                        m = SCow::Owned(FConstr {
                            norm: Cell::new(norm),
                            term: Cell::new(Some(ctx.term_arena.alloc(t))),
                        });
                    },
                    StackMember::Case(o, ref p, ref br, _) => {
                        let norm = set.get(&m.norm).neutr();
                        let t = FTerm::Case(o, p.clone(set), m.clone(set),
                                            clone_vec(br, set) /* expensive */);
                        m = SCow::Owned(FConstr {
                            norm: Cell::new(norm),
                            term: Cell::new(Some(ctx.term_arena.alloc(t))),
                        });
                    },
                    StackMember::CaseT(o, ref e, _) => {
                        let norm = set.get(&m.norm).neutr();
                        let t = FTerm::CaseT(o, m.clone(set), e.clone(set) /* expensive */);
                        m = SCow::Owned(FConstr {
                            norm: Cell::new(norm),
                            term: Cell::new(Some(ctx.term_arena.alloc(t))),
                        });
                    },
                    StackMember::Proj(_, _, p, ref b, _) => {
                        let norm = set.get(&m.norm).neutr();
                        let t = FTerm::Proj(p, b.clone(), m.clone(set));
                        m = SCow::Owned(FConstr {
                            norm: Cell::new(norm),
                            term: Cell::new(Some(ctx.term_arena.alloc(t))),
                        });
                    },
                    StackMember::Fix(ref fx, ref par, _) => {
                        // FIXME: This seems like a very weird and convoluted way to do this.
                        let mut v = vec![m.clone(set)];
                        m = SCow::Borrowed(fx);
                        append(set, &mut bstk, v);
                        // mem::swap(stk, &mut par);
                        // NOTE: Since we use a Vec rather than a list, the "head" of our stack is
                        // actually at the end of the Vec.  Therefore, where in the OCaml we
                        // perform par @ stk, here we have reversed par and reversed stk, and
                        // perform stk ++ par (or kst ++ rap).
                        bstk.extend(par.0.iter().map(SCow::Borrowed));
                    },
                    StackMember::Shift(n, _) => {
                        m = SCow::Owned(m.lft(set, n, ctx)?);
                    },
                    StackMember::Update(ref rf, _) => {
                        let norm = *set.get(&m.norm);
                        let term = *set.get(&m.term);
                        rf.update(set, norm, term);
                        // TODO: The below is closer to the OCaml implementation, but it doesn't
                        // seem like there's any point in doing it, since we never update m anyway.
                        // m = SCow::Borrowed(rf);
                    },
                }
                // Continue the loop only if we added some elements to the head of the stack (a
                // fixpoint does this).
                s_ = { if let Some(s) = bstk.pop() { s } else { break } };
            }
        }
        Ok(())
    }

    /// The immutable version of fapp_stack.
    fn fapp_stack<I, S>(&self, set: &mut Set<'id>, stk: &Stack<'id, 'a, 'b, I, S>,
                        ctx: Context<'id, 'a, 'b>) -> IdxResult<()> {
        self.zip(set, stk, ctx)
    }

    /// Initialization and then normalization

    /// Weak reduction
    /// [whd_val] is for weak head normalization
    /// Note: self must be typechecked beforehand!
    pub fn whd_val<'r,'g>(self, info: &mut ClosInfos<'id, 'a, 'b>, globals: &Globals<'g>,
                          ctx: Context<'id, 'a, 'b>) -> RedResult<Constr>
            where 'g: 'b,
    {
        let mut stk = Stack(Vec::new());
        let ft = stk.kh(info, globals, self, ctx, (), ())?;
        Ok(Constr::of_fconstr(&ft, &mut info.set, ctx)?)
    }
}

impl<'id, 'a, 'b> Subs<FConstr<'id, 'a, 'b>> {
    pub fn clone(&self, set: &Set<'id>) -> Self {
        self.dup( |i| i.iter().map( |x| x.clone(set) ).collect() )
    }

    fn clos_rel(&self, set: &Set<'id>, i: Idx,
                ctx: Context<'id, 'a, 'b>) -> IdxResult<FConstr<'id, 'a, 'b>> {
        match self.expand_rel(i)? {
            (n, Expr::Val(mt)) => mt.lft(set, n, ctx),
            (k, Expr::Var(None)) => Ok(FConstr {
                norm: Cell::new(RedState::Norm),
                term: Cell::new(Some(ctx.term_arena.alloc(FTerm::Rel(k)))),
            }),
            (k, Expr::Var(Some(p))) => {
                let v = FConstr {
                    norm: Cell::new(RedState::Red),
                    term: Cell::new(Some(ctx.term_arena.alloc(FTerm::Flex(TableKey::RelKey(p))))),
                };
                // We know k-p is non-negative by inspecting the implementation of expand_rel,
                // but we can't really prove this to Rust from here
                // FIXME: Consider changing the return specification of expand_rel to make this
                // expect unnecessary.
                if let Some(k) = k.checked_sub(p).expect("k-p should always be non-negative!") {
                    // Positive k
                    v.lft(set, k, ctx)
                } else {
                    // Zero k.
                    // Don't try to lift, since you don't have anything positive by which to lift.
                    Ok(v)
                }
            }
        }
    }

    fn mk_lambda(self,
                 /*t: ORef<(Name, Constr, Constr)>*/
                 t: &'b Constr) -> IdxResult<FTerm<'id, 'a, 'b>> {
        // let t = Constr::Lambda(t);
        let (mut rvars, t_) = t.decompose_lam(); // expensive because it allocates a new vector.
        // We know rvars.len() is nonzero.
        // let idx = Idx::new(NonZero::new(rvars.len())
        //           .expect("lambda terms have at least 1 argument."))?;
        rvars.reverse(); // FIXME: Why not just keep it in the old order?
                         // PROBABLE ANSWER: Because we want to cheaply pop off the head, and in
                         // the old order the head is at the front.  However, a VecDeque would
                         // probably work just fine... and/or slicing rather than mutation, which
                         // would work well from either end.
                         //
                         // Perhaps the thing that would work the best would be a custom iterator
                         // that went down a lambda chain... or maybe we just need a direct
                         // reference to the topmost ORef, and an indication of the length?  That
                         // would avoid allocations altogether.  What would be the disadvantage
                         // of that, given how the FLambda appears to be used?
        Ok(FTerm::Lambda(rvars, t_, self))
    }

    fn mk_clos_raw<T>(&self, set: &Set<'id>, t: T,
                      ctx: Context<'id, 'a, 'b>) -> Result<FConstr<'id, 'a, 'b>, (IdxError, T)>
        where T: Into<&'b Constr> + 'b,
              T: Deref<Target=Constr>,
    {
        if let Constr::Rel(i) = *t {
           let i = match NonZero::new(i) {
               Some(i) => i,
               None => return Err((IdxError::from(NoneError), t))
           };
           let i = match Idx::new(i) {
               Ok(i) => i,
               Err(e) => return Err((e, t))
           };
           return match self.clos_rel(set, i, ctx) {
               Err(e) => Err((e, t)),
               Ok(i)  => Ok(i),
           }
        }
        // We have to split out these cases because the first one requires us to have ownership
        // over the original T.  This is what we get for trying to be generic over &mut and &.
        // Maybe we should just have two versions of this function...
        let t = t.into();
        match *t {
            Constr::Rel(_) =>
                unreachable!("Rel was already handled"),
            Constr::Const(ref c) => Ok(FConstr {
                norm: Cell::new(RedState::Red),
                term: Cell::new(Some(ctx.term_arena.alloc(FTerm::Flex(TableKey::ConstKey(c))))),
            }),
            /*Constr::Meta(_) | Constr::Var(_) | Constr::Evar(_) =>
                unreachable!("Constrs should not be Meta, Var, or Evar"),*/
            Constr::Sort(_) => Ok(FConstr {
                norm: Cell::new(RedState::Norm),
                term: Cell::new(Some(ctx.term_arena.alloc(FTerm::Atom(t)))),
            }),
            Constr::Ind(ref kn) => Ok(FConstr {
                norm: Cell::new(RedState::Norm),
                term: Cell::new(Some(ctx.term_arena.alloc(FTerm::Ind(kn)))),
            }),
            Constr::Construct(ref kn) => Ok(FConstr {
                norm: Cell::new(RedState::Cstr),
                term: Cell::new(Some(ctx.term_arena.alloc(FTerm::Construct(kn)))),
            }),
            Constr::CoFix(_) | Constr::Lambda(_)
            | Constr::Fix(_) | Constr::Prod(_)
            | Constr::App(_) | Constr::Case(_)
            | Constr::Cast(_) | Constr::LetIn(_)
            | Constr::Proj(_) => Ok(FConstr {
                norm: Cell::new(RedState::Red),
                term: Cell::new(Some(ctx.term_arena.alloc(
                            FTerm::Clos(t, self.clone(set) /* expensive */))))
            }),
        }
    }

    /// Optimization: do not enclose variables in a closure.
    /// Makes variable access much faster
    pub fn mk_clos(&self, set: &Set<'id>, t: &'b Constr,
                   ctx: Context<'id, 'a, 'b>) -> Result<FConstr<'id, 'a, 'b>, IdxError>
    {
        self.mk_clos_raw(set, t, ctx).map_err( |(e, _)| e)
    }

    pub fn mk_clos_vect(&self, set: &Set<'id>, v: &'b [Constr],
                        ctx: Context<'id, 'a, 'b>) -> IdxResult<Vec<FConstr<'id, 'a, 'b>>> {
        // Expensive, makes a vector
        v.into_iter().map( |t| self.mk_clos(set, t, ctx)).collect()
    }

    /// Translate the head constructor of t from constr to fconstr. This
    /// function is parameterized by the function to apply on the direct
    /// subterms.
    /// Could be used insted of mk_clos.
    /// Note: t must be typechecked beforehand!
    pub fn mk_clos_deep<F>(&self, set: &Set<'id>, clos_fun: F, t: &'b Constr,
                           ctx: Context<'id, 'a, 'b>) -> IdxResult<FConstr<'id, 'a, 'b>>
        where F: Fn(&Subs<FConstr<'id, 'a, 'b>>, &Set<'id>,
                    &'b Constr, Context<'id,'a, 'b>) -> IdxResult<FConstr<'id, 'a, 'b>>,
    {
        match *t {
            Constr::Rel(_) | Constr::Ind(_) |
            Constr::Const(_) | Constr::Construct(_) |
            // Constr::Var(_) | Constr::Meta(_) | Constr::Evar(_)
            Constr::Sort(_) => self.mk_clos(set, t, ctx),
            Constr::Cast(ref o) => {
                let (a, b) = {
                    let (ref a, _, ref b) = **o;
                    let a = clos_fun(self, set, a, ctx)?;
                    let b = clos_fun(self, set, b, ctx)?;
                    (a, b)
                };
                Ok(FConstr {
                    norm: Cell::new(RedState::Red),
                    term: Cell::new(Some(ctx.term_arena.alloc(FTerm::Cast(a, o, b)))),
                })
            },
            Constr::App(ref o) => {
                let (f, v) = {
                    let (ref f, ref v) = **o;
                    let f = clos_fun(self, set, f, ctx)?;
                    // Expensive, makes a vector
                    let v: Result<_, _> =
                        v.iter().map( |t| clos_fun(self, set, t, ctx))
                         .collect();
                    (f, v?)
                };
                Ok(FConstr {
                    norm: Cell::new(RedState::Red),
                    term: Cell::new(Some(ctx.term_arena.alloc(FTerm::App(f, v)))),
                })
            },
            Constr::Proj(ref o) => {
                let (Proj(ref p, b), ref c) = **o;
                let c = clos_fun(self, set, c, ctx)?;
                Ok(FConstr {
                    norm: Cell::new(RedState::Red),
                    term: Cell::new(Some(ctx.term_arena.alloc(FTerm::Proj(p, b, c)))),
                })
            },
            Constr::Case(ref o) => {
                let c = {
                    let (_, _, ref c, _) = **o;
                    clos_fun(self, set, c, ctx)?
                };
                let env = self.clone(set); // expensive
                Ok(FConstr {
                    norm: Cell::new(RedState::Red),
                    term: Cell::new(Some(ctx.term_arena.alloc(FTerm::CaseT(o, c, env)))),
                })
            },
            Constr::Fix(ref o) => {
                let Fix(Fix2(_, i), _) = **o;
                // TODO: Verify that this is checked at some point during typechecking.
                // FIXME: Verify that i < reci.len() (etc.) is checked at some point during
                // typechecking.
                let i = usize::try_from(i).map_err(IdxError::from)?;
                let env = self.clone(set); // expensive
                Ok(FConstr {
                    norm: Cell::new(RedState::Cstr),
                    term: Cell::new(Some(ctx.term_arena.alloc(FTerm::Fix(o, i, env)))),
                })
            },
            Constr::CoFix(ref o) => {
                let CoFix(i, _) = **o;
                // TODO: Verify that this is checked at some point during typechecking.
                // FIXME: Verify that i < reci.len() (etc.) is checked at some point during
                // typechecking.
                let i = usize::try_from(i).map_err(IdxError::from)?;
                let env = self.clone(set); // expensive
                Ok(FConstr {
                    norm: Cell::new(RedState::Cstr),
                    term: Cell::new(Some(ctx.term_arena.alloc(FTerm::CoFix(o, i, env)))),
                })
            },
            Constr::Lambda(_) => {
                let env = self.clone(set); // expensive
                Ok(FConstr {
                    norm: Cell::new(RedState::Cstr),
                    term: Cell::new(Some(ctx.term_arena.alloc(env.mk_lambda(t)?))),
                })
            },
            Constr::Prod(ref o) => {
                let (t, c) = {
                    let (_, ref t, ref c) = **o;
                    let t = clos_fun(self, set, t, ctx)?;
                    // expensive, but doesn't outlive this block.
                    let mut env = self.clone(set);
                    env.lift()?;
                    let c = clos_fun(&env, set, c, ctx)?;
                    (t, c)
                };
                Ok(FConstr {
                    norm: Cell::new(RedState::Whnf),
                    term: Cell::new(Some(ctx.term_arena.alloc(FTerm::Prod(o, t, c)))),
                })
            },
            Constr::LetIn(ref o) => {
                let (b, t) = {
                    let (_, ref b, ref t, _) = **o;
                    let b = clos_fun(self, set, b, ctx)?;
                    let t = clos_fun(self, set, t, ctx)?;
                    (b, t)
                };
                let env = self.clone(set); // expensive
                Ok(FConstr {
                    norm: Cell::new(RedState::Red),
                    term: Cell::new(Some(ctx.term_arena.alloc(FTerm::LetIn(o,
                                                              b, t, env)))),
                })
            },
        }
    }

    /// A better mk_clos?
    /// Note: t must be typechecked beforehand!
    fn mk_clos2(&self, set: &Set<'id>, t: &'b Constr,
                ctx: Context<'id, 'a, 'b>) -> IdxResult<FConstr<'id, 'a, 'b>> {
        self.mk_clos_deep(set, Subs::<FConstr>::mk_clos, t, ctx)
    }
}

impl<'id, 'a, 'b, I, S> ::std::ops::Deref for Stack<'id, 'a, 'b, I, S> {
    type Target = Vec<StackMember<'id, 'a, 'b, I, S>>;
    fn deref(&self) -> &Vec<StackMember<'id, 'a, 'b, I, S>> {
        &self.0
    }
}

impl<'id, 'a, 'b, I, S> ::std::ops::DerefMut for Stack<'id, 'a, 'b, I, S> {
    fn deref_mut(&mut self) -> &mut Vec<StackMember<'id, 'a, 'b, I, S>> {
        &mut self.0
    }
}

impl<'id, 'a, 'b, I, S> Stack<'id, 'a, 'b, I, S> {
    pub fn new () -> Self {
        Stack(Vec::new())
    }

    fn push(&mut self, o: StackMember<'id, 'a, 'b, I, S>) {
        self.0.push(o);
    }

    pub fn append(&mut self, mut v: Vec<FConstr<'id, 'a, 'b>>) {
        if v.len() == 0 { return }
        if let Some(&mut StackMember::App(ref mut l)) = self.last_mut() {
            mem::swap(&mut v, l);
            l.extend(v.into_iter());
            return
        }
        self.push(StackMember::App(v))
    }

    fn shift(&mut self, n: Idx, s: S) -> IdxResult<()> {
        if let Some(&mut StackMember::Shift(ref mut k, _)) = self.last_mut() {
            *k = k.checked_add(n)?;
            return Ok(())
        }
        Ok(self.push(StackMember::Shift(n, s)))
    }

    // since the head may be reducible, we might introduce lifts of 0
    // FIXME: Above comment is not currently true.  Should it be?
    fn compact(&mut self, set: &mut Set<'id>, head: &FConstr<'id, 'a, 'b>,
               ctx: Context<'id, 'a, 'b>) -> IdxResult<()> {
        let mut depth = None;
        while let Some(shead) = self.pop() {
            match shead {
                StackMember::Shift(k, s) => {
                    depth = match depth {
                        None => Some((k, s)),
                        Some((depth, s)) => Some((depth.checked_add(k)?, s)),
                    };
                },
                StackMember::Update(m, _) => {
                    // Be sure to create a new cell otherwise sharing would be
                    // lost by the update operation.
                    // FIXME: Figure out what the above cryptic comment means and whether it
                    // applies to Rust.
                    let h_ = match depth {
                        Some((depth, _)) => head.lft(set, depth, ctx),
                        None => head.lft0(set, ctx),
                    }?;
                    let norm = *set.get(&h_.norm);
                    let term = *set.get(&h_.term);
                    m.update(set, norm, term);
                },
                s => {
                    // It was fine on the stack before, so it should be fine now.
                    self.0.push(s);
                    return match depth {
                        Some((depth, s)) => self.shift(depth, s),
                        None => Ok(()),
                    }
                }
            }
        }
        Ok(())
    }

    /// Put an update mark in the stack, only if needed
    fn update(&mut self, set: &mut Set<'id>, m: &'a FConstr<'id, 'a, 'b>, i: I,
              ctx: Context<'id, 'a, 'b>) -> IdxResult<()> {
        if *set.get(&m.norm) == RedState::Red {
            // const LOCKED: &'static FTerm<'static> = &FTerm::Locked;
            self.compact(set, &m, ctx)?;
            *set.get_mut(&m.term) = None;
            Ok(self.push(StackMember::Update(m, i)))
        } else { Ok(()) }
    }

    /// The assertions in the functions below are granted because they are
    /// called only when m is a constructor, a cofix
    /// (strip_update_shift_app), a fix (get_nth_arg) or an abstraction
    /// (strip_update_shift, through get_arg).

    /// optimized for the case where there are no shifts...
    fn strip_update_shift_app(&mut self, set: &mut Set<'id>, mut head: FConstr<'id, 'a, 'b>,
                              ctx: Context<'id, 'a, 'b>) ->
                              IdxResult<((Option<Idx>, Stack<'id, 'a, 'b, /* !, */I, S>))> {
        // FIXME: This could almost certainly be made more efficient using slices (for example) or
        // custom iterators.
        assert!(*set.get(&head.norm) != RedState::Red);
        let mut rstk = Stack(Vec::with_capacity(self.len()));
        let mut depth = None;
        while let Some(shead) = self.pop() {
            match shead {
                StackMember::Shift(k, s) => {
                    rstk.push(StackMember::Shift(k, s));
                    head = head.lft(set, k, ctx)?;
                    depth = match depth {
                        None => Some(k),
                        Some(depth) => Some(depth.checked_add(k)?),
                    };
                },
                StackMember::App(args) => {
                    rstk.push(StackMember::App(clone_vec(&args, set) /* expensive */));
                    let h = head.clone(set);
                    head.term = Cell::new(Some(ctx.term_arena.alloc(FTerm::App(h, args))));
                },
                StackMember::Update(m, _) => {
                    let norm = *set.get(&head.norm);
                    let term = *set.get(&head.term);
                    m.update(set, norm, term);
                    // NOTE: In the OCaml implementation this might be worthwhile, but I'm not sure
                    // about this one since head is never (AFAICT?) able to be made into a shared
                    // reference before the function returns.
                    // head = m;
                },
                s => {
                    // It was fine on the stack before, so it should be fine now.
                    self.0.push(s);
                    break
                }
            }
        }
        // FIXME: Seriously, slices have to be better than this.
        // Getting rid of update marks in the stack is nice, but if by avoiding them we
        // can avoid a bunch of allocation, it's probably a win... and we might be able
        // to create an iterator that just skips over the updates, or something.
        rstk.reverse();
        Ok((depth, rstk))
    }

    fn get_nth_arg(&mut self, set: &mut Set<'id>, mut head: FConstr<'id, 'a, 'b>, mut n: usize,
                   ctx: Context<'id, 'a, 'b>) ->
                   IdxResult<Option<(Stack<'id, 'a, 'b, /* ! */I, S>, FConstr<'id, 'a, 'b>)>> {
        // FIXME: This could almost certainly be made more efficient using slices (for example) or
        // custom iterators.
        assert!(*set.get(&head.norm) != RedState::Red);
        let mut rstk = Stack(Vec::with_capacity(self.len()));
        while let Some(shead) = self.pop() {
            match shead {
                StackMember::Shift(k, s) => {
                    rstk.push(StackMember::Shift(k, s));
                    head = head.lft(set, k, ctx)?;
                },
                StackMember::App(args) => {
                    let q = args.len();
                    if n >= q {
                        // TODO: Check to see if args.len() could ever be zero?  If not, should we
                        // assert here, given that we check below to make sure we don't push onto
                        // rstk if n = 0?  Otherwise, should we add similar logic to the below to
                        // avoid pushing an empty arg stack?
                        rstk.push(StackMember::App(clone_vec(&args, set) /* expensive */));
                        let h = head.clone(set);
                        head.term = Cell::new(Some(ctx.term_arena.alloc(FTerm::App(h, args))));
                        // Safe because n >= q
                        n -= q;
                    } else {
                        // FIXME: Make this all use the proper vector methods (draining etc.).
                        // Safe because n ≤ args.len() (actually < args.len())
                        let bef = clone_vec(&args[..n], set); // expensive
                        // Safe because n < args.len()
                        let arg = args[n].clone(set);
                        // Safe because (1) n + 1 is in bounds for usize, and
                        // (2) n + 1 ≤ args.len()
                        let aft = clone_vec(&args[n+1..], set); // expensive
                        // n = bef.len()
                        if n > 0 {
                            rstk.push(StackMember::App(bef));
                        }
                        rstk.reverse();
                        self.append(aft);
                        return Ok(Some((rstk, arg)))
                    }
                },
                StackMember::Update(m, _) => {
                    let norm = *set.get(&head.norm);
                    let term = *set.get(&head.term);
                    m.update(set, norm, term);
                    // NOTE: In the OCaml implementation this might be worthwhile, but I'm not sure
                    // about this one since head is never (AFAICT?) able to be made into a shared
                    // reference before the function returns.
                    // head = m;
                },
                s => {
                    // It was fine on the stack before, so it should be fine now.
                    self.0.push(s);
                    break
                }
            }
        }
        // FIXME: Seriously, slices have to be better than this.
        // Getting rid of update marks in the stack is nice, but if by avoiding them we
        // can avoid a bunch of allocation, it's probably a win... and we might be able
        // to create an iterator that just skips over the updates, or something.
        rstk.reverse();
        self.extend(rstk.0.into_iter()/* .map( |v| match v {
            StackMember::Shift(k, s) => StackMember::Shift(k, s),
            StackMember::App(args) => StackMember::App(args),
        }) */);
        Ok(None)
    }

    /// Beta reduction: look for an applied argument in the stack.
    /// Since the encountered update marks are removed, h must be a whnf
    /// tys, f, and e must be from a valid FTerm (e.g. tys.len() must be nonzero).
    fn get_args(&mut self, set: &mut Set<'id>,
                mut tys: &[MRef<'b, (Name, Constr, Constr)>],
                f: &'b Constr,
                mut e: Subs<FConstr<'id, 'a, 'b>>,
                ctx: Context<'id, 'a, 'b>) -> IdxResult<Application<FConstr<'id, 'a, 'b>>> {
        while let Some(shead) = self.pop() {
            match shead {
                StackMember::Update(r, _) => {
                    // FIXME: If we made FLambdas point into slices, this silly allocation would
                    // not be necessary.
                    // Also: note that if tys.len() = 0, we will get an assertion later trying to
                    // convert it back.  The loop, however, should preserve tys.len() > 0 as long
                    // as it was initially > 0.
                    let tys = tys.to_vec(); // expensive
                    let e = e.clone(set); // expensive
                    r.update(set, RedState::Cstr,
                             Some(ctx.term_arena.alloc(FTerm::Lambda(tys, f, e))));
                },
                StackMember::Shift(k, _) => {
                    e.shift(k)?;
                },
                StackMember::App(l) => {
                    let n = tys.len();
                    let na = l.len();
                    if n == na {
                        // All arguments have been applied
                        e.cons(l)?;
                        return Ok(Application::Full(e))
                    } else if n < na {
                        // More arguments
                        // FIXME: If we made FLambdas point into slices, these silly allocations
                        // would not be necessary.
                        // Safe because n ≤ l.len()
                        let args = clone_vec(&l[..n], set); // expensive
                        e.cons(args)?;
                        // Safe because n ≤ na ≤ l.len() (n < na, actually, so eargs will be
                        // nonempty).
                        let eargs = clone_vec(&l[n..na], set); // expensive
                        self.push(StackMember::App(eargs));
                        return Ok(Application::Full(e))
                    } else {
                        // More lambdas
                        // Safe because na ≤ tys.len() (na < tys.len(), actually, so tys will
                        // still be nonempty).
                        tys = &tys[na..];
                        e.cons(l)?;
                    }
                },
                s => {
                    // It was fine on the stack before, so it should be fine now.
                    self.0.push(s);
                    break
                }
            }
        }
        let tys = tys.to_vec(); // expensive
        Ok(Application::Partial(FConstr {
            norm: Cell::new(RedState::Cstr),
            term: Cell::new(Some(ctx.term_arena.alloc(FTerm::Lambda(tys, f, e)))),
        }))
    }

/* }

impl<'id, 'a, 'b, I> Stack<'id, 'a, 'b, I, ()> { */
    /// Eta expansion: add a reference to implicit surrounding lambda at end of stack
    pub fn eta_expand_stack(&mut self, ctx: Context<'id, 'a, 'b>, s: S) {
        // FIXME: Given that we want to do this, seriously consider using a VecDeque rather than a
        // stack.  That would make this operation O(1).  The only potential downside would be less
        // easy slicing, but that might not matter too much if we do things correctly (as_slices is
        // quite handy).
        self.reverse();
        // This allocates a Vec, but it's not really that expensive.
        let app = vec![FConstr {
            norm: Cell::new(RedState::Norm),
            term: Cell::new(Some(ctx.term_arena.alloc(FTerm::Rel(Idx::ONE)))),
        }];
        self.push(StackMember::App(app));
        self.push(StackMember::Shift(Idx::ONE, s));
        self.reverse();
    }
/* }

impl<'id, 'a, 'b, S> Stack<'id, 'a, 'b, !, S> { */
    /// Iota reduction: extract the arguments to be passed to the Case
    /// branches
    /// Stacks on which this is called must satisfy:
    /// - stack is composed exclusively of Apps and Shifts.
    /// - depth = sum of shifts in this stack.
    fn reloc_rargs(&mut self, set: &Set<'id>, depth: Option<Idx>,
                   ctx: Context<'id, 'a, 'b>) -> IdxResult<()> {
        let mut depth = if let Some(depth) = depth { depth } else { return Ok(()) };
        let done = RustCell::new(None);
        // We wastefully drop the shifts.
        let iter = self.drain_filter( |shead| {
            if done.get().is_some() { return false }
            match *shead {
                StackMember::App(ref mut args) => {
                    for arg in args.iter_mut() {
                        match arg.lft(set, depth, ctx) {
                            Ok(h) => { *arg = h },
                            Err(e) => {
                                done.set(Some(Err(e)));
                                // Note that args before this are partially lifted!
                                // Can't rely on the state of the stack in the case of an
                                // error.
                                break
                            },
                        }
                    }
                    // Retain the lifted ZApp
                    return false
                },
                StackMember::Shift(k, _) => {
                    const ERR_STRING : &'static str =
                        "reloc_rargs should always be called with depth = sum of shifts";
                    // The below assertion is granted because reloc_args is generally called on
                    // stacks produced by strip_update_shift_app, which (1) only have shifts and
                    // apps in them, and (2) always have depth = sum of shifts.  The only
                    // modification made to these stacks before calling reloc_rargs is by
                    // try_drop_parameters, which only adds new apps, not shifts (it calls
                    // append_stack).  Since the sum of shifts is equal to the depth, subtracting
                    // k from the depth should be non-negative.
                    if let Some(depth_) = depth.checked_sub(k).expect(ERR_STRING) {
                        // k < depth
                        depth = depth_;
                    } else {
                        // k = depth; end the loop.
                        done.set(Some(Ok(())));
                    }
                    // Drop the shift.
                    return true
                },
                _ => panic!("Stacks passed to reloc_rargs should only have App and Shift"),
            }
        });
        // Execute the iterator for its side effects.
        for _ in iter {}
        done.get().unwrap_or(Ok(()))
    }

    /// Only call with a stack and depth produced by strip_update_shift_app.
    /// (strip_update_shift_app produces a stack with only Zapp and Zshift items, and depth = sum
    /// of shifts in the stack).
    fn try_drop_parameters(&mut self, set: &Set<'id>, mut depth: Option<Idx>, mut n: usize,
                           ctx: Context<'id, 'a, 'b>) -> IdxResult<Option<()>> {
        // Drop should only succeed here if n == 0 (i.e. there were no additional parameters to
        // drop).  But we should never reach the end of the while loop unless there was no
        // StackMember::App in the stack, because if n = 0, ∀ q : usize, n ≤ q, which would
        // mean the App branches returned.  Since we don't actually *do* anything in the Shift
        // branch other than decrement depth, it doesn't affect whether n == 0 at the end, so we
        // can just check it at the beginning.
        if n == 0 { return Ok(Some(())) }
        while let Some(shead) = self.pop() {
            match shead {
                StackMember::App(args) => {
                    let q = args.len();
                    if n > q {
                        // Safe because n > q → n - q > 0.
                        n -= q;
                    } else {
                        if n < q {
                            // Safe because n ≤ args.len (n < args.len(), actually, so aft will
                            // be nonempty).
                            // FIXME: If we made FLambdas point into slices, this silly allocation
                            // would not be necessary (note to self: is this actually true?).
                            let aft = clone_vec(&args[n..], set); // expensive
                            self.append(aft);
                        }
                        self.reloc_rargs(set, depth, ctx)?;
                        return Ok(Some(()));
                    }
                },
                StackMember::Shift(k, _) => {
                    const ERR_STRING : &'static str =
                        "try_drop_parameters should always be called with depth = sum of shifts";
                    // The below assertions are granted because reloc_args is necessarily called on
                    // stacks produced by strip_update_shift_app, which (1) only have shifts and
                    // apps in them, and (2) always have depth = sum of shifts.
                    depth = depth.expect(ERR_STRING).checked_sub(k).expect(ERR_STRING);
                },
                _ => panic!("Stacks passed to try_drop_parameters should only have App and Shift"),
            }
        }
        // We exhausted the argument stack before we finished dropping all the parameters.
        return Ok(None)
    }

    /// Only call this on type-checked terms (otherwise the assertion may be false!)
    /// Also, only call with a stack and depth produced by strip_update_shift_app.
    /// (strip_update_shift_app produces a stack with only Zapp and Zshift items, and depth = sum
    /// of shifts in the stack).
    /// FIXME: Figure out a way to usefully incorporate "this term has been typechecked" into
    /// Rust's type system (maybe some sort of weird wrapper around Constr?).
    fn drop_parameters(&mut self, set: &Set<'id>, depth: Option<Idx>, n: usize,
                       ctx: Context<'id, 'a, 'b>) -> IdxResult<()> {
        self.try_drop_parameters(set, depth, n, ctx)
            .map( |res| res.expect("We know n < stack_arg_size(self) if well-typed term") )
    }

    /// Projections and eta expansion

    /* let rec get_parameters depth n argstk =
      match argstk with
          Zapp args::s ->
            let q = Array.length args in
            if n > q then Array.append args (get_parameters depth (n-q) s)
            else if Int.equal n q then [||]
            else Array.sub args 0 n
        | Zshift(k)::s ->
          get_parameters (depth-k) n s
        | [] -> (* we know that n < stack_args_size(argstk) (if well-typed term) *)
        if Int.equal n 0 then [||]
        else raise Not_found (* Trying to eta-expand a partial application..., should do
                    eta expansion first? *)
        | _ -> assert false
        (* strip_update_shift_app only produces Zapp and Zshift items *) */

    /// Must be called on a type-checked term.
    ///
    /// NOTE: This is different from the OCaml version in two ways.
    ///
    /// The first is that it mutates the stacks that are passed in.  In the cases where
    /// eta_expand_ind_stack is actually used, this is fine, because we never need to touch them
    /// again (we use the stacks returned from the function instead).
    ///
    /// Secondly, there is some subtlety around the handling of Not_found compared to the OCaml
    /// implementation.  In Ocaml, try_drop_parameters can throw a Not_found, which may propagate
    /// through eta_expand_ind_stack, and so can lookup_mind.  Additionally, eta_expand_ind_stack
    /// throws Not_found explicitly if it turns out that the referenced ind isn't a primitive
    /// record.
    ///
    /// In the Rust implementation, by contrast, we tentatively differentiate between two kinds of
    /// Not_found errors: those that indicate an ill-constructed environment (the one from
    /// lookup_mind, in this case, but also the failed lookup_projection in knh on Proj terms), and
    /// those that may merely indicate that eta expansion is impossible (the constructor not being
    /// a primitive record, or the constructor only being partially applied).
    ///
    /// The reason we do this is that Not_found is actually caught during conversion when one term
    /// is a constructor and the other is some other term in weak-head normal form, and (in the
    /// current Coq implementation) always interpreted as NotConvertible.  However, my suspicion is
    /// that the catch is actually designed to catch the eta-expansion errors, not ill-formed
    /// environment errors; otherwise, NotFound would presumably be interpreted as NotConvertible
    /// in other cases as well, since (for example) projection lookup failure within a Proj could
    /// be caught by the same catch.  Additionally, typechecking *does* appear to check that
    /// Construct referencing an inductive that's not in the environment shouldn't happen,
    /// regardless of conversion errors.
    pub fn eta_expand_ind_stack<'id_, 'c, 'g>(globals: &Globals<'g>,
                                              set: &mut Set<'id>,
                                              set_: &mut Set<'id_>,
                                              ind: &'b Ind,
                                              m: FConstr<'id, 'a, 'b>,
                                              s: &mut Stack<'id, 'a, 'b, I, S>,
                                              f: FConstr<'id_, 'c, 'b>,
                                              s_: &mut Stack<'id_, 'c, 'b, I, S>,
                                              ctx: Context<'id, 'a, 'b>,
                                              ctx_: Context<'id_, 'c, 'b>) ->
        RedResult<Option<(Stack<'id, 'a, 'b, I, S>, Stack<'id_, 'c, 'b, I, S>)>>
        where 'g: 'b,
    {
        // FIXME: Typechecking appears to verify that this should always be found, so consider
        // asserting here instead.
        let mib = globals.lookup_mind(&ind.name).ok_or(RedError::NotFound)?;
        match mib.record {
            Some(Some(RecordBody(_, ref projs, _))) if mib.finite != Finite::CoFinite => {
                // (Construct, pars1 .. parsm :: arg1...argn :: []) ~= (f, s') ->
                // arg1..argn ~= (proj1 t...projn t) where t = zip (f,s')
                // TODO: Verify that this is checked at some point during typechecking.
                let pars = usize::try_from(mib.nparams).map_err(IdxError::from)?;
                let right = f.fapp_stack_mut(set_, s_, ctx_)?;
                let (depth, mut args) = s.strip_update_shift_app(set, m, ctx)?;
                // Try to drop the params, might fail on partially applied constructors.
                if let None = args.try_drop_parameters(set, depth, pars, ctx)? {
                    return Ok(None);
                }
                // expensive: makes a Vec.
                let hstack: Vec<_> = projs.iter().map( |p| FConstr {
                    norm: Cell::new(RedState::Red), // right can't be a constructor though
                    term: Cell::new(Some(ctx_.term_arena.alloc(FTerm::Proj(p, false,
                                                                           right.clone(set_))))),
                }).collect();
                // FIXME: Ensure that projs is non-empty, since otherwise we'll have an empty
                // ZApp.
                // makes a Vec, but not that expensive.
                Ok(Some((args, Stack(vec![StackMember::App(hstack)]))))
            },
            _ => Ok(None), // disallow eta-exp for non-primitive records
        }
    }

    /// Only call this on type-checked terms (otherwise the assertion may be false!)
    /// Also, only call with a stack produced by drop_parameters and an n that is part
    /// of a projection.
    /// (drop_parameters produces a stack with only Zapp items, and thanks to type-
    /// checking n should be an index somewhere in the stack).
    fn project_nth_arg(&mut self, mut n: usize) -> FConstr<'id, 'a, 'b> {
        while let Some(shead) = self.pop() {
            match shead {
                StackMember::App(mut args) => {
                    let q = args.len();
                    if n >= q {
                        // Safe because n >= q → n - q ≥ 0.
                        n -= q;
                    } else {
                        // Safe because n < args.len()
                        return args.swap_remove(n)
                    }
                },
                _ => panic!("Stacks passed to project_nth_arg should be purely applicative."),
            }
        }
        panic!("We know m < stack_arg_size(self) if well-typed projection index");
    }
    /// A machine that inspects the head of a term until it finds an
    /// atom or a subterm that may produce a redex (abstraction,
    /// constructor, cofix, letin, constant), or a neutral term (product,
    /// inductive).
    ///
    /// Note: m must be typechecked beforehand!
    fn knh<'r, 'g>(&mut self, info: &mut ClosInfos<'id, 'a, 'b>, globals: &Globals<'g>,
                   m: FConstr<'id, 'a, 'b>,
                   ctx: Context<'id, 'a, 'b>, i: I, s: S) -> RedResult<FConstr<'id, 'a, 'b>>
        where 'g: 'b, S: Clone, I: Clone,
    {
        let mut m: SCow<'a, FConstr<'id, 'a, 'b>> = SCow::Owned(m);
        loop {
            match *m.fterm(&info.set).expect("Tried to lift a locked term") {
                FTerm::Lift(k, ref a) => {
                    self.shift(k, s.clone())?;
                    m = SCow::Borrowed(a);
                },
                FTerm::Clos(mut t, ref e) => {
                    if let SCow::Borrowed(m) = m {
                        // NOTE: We probably only want to bother updating this reference if it's
                        // shared, right?
                        self.update(&mut info.set, m, i.clone(), ctx)?;
                    }
                    // NOTE: Mutual recursion is fine in OCaml since it's all tail recursive, but
                    // not in Rust.
                    loop {
                        // The same for pure terms (knht)
                        match *t {
                            Constr::App(ref o) => {
                                let (ref a, ref b) = **o;
                                self.append(e.mk_clos_vect(&info.set, b, ctx)?);
                                t = a;
                            },
                            Constr::Case(ref o) => {
                                let (_, _, ref a, _) = **o;
                                self.push(StackMember::CaseT(o, e.clone(&info.set) /* expensive */,
                                                             i.clone()));
                                t = a;
                            },
                            Constr::Fix(_) => { // laziness
                                // FIXME: Are we creating a term here and then immediately
                                // destroying it?
                                m = SCow::Owned(e.mk_clos2(&info.set, t, ctx)?);
                                break; // knh
                            },
                            Constr::Cast(ref o) => {
                                let (_, _, ref a) = **o;
                                t = a;
                            },
                            Constr::Rel(n) => {
                                // TODO: Might know n is NonZero if it's been typechecked?
                                let n = Idx::new(NonZero::new(n).ok_or(IdxError::from(NoneError))?)?;
                                m = SCow::Owned(e.clos_rel(&info.set, n, ctx)?);
                                break; // knh
                            },
                            Constr::Proj(_) => { // laziness
                                // FIXME: Are we creating a term here and then immediately
                                // destroying it?
                                m = SCow::Owned(e.mk_clos2(&info.set, t, ctx)?);
                                break; // knh
                            },
                            Constr::Lambda(_) | Constr::Prod(_) | Constr::Construct(_) |
                            Constr::CoFix(_) | Constr::Ind(_) | Constr::LetIn(_) |
                            Constr::Const(_) | /*Constr::Var(_) | Constr::Evar(_) |
                            Constr::Meta(_) | */Constr::Sort(_) =>
                                return Ok(e.mk_clos2(&info.set, t, ctx)?),
                        }
                    }
                },
                FTerm::App(ref a, ref b) => {
                    if let SCow::Borrowed(m) = m {
                        // NOTE: We probably only want to bother updating this reference if it's
                        // shared, right?
                        self.update(&mut info.set, m, i.clone(), ctx)?;
                    }
                    self.append(clone_vec(b, &info.set) /* expensive */);
                    m = SCow::Borrowed(a);
                },
                FTerm::Case(o, ref p, ref t, ref br) => {
                    if let SCow::Borrowed(m) = m {
                        // NOTE: We probably only want to bother updating this reference if it's
                        // shared, right?
                        self.update(&mut info.set, m, i.clone(), ctx)?;
                    }
                    self.push(StackMember::Case(o, p.clone(&info.set),
                                                clone_vec(br, &info.set) /* expensive */,
                                                i.clone()));
                    m = SCow::Borrowed(t);
                },
                FTerm::CaseT(o, ref t, ref env) => {
                    if let SCow::Borrowed(m) = m {
                        // NOTE: We probably only want to bother updating this reference if it's
                        // shared, right?
                        self.update(&mut info.set, m, i.clone(), ctx)?;
                    }
                    self.push(StackMember::CaseT(o, env.clone(&info.set) /* expensive */,
                                                 i.clone()));
                    m = SCow::Borrowed(t);
                },
                FTerm::Fix(o, n, _) => {
                    let Fix(Fix2(ref ri, _), _) = **o;
                    // FIXME: Verify that ri[n] in bounds is checked at some point during
                    // typechecking.  If not, we must check for it here (we never produce terms
                    // that should make it fail the bounds check provided that ri and bds have the
                    // same length).
                    // TODO: Verify that ri[n] is within usize is checked at some point during
                    // typechecking.
                    let n = usize::try_from(ri[n]).map_err(IdxError::from)?;
                    let m_ = m.clone(&info.set);
                    let m__ = m_.clone(&info.set);
                    match self.get_nth_arg(&mut info.set, m__, n, ctx)? {
                        Some((pars, arg)) => {
                            self.push(StackMember::Fix(m_, pars, i.clone()));
                            m = SCow::Owned(arg);
                        },
                        None => return Ok(m_),
                    }
                },
                FTerm::Cast(ref t, _, _) => {
                    m = SCow::Borrowed(t);
                },
                FTerm::Proj(p, b, ref c) => {
                    // DELTA
                    if info.flags.contains(Reds::DELTA) {
                        // NOTE: Both NotFound and an anomaly would usually be exceptions here,
                        // but it's not clear to me whether typechecking necessarily catches this
                        // error, especially since the env can presumably be mutated after
                        // typechecking.  So I'm choosing not to panic on either lookup failure or
                        // not finding a projection.  I'm open to changing this!
                        let pb = globals.lookup_projection(p)
                                        .ok_or(RedError::NotFound)??;
                        if let SCow::Borrowed(m) = m {
                            // NOTE: We probably only want to bother updating this reference if
                            // it's shared, right?
                            self.update(&mut info.set, m, i.clone(), ctx)?;
                        }
                        // TODO: Verify that npars and arg being within usize is checked at some
                        // point during typechecking.
                        let npars = usize::try_from(pb.npars).map_err(IdxError::from)?;
                        let arg = usize::try_from(pb.arg).map_err(IdxError::from)?;
                        self.push(StackMember::Proj(npars, arg, p, b, i.clone()));
                        m = SCow::Borrowed(c);
                    } else {
                        return Ok(m.clone(&info.set))
                    }
                },

                // cases where knh stops
                FTerm::Flex(_) | FTerm::LetIn(_, _, _, _) | FTerm::Construct(_) |
                /*FTerm::Evar(_) |*/
                FTerm::CoFix(_, _, _) | FTerm::Lambda(_, _, _) | FTerm::Rel(_) | FTerm::Atom(_) |
                FTerm::Ind(_) | FTerm::Prod(_, _, _) => return Ok(m.clone(&info.set)),
            }
        }
    }

    /// The same for pure terms
    ///
    /// Note: m must be typechecked beforehand!
    fn knht<'r, 'g>(&mut self, info: &mut ClosInfos<'id, 'a, 'b>, globals: &Globals<'g>,
                    env: &Subs<FConstr<'id, 'a, 'b>>, mut t: &'b Constr,
                    ctx: Context<'id, 'a, 'b>, i: I, s: S) -> RedResult<FConstr<'id, 'a, 'b>>
        where 'g: 'b, S: Clone, I: Clone,
    {
        loop {
            match *t {
                Constr::App(ref o) => {
                    let (ref a, ref b) = **o;
                    self.append(env.mk_clos_vect(&info.set, b, ctx)?);
                    t = a;
                },
                Constr::Case(ref o) => {
                    let (_, _, ref a, _) = **o;
                    self.push(StackMember::CaseT(o, env.clone(&info.set) /* expensive */,
                                                 i.clone()));
                    t = a;
                },
                Constr::Fix(_) => { // laziness
                    // FIXME: Are we creating a term here and then immediately
                    // destroying it?
                    let t = env.mk_clos2(&info.set, t, ctx)?;
                    return self.knh(info, globals, t, ctx, i, s)
                },
                Constr::Cast(ref o) => {
                    let (_, _, ref a) = **o;
                    t = a;
                },
                Constr::Rel(n) => {
                    // TODO: Might know n is NonZero if it's been typechecked?
                    let n = Idx::new(NonZero::new(n).ok_or(IdxError::from(NoneError))?)?;
                    let t = env.clos_rel(&info.set, n, ctx)?;
                    return self.knh(info, globals, t, ctx, i, s)
                },
                Constr::Proj(_) => { // laziness
                    // FIXME: Are we creating a term here and then immediately
                    // destroying it?
                    let t = env.mk_clos2(&info.set, t, ctx)?;
                    return self.knh(info, globals, t, ctx, i, s)
                },
                Constr::Lambda(_) | Constr::Prod(_) | Constr::Construct(_) |
                Constr::CoFix(_) | Constr::Ind(_) | Constr::LetIn(_) |
                Constr::Const(_) | /*Constr::Var(_) | Constr::Evar(_) |
                Constr::Meta(_) | */Constr::Sort(_) => return Ok(env.mk_clos2(&info.set, t, ctx)?),
            }
        }
    }

    /// Computes a weak head normal form from the result of knh.
    ///
    /// Note: m must be typechecked beforehand!
    pub fn knr<'r, 'g>(&mut self, info: &'r mut ClosInfos<'id, 'a, 'b>,
                       globals: &'r Globals<'g>,
                       mut m: FConstr<'id, 'a, 'b>,
                       ctx: Context<'id, 'a, 'b>, i: I, s: S) -> RedResult<FConstr<'id, 'a, 'b>>
        where 'g: 'b, S: Clone, I: Clone,
    {
        loop {
            let t = if let Some(t) = m.fterm(&info.set) { t } else { return Ok(m) };
            match *t {
                FTerm::Lambda(ref tys, f, ref e) if info.flags.contains(Reds::BETA) => {
                    let e = e.clone(&info.set); /* expensive */
                    match self.get_args(&mut info.set, tys, f, e, ctx)? {
                        Application::Full(e) => {
                            // Mutual tail recursion is fine in OCaml, but not Rust.
                            m = self.knht(info, globals, &e, f, ctx, i.clone(), s.clone())?;
                        },
                        Application::Partial(lam) => return Ok(lam),
                    }
                },
                FTerm::Flex(rf) if info.flags.contains(Reds::DELTA) => {
                    let v = match Infos::ref_value_cache(&info.set, &mut info.rels, &mut info.tab,
                                                         globals, rf, ctx)? {
                        Some(v) => {
                            // TODO: Consider somehow keeping a reference alive here (maybe by
                            // allocating the term in an arena).  This is the only place (I
                            // believe) where we'd want to call knh with something that wasn't
                            // already owned, but currently we can't for lifetime reasons; the
                            // arena would fix that, but it seems a bit silly to have a special
                            // arena just for top-level constant terms.  So let's see what the
                            // performance impact actually is.
                            //
                            // (Also perhaps worth noting: it's not entirely clear to me whether
                            // this borrowck error is flagging anything real or not.  To figure
                            // that out we'd have to inspect the stack machine some more to see
                            // whether there could be any updates left by the time tabs or rels
                            // needed to be accessed mutably again; knh itself only needs a few
                            // things in infos to be borrowed mutably, none of which are used by
                            // ref_value_cache.  If that is indeed the case, we might be able to
                            // refactor to let update lifetimes live only for the length of the
                            // knh function call, or something).
                            v.clone(&info.set)
                        },
                        None => {
                            m.set_norm(&mut info.set);
                            return Ok(m)
                        }
                    };
                    // Mutual tail recursion is fine in OCaml, but not Rust.
                    m = self.knh(info, globals, v, ctx, i.clone(), s.clone())?;
                },
                FTerm::Construct(o) if info.flags.contains(Reds::IOTA) => {
                    let c = ((*o).0).0.idx;
                    let m_ = m.clone(&info.set);
                    let (depth, mut args) = self.strip_update_shift_app(&mut info.set,
                                                                        m_, ctx)?;
                    let shead = if let Some(shead) = self.pop() { shead } else {
                        *self = args;
                        return Ok(m)
                    };
                    match shead {
                        StackMember::Case(o, _, mut br, _) => {
                            let (ref ci, _, _, _) = **o;
                            // TODO: Verify that this is checked at some point during typechecking.
                            let npar = usize::try_from(ci.npar).map_err(IdxError::from)?;
                            args.drop_parameters(&info.set, depth, npar, ctx)?;
                            // TODO: Verify that this is checked at some point during typechecking.
                            let c = usize::try_from(c).map_err(IdxError::from)?;
                            self.extend(args.0.into_iter());
                            // FIXME: Verify that after typechecking, c > 0.
                            m = br.remove(c - 1);
                        },
                        StackMember::CaseT(o, env, i) => {
                            let (ref ci, _, _, ref br) = **o;
                            // TODO: Verify that this is checked at some point during typechecking.
                            let npar = usize::try_from(ci.npar).map_err(IdxError::from)?;
                            args.drop_parameters(&info.set, depth, npar, ctx)?;
                            // TODO: Verify that this is checked at some point during typechecking.
                            let c = usize::try_from(c).map_err(IdxError::from)?;
                            self.extend(args.0.into_iter());
                            // Mutual tail recursion is fine in OCaml, but not Rust.
                            // FIXME: Verify that after typechecking, c > 0.
                            m = self.knht(info, globals, &env, &br[c - 1], ctx, i, s.clone())?;
                        },
                        StackMember::Fix(fx, par, i) => {
                            let rarg = m.fapp_stack_mut(&mut info.set, &mut args, ctx)?;
                            // makes a Vec, but not that expensive.
                            self.append(vec![rarg]);
                            self.extend(par.0.into_iter());
                            let (fxe, fxbd) = fx.fterm(&info.set)
                                .expect("Tried to lift a locked term")
                                .contract_fix_vect(&info.set, ctx)?;
                            // Mutual tail recursion is fine in OCaml, but not Rust.
                            m = self.knht(info, globals, &fxe, fxbd, ctx, i, s.clone())?;
                        },
                        StackMember::Proj(n, m_, _, _, i) => {
                            args.drop_parameters(&info.set, depth, n, ctx)?;
                            let rarg = args.project_nth_arg(m_);
                            // Mutual tail recursion is fine in OCaml, but not Rust.
                            m = self.knh(info, globals, rarg, ctx, i, s.clone())?;
                        },
                        _ => {
                            // It was fine on the stack before, so it should be fine now.
                            self.0.push(shead);
                            self.extend(args.0.into_iter());
                            return Ok(m);
                        },
                    }
                },
                FTerm::CoFix(_, _, _) if info.flags.contains(Reds::IOTA) => {
                    let m_ = m.clone(&info.set);
                    let (_, mut args) = self.strip_update_shift_app(&mut info.set, m_, ctx)?;
                    match self.last() {
                        Some(&StackMember::Case(_, _, _, _)) |
                        Some(&StackMember::CaseT(_, _, _)) => {
                            let (fxe,fxbd) = m.fterm(&info.set)
                                .expect("Tried to lift a locked term")
                                .contract_fix_vect(&info.set, ctx)?;
                            self.extend(args.0.into_iter());
                            // Mutual tail recursion is fine in OCaml, but not Rust.
                            m = self.knht(info, globals, &fxe, fxbd, ctx, i.clone(), s.clone())?;
                        },
                        Some(_) => {
                            self.extend(args.0.into_iter());
                            return Ok(m);
                        },
                        None => {
                            *self = args;
                            return Ok(m);
                        }
                    }
                },
                FTerm::LetIn(o, ref v, _, ref e) if info.flags.contains(Reds::ZETA) => {
                    let (_, _, _, ref bd) = **o;
                    let mut e = e.clone(&info.set); // expensive
                    // makes a Vec, but not that expensive.
                    e.cons(vec![v.clone(&info.set)])?;
                    // Mutual tail recursion is fine in OCaml, but not Rust.
                    m = self.knht(info, globals, &e, bd, ctx, i.clone(), s.clone())?;
                },
                _ => return Ok(m)
            }
        }
    }

    /// Computes the weak head normal form of a term
    ///
    /// Note: m must be typechecked beforehand!
    pub fn kni<'r, 'g>(&'r mut self, info: &mut ClosInfos<'id, 'a, 'b>,
                       globals: &'r Globals<'g>,
                       m: FConstr<'id, 'a, 'b>,
                       ctx: Context<'id, 'a, 'b>, i: I, s: S) -> RedResult<FConstr<'id, 'a, 'b>>
        where 'g: 'b, S: Clone, I: Clone,
    {
        let hm = self.knh(info, globals, m, ctx, i.clone(), s.clone())?;
        self.knr(info, globals, hm, ctx, i, s)
    }

    fn kh<'r, 'g>(&mut self, info: &'r mut ClosInfos<'id, 'a, 'b>, globals: &'r Globals<'g>,
                  v: FConstr<'id, 'a, 'b>,
                  ctx: Context<'id, 'a, 'b>, i: I, s: S) -> RedResult<FConstr<'id, 'a, 'b>>
        where 'g: 'b, S: Clone, I: Clone,
    {
        Ok(self.kni(info, globals, v, ctx, i, s)?
               .fapp_stack_mut(&mut info.set, self, ctx)?)
    }


    /// [whd_stack] performs weak head normalization in a given stack. It
    /// stops whenever a reduction is blocked.
    /// Note: v must be typechecked beforehand!
    pub fn whd_stack<'r, 'g>(&mut self, info: &'r mut ClosInfos<'id, 'a, 'b>,
                             globals: &'r Globals<'g>,
                             v: FConstr<'id, 'a, 'b>,
                             ctx: Context<'id, 'a, 'b>, i: I, s: S) -> RedResult<FConstr<'id, 'a, 'b>>
        where 'g: 'b, S: Clone, I: Clone,
    {
        let k = self.kni(info, globals, v, ctx, i, s)?;
        // expensive -- we avoid a bit of the work by not cloning the stack, but in general we need
        // to clone all of its contents when we zip up the remaining terms, if there are any
        // updates.
        // TODO: See if this can be optimized further--e.g. maybe we can avoid zipping if we know
        // we don't have any updates?
        // TODO: Maybe there's a clever way FTerms can "point into the stack" which would allow us
        // to avoid this step entirely...
        k.fapp_stack(&mut info.set, self, ctx)?; // to unlock Zupdates!
        Ok(k)
    }
}

impl<'id, 'a, 'b> FTerm<'id, 'a, 'b> {
    /// Do not call this function unless tys.len() ≥ 1.
    pub fn dest_flambda<F>(set: &Set<'id>,
                           clos_fun: F,
                           tys: &[MRef<'b, (Name, Constr, Constr)>],
                           b: &'b Constr,
                           e: &Subs<FConstr<'id, 'a, 'b>>,
                           ctx: Context<'id, 'a, 'b>) ->
        IdxResult<(Name, FConstr<'id, 'a, 'b>, FConstr<'id, 'a, 'b>)>
        where F: Fn(&Subs<FConstr<'id, 'a, 'b>>, &Set<'id>,
                    &'b Constr, Context<'id, 'a, 'b>) -> IdxResult<FConstr<'id, 'a, 'b>>,
    {
        // FIXME: consider using references to slices for FTerm::Lambda arguments instead of Vecs.
        // That would allow us to avoid cloning tys here.  However, this might not matter if it
        // turns out the uses of dest_flambda are inherently wasteful.
        // UPDATE: It turns out get_args would also probably benefit from FTerm::Lambda using
        // slices or pointers.
        // FIXME: If we do for some reason stick with vectors, no need to convert and then pop...
        // can just convert the slice.  Might make a vector size difference, if nothing else.
        let mut tys = tys.to_vec(); // expensive
        let o = tys.pop().expect("Should not call dest_flambda with tys.len() = 0");
        let (ref na, ref ty, _) = **o;
        let ty = clos_fun(e, set, ty, ctx)?;
        let mut e = e.clone(set); /* expensive */
        e.lift()?;
        Ok((na.clone(), ty, if tys.len() == 0 {
            clos_fun(&e, set, &b, ctx)?
        } else {
            FConstr {
                norm: Cell::new(RedState::Cstr),
                term: Cell::new(Some(ctx.term_arena.alloc(FTerm::Lambda(tys, b, e))))
            }
        }))
    }

    /// Iota reduction: expansion of a fixpoint.
    ///
    /// Given a fixpoint and a substitution, returns the corresponding
    /// fixpoint body, and the substitution in which it should be
    /// evaluated: its first variables are the fixpoint bodies
    ///
    /// FCLOS(fix Fi {F0 := T0 .. Fn-1 := Tn-1}, S)
    ///    -> (S. FCLOS(F0,S) . ... . FCLOS(Fn-1,S), Ti)
    ///
    /// (does not deal with FLIFT)
    ///
    /// Must be passed a FTerm::Fix or FTerm::CoFix.
    /// Also, the term it is passed must be typechecked.
    fn contract_fix_vect(&self, set: &Set<'id>, ctx: Context<'id, 'a, 'b>) ->
        IdxResult<(Subs<FConstr<'id, 'a, 'b>>, &'b Constr)>
    {
        // TODO: This function is *hugely* wasteful.  It allocates a gigantic number of potential
        // fixpoint substitutions every time it's called, even though most of them almost certainly
        // will not be applied (in cases where there's lots of mutually inductive fixpoints).  Not
        // only that, the fixpoints are almost the same each time (up to the current environment),
        // so it makes almost no sense to keep reallocating them!  For now we just swallow it, but
        // there has to be a better way.
        // NOTE: It's certainly the case that if we *do* needs to use a Fixpoint substitution, it
        // lives somewhere in the Constr.  So we might at least be able to save the irritating
        // special casing of Fix and CoFix keeping the index separate by reusing the existing
        // reference.
        // FIXME: This is a very good example of where sharing subs allocations (or trying to share
        // them) could make a big difference, since we copy the old one indiscriminately to all the
        // (potentially) substituted terms.
        match *self {
            FTerm::Fix(o, i, ref env_) => {
                // NOTE: i = index of this function into mutually recursive block
                //       bds = function bodies of the mutually recursive block
                let Fix(_, PRec(_, _, ref bds)) = **o;
                let mut env = env_.clone(set); // expensive
                // FIXME: If we can use (boxed?) iterators rather than slices, can we avoid copying
                // a big vector here?  How important is the cheap at-index access during
                // substitution, considering that we have to iterate through the list at least once
                // anyway to create the vector in the first place?
                // expensive: makes a Vec.
                env.cons((0..bds.len()).map( |j| {
                    let env = env_.clone(set); // expensive
                    FConstr {
                        norm: Cell::new(RedState::Cstr),
                        term: Cell::new(Some(ctx.term_arena.alloc(FTerm::Fix(o, j, env)))),
                    }
                }).collect())?;
                // FIXME: Verify that bds[i] in bounds is checked at some point during
                // typechecking.  If not, we must check for it here.
                Ok((env, &bds[i]))
            },
            FTerm::CoFix(o, i, ref env_) => {
                let CoFix(_, PRec(_, _, ref bds)) = **o;
                let mut env = env_.clone(set); // expensive
                // FIXME: If we can use (boxed?) iterators rather than slices, can we avoid copying
                // a big vector here?  How important is the cheap at-index access during
                // substitution, considering that we have to iterate through the list at least once
                // anyway to create the vector in the first place?
                // expensive: makes a Vec.
                env.cons((0..bds.len()).map(|j| {
                    let env = env_.clone(set); // expensive
                    FConstr {
                        norm: Cell::new(RedState::Cstr),
                        term: Cell::new(Some(ctx.term_arena.alloc(FTerm::CoFix(o, j, env)))),
                    }
                }).collect())?;
                // FIXME: Verify that bds[i] in bounds is checked at some point during
                // typechecking.  If not, we must check for it here.
                Ok((env, &bds[i]))
            },
            _ => panic!("contract_fix_vect must be passed FTerm::Fix or FTerm::Cofix"),
        }
    }
}

impl Constr {
    /// Note: v must be typechecked beforehand!
    fn of_fconstr_lift<'id, 'a, 'b>(v: &FConstr<'id, 'a, 'b>, set: &mut Set<'id>, lfts: &Lift,
                           ctx: Context<'id, 'a, 'b>) -> IdxResult<Constr> {
        // In general, it might be nice to make this function tail recursive (by using an explicit
        // stack) rather than having confusing mutual recursion between of_fconstr_lift and
        // to_constr.
        if !lfts.is_id() { return v.to_constr(set, Constr::of_fconstr_lift, lfts, ctx) }
        let term = if let Some(v) = v.fterm(set) { v } else {
            return v.to_constr(set, Constr::of_fconstr_lift, lfts, ctx);
        };
        match *term {
            FTerm::Clos(t, ref env) if env.is_id() => Ok(t.clone()),
            FTerm::Lambda(ref tys, f, ref e) if e.is_id() => {
                // compose_lam (List.rev tys) f
                // NOTE: Instead of recursively reconstructing the old Lambda term (as the OCaml
                // implementation does), we assume that the last entry in the tys array (or just f,
                // if empty) is already the term we want.  This should be true for us here because
                // reduction only ever pops terms off the head of a lambda sequence, unless it
                // decides to perform a substitution.  But because the substitution is the
                // identity, we shouldn't have touched the interior term.
                // TODO: Verify the above.  The critical bit seems to be: if you do ever create a
                // new Lambda term, you are either converting directly from a Constr, or you are
                // either lifting or shifting.  The only apparent exceptions are in get_args, which
                // sometimes reuses its argument environment, but if you look at the places it's
                // called you'll note that it always starts with the environment of the same
                // FLambda, so the new FLambdas it creates should preserve the properties of the
                // other ways FLambdas can be constructed.
                // TODO: Consider performing the following assertion to check our assumption: the
                // body of tys.first() should be identical to e (and presumably the body of each
                // other element of the array is a Lambda reference to the previous element, but
                // that is less subtle to verify by inspecting the code).
                Ok(match tys.last() {
                    None => f.clone(),
                    Some(&o) => Constr::Lambda(o.clone()),
                })
            },
            FTerm::CaseT(o, ref c, ref e) if e.is_id() => {
                // FIXME: Make this tail-recursive / use an explicit stack?
                // FIXME: Is there any way to determine that the interior term hasn't been touched?
                // If so, can we reuse the old case allocation?
                let (ref ci, ref p, _, ref b) = **o;
                let c = Constr::of_fconstr_lift(c, set, lfts, ctx)?;
                Ok(Constr::Case(ORef(Arc::from((ci.clone(), p.clone(), c, b.clone())))))
            },
            FTerm::Fix(o, i, ref e) if e.is_id() => {
                let Fix(Fix2(ref reci, _), ref p) = **o;
                // TODO: If we can figure out how to cache this we may be able to avoid
                // allocating a fresh Arc.
                // FIXME: We know (assuming reasonable FTerm construction) that i fits in an
                // i64 if it was created directly from a Constr.  We also know that i fits in
                // an isize if it was created by unfolding a Fix, since all the FTerm::Fix
                // terms we derive have i < reci.len(), and reci is a vector; Rust guarantees
                // that vector lengths (in bytes, actually!) fit in an isize.  What remains to
                // be determined is whether isize is always guaranteed to fit in an i64.  If
                // that's true, this cast necessarily succeeds.
                Ok(Constr::Fix(ORef(Arc::from(Fix(Fix2(reci.clone(), i as i64), p.clone())))))
            },
            FTerm::CoFix(o, i, ref e) if e.is_id() => {
                let CoFix(_, ref p) = **o;
                // TODO: If we can figure out how to cache this we may be able to avoid
                // allocating a fresh Arc.
                // FIXME: We know (assuming reasonable FTerm construction) that i fits in an
                // i64 if it was created directly from a Constr.  We also know that i fits in
                // an isize if it was created by unfolding a CoFix, since all the FTerm::CoFix
                // terms we derive have i < reci.len(), and reci is a vector; Rust guarantees
                // that vector lengths (in bytes, actually!) fit in an isize.  What remains to
                // be determined is whether isize is always guaranteed to fit in an i64.  If
                // that's true, this cast necessarily succeeds.
                Ok(Constr::CoFix(ORef(Arc::from(CoFix(i as i64, p.clone())))))
            },
            _ => v.to_constr(set, Constr::of_fconstr_lift, lfts, ctx)
        }
    }

    /// This function defines the correspondance between constr and
    /// fconstr. When we find a closure whose substitution is the identity,
    /// then we directly return the constr to avoid possibly huge
    /// reallocation.
    /// Note: v must be typechecked beforehand!
    pub fn of_fconstr<'id, 'a, 'b>(v: &FConstr<'id, 'a, 'b>,
                                   set: &mut Set<'id>,
                                   ctx: Context<'id, 'a, 'b>) -> IdxResult<Constr> {
        let lfts = Lift::id();
        Constr::of_fconstr_lift(v, set, &lfts, ctx)
    }

    pub fn inject<'id, 'a, 'b>(&'b self,
                               set: &Set<'id>,
                               ctx: Context<'id, 'a, 'b>) -> IdxResult<FConstr<'id, 'a, 'b>>
    {
        let env = Subs::id(None);
        env.mk_clos(set, self, ctx)
    }
}

impl<'id, 'a, 'b, T> Infos<'id, 'b, T> {
    fn defined_rels<I>(rel_context: I) -> IdxResult<(u32, VecMap<&'b mut Constr>)>
        where I: Iterator<Item=&'b mut RDecl>
    {
        let mut i = 0u32;
        // TODO: If we had an ExactSizeIterator or something, we would be able to know we were in
        // bounds for usize the entire time and wait to check for u32 overflow until the end.
        let rels: Result<VecMap<_>, _> = rel_context
            .filter_map( |decl| {
                let res = match *decl {
                    RDecl::LocalAssum(_, _) => None,
                    // FIXME: Verify that u32 to usize is always a valid cast.
                    RDecl::LocalDef(_, ref mut body, _) => Some(Ok((i as usize, body))),
                };
                i = match i.checked_add(1) {
                    Some(i) => i,
                    None => return Some(Err(IdxError::from(NoneError))),
                };
                res
            }).collect();
        Ok((i, rels?))
    }

    pub fn create<I>(set: Set<'id>, flgs: Reds, rel_context: I) -> IdxResult<Self>
        where I: Iterator<Item=&'b mut RDecl>
    {
        Ok(Infos {
            set: set,
            flags: flgs,
            rels: Self::defined_rels(rel_context)?,
            tab: KeyTable(HashMap::with_capacity(17)),
        })
    }
}
