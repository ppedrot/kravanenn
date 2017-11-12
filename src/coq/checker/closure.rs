use std::cell::{Cell};
use std::rc::{Rc};
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
    Ind,
    PRec,
    Proj,
    PUniverses,
    RecordBody,
};
use coq::checker::environ::{Env};
use coq::kernel::esubst::{Expr, Idx, IdxError, IdxResult, SubsV as Subs, Lift};
use typed_arena::{Arena};
use core::nonzero::NonZero;
use core::convert::{TryFrom};
use ocaml::de::{Array, ORef};
use std::borrow::{Cow};
use std::mem;

type MRef<'b, T> = &'b ORef<T>;

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

#[derive(Clone,Debug)]
pub enum TableKey<T> {
    ConstKey(T),
    // should not occur
    // VarKey(Id),
    RelKey(Idx),
}

pub enum RedError {
    Idx(IdxError),
    NotFound,
}

impl ::std::convert::From<IdxError> for RedError {
    fn from(e: IdxError) -> Self {
        RedError::Idx(e)
    }
}

pub type RedResult<T> = Result<T, RedError>;

pub struct Context<T> {
    term_arena: Arena<T>,
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
#[derive(Clone,Debug)]
pub struct FConstr<'a, 'b> where 'b: 'a {
    norm: Cell<RedState>,
    term: Cell<Option<&'a FTerm<'a, 'b>>>,
}

#[derive(Clone,Debug)]
pub enum FTerm<'a, 'b> where 'b: 'a {
  Rel(Idx),
  /// Metas and sorts; but metas shouldn't occur in a .vo...
  Atom(&'b Constr),
  Cast(FConstr<'a, 'b>, MRef<'b, (Constr, Cast, Constr)>, FConstr<'a, 'b>),
  Flex(TableKeyC<'b>),
  Ind(MRef<'b, PUniverses<Ind>>),
  Construct(MRef<'b, PUniverses<Cons>>),
  App(FConstr<'a, 'b>, Vec<FConstr<'a, 'b>>),
  Proj(&'b Cst, bool, FConstr<'a, 'b>),
  Fix(MRef<'b, Fix>, Subs<FConstr<'a, 'b>>),
  CoFix(MRef<'b, CoFix>, Subs<FConstr<'a, 'b>>),
  Case(MRef<'b, (CaseInfo, Constr, Constr, Array<Constr>)>, FConstr<'a, 'b>, FConstr<'a, 'b>,
       Vec<FConstr<'a, 'b>>),
  /// predicate and branches are closures
  CaseT(MRef<'b, (CaseInfo, Constr, Constr, Array<Constr>)>, FConstr<'a, 'b>,
        Subs<FConstr<'a, 'b>>),
  Lambda(Vec</*(Name, Constr)*/MRef<'b, (Name, Constr, Constr)>>,
         &'b Constr, Subs<FConstr<'a, 'b>>),
  Prod(MRef<'b, (Name, Constr, Constr)>, FConstr<'a, 'b>, FConstr<'a, 'b>),
  LetIn(MRef<'b, (Name, Constr, Constr, Constr)>,
        FConstr<'a, 'b>, FConstr<'a, 'b>, Subs<FConstr<'a, 'b>>),
  // should not occur
  // | FEvar of existential_key * fconstr array (* why diff from kernel/closure? *)
  /// FLIFT is a delayed shift; allows sharing between 2 lifted copies
  /// of a given term.
  Lift(Idx, FConstr<'a, 'b>),
  /// FCLOS is a delayed substitution applied to a constr
  Clos(&'b Constr, Subs<FConstr<'a, 'b>>),
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
pub enum StackMember<'a, 'b, Inst, Shft> where 'b: 'a {
    App(Vec<FConstr<'a, 'b>>),
    Case(MRef<'b, (CaseInfo, Constr, Constr, Array<Constr>)>, FConstr<'a, 'b>,
         Vec<FConstr<'a, 'b>>, Inst),
    CaseT(MRef<'b, (CaseInfo, Constr, Constr, Array<Constr>)>, Subs<FConstr<'a, 'b>>, Inst),
    Proj(Idx, Idx, &'b Cst, bool, Inst),
    Fix(FConstr<'a, 'b>, Stack<'a, 'b, Inst, Shft>, Inst),
    Shift(Idx, Shft),
    Update(&'a FConstr<'a, 'b>, Inst),
}

/// A [stack] is a context of arguments, arguments are pushed by
/// [append_stack] one array at a time but popped with [decomp_stack]
/// one by one
pub struct Stack<'a, 'b, Inst, Shft>(Vec<StackMember<'a, 'b, Inst, Shft>>) where 'b: 'a;

/// Full stack (all operations are allowed).
pub type FStack<'a, 'b> = Stack<'a, 'b, (), ()>;

/// Purely applicative stack (only Apps are allowed).
pub type AStack<'a, 'b> = Stack<'a, 'b, !, !>;

/// Applicative + shifts (only Shift and App are allowed).
pub type SStack<'a, 'b> = Stack<'a, 'b, !, ()>;

/// The result of trying to perform beta reduction.
enum Application<T> {
    /// Arguments are fully applied; this is the corresponding substitution.
    Full(Subs<T>),
    /// Arguments are partially applied; this is the corresponding thunk.
    Partial(T),
}

impl RedState {
    pub fn neutr(&self) -> Self {
        match *self {
            RedState::Whnf => RedState::Whnf,
            RedState::Norm => RedState::Whnf,
            RedState::Red => RedState::Red,
            RedState::Cstr => RedState::Red,
        }
    }
}

impl<'a, 'b> FConstr<'a, 'b> {
    pub fn fterm(&self) -> Option<&'a FTerm<'a, 'b>> {
        self.term.get()
    }

    pub fn set_norm(&self) {
        self.norm.set(RedState::Norm)
    }

    pub fn update(&self, no: RedState, term: Option<&'a FTerm<'a, 'b>>) {
        // Could issue a warning if no is still Red, pointing out that we lose sharing.
        self.norm.set(no);
        self.term.set(term);
    }

    fn lft(&self, mut n: Idx, ctx: &'a Context<FTerm<'a, 'b>>) -> IdxResult<Self> {
        let mut ft = self;
        loop {
            match *ft.fterm().expect("Tried to lift a locked term") {
                FTerm::Ind(_) | FTerm::Construct(_)
                | FTerm::Flex(TableKey::ConstKey(_)/* | VarKey _*/) => return Ok(self.clone()),
                FTerm::Rel(i) => return Ok(FConstr {
                    norm: Cell::new(RedState::Norm),
                    term: Cell::new(Some(ctx.term_arena.alloc(FTerm::Rel(i.checked_add(n)?)))),
                }),
                FTerm::Lambda(ref tys, f, ref e) => {
                    let mut e = e.clone(); // expensive
                    e.shift(n)?;
                    return Ok(FConstr {
                        norm: Cell::new(RedState::Cstr),
                        term: Cell::new(Some(
                                ctx.term_arena.alloc(FTerm::Lambda(tys.clone(), // expensive
                                                                   f, e)))),
                    })
                },
                FTerm::Fix(fx, ref e) => {
                    let mut e = e.clone(); // expensive
                    e.shift(n)?;
                    return Ok(FConstr {
                        norm: Cell::new(RedState::Cstr),
                        term: Cell::new(Some(ctx.term_arena.alloc(FTerm::Fix(fx, e)))),
                    })
                },
                FTerm::CoFix(cfx, ref e) => {
                    let mut e = e.clone(); // expensive
                    e.shift(n)?;
                    return Ok(FConstr {
                        norm: Cell::new(RedState::Cstr),
                        term: Cell::new(Some(ctx.term_arena.alloc(FTerm::CoFix(cfx, e)))),
                    })
                },
                FTerm::Lift(k, ref m) => {
                    n = n.checked_add(k)?;
                    ft = m;
                },
                _ => return Ok(FConstr {
                    norm: ft.norm.clone(),
                    term: Cell::new(Some(ctx.term_arena.alloc(FTerm::Lift(n, ft.clone())))),
                })
            }
        }
    }

    /// Lifting specialized to the case where n = 0.
    fn lft0(&self, ctx: &'a Context<FTerm<'a, 'b>>) -> IdxResult<Self> {
        match *self.fterm().expect("Tried to lift a locked term") {
            FTerm::Ind(_) | FTerm::Construct(_)
            | FTerm::Flex(TableKey::ConstKey(_)/* | VarKey _*/) => Ok(self.clone()),
            FTerm::Rel(_) => Ok(FConstr {
                norm: Cell::new(RedState::Norm),
                term: self.term.clone(),
            }),
            FTerm::Lambda(_, _, _) | FTerm::Fix(_, _) | FTerm::CoFix(_, _) => Ok(FConstr {
                norm: Cell::new(RedState::Cstr),
                term: self.term.clone(),
            }),
            FTerm::Lift(k, ref m) => m.lft(k, ctx),
            _ => Ok(self.clone())
        }
    }

    /// The inverse of mk_clos_deep: move back to constr
    fn to_constr<F>(&self, constr_fun: F, lfts: &Lift,
                    ctx: &'a Context<FTerm<'a, 'b>>) -> IdxResult<Constr>
        where F: Fn(&FConstr<'a, 'b>, &Lift, &'a Context<FTerm<'a, 'b>>) -> IdxResult<Constr>,
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
            match *v.fterm().expect("Tried to lift a locked term!") {
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
                    let a = constr_fun(a, &lfts, ctx)?;
                    let b = constr_fun(b, &lfts, ctx)?;
                    return Ok(Constr::Cast(ORef(Rc::from((a, k.1, b)))))
                },
                FTerm::Flex(TableKey::ConstKey(c)) => return Ok(Constr::Const(c.clone())),
                FTerm::Ind(op) => return Ok(Constr::Ind(op.clone())),
                FTerm::Construct(op) => return Ok(Constr::Construct(op.clone())),
                FTerm::Case(ci, ref p, ref c, ref ve) => {
                    let (ref ci, _, _, _) = **ci;
                    let p = constr_fun(p, &lfts, ctx)?;
                    let c = constr_fun(c, &lfts, ctx)?;
                    // expensive -- allocates a Vec
                    let ve: Result<Vec<_>, _> = ve.iter()
                        .map( |v| constr_fun(v, &lfts, ctx) )
                        .collect();
                    return Ok(Constr::Case(ORef(Rc::from((ci.clone(), p, c,
                                                          Array(Rc::from(ve?)))))))
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
                    let p = e.mk_clos2(p, ctx)?;
                    let p = constr_fun(&p, &lfts, ctx)?;
                    let c = constr_fun(c, &lfts, ctx)?;
                    // expensive -- allocates a Vec
                    let ve: Result<Vec<_>, _> = ve.iter()
                        .map( |t| e.mk_clos(t, ctx))
                        .map( |v| constr_fun(&v?, &lfts, ctx) )
                        .collect();
                    return Ok(Constr::Case(ORef(Rc::from((ci.clone(), p, c,
                                                          Array(Rc::from(ve?)))))))
                },
                FTerm::Fix(o, ref e) => {
                    // FIXME: The recursion here seems like it potentially wastes a lot of work
                    // converting Constrs to FTerms and back... same with CoFix below, and possibly
                    // CaseT above to some extent.  Also, we probably prematurely allocate a few
                    // times, since this is one of the cases where we only need references to
                    // FTerms and FConstrs rather than full-fledged FTerms / FConstrs.
                    let Fix(ref op, PRec(ref lna, ref tys, ref bds)) = **o;
                    // expensive, makes a Vec
                    let ftys: Result<Vec<_>, _> = tys.iter()
                        .map( |t| e.mk_clos(t, ctx))
                        .map( |t| constr_fun(&t?, &lfts, ctx))
                        .collect();
                    // Note: I believe the length should always be nonzero here, but I'm not 100%
                    // sure.  For now, we separate the two cases to avoid failing outright in the
                    // zero case (it would also save useless work, but our implementation won't
                    // let you try to lift by zero so this is an academic point).  This also
                    // applies to CoFix below.

                    // expensive, makes a Vec
                    let fbds: Result<Vec<_>, _> = if let Some(n) = NonZero::new(bds.len()) {
                        let n = Idx::new(n)?;
                        let mut e = e.clone(); // expensive, but shouldn't outlive this block.
                        e.liftn(n)?;
                        // expensive, but shouldn't outlive this block.
                        let mut lfts = lfts.into_owned();
                        lfts.liftn(n)?;
                        bds.iter()
                           .map( |t| e.mk_clos(t, ctx))
                           .map( |t| constr_fun(&t?, &lfts, ctx))
                           .collect()
                    } else {
                        // expensive, makes a Vec
                        bds.iter()
                           .map( |t| e.mk_clos(t, ctx))
                           .map( |t| constr_fun(&t?, &lfts, ctx))
                           .collect()
                    };
                    return Ok(Constr::Fix(ORef(Rc::from(Fix(op.clone(),
                                                            PRec(lna.clone(),
                                                                 Array(Rc::new(ftys?)),
                                                                 Array(Rc::new(fbds?))))))))
                },
                FTerm::CoFix(o, ref e) => {
                    let CoFix(op, PRec(ref lna, ref tys, ref bds)) = **o;
                    // expensive, makes a Vec
                    let ftys: Result<Vec<_>, _> = tys.iter()
                        .map( |t| e.mk_clos(t, ctx))
                        .map( |t| constr_fun(&t?, &lfts, ctx))
                        .collect();
                    // expensive, makes a Vec
                    let fbds: Result<Vec<_>, _> = if let Some(n) = NonZero::new(bds.len()) {
                        let n = Idx::new(n)?;
                        let mut e = e.clone(); // expensive, but shouldn't outlive this block.
                        e.liftn(n)?;
                        // expensive, but shouldn't outlive this block.
                        let mut lfts = lfts.into_owned();
                        lfts.liftn(n)?;
                        bds.iter()
                           .map( |t| e.mk_clos(t, ctx))
                           .map( |t| constr_fun(&t?, &lfts, ctx))
                           .collect()
                    } else {
                        // expensive, makes a Vec
                        bds.iter()
                           .map( |t| e.mk_clos(t, ctx))
                           .map( |t| constr_fun(&t?, &lfts, ctx))
                           .collect()
                    };
                    return Ok(Constr::CoFix(ORef(Rc::from(CoFix(op,
                                                                PRec(lna.clone(),
                                                                     Array(Rc::new(ftys?)),
                                                                     Array(Rc::new(fbds?))))))))
                },
                FTerm::App(ref f, ref ve) => {
                    let f = constr_fun(f, &lfts, ctx)?;
                    // expensive -- allocates a Vec
                    let ve: Result<Vec<_>, _> = ve.iter()
                        .map( |v| constr_fun(v, &lfts, ctx) )
                        .collect();
                    return Ok(Constr::App(ORef(Rc::from((f, Array(Rc::from(ve?)))))))
                },
                FTerm::Proj(p, b, ref c) => {
                    let c = constr_fun(c, &lfts, ctx)?;
                    return Ok(Constr::Proj(ORef(Rc::from((Proj(p.clone(), b), c)))))
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
                        FTerm::dest_flambda(Subs::mk_clos2, tys, b, e, ctx)?;
                    let ty = constr_fun(&ty, &lfts, ctx)?;
                    // expensive, but shouldn't outlive this block.
                    let mut lfts = lfts.into_owned();
                    lfts.lift()?;
                    let bd = constr_fun(&bd, &lfts, ctx)?;
                    return Ok(Constr::Lambda(ORef(Rc::from((na, ty, bd)))))
                },
                FTerm::Prod(o, ref t, ref c) => {
                    let (ref n, _, _) = **o;
                    let t = constr_fun(t, &lfts, ctx)?;
                    // expensive, but shouldn't outlive this block.
                    let mut lfts = lfts.into_owned();
                    lfts.lift()?;
                    let c = constr_fun(c, &lfts, ctx)?;
                    return Ok(Constr::Prod(ORef(Rc::from((n.clone(), t, c)))))
                },
                FTerm::LetIn(o, ref b, ref t, ref e) => {
                    let (ref n, _, _, ref f) = **o;
                    let b = constr_fun(b, &lfts, ctx)?;
                    let t = constr_fun(t, &lfts, ctx)?;
                    let mut e = e.clone(); // expensive, but shouldn't outlive this block.
                    e.lift()?;
                    let fc = e.mk_clos2(f, ctx)?;
                    // expensive, but shouldn't outlive this block.
                    let mut lfts = lfts.into_owned();
                    lfts.lift()?;
                    let fc = constr_fun(&fc, &lfts, ctx)?;
                    return Ok(Constr::LetIn(ORef(Rc::from((n.clone(), b, t, fc)))))
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
                    let fr = env.mk_clos2(t, ctx)?;
                    // TODO: check whether the update here is useful.  If so, we should
                    // slightly change the function definition.
                    // norm_ = ...
                    // let a = constr_fun(a, &lfts, ctx)?;
                    v.update(fr.norm.get(), fr.term.get());
                }
            }
        }
    }

    fn zip<I, S>(&self, stk: &mut Stack<'a, 'b, I, S>,
           ctx: &'a Context<FTerm<'a, 'b>>) -> IdxResult<FConstr<'a, 'b>> {
        let mut m = Cow::Borrowed(self);
        while let Some(s) = stk.pop() {
            match s {
                StackMember::App(args) => {
                    let norm = m.norm.get().neutr();
                    let t = FTerm::App(m.into_owned(), args);
                    m = Cow::Owned(FConstr {
                        norm: Cell::new(norm),
                        term: Cell::new(Some(ctx.term_arena.alloc(t))),
                    });
                },
                StackMember::Case(o, p, br, _) => {
                    let norm = m.norm.get().neutr();
                    let t = FTerm::Case(o, p, m.into_owned(), br);
                    m = Cow::Owned(FConstr {
                        norm: Cell::new(norm),
                        term: Cell::new(Some(ctx.term_arena.alloc(t))),
                    });
                },
                StackMember::CaseT(o, e, _) => {
                    let norm = m.norm.get().neutr();
                    let t = FTerm::CaseT(o, m.into_owned(), e);
                    m = Cow::Owned(FConstr {
                        norm: Cell::new(norm),
                        term: Cell::new(Some(ctx.term_arena.alloc(t))),
                    });
                },
                StackMember::Proj(_, _, p, b, _) => {
                    let norm = m.norm.get().neutr();
                    let t = FTerm::Proj(p, b, m.into_owned());
                    m = Cow::Owned(FConstr {
                        norm: Cell::new(norm),
                        term: Cell::new(Some(ctx.term_arena.alloc(t))),
                    });
                },
                StackMember::Fix(fx, mut par, _) => {
                    // FIXME: This seems like a very weird and convoluted way to do this.
                    let mut v = vec![m.into_owned()];
                    m = Cow::Owned(fx);
                    stk.append(v)?;
                    // mem::swap(stk, &mut par);
                    // NOTE: Since we use a Vec rather than a list, the "head" of our stack is
                    // actually at the end of the Vec.  Therefore, where in the OCaml we perform
                    // par @ stk, here we have reversed par and reversed stk, and perform
                    // stk ++ par (or kst ++ rap).
                    stk.extend(par.0.into_iter());
                },
                StackMember::Shift(n, _) => {
                    m = Cow::Owned(m.lft(n, ctx)?);
                },
                StackMember::Update(rf, _) => {
                    rf.update(m.norm.get(), m.term.get());
                    // TODO: The below is closer to the OCaml implementation, but it doesn't seem
                    // like there's any point in doing it, since we never update m anyway (we do
                    // return it at the end, but we're currently returning an owned FTerm rather
                    // than a shared reference).
                    // m = Cow::Borrowed(rf);
                },
            }
        }
        Ok(m.into_owned())
    }

    pub fn fapp_stack<I, S>(&self, stk: &mut Stack<'a, 'b, I, S>,
                            ctx: &'a Context<FTerm<'a, 'b>>) -> IdxResult<FConstr<'a, 'b>> {
        self.zip(stk, ctx)
    }
}

impl<'a, 'b> Subs<FConstr<'a, 'b>> {
    fn clos_rel(&self, i: Idx, ctx: &'a Context<FTerm<'a, 'b>>) -> IdxResult<FConstr<'a, 'b>> {
        match self.expand_rel(i)? {
            (n, Expr::Val(mt)) => mt.lft(n, ctx),
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
                    v.lft(k, ctx)
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
                 t: &'b Constr) -> IdxResult<FTerm<'a, 'b>> {
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

    /// Optimization: do not enclose variables in a closure.
    /// Makes variable access much faster
    pub fn mk_clos(&self, t: &'b Constr,
                   ctx: &'a Context<FTerm<'a, 'b>>) -> IdxResult<FConstr<'a, 'b>> {
        match *t {
            Constr::Rel(i) => { self.clos_rel(Idx::new(NonZero::new(i)?)?, ctx) },
            Constr::Const(ref c) => Ok(FConstr {
                norm: Cell::new(RedState::Red),
                term: Cell::new(Some(ctx.term_arena.alloc(FTerm::Flex(TableKey::ConstKey(c))))),
            }),
            /* Constr::Meta(_) | Constr::Var(_) | Constr::Evar(_) =>
                unreachable!("Constrs should not be Meta, Var, or Evar"), */
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
                            FTerm::Clos(t, self.clone() /* expensive */))))
            }),
        }
    }

    pub fn mk_clos_vect(&self, v: &'b [Constr],
                        ctx: &'a Context<FTerm<'a, 'b>>) -> IdxResult<Vec<FConstr<'a, 'b>>> {
        // Expensive, makes a vector
        v.into_iter().map( |t| self.mk_clos(t, ctx)).collect()
    }

    /// Translate the head constructor of t from constr to fconstr. This
    /// function is parameterized by the function to apply on the direct
    /// subterms.
    /// Could be used insted of mk_clos.
    pub fn mk_clos_deep<F>(&self, clos_fun: F, t: &'b Constr,
                           ctx: &'a Context<FTerm<'a, 'b>>) -> IdxResult<FConstr<'a, 'b>>
        where F: Fn(&Subs<FConstr<'a, 'b>>,
                    &'b Constr, &'a Context<FTerm<'a, 'b>>) -> IdxResult<FConstr<'a, 'b>>,
    {
        match *t {
            Constr::Rel(_) | Constr::Ind(_) |
            Constr::Const(_) | Constr::Construct(_) |
            // Constr::Var(_) | Constr::Meta(_) | Constr::Evar(_)
            Constr::Sort(_) => self.mk_clos(t, ctx),
            Constr::Cast(ref o) => {
                let (a, b) = {
                    let (ref a, _, ref b) = **o;
                    let a = clos_fun(self, a, ctx)?;
                    let b = clos_fun(self, b, ctx)?;
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
                    let f = clos_fun(self, f, ctx)?;
                    // Expensive, makes a vector
                    let v: Result<_, _> =
                        v.iter().map( |t| clos_fun(self, t, ctx))
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
                let c = clos_fun(self, c, ctx)?;
                Ok(FConstr {
                    norm: Cell::new(RedState::Red),
                    term: Cell::new(Some(ctx.term_arena.alloc(FTerm::Proj(p, b, c)))),
                })
            },
            Constr::Case(ref o) => {
                let c = {
                    let (_, _, ref c, _) = **o;
                    clos_fun(self, c, ctx)?
                };
                let env = self.clone(); // expensive
                Ok(FConstr {
                    norm: Cell::new(RedState::Red),
                    term: Cell::new(Some(ctx.term_arena.alloc(FTerm::CaseT(o, c, env)))),
                })
            },
            Constr::Fix(ref o) => {
                let env = self.clone(); // expensive
                Ok(FConstr {
                    norm: Cell::new(RedState::Cstr),
                    term: Cell::new(Some(ctx.term_arena.alloc(FTerm::Fix(o, env)))),
                })
            },
            Constr::CoFix(ref o) => {
                let env = self.clone(); // expensive
                Ok(FConstr {
                    norm: Cell::new(RedState::Cstr),
                    term: Cell::new(Some(ctx.term_arena.alloc(FTerm::CoFix(o, env)))),
                })
            },
            Constr::Lambda(_) => {
                let env = self.clone(); // expensive
                Ok(FConstr {
                    norm: Cell::new(RedState::Cstr),
                    term: Cell::new(Some(ctx.term_arena.alloc(env.mk_lambda(t)?))),
                })
            },
            Constr::Prod(ref o) => {
                let (t, c) = {
                    let (_, ref t, ref c) = **o;
                    let t = clos_fun(self, t, ctx)?;
                    // expensive, but doesn't outlive this block.
                    let mut env = self.clone();
                    env.lift()?;
                    let c = clos_fun(&env, c, ctx)?;
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
                    let b = clos_fun(self, b, ctx)?;
                    let t = clos_fun(self, t, ctx)?;
                    (b, t)
                };
                let env = self.clone(); // expensive
                Ok(FConstr {
                    norm: Cell::new(RedState::Red),
                    term: Cell::new(Some(ctx.term_arena.alloc(FTerm::LetIn(o,
                                                              b, t, env)))),
                })
            },
        }
    }

    /// A better mk_clos?
    pub fn mk_clos2(&self, t: &'b Constr,
                    ctx: &'a Context<FTerm<'a, 'b>>) -> IdxResult<FConstr<'a, 'b>> {
        self.mk_clos_deep((Subs::<FConstr>::mk_clos), t, ctx)
    }
}

impl<'a, 'b, I, S> ::std::ops::Deref for Stack<'a, 'b, I, S> {
    type Target = Vec<StackMember<'a, 'b, I, S>>;
    fn deref(&self) -> &Vec<StackMember<'a, 'b, I, S>> {
        &self.0
    }
}

impl<'a, 'b, I, S> ::std::ops::DerefMut for Stack<'a, 'b, I, S> {
    fn deref_mut(&mut self) -> &mut Vec<StackMember<'a, 'b, I, S>> {
        &mut self.0
    }
}

impl<'a, 'b, I, S> Stack<'a, 'b, I, S> {
    fn push(&mut self, o: StackMember<'a, 'b, I, S>) -> IdxResult<()> {
        self.0.push(o);
        Ok(())
    }

    pub fn append(&mut self, mut v: Vec<FConstr<'a, 'b>>) -> IdxResult<()> {
        if v.len() == 0 { return Ok(()) }
        if let Some(&mut StackMember::App(ref mut l)) = self.last_mut() {
            mem::swap(&mut v, l);
            l.extend(v.into_iter());
            return Ok(())
        }
        self.push(StackMember::App(v))
    }

    pub fn shift(&mut self, n: Idx, s: S) -> IdxResult<()> {
        if let Some(&mut StackMember::Shift(ref mut k, _)) = self.last_mut() {
            *k = k.checked_add(n)?;
            return Ok(())
        }
        self.push(StackMember::Shift(n, s))
    }

    // since the head may be reducible, we might introduce lifts of 0
    // FIXME: Above comment is not currently true.  Should it be?
    pub fn compact(&mut self, head: &FConstr<'a, 'b>,
                   ctx: &'a Context<FTerm<'a, 'b>>) -> IdxResult<()> {
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
                        Some((depth, _)) => head.lft(depth, ctx),
                        None => head.lft0(ctx),
                    }?;
                    m.update(h_.norm.get(), h_.term.get());
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
    pub fn update(&mut self, i: I, m: &'a FConstr<'a, 'b>,
                  ctx: &'a Context<FTerm<'a, 'b>>) -> IdxResult<()> {
        if m.norm.get() == RedState::Red {
            // const LOCKED: &'static FTerm<'static> = &FTerm::Locked;
            self.compact(&m, ctx)?;
            m.term.set(None);
            self.push(StackMember::Update(m, i))
        } else { Ok(()) }
    }

    /// The assertions in the functions below are granted because they are
    /// called only when m is a constructor, a cofix
    /// (strip_update_shift_app), a fix (get_nth_arg) or an abstraction
    /// (strip_update_shift, through get_arg).

    /// optimized for the case where there are no shifts...
    fn strip_update_shift_app(&mut self, mut head: FConstr<'a, 'b>,
                              ctx: &'a Context<FTerm<'a, 'b>>) ->
                              IdxResult<((Option<Idx>, Stack<'a, 'b, /* !, */I, S>))> {
        // FIXME: This could almost certainly be made more efficient using slices (for example) or
        // custom iterators.
        assert!(head.norm.get() != RedState::Red);
        let mut rstk = Stack(Vec::new());
        let mut depth = None;
        while let Some(shead) = self.pop() {
            match shead {
                StackMember::Shift(k, s) => {
                    rstk.push(StackMember::Shift(k, s))?;
                    head = head.lft(k, ctx)?;
                    depth = match depth {
                        None => Some(k),
                        Some(depth) => Some(depth.checked_add(k)?),
                    };
                },
                StackMember::App(args) => {
                    rstk.push(StackMember::App(args.clone() /* expensive */))?;
                    let h = head.clone();
                    head.term = Cell::new(Some(ctx.term_arena.alloc(FTerm::App(h, args))));
                },
                StackMember::Update(m, _) => {
                    m.update(head.norm.get(), head.term.get());
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

    fn get_nth_arg(&mut self, mut head: FConstr<'a, 'b>, mut n: usize,
                   ctx: &'a Context<FTerm<'a, 'b>>) ->
                   IdxResult<Option<(Stack<'a, 'b, /* ! */I, S>, FConstr<'a, 'b>)>> {
        // FIXME: This could almost certainly be made more efficient using slices (for example) or
        // custom iterators.
        assert!(head.norm.get() != RedState::Red);
        let mut rstk = Stack(Vec::new());
        while let Some(shead) = self.pop() {
            match shead {
                StackMember::Shift(k, s) => {
                    rstk.push(StackMember::Shift(k, s))?;
                    head = head.lft(k, ctx)?;
                },
                StackMember::App(args) => {
                    let q = args.len();
                    if n >= q {
                        // TODO: Check to see if args.len() could ever be zero?  If not, should we
                        // assert here, given that we check below to make sure we don't push onto
                        // rstk if n = 0?  Otherwise, should we add similar logic to the below to
                        // avoid pushing an empty arg stack?
                        rstk.push(StackMember::App(args.clone() /* expensive */))?;
                        let h = head.clone();
                        head.term = Cell::new(Some(ctx.term_arena.alloc(FTerm::App(h, args))));
                        // Safe because n >= q
                        n -= q;
                    } else {
                        // FIXME: Make this all use the proper vector methods (draining etc.).
                        // Safe because n ≤ args.len() (actually < args.len())
                        let bef = args[..n].to_vec(); // expensive
                        // Safe because n < args.len()
                        let arg = args[n].clone();
                        // Safe because (1) n + 1 is in bounds for usize, and
                        // (2) n + 1 ≤ args.len()
                        let aft = args[n+1..].to_vec(); // expensive
                        // n = bef.len()
                        if n > 0 {
                            rstk.push(StackMember::App(bef))?;
                        }
                        rstk.reverse();
                        self.append(aft)?;
                        return Ok(Some((rstk, arg)))
                    }
                },
                StackMember::Update(m, _) => {
                    m.update(head.norm.get(), head.term.get());
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
    fn get_args(&mut self,
                mut tys: &[MRef<'b, (Name, Constr, Constr)>],
                f: &'b Constr,
                mut e: Subs<FConstr<'a, 'b>>,
                ctx: &'a Context<FTerm<'a, 'b>>) -> IdxResult<Application<FConstr<'a, 'b>>> {
        while let Some(shead) = self.pop() {
            match shead {
                StackMember::Update(r, _) => {
                    // FIXME: If we made FLambdas point into slices, this silly allocation would
                    // not be necessary.
                    // Also: note that if tys.len() = 0, we will get an assertion later trying to
                    // convert it back.  The loop, however, should preserve tys.len() > 0 as long
                    // as it was initially > 0.
                    let tys = tys.to_vec(); // expensive
                    let e = e.clone(); // expensive
                    r.update(RedState::Cstr,
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
                        let args = l[..n].to_vec(); // expensive
                        e.cons(args)?;
                        // Safe because n ≤ na ≤ l.len() (n < na, actually, so eargs will be
                        // nonempty).
                        let eargs = l[n..na].to_vec(); // expensive
                        self.push(StackMember::App(eargs))?;
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

impl<'a, 'b, I> Stack<'a, 'b, I, ()> { */
    /// Eta expansion: add a reference to implicit surrounding lambda at end of stack
    pub fn eta_expand_stack(&mut self, ctx: &'a Context<FTerm<'a, 'b>>, s: S) -> IdxResult<()> {
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
        self.push(StackMember::App(app))?;
        self.push(StackMember::Shift(Idx::ONE, s))?;
        self.reverse();
        Ok(())
    }
/* }

impl<'a, 'b, S> Stack<'a, 'b, !, S> { */
    /// Iota reduction: extract the arguments to be passed to the Case
    /// branches
    /// Stacks on which this is called must satisfy:
    /// - stack is composed exclusively of Apps and Shifts.
    /// - depth = sum of shifts in this stack.
    fn reloc_rargs(&mut self, depth: Option<Idx>,
                   ctx: &'a Context<FTerm<'a, 'b>>) -> IdxResult<()> {
        let mut depth = if let Some(depth) = depth { depth } else { return Ok(()) };
        let done = Cell::new(None);
        // We wastefully drop the shifts.
        let iter = self.drain_filter( |shead| {
            if done.get().is_some() { return false }
            match *shead {
                StackMember::App(ref mut args) => {
                    for arg in args.iter_mut() {
                        match arg.lft(depth, ctx) {
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
    fn try_drop_parameters(&mut self, mut depth: Option<Idx>, mut n: usize,
                           ctx: &'a Context<FTerm<'a, 'b>>) -> RedResult<()> {
        // Drop should only succeed here if n == 0 (i.e. there were no additional parameters to
        // drop).  But we should never reach the end of the while loop unless there was no
        // StackMember::App in the stack, because if n = 0, ∀ q : usize, n ≤ q, which would
        // mean the App branches returned.  Since we don't actually *do* anything in the Shift
        // branch other than decrement depth, it doesn't affect whether n == 0 at the end, so we
        // can just check it at the beginning.
        if n == 0 { return Ok(()) }
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
                            let aft = args[n..].to_vec(); // expensive
                            self.append(aft)?;
                        }
                        self.reloc_rargs(depth, ctx)?;
                        return Ok(());
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
        return Err(RedError::NotFound)
    }

    /// Only call this on type-checked terms (otherwise the assertion may be false!)
    /// Also, only call with a stack and depth produced by strip_update_shift_app.
    /// (strip_update_shift_app produces a stack with only Zapp and Zshift items, and depth = sum
    /// of shifts in the stack).
    /// FIXME: Figure out a way to usefully incorporate "this term has been typechecked" into
    /// Rust's type system (maybe some sort of weird wrapper around Constr?).
    fn drop_parameters(&mut self, depth: Option<Idx>, n: usize,
                       ctx: &'a Context<FTerm<'a, 'b>>) -> IdxResult<()> {
        match self.try_drop_parameters(depth, n, ctx) {
            Err(RedError::NotFound) =>
                panic!("We know n < stack_arg_size(self) if well-typed term"),
            Err(RedError::Idx(e)) => Err(e),
            Ok(o) => Ok(o),
        }
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
    pub fn eta_expand_ind_stack(env: &Env<'b>,
                                ind: &'b Ind,
                                m: FConstr<'a, 'b>,
                                s: &mut Stack<'a, 'b, I, S>,
                                (f, s_): (FConstr<'a, 'b>, &mut Stack<'a, 'b, I, S>),
                                ctx: &'a Context<FTerm<'a, 'b>>) ->
        RedResult<(Stack<'a, 'b, I, S>, Stack<'a, 'b, I, S>)>
    {
        let mib = env.lookup_mind(&ind.name).ok_or(RedError::NotFound)?;
        match mib.record {
            Some(Some(RecordBody(_, ref projs, _))) if mib.finite != Finite::CoFinite => {
                // (Construct, pars1 .. parsm :: arg1...argn :: []) ~= (f, s') ->
                // arg1..argn ~= (proj1 t...projn t) where t = zip (f,s')
                // TODO: Verify that this is checked at some point during typechecking.
                let pars = usize::try_from(mib.nparams).map_err(IdxError::from)?;
                let right = f.fapp_stack(s_, ctx)?;
                let (depth, mut args) = s.strip_update_shift_app(m, ctx)?;
                // Try to drop the params, might fail on partially applied constructors.
                args.try_drop_parameters(depth, pars, ctx)?;
                let hstack: Vec<_> = projs.iter().map( |p| FConstr {
                    norm: Cell::new(RedState::Red), // right can't be a constructor though
                    term: Cell::new(Some(ctx.term_arena.alloc(FTerm::Proj(p, false,
                                                                          right.clone())))),
                }).collect();
                // FIXME: Ensure that projs is non-empty, since otherwise we'll have an empty
                // ZApp.
                Ok((args, Stack(vec![StackMember::App(hstack)])))
            },
            _ => Err(RedError::NotFound), // disallow eta-exp for non-primitive records
        }
    }

    /// Only call this on type-checked terms (otherwise the assertion may be false!)
    /// Also, only call with a stack produced by drop_parameters and an n that is part
    /// of a projection.
    /// (drop_parameters produces a stack with only Zapp items, and thanks to type-
    /// checking n should be an index somewhere in the stack).
    fn project_nth_arg(&mut self, mut n: usize) -> FConstr<'a, 'b> {
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
}

impl<'a, 'b> FTerm<'a, 'b> {
    /// Do not call this function unless tys.len() ≥ 1.
    pub fn dest_flambda<F>(clos_fun: F,
                           tys: &[MRef<'b, (Name, Constr, Constr)>],
                           b: &'b Constr,
                           e: &Subs<FConstr<'a, 'b>>,
                           ctx: &'a Context<FTerm<'a, 'b>>) ->
        IdxResult<(Name, FConstr<'a, 'b>, FConstr<'a, 'b>)>
        where F: Fn(&Subs<FConstr<'a, 'b>>,
                    &'b Constr, &'a Context<FTerm<'a, 'b>>) -> IdxResult<FConstr<'a, 'b>>,
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
        let ty = clos_fun(e, ty, ctx)?;
        let mut e = e.clone(); /* expensive */
        e.lift()?;
        Ok((na.clone(), ty, if tys.len() == 0 {
            clos_fun(&e, &b, ctx)?
        } else {
            FConstr {
                norm: Cell::new(RedState::Cstr),
                term: Cell::new(Some(ctx.term_arena.alloc(FTerm::Lambda(tys, b, e))))
            }
        }))
    }
}

impl Constr {
    fn of_fconstr_lift<'a, 'b>(v: &FConstr<'a, 'b>, lfts: &Lift,
                           ctx: &'a Context<FTerm<'a, 'b>>) -> IdxResult<Constr> {
        // In general, it might be nice to make this function tail recursive (by using an explicit
        // stack) rather than having confusing mutual recursion between of_fconstr_lift and
        // to_constr.
        if !lfts.is_id() { return v.to_constr(Constr::of_fconstr_lift, lfts, ctx) }
        let term = if let Some(v) = v.fterm() { v } else {
            return v.to_constr(Constr::of_fconstr_lift, lfts, ctx);
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
                let c = Constr::of_fconstr_lift(c, lfts, ctx)?;
                Ok(Constr::Case(ORef(Rc::from((ci.clone(), p.clone(), c, b.clone())))))
            },
            FTerm::Fix(o, ref e) if e.is_id() => Ok(Constr::Fix(o.clone())),
            FTerm::CoFix(o, ref e) if e.is_id() => Ok(Constr::CoFix(o.clone())),
            _ => v.to_constr(Constr::of_fconstr_lift, lfts, ctx)
        }
    }

    /// This function defines the correspondance between constr and
    /// fconstr. When we find a closure whose substitution is the identity,
    /// then we directly return the constr to avoid possibly huge
    /// reallocation.
    pub fn of_fconstr<'a, 'b>(v: &FConstr<'a, 'b>,
                              ctx: &'a Context<FTerm<'a, 'b>>) -> IdxResult<Constr> {
        let lfts = Lift::id();
        Constr::of_fconstr_lift(v, &lfts, ctx)
    }
}
