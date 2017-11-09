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
    Fix,
    Ind,
    PRec,
    Proj,
    PUniverses,
};
use coq::kernel::esubst::{Expr, Idx, IdxResult, SubsV as Subs, Lift};
use typed_arena::{Arena};
use core::nonzero::NonZero;
use ocaml::de::{Array, ORef};
use std::borrow::{Cow};

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

pub type TableKeyC = TableKey<ORef<PUniverses<Cst>>>;

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

/// type of shared terms. fconstr and frterm are mutually recursive.
/// Clone of the constr structure, but completely mutable, and
/// annotated with reduction state (reducible or not).
#[derive(Clone,Debug)]
pub struct FConstr<'a> {
    norm: Cell<RedState>,
    term: Cell<Option<&'a FTerm<'a>>>,
}

impl<'a> FConstr<'a> {
    pub fn fterm(&self) -> Option<&'a FTerm<'a>> {
        self.term.get()
    }

    pub fn set_norm(&self) {
        self.norm.set(RedState::Norm)
    }

    pub fn update(&self, no: RedState, term: Option<&'a FTerm<'a>>) {
        // Could issue a warning if no is still Red, pointing out that we lose sharing.
        self.norm.set(no);
        self.term.set(term);
    }

    pub fn lft(&self, mut n: Idx, ctx: &'a Context<FTerm<'a>>) -> IdxResult<Self> {
        let mut ft = self;
        loop {
            match *ft.fterm().expect("Tried to lift a locked term") {
                FTerm::Ind(_) | FTerm::Construct(_)
                | FTerm::Flex(TableKey::ConstKey(_)/* | VarKey _*/) => return Ok(self.clone()),
                FTerm::Rel(i) => return Ok(FConstr {
                    norm: Cell::new(RedState::Norm),
                    term: Cell::new(Some(ctx.term_arena.alloc(FTerm::Rel(i.checked_add(n)?)))),
                }),
                FTerm::Lambda(ref tys, ref f, ref e) => {
                    let mut e = e.clone(); // expensive
                    e.shift(n)?;
                    return Ok(FConstr {
                        norm: Cell::new(RedState::Cstr),
                        term: Cell::new(Some(
                                ctx.term_arena.alloc(FTerm::Lambda(tys.clone(), // expensive
                                                                   f.clone(), e)))),
                    })
                },
                FTerm::Fix(ref fx, ref e) => {
                    let mut e = e.clone(); // expensive
                    e.shift(n)?;
                    return Ok(FConstr {
                        norm: Cell::new(RedState::Cstr),
                        term: Cell::new(Some(ctx.term_arena.alloc(FTerm::Fix(fx.clone(), e)))),
                    })
                },
                FTerm::CoFix(ref cfx, ref e) => {
                    let mut e = e.clone(); // expensive
                    e.shift(n)?;
                    return Ok(FConstr {
                        norm: Cell::new(RedState::Cstr),
                        term: Cell::new(Some(ctx.term_arena.alloc(FTerm::CoFix(cfx.clone(), e)))),
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
    pub fn lft0(&self, ctx: &'a Context<FTerm<'a>>) -> IdxResult<Self> {
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
                    ctx: &'a Context<FTerm<'a>>) -> IdxResult<Constr>
        where F: Fn(&FConstr<'a>, &Lift, &'a Context<FTerm<'a>>) -> IdxResult<Constr>,
    {
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
                FTerm::Atom(ref c) => {
                    // Unless something weird is happening, this should be a cheap operation,
                    // because atoms should only contain sorts in our implementation (so this just
                    // becomes a clone()).  Really, this could probably just be replaced by a
                    // c.clone(), for more clarity.
                    return c.exliftn(&lfts)
                },
                FTerm::Cast(ref a, ref k, ref b) => {
                    let a = constr_fun(a, &lfts, ctx)?;
                    let b = constr_fun(b, &lfts, ctx)?;
                    return Ok(Constr::Cast(ORef(Rc::from((a, k.1, b)))))
                },
                FTerm::Flex(TableKey::ConstKey(ref c)) => return Ok(Constr::Const(c.clone())),
                FTerm::Ind(ref op) => return Ok(Constr::Ind(op.clone())),
                FTerm::Construct(ref op) => return Ok(Constr::Construct(op.clone())),
                FTerm::Case(ref ci, ref p, ref c, ref ve) => {
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
                FTerm::CaseT(ref ci, ref c, ref e) => {
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
                        .map( |t| e.mk_clos(t.clone(), ctx))
                        .map( |v| constr_fun(&v?, &lfts, ctx) )
                        .collect();
                    return Ok(Constr::Case(ORef(Rc::from((ci.clone(), p, c,
                                                          Array(Rc::from(ve?)))))))
                },
                FTerm::Fix(ref o, ref e) => {
                    // FIXME: The recursion here seems like it potentially wastes a lot of work
                    // converting Constrs to FTerms and back... same with CoFix below, and possibly
                    // CaseT above to some extent.  Also, we probably prematurely allocate a few
                    // times, since this is one of the cases where we only need references to
                    // FTerms and FConstrs rather than full-fledged FTerms / FConstrs.
                    let Fix(ref op, PRec(ref lna, ref tys, ref bds)) = **o;
                    // expensive, makes a Vec
                    let ftys: Result<Vec<_>, _> = tys.iter()
                        .map( |t| e.mk_clos(t.clone(), ctx))
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
                           .map( |t| e.mk_clos(t.clone(), ctx))
                           .map( |t| constr_fun(&t?, &lfts, ctx))
                           .collect()
                    } else {
                        // expensive, makes a Vec
                        bds.iter()
                           .map( |t| e.mk_clos(t.clone(), ctx))
                           .map( |t| constr_fun(&t?, &lfts, ctx))
                           .collect()
                    };
                    return Ok(Constr::Fix(ORef(Rc::from(Fix(op.clone(),
                                                            PRec(lna.clone(),
                                                                 Array(Rc::new(ftys?)),
                                                                 Array(Rc::new(fbds?))))))))
                },
                FTerm::CoFix(ref o, ref e) => {
                    let CoFix(op, PRec(ref lna, ref tys, ref bds)) = **o;
                    // expensive, makes a Vec
                    let ftys: Result<Vec<_>, _> = tys.iter()
                        .map( |t| e.mk_clos(t.clone(), ctx))
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
                           .map( |t| e.mk_clos(t.clone(), ctx))
                           .map( |t| constr_fun(&t?, &lfts, ctx))
                           .collect()
                    } else {
                        // expensive, makes a Vec
                        bds.iter()
                           .map( |t| e.mk_clos(t.clone(), ctx))
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
                FTerm::Proj(ref o, ref c) => {
                    let (ref p, _) = **o;
                    let c = constr_fun(c, &lfts, ctx)?;
                    return Ok(Constr::Proj(ORef(Rc::from((p.clone(), c)))))
                },
                FTerm::Lambda(ref tys, ref b, ref e) => {
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
                    let mut tys = tys.clone(); // expensive
                    let (na, ty, bd) =
                        FTerm::dest_flambda(Subs::mk_clos2, tys, b.clone(), e, ctx)?;
                    let ty = constr_fun(&ty, &lfts, ctx)?;
                    let mut lfts = lfts.into_owned(); // expensive, but shouldn't outlive this block.
                    lfts.lift()?;
                    let bd = constr_fun(&bd, &lfts, ctx)?;
                    return Ok(Constr::Lambda(ORef(Rc::from((na, ty, bd)))))
                },
                FTerm::Prod(ref o, ref t, ref c) => {
                    let (ref n, _, _) = **o;
                    let t = constr_fun(t, &lfts, ctx)?;
                    let mut lfts = lfts.into_owned(); // expensive, but shouldn't outlive this block.
                    lfts.lift()?;
                    let c = constr_fun(c, &lfts, ctx)?;
                    return Ok(Constr::Prod(ORef(Rc::from((n.clone(), t, c)))))
                },
                FTerm::LetIn(ref o, ref b, ref t, ref e) => {
                    let (ref n, _, _, ref f) = **o;
                    let b = constr_fun(b, &lfts, ctx)?;
                    let t = constr_fun(t, &lfts, ctx)?;
                    let mut e = e.clone(); // expensive, but shouldn't outlive this block.
                    e.lift()?;
                    let fc = e.mk_clos2(f, ctx)?;
                    let mut lfts = lfts.into_owned(); // expensive, but shouldn't outlive this block.
                    lfts.lift()?;
                    let fc = constr_fun(&fc, &lfts, ctx)?;
                    return Ok(Constr::LetIn(ORef(Rc::from((n.clone(), b, t, fc)))))
                },
                // | FEvar (ev,args) -> Evar(ev,Array.map (constr_fun lfts) args)
                FTerm::Lift(k, ref a) => {
                    let mut lfts_ = lfts.into_owned();
                    lfts_.shift(k)?;
                    lfts = Cow::Owned(lfts_);
                    // norm_ = a.norm.get();
                    // term_ = Cow::Borrowed(a.fterm().expect("Tried to lift a locked term!"));
                    v = a;
                },
                FTerm::Clos(ref t, ref env) => {
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
}

impl<'a> Subs<FConstr<'a>> {
    pub fn clos_rel(&self, i: Idx, ctx: &'a Context<FTerm<'a>>) -> IdxResult<FConstr<'a>> {
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

    pub fn mk_lambda(self, t: ORef<(Name, Constr, Constr)>) -> IdxResult<FTerm<'a>> {
        let t = Constr::Lambda(t);
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
        Ok(FTerm::Lambda(rvars, t_.clone(), self))
    }

    /// Optimization: do not enclose variables in a closure.
    /// Makes variable access much faster
    pub fn mk_clos(&self, t: Constr, ctx: &'a Context<FTerm<'a>>) -> IdxResult<FConstr<'a>> {
        match t {
            Constr::Rel(i) => { self.clos_rel(Idx::new(NonZero::new(i)?)?, ctx) },
            Constr::Const(c) => Ok(FConstr {
                norm: Cell::new(RedState::Red),
                term: Cell::new(Some(ctx.term_arena.alloc(FTerm::Flex(TableKey::ConstKey(c))))),
            }),
            /* Constr::Meta(_) | Constr::Var(_) | Constr::Evar(_) =>
                unreachable!("Constrs should not be Meta, Var, or Evar"), */
            Constr::Sort(_) => Ok(FConstr {
                norm: Cell::new(RedState::Norm),
                term: Cell::new(Some(ctx.term_arena.alloc(FTerm::Atom(t)))),
            }),
            Constr::Ind(kn) => Ok(FConstr {
                norm: Cell::new(RedState::Norm),
                term: Cell::new(Some(ctx.term_arena.alloc(FTerm::Ind(kn)))),
            }),
            Constr::Construct(kn) => Ok(FConstr {
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

    pub fn mk_clos_vect(&self, v: &[Constr],
                        ctx: &'a Context<FTerm<'a>>) -> IdxResult<Vec<FConstr<'a>>> {
        // Expensive, makes a vector
        v.into_iter().map( |t| self.mk_clos(t.clone(), ctx)).collect()
    }

    /// Translate the head constructor of t from constr to fconstr. This
    /// function is parameterized by the function to apply on the direct
    /// subterms.
    /// Could be used insted of mk_clos.
    pub fn mk_clos_deep<F>(&self, clos_fun: F, t: &Constr,
                           ctx: &'a Context<FTerm<'a>>) -> IdxResult<FConstr<'a>>
        where F: Fn(&Subs<FConstr<'a>>, Constr, &'a Context<FTerm<'a>>) -> IdxResult<FConstr<'a>>,
    {
        match *t {
            Constr::Rel(_) | Constr::Ind(_) |
            Constr::Const(_) | Constr::Construct(_) |
            // Constr::Var(_) | Constr::Meta(_) | Constr::Evar(_)
            Constr::Sort(_) => self.mk_clos(t.clone(), ctx),
            Constr::Cast(ref o) => {
                let (a, b) = {
                    let (ref a, _, ref b) = **o;
                    let a = clos_fun(self, a.clone(), ctx)?;
                    let b = clos_fun(self, b.clone(), ctx)?;
                    (a, b)
                };
                Ok(FConstr {
                    norm: Cell::new(RedState::Red),
                    term: Cell::new(Some(ctx.term_arena.alloc(FTerm::Cast(a, o.clone(), b)))),
                })
            },
            Constr::App(ref o) => {
                let (f, v) = {
                    let (ref f, ref v) = **o;
                    let f = clos_fun(self, f.clone(), ctx)?;
                    // Expensive, makes a vector
                    let v: Result<_, _> =
                        v.iter().map( |t| clos_fun(self, t.clone(), ctx))
                         .collect();
                    (f, v?)
                };
                Ok(FConstr {
                    norm: Cell::new(RedState::Red),
                    term: Cell::new(Some(ctx.term_arena.alloc(FTerm::App(f, v)))),
                })
            },
            Constr::Proj(ref o) => {
                let c = {
                    let (_, ref c) = **o;
                    clos_fun(self, c.clone(), ctx)?
                };
                Ok(FConstr {
                    norm: Cell::new(RedState::Red),
                    term: Cell::new(Some(ctx.term_arena.alloc(FTerm::Proj(o.clone(), c)))),
                })
            },
            Constr::Case(ref o) => {
                let c = {
                    let (_, _, ref c, _) = **o;
                    clos_fun(self, c.clone(), ctx)?
                };
                let env = self.clone(); // expensive
                Ok(FConstr {
                    norm: Cell::new(RedState::Red),
                    term: Cell::new(Some(ctx.term_arena.alloc(FTerm::CaseT(o.clone(), c, env)))),
                })
            },
            Constr::Fix(ref o) => {
                let env = self.clone(); // expensive
                Ok(FConstr {
                    norm: Cell::new(RedState::Cstr),
                    term: Cell::new(Some(ctx.term_arena.alloc(FTerm::Fix(o.clone(), env)))),
                })
            },
            Constr::CoFix(ref o) => {
                let env = self.clone(); // expensive
                Ok(FConstr {
                    norm: Cell::new(RedState::Cstr),
                    term: Cell::new(Some(ctx.term_arena.alloc(FTerm::CoFix(o.clone(), env)))),
                })
            },
            Constr::Lambda(ref o) => {
                let env = self.clone(); // expensive
                Ok(FConstr {
                    norm: Cell::new(RedState::Cstr),
                    term: Cell::new(Some(ctx.term_arena.alloc(env.mk_lambda(o.clone())?))),
                })
            },
            Constr::Prod(ref o) => {
                let (t, c) = {
                    let (_, ref t, ref c) = **o;
                    let t = clos_fun(self, t.clone(), ctx)?;
                    // expensive, but doesn't outlive this block.
                    let mut env = self.clone();
                    env.lift()?;
                    let c = clos_fun(&env, c.clone(), ctx)?;
                    (t, c)
                };
                Ok(FConstr {
                    norm: Cell::new(RedState::Whnf),
                    term: Cell::new(Some(ctx.term_arena.alloc(FTerm::Prod(o.clone(), t, c)))),
                })
            },
            Constr::LetIn(ref o) => {
                let (b, t) = {
                    let (_, ref b, ref t, _) = **o;
                    let b = clos_fun(self, b.clone(), ctx)?;
                    let t = clos_fun(self, t.clone(), ctx)?;
                    (b, t)
                };
                let env = self.clone(); // expensive
                Ok(FConstr {
                    norm: Cell::new(RedState::Red),
                    term: Cell::new(Some(ctx.term_arena.alloc(FTerm::LetIn(o.clone(),
                                                              b, t, env)))),
                })
            },
        }
    }

    /// A better mk_clos?
    pub fn mk_clos2(&self, t: &Constr, ctx: &'a Context<FTerm<'a>>) -> IdxResult<FConstr<'a>> {
        self.mk_clos_deep((Subs::<FConstr>::mk_clos), t, ctx)
    }
}

#[derive(Clone,Debug)]
pub enum FTerm<'a> {
  Rel(Idx),
  /// Metas and sorts; but metas shouldn't occur in a .vo...
  Atom(Constr),
  Cast(FConstr<'a>, ORef<(Constr, Cast, Constr)>, FConstr<'a>),
  Flex(TableKeyC),
  Ind(ORef<PUniverses<Ind>>),
  Construct(ORef<PUniverses<Cons>>),
  App(FConstr<'a>, Vec<FConstr<'a>>),
  Proj(ORef<(Proj, Constr)>, FConstr<'a>),
  Fix(ORef<Fix>, Subs<FConstr<'a>>),
  CoFix(ORef<CoFix>, Subs<FConstr<'a>>),
  Case(ORef<(CaseInfo, Constr, Constr, Array<Constr>)>, FConstr<'a>, FConstr<'a>,
       Vec<FConstr<'a>>),
  /// predicate and branches are closures
  CaseT(ORef<(CaseInfo, Constr, Constr, Array<Constr>)>, FConstr<'a>, Subs<FConstr<'a>>),
  Lambda(Vec</*(Name, Constr)*/ORef<(Name, Constr, Constr)>>, Constr, Subs<FConstr<'a>>),
  Prod(ORef<(Name, Constr, Constr)>, FConstr<'a>, FConstr<'a>),
  LetIn(ORef<(Name, Constr, Constr, Constr)>, FConstr<'a>, FConstr<'a>, Subs<FConstr<'a>>),
  // should not occur
  // | FEvar of existential_key * fconstr array (* why diff from kernel/closure? *)
  /// FLIFT is a delayed shift; allows sharing between 2 lifted copies
  /// of a given term.
  Lift(Idx, FConstr<'a>),
  /// FCLOS is a delayed substitution applied to a constr
  Clos(Constr, Subs<FConstr<'a>>),
  // /// FLOCKED is used to erase the content of a reference that must
  // /// be updated. This is to allow the garbage collector to work
  // /// before the term is computed.
  // Locked,
}

/// The type of (machine) stacks (= lambda-bar-calculus' contexts)
pub enum StackMember<'a> {
    App(Vec<FConstr<'a>>),
    Case(ORef<(CaseInfo, Constr, Constr, Array<Constr>)>, FConstr<'a>, Vec<FConstr<'a>>),
    CaseT(ORef<(CaseInfo, Constr, Constr, Array<Constr>)>, Subs<FConstr<'a>>),
    Proj(Idx, Idx, ORef<(Proj, Constr)>),
    Fix(FConstr<'a>, Stack<'a>),
    Shift(Idx),
    Update(FConstr<'a>),
}

pub struct Stack<'a>(Vec<StackMember<'a>>);

impl<'a> ::std::ops::Deref for Stack<'a> {
    type Target = Vec<StackMember<'a>>;
    fn deref(&self) -> &Vec<StackMember<'a>> {
        &self.0
    }
}

impl<'a> ::std::ops::DerefMut for Stack<'a> {
    fn deref_mut(&mut self) -> &mut Vec<StackMember<'a>> {
        &mut self.0
    }
}

impl<'a> Stack<'a> {
    fn push(&mut self, o: StackMember<'a>) -> IdxResult<()> {
        self.0.push(o);
        Ok(())
    }
    pub fn append(&mut self, s: Vec<FConstr<'a>>) -> IdxResult<()> {
        if let Some(&mut StackMember::App(ref mut l)) = self.last_mut() {
            l.extend(s.into_iter());
            return Ok(())
        }
        self.push(StackMember::App(s))
    }

    pub fn shift(&mut self, n: Idx) -> IdxResult<()> {
        if let Some(&mut StackMember::Shift(ref mut k)) = self.last_mut() {
            *k = k.checked_add(n)?;
            return Ok(())
        }
        self.push(StackMember::Shift(n))
    }

    // since the head may be reducible, we might introduce lifts of 0
    // FIXME: Above comment is not currently true.  Should it be?
    pub fn compact(&mut self, head: &FConstr<'a>, ctx: &'a Context<FTerm<'a>>) -> IdxResult<()> {
        let mut depth = None;
        while let Some(shead) = self.pop() {
            match shead {
                StackMember::Shift(k) => {
                    depth = match depth {
                        None => Some(k),
                        Some(depth) => Some(depth.checked_add(k)?),
                    };
                },
                StackMember::Update(ref m) => {
                    // Be sure to create a new cell otherwise sharing would be
                    // lost by the update operation.
                    // FIXME: Figure out what the above cryptic comment means and whether it
                    // applies to Rust.
                    let h_ = match depth {
                        Some(depth) => head.lft(depth, ctx),
                        None => head.lft0(ctx),
                    }?;
                    m.update(h_.norm.get(), h_.term.get());
                },
                s => {
                    // It was fine on the stack before, so it should be fine now.
                    self.0.push(s);
                    return match depth {
                        Some(depth) => self.shift(depth),
                        None => Ok(()),
                    }
                }
            }
        }
        Ok(())
    }

    /// Put an update mark in the stack, only if needed
    pub fn update(&mut self, m: FConstr<'a>, ctx: &'a Context<FTerm<'a>>) -> IdxResult<()> {
        if m.norm.get() == RedState::Red {
            // const LOCKED: &'static FTerm<'static> = &FTerm::Locked;
            self.compact(&m, ctx)?;
            m.term.set(None);
            self.push(StackMember::Update(m))
        } else { Ok(()) }
    }
}

impl<'a> FTerm<'a> {
    /// Do not call this function unless tys.len() ≥ 1.
    pub fn dest_flambda<F>(clos_fun: F,
                           mut tys: Vec</*(Name, Constr)*/ORef<(Name, Constr, Constr)>>,
                           b: Constr,
                           e: &Subs<FConstr<'a>>,
                           ctx: &'a Context<FTerm<'a>>) ->
        IdxResult<(Name, FConstr<'a>, FConstr<'a>)>
        where F: Fn(&Subs<FConstr<'a>>, &Constr, &'a Context<FTerm<'a>>) -> IdxResult<FConstr<'a>>,
    {
        // FIXME: consider using references to slices for FTerm::Lambda arguments instead of Vecs.
        // That would allow us to avoid taking tys by value.  However, this might not matter if it
        // turns out the uses of dest_flambda are inherently wasteful.
        let o = tys.pop().expect("Should not call dest_flambda with tys.len() = 0");
        let (ref na, ref ty, _) = *o;
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
    fn of_fconstr_lift<'a>(v: &FConstr<'a>, lfts: &Lift,
                           ctx: &'a Context<FTerm<'a>>) -> IdxResult<Constr> {
        // In general, it might be nice to make this function tail recursive (by using an explicit
        // stack) rather than having confusing mutual recursion between of_fconstr_lift and
        // to_constr.
        if !lfts.is_id() { return v.to_constr(Constr::of_fconstr_lift, lfts, ctx) }
        let term = if let Some(v) = v.fterm() { v } else {
            return v.to_constr(Constr::of_fconstr_lift, lfts, ctx);
        };
        match *term {
            FTerm::Clos(ref t, ref env) if env.is_id() => Ok(t.clone()),
            FTerm::Lambda(ref tys, ref f, ref e) if e.is_id() => {
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
                    Some(o) => Constr::Lambda(o.clone()),
                })
            },
            FTerm::CaseT(ref o, ref c, ref e) if e.is_id() => {
                // FIXME: Make this tail-recursive / use an explicit stack?
                // FIXME: Is there any way to determine that the interior term hasn't been touched?
                // If so, can we reuse the old case allocation?
                let (ref ci, ref p, _, ref b) = **o;
                let c = Constr::of_fconstr_lift(c, lfts, ctx)?;
                Ok(Constr::Case(ORef(Rc::from((ci.clone(), p.clone(), c, b.clone())))))
            },
            FTerm::Fix(ref o, ref e) if e.is_id() => Ok(Constr::Fix(o.clone())),
            FTerm::CoFix(ref o, ref e) if e.is_id() => Ok(Constr::CoFix(o.clone())),
            _ => v.to_constr(Constr::of_fconstr_lift, lfts, ctx)
        }
    }

    /// This function defines the correspondance between constr and
    /// fconstr. When we find a closure whose substitution is the identity,
    /// then we directly return the constr to avoid possibly huge
    /// reallocation.
    pub fn of_fconstr<'a>(v: &FConstr<'a>, ctx: &'a Context<FTerm<'a>>) -> IdxResult<Constr> {
        let lfts = Lift::id();
        Constr::of_fconstr_lift(v, &lfts, ctx)
    }
}
