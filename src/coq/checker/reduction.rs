use coq::checker::closure::{
    self,
    ClosInfos,
    Context,
    FConstr,
    FTerm,
    Infos,
    MRef,
    RedError,
    RedResult,
    Reds,
    Stack,
    StackMember,
    TableKey,
    TableKeyC,
};
use coq::checker::environ::{
    Env,
    EnvError,
    Globals,
};
use coq::checker::term::{
    Arity,
};
use coq::checker::univ::{
    UnivError,
    Universes,
};
use coq::kernel::esubst::{
    Idx,
    IdxError,
    IdxResult,
    Lift,
    SubsV as Subs,
};
use core::convert::{TryFrom};
use core::nonzero::{NonZero};
use ocaml::de::{
    ORef,
    Array,
};
use ocaml::values::{
    CaseInfo,
    CoFix,
    Cons,
    Constr,
    Cst,
    Engagement,
    Fix,
    Fix2,
    Ind,
    Instance,
    PRec,
    PUniverses,
    RDecl,
    Sort,
    SortContents,
};
use std::borrow::{Cow};
use std::iter;
use std::mem;
use std::sync::{Arc};
use typed_arena::{Arena};
use util::ghost_cell::{Set};

/// lft_constr_stack_elt
enum ZL<'id, 'a, 'b> where 'b: 'a, 'id: 'a {
    App(Vec<(Lift, FConstr<'id, 'a, 'b>)>),
    Proj(&'b Cst, bool, Lift),
    Fix(Lift, FConstr<'id, 'a, 'b>, LftConstrStack<'id, 'a, 'b>),
    Case(MRef<'b, (CaseInfo, Constr, Constr, Array<Constr>)>, Lift,
         FConstr<'id, 'a, 'b>, Vec<FConstr<'id, 'a, 'b>>),
}

struct LftConstrStack<'id, 'a, 'b>(Vec<ZL<'id, 'a, 'b>>) where 'b: 'a, 'id: 'a;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ConvError {
    Anomaly(String),
    Env(EnvError),
    Idx(IdxError),
    Univ(UnivError),
    Red(Box<RedError>),
    NotConvertible,
    NotConvertibleVect(usize),
    NotFound,
    UserError(String),
}

pub type ConvResult<T> = Result<T, Box<ConvError>>;

#[derive(Clone,Copy,Debug,Eq,PartialEq)]
pub enum ConvPb {
  Conv,
  Cumul,
}

impl<'id, 'a, 'b> ::std::ops::Deref for LftConstrStack<'id, 'a, 'b> {
    type Target = Vec<ZL<'id, 'a, 'b>>;
    fn deref(&self) -> &Vec<ZL<'id, 'a, 'b>> {
        &self.0
    }
}

impl<'id, 'a, 'b> ::std::ops::DerefMut for LftConstrStack<'id, 'a, 'b> {
    fn deref_mut(&mut self) -> &mut Vec<ZL<'id, 'a, 'b>> {
        &mut self.0
    }
}

impl ::std::convert::From<EnvError> for Box<ConvError> {
    fn from(e: EnvError) -> Self {
        Box::new(ConvError::Env(e))
    }
}

impl ::std::convert::From<IdxError> for Box<ConvError> {
    fn from(e: IdxError) -> Self {
        Box::new(ConvError::Idx(e))
    }
}

impl ::std::convert::From<UnivError> for Box<ConvError> {
    fn from(e: UnivError) -> Self {
        Box::new(ConvError::Univ(e))
    }
}

impl ::std::convert::From<Box<RedError>> for Box<ConvError> {
    fn from(e: Box<RedError>) -> Self {
        Box::new(ConvError::Red(e))
    }
}

impl<'id, 'a, 'b> LftConstrStack<'id, 'a, 'b> {
    fn append(&mut self, mut v: Vec<(Lift, FConstr<'id, 'a, 'b>)>) {
        // TODO: Work out why we don't do this here?
        // if v.len() == 0 { return }
        if let Some(&mut ZL::App(ref mut l)) = self.last_mut() {
            mem::swap(&mut v, l);
            l.extend(v.into_iter());
            return
        }
        self.push(ZL::App(v))
    }
}

impl<'id, 'a, 'b, Inst, Shft> Stack<'id, 'a, 'b, Inst, Shft> {
    fn is_empty(&self) -> bool {
        self.iter().all( |x| match *x {
            StackMember::Update(_, _) => true,
            StackMember::Shift(_, _) => true,
            _ => false,
        })
    }

    /// Compute the lift to be performed on a term placed in a given stack
    fn el(&self, el: &mut Lift) -> IdxResult<()> {
        let mut i = None::<Idx>;
        for z in self.iter() {
            if let StackMember::Shift(n, _) = *z {
                match i {
                    Some(ref mut i) => { *i = i.checked_add(n)? },
                    None => { i = Some(n) },
                };
            }
        }
        if let Some(i) = i {
            el.shift(i)
        } else { Ok(()) }
    }

    fn compare_shape<'id_, 'c>(&self, stk: &Stack<'id_, 'c, 'b, Inst, Shft>) -> IdxResult<bool> {
        let mut bal = 0isize;
        let mut stk1 = self.iter();
        let mut stk2 = stk.iter();
        let mut s1 = stk1.next();
        let mut s2 = stk2.next();
        loop {
            match (s1, s2) {
                (None, None) => { return Ok(bal == 0) },
                (Some(&StackMember::Update(_, _)), _) | (Some(&StackMember::Shift(_, _)), _) => {
                    s1 = stk1.next();
                },
                (_, Some(&StackMember::Update(_, _))) | (_, Some(&StackMember::Shift(_, _))) => {
                    s2 = stk2.next();
                },
                (Some(&StackMember::App(ref l1)), _) => {
                    // Safe because length of l1 in bytes must not exceed isize::MAX.
                    bal = bal.checked_add(l1.len() as isize)?;
                    s1 = stk1.next();
                },
                (_, Some(&StackMember::App(ref l2))) => {
                    // Safe because length of l1 in bytes must not exceed isize::MAX.
                    bal = bal.checked_sub(l2.len() as isize)?;
                    s2 = stk2.next();
                },
                (Some(&StackMember::Proj(_,_,_,_,_)), Some(&StackMember::Proj(_,_,_,_,_))) => {
                    if bal != 0 { return Ok(false) };
                    s1 = stk1.next();
                    s2 = stk2.next();
                },
                (Some(&StackMember::Case(_,_,_,_)), Some(&StackMember::Case(_,_,_,_))) |
                (Some(&StackMember::Case(_,_,_,_)), Some(&StackMember::CaseT(_,_,_))) |
                (Some(&StackMember::CaseT(_,_,_)), Some(&StackMember::Case(_,_,_,_))) |
                (Some(&StackMember::CaseT(_,_,_)), Some(&StackMember::CaseT(_,_,_))) => {
                    // TODO: Work out why c1.ci_ind  = c2.ci_ind was commented out in the first
                    // place, in Coq commit 7c290a484d4167d91fbe2de84bba6931e2e2dd8f.
                    if bal != 0 { return Ok(false) };
                    s1 = stk1.next();
                    s2 = stk2.next();
                },
                (Some(&StackMember::Fix(_, ref a1, _)), Some(&StackMember::Fix(_, ref a2, _))) => {
                    // Maybe there's a way not to recurse here?
                    if bal != 0 || !a1.compare_shape(a2)? { return Ok(false) }
                    s1 = stk1.next();
                    s2 = stk2.next();
                },
                (_, _) => return Ok(false),
            }
        }
    }

    /// pure_stack
    fn to_pure(&self, set: &Set<'id>, l: &mut Lift,
               ctx: Context<'id, 'a, 'b>) -> IdxResult<LftConstrStack<'id, 'a, 'b>> {
        // NB: This function seemed *very* susceptible to stack overflow, so it's been changed
        // significantly from its OCaml implementation to be more amenable to loops (the version in
        // OCaml is very obviously not tail recursive).  As a result, it is not obviously correct;
        // however, I believe the reason the OCaml implementation is not written this way is mostly
        // that its stacks are linked lists, and therefore can't be efficiently iterated in
        // reverse.  Since we are using vectors in Rust, we don't have this issue.
        // TODO: If it weren't for coalescing Apps together, can this be replaced with a
        // filter_map?
        let mut stk = LftConstrStack(Vec::with_capacity(self.len()));
        for s in self.iter().rev() {
            match *s {
                StackMember::Update(_, _) => {},
                StackMember::Shift(n, _) => {
                    l.shift(n)?;
                },
                StackMember::App(ref a) => {
                    // expensive, makes a Vec
                    stk.append(a.iter().map( |t| (l.clone() /* expensive */, t.clone(set)))
                                       .collect());
                },
                StackMember::Proj(_, _, p, b, _) => {
                    stk.push(ZL::Proj(p, b, l.clone() /* expensive */ ));
                },
                StackMember::Fix(ref fx, ref a, _) => {
                    let mut lfx = l.clone(); // expensive
                    let pa = a.to_pure(set, &mut lfx, ctx)?;
                    stk.push(ZL::Fix(lfx, fx.clone(set), pa));
                },
                StackMember::CaseT(o, ref env, _) => {
                    let (_, ref p, _, ref br) = **o;
                    stk.push(ZL::Case(o, l.clone() /* expensive */,
                                      env.mk_clos(set, p, ctx)?, env.mk_clos_vect(set, br, ctx)?));
                },
                StackMember::Case(o, ref p, ref br, _) => {
                    stk.push(ZL::Case(o, l.clone() /* expensive */, p.clone(set),
                                      closure::clone_vec(br, set) /* expensive */));
                },
            }
        }
        return Ok(stk)
    }
}

impl Constr {
    /// Reduction functions

    /// Note: self must be type-checked beforehand!
    ///
    /// This function is a bit weird because it actually mutates self in place.  This seems like it
    /// might not be the desired behavior, but it turns out to be quite convenient (in particular,
    /// because the lifetime of c exists outside the function call, it's easy to point into it if
    /// you need to manipulate the result of the whd afterwards and then return something
    /// pointing into it).  The same applies to the other whd_ functions.
    ///
    /// (Worth noting: if there's a panic, *self will be untouched.  But if you're using UnwindSafe
    /// properly this should not affect you anyway).
    pub fn whd_betaiotazeta(&mut self) -> RedResult<()> {
        match *self {
            Constr::Sort(_) | /* Constr::Var(_) | Constr::Meta(_) | Constr::Evar(_) |*/
            Constr::Const(_) | Constr::Ind(_) | Constr::Construct(_) | Constr::Prod(_) |
            Constr::Lambda(_) | Constr::Fix(_) | Constr::CoFix(_) => Ok(()),
            _ => {
                let mut globals = Globals::default();
                *self = Set::new( |set| {
                    let constr_arena = Arena::with_capacity(0x2000);
                    // (8 * 2^20, just an arbitrary number to start with).
                    let term_arena = Arena::with_capacity(0x800000);
                    let ctx = Context::new(&term_arena, &constr_arena);
                    let mut infos = Infos::create(set, Reds::BETAIOTAZETA,
                                                  iter::empty())?;
                    let v = self.inject(&infos.set, ctx)?;
                    v.whd_val(&mut infos, &mut globals, ctx)
                } )?;
                Ok(())
            }
        }
    }

    /// Note: self must be type-checked beforehand!
    ///
    /// Mutates self in place; see whd_betaiotazeta for more information.
    pub fn whd_all<'b, 'g>(&mut self, env: &mut Env<'b, 'g>) -> RedResult<()>
        where 'g: 'b,
    {
        match *self {
            Constr::Sort(_) | /* Constr::Meta(_) | Constr::Evar(_) |*/
            Constr::Ind(_) | Constr::Construct(_) | Constr::Prod(_) | Constr::Lambda(_) |
            Constr::Fix(_) | Constr::CoFix(_) => Ok(()),
            _ => {
                let Env { ref mut globals, ref mut rel_context, .. } = *env;
                *self = Set::new( |set| {
                    let constr_arena = Arena::with_capacity(0x2000);
                    // (8 * 2^20, just an arbitrary number to start with).
                    let term_arena = Arena::with_capacity(0x800000);
                    let ctx = Context::new(&term_arena, &constr_arena);
                    let mut infos = Infos::create(set, Reds::BETADELTAIOTA,
                                                  rel_context.iter_mut())?;
                    let v = self.inject(&infos.set, ctx)?;
                    v.whd_val(&mut infos, globals, ctx)
                } )?;
                Ok(())
            }
        }
    }

    /// Note: self must be type-checked beforehand!
    ///
    /// Mutates self in place; see whd_betaiotazeta for more information.
    pub fn whd_allnolet<'b, 'g>(&mut self, env: &mut Env<'b, 'g>) -> RedResult<()>
        where 'g: 'b,
    {
        match *self {
            Constr::Sort(_) | /* Constr::Meta(_) | Constr::Evar(_) |*/
            Constr::Ind(_) | Constr::Construct(_) | Constr::Prod(_) | Constr::Lambda(_) |
            Constr::Fix(_) | Constr::CoFix(_) | Constr::LetIn(_) => Ok(()),
            _ => {
                let Env { ref mut globals, ref mut rel_context, .. } = *env;
                *self = Set::new( |set| {
                    let constr_arena = Arena::with_capacity(0x2000);
                    // (8 * 2^20, just an arbitrary number to start with).
                    let term_arena = Arena::with_capacity(0x800000);
                    let ctx = Context::new(&term_arena, &constr_arena);
                    let mut infos = Infos::create(set, Reds::BETADELTAIOTANOLET,
                                                  rel_context.iter_mut())?;
                    let v = self.inject(&infos.set, ctx)?;
                    v.whd_val(&mut infos, globals, ctx)
                } )?;
                Ok(())
            }
        }
    }

    /// Builds an application node, reducing beta redexes it may produce.
    /// Note: self must be type-checked beforehand!
    pub fn beta_appvect(&self, stack: &mut [Constr]) -> IdxResult<Constr> {
        let mut t = self;
        // Invariant: i ≤ stack.len()
        let mut i = 0;
        while let Constr::Lambda(ref o) = *t {
            if i < stack.len() {
                let (_, _, ref c) = **o;
                t = c;
                // i < stack.len() →
                // i + 1 ≤ stack.len()
                i += 1;
                // i ≤ stack.len()
            } else {
                // Correct environment is the entire stack, with an empty argument list; however,
                // the environment needs to be reversed, since in the OCaml implementation it was
                // generated by recursively consing entries onto the head of a list, and in our
                // setting we just take slices into a Vec.
                // FIXME: If we just write substl to operate on reversed stacks, we don't need
                // mutability here.
                stack.reverse();
                let t = t.substl(stack)?;
                stack.reverse();
                return Ok(t.applist(Vec::new()))
            }
        }
        // split_at_mut cannot panic because i ≤ stack.len();
        // correct environment is part through i, and correct stack is part after i.
        // However, the environment needs to be reversed, for the same reason given above (the
        // FIXME from above still applies here, too).
        let (env, stack) = stack.split_at_mut(i);
        env.reverse();
        let t = t.substl(env)?;
        env.reverse();
        Ok(t.applist(stack.to_vec()))
    }
}

/// Conversion

/// Conversion utility functions

impl Universes {
    fn convert(&self, u: &Instance, u_: &Instance) -> ConvResult<()> {
        if u.check_eq(u_, self)? { Ok(()) }
        else { Err(Box::new(ConvError::NotConvertible)) }
    }
}

fn compare_stacks<'id, 'id_, 'a, 'c, 'b, I, S, T, F, FMind>
    (infos: &mut ClosInfos<'id, 'a, 'b>, infos_: &mut ClosInfos<'id_, 'c, 'b>,
     f: &mut F, fmind: &mut FMind,
     lft1: &mut Lift, stk1: &Stack<'id, 'a, 'b, I, S>,
     lft2: &mut Lift, stk2: &Stack<'id_, 'c, 'b, I, S>,
     ctx: Context<'id, 'a, 'b>, ctx_: Context<'id_, 'c, 'b>,
     env: &T) -> ConvResult<()>
    where
        F: for<'r> FnMut(&'r mut ClosInfos<'id, 'a, 'b>, &'r mut ClosInfos<'id_, 'c, 'b>,
                         &'r T, (&Lift, FConstr<'id, 'a, 'b>),
                         (&Lift, FConstr<'id_, 'c, 'b>),
                         Context<'id, 'a, 'b>, Context<'id_, 'c, 'b>) -> ConvResult<()>,
        FMind: Fn(&T, &Ind, &Ind) -> bool,
        F: Send,
        for<'id__> ClosInfos<'id__, 'a, 'b> : Send,
        for<'id__> FConstr<'id__, 'a, 'b>: Send + Sync,
        Lift: Send,
        Lift: Sync,
        for<'id__> Stack<'id__, 'a, 'b, I, S>: Sync,
        T: Sync,
{
    /// Prerequisite: call with stacks of the same shape.
    fn cmp_rec<'id, 'id_, 'a, 'c, 'b, T, F, FMind>
        (infos: &mut ClosInfos<'id, 'a, 'b>, infos_: &mut ClosInfos<'id_, 'c, 'b>,
         f: &mut F, fmind: &mut FMind,
         pstk1: LftConstrStack<'id, 'a, 'b>,
         pstk2: LftConstrStack<'id_, 'c, 'b>,
         ctx: Context<'id, 'a, 'b>, ctx_: Context<'id_, 'c, 'b>,
         env: &T) -> ConvResult<()>
        where
            F: for<'r> FnMut(&'r mut ClosInfos<'id, 'a, 'b>, &'r mut ClosInfos<'id_, 'c, 'b>,
                             &'r T, (&Lift, FConstr<'id, 'a, 'b>),
                             (&Lift, FConstr<'id_, 'c, 'b>),
                             Context<'id, 'a, 'b>, Context<'id_, 'c, 'b>) -> ConvResult<()>,
            FMind: FnMut(&T, &Ind, &Ind) -> bool,
    {
        // The stacks have the same shape, so we don't need to worry about these mismatching.
        for (z1, z2) in pstk1.0.into_iter().zip(pstk2.0.into_iter()) {
            // Not sure why the loop doesn't tail recurse on the first element in OCaml.
            // Presumably, changing the order in which we check these doesn't ruin everything...
            match (z1, z2) {
                (ZL::App(a1), ZL::App(a2)) => {
                    for ((l1, c1), (l2, c2)) in a1.into_iter().zip(a2.into_iter()) {
                        f(infos, infos_, env, (&l1, c1), (&l2, c2), ctx, ctx_)?;
                    }
                },
                (ZL::Fix(lfx1, fx1, a1), ZL::Fix(lfx2, fx2, a2)) => {
                    f(infos, infos_, env, (&lfx1, fx1), (&lfx2, fx2), ctx, ctx_)?;
                    cmp_rec(infos, infos_, f, fmind, a1, a2, ctx, ctx_, env)?;
                },
                (ZL::Proj(c1, _, _), ZL::Proj(c2, _, _)) => {
                    if !c1.eq_con_chk(c2) { return Err(Box::new(ConvError::NotConvertible)) }
                    // TODO: Figure out why we don't compare lifts here?
                },
                (ZL::Case(o1, l1, p1, br1),
                 ZL::Case(o2, l2, p2, br2)) => {
                    let (ref ci1, _, _, _) = **o1;
                    let (ref ci2, _, _, _) = **o2;
                    if !fmind(env, &ci1.ind, &ci2.ind) {
                        return Err(Box::new(ConvError::NotConvertible))
                    }
                    f(infos, infos_, env, (&l1, p1), (&l2, p2), ctx, ctx_)?;
                    for (c1, c2) in br1.into_iter().zip(br2.into_iter()) {
                        f(infos, infos_, env, (&l1, c1), (&l2, c2), ctx, ctx_)?;
                    }
                },
                _ => unreachable!("Stacks should have the same shape."),
            }
        }
        return Ok(())
    }

    if stk1.compare_shape(stk2)? {
        let stk1 = stk1.to_pure(&infos.set, lft1, ctx)?;
        let stk2 = stk2.to_pure(&infos_.set, lft2, ctx_)?;
        cmp_rec(infos, infos_, f, fmind, stk1, stk2, ctx, ctx_, env)
    } else {
        Err(Box::new(ConvError::NotConvertible))
    }
}

impl Engagement {
    /// Convertibility of sorts
    fn sort_cmp(&self, univ: &Universes, pb: ConvPb, s0: &Sort, s1: &Sort) -> ConvResult<()> {
        match (s0, s1) {
            (&Sort::Prop(c1), &Sort::Prop(c2)) if pb == ConvPb::Cumul => {
                if c1 == SortContents::Pos && c2 == SortContents::Null {
                    return Err(Box::new(ConvError::NotConvertible))
                }
            },
            (&Sort::Prop(ref c1), &Sort::Prop(ref c2)) => {
                if c1 != c2 {
                    return Err(Box::new(ConvError::NotConvertible))
                }
            },
            (&Sort::Prop(_), &Sort::Type(_)) => {
                match pb {
                    ConvPb::Cumul => (),
                    _ => return Err(Box::new(ConvError::NotConvertible)),
                }
            },
            (&Sort::Type(ref u1), &Sort::Type(ref u2)) => {
                // FIXME: handle type-in-type option here
                // TODO: Figure out what the above comment means.
                if /* snd (engagement env) == StratifiedType && */
                    !(match pb {
                        // TODO: Maybe make this a trait?  Not that the dynamic dispatch here takes
                        // very much time, but why leave performance on the table?
                        ConvPb::Conv => u1.check_eq(u2, univ)?,
                        ConvPb::Cumul => u1.check_leq(u2, univ)?,
                    }) {
                    // TODO: Print information here (as OCaml does) on error if debug mode is set.
                    return Err(Box::new(ConvError::NotConvertible))
                }
            },
            (_, _) => return Err(Box::new(ConvError::NotConvertible)),
        }
        return Ok(())
    }
}

impl<'b> TableKeyC<'b> {
    fn oracle_order(&self, fl2: &Self) -> bool {
        match (*self, *fl2) {
            (TableKey::ConstKey(_), TableKey::ConstKey(_)) => /* height c1 > height c2 */false,
            (_, TableKey::ConstKey(_)) => true,
            (_, _) => false,
        }
    }
}

impl<'g> Globals<'g> {
    fn unfold_projection_infos<'id, 'a, 'b, I, S>
        (&self, p: &'b Cst, b: bool, i: I) -> ConvResult<StackMember<'id, 'a, 'b, I, S>> {
        let pb = self.lookup_projection(p)
                     .ok_or_else(|| Box::new(ConvError::NotFound))??;
        // TODO: Verify that npars and arg being within usize is checked at some
        // point during typechecking.
        let npars = usize::try_from(pb.npars).map_err(IdxError::from)?;
        let arg = usize::try_from(pb.arg).map_err(IdxError::from)?;
        Ok(StackMember::Proj(npars, arg, p, b, i))
    }
}

impl<'id, 'id_, 'a, 'c, 'b, 'g> ClosInfos<'id, 'a, 'b> where 'g: 'b {
    /// Conversion between [lft1]term1 and [lft2]term2.
    /// Note: term1 and term2 must be type-checked beforehand!
    fn ccnv<'r, I, S>(&'r mut self, infos_: &'r mut ClosInfos<'id_, 'c, 'b>,
                      univ: &Universes, enga: &Engagement,
                      globals: &'r Globals<'g>, cv_pb: ConvPb,
                      lft1: &Lift, lft2: &Lift,
                      term1: FConstr<'id, 'a, 'b>, term2: FConstr<'id_, 'c, 'b>,
                      i: I, s: S,
                      ctx: Context<'id, 'a, 'b>, ctx_: Context<'id_, 'c, 'b>) -> ConvResult<()>
        where
            I: Clone + Sync,
            S: Clone + Sync,
    {
        self.eqappr(infos_, univ, enga, globals, cv_pb,
                    lft1, term1, &mut Stack::new(),
                    lft2, term2, &mut Stack::new(),
                    i, s, ctx, ctx_)
    }

    /// Conversion between [lft1](hd1 v1) and [lft2](hd2 v2)
    /// Note: term1 and term2 must be type-checked beforehand in the context of stk1 and stk2,
    /// respectively!
    fn eqappr<'r, I, S>(&'r mut self, infos_: &'r mut ClosInfos<'id_, 'c, 'b>,
                        univ: &Universes, enga: &Engagement,
                        globals: &'r Globals<'g>, mut cv_pb: ConvPb,
                        lft1: &Lift, mut hd1: FConstr<'id, 'a, 'b>,
                        v1: &mut Stack<'id, 'a, 'b, I, S>,
                        lft2: &Lift, mut hd2: FConstr<'id_, 'c, 'b>,
                        v2: &mut Stack<'id_, 'c, 'b, I, S>,
                        i: I, s: S,
                        ctx: Context<'id, 'a, 'b>,
                        ctx_: Context<'id_, 'c, 'b>) -> ConvResult<()>
        where
            I: Clone + Sync,
            S: Clone + Sync,
    {
        let mut lft1 = Cow::Borrowed(lft1);
        let mut lft2 = Cow::Borrowed(lft2);
        // FIXME: Essentially *all* the cloning we do in this and related functions like
        // compare_stack (in this file, that is) can be eliminated if we mutate el in-place by
        // popping and pushing.  The code may become more subtle, though; maybe utilizing a
        // destructor or closure somehow would be worthwhile?  Anyway, this API would be useful in
        // a number of other places, but this is the only one where in some cases allocations would
        // completely disappear if we did this.

        loop {
            // FIXME: Why is the below line necessary?
            // Control.check_for_interrupt ();

            // First head reduce both terms
            // NOTE: In the OCaml implementation, we loop here because whd_stack on term2 might
            // have modified st1 (due to sharing), and st1 might not be in whnf anymore.  However,
            // in the Rust implementation, we can guarantee that this is not the case, because they
            // are using separate resources.  We guarantee this by requiring them to be at
            // different parametric lifetimes, so we never use (for example) a term allocated in
            // ctx with v2.  As a result, we know that in order to modify an FTerm created in ctx,
            // you need a reference with lifetime 'a to an FTerm<'id, 'a, 'b>; but there's no way
            // shc a reference could work with 'c unless 'a = 'c, and we know 'a ≠ 'c because we
            // only call this function initially with arenas at incompatible lifetimes (through
            // clos_fconv).  The only other way to make is_whnf fail would be to change a Fix
            // Constr to something else, and the only way we change Constrs in a shared way is
            // through mutable references in Globals, which only change monotonically via forcing;
            // since they are always mutated before they're returned, and never mutated again, such
            // references can't become valid afterwards if they're not valid already, so looping
            // wouldn't help there.
            hd1 = v1.whd_stack(self, globals, hd1, ctx, i.clone(), s.clone())?;
            hd2 = v2.whd_stack(infos_, globals, hd2, ctx_, i.clone(), s.clone())?;
            // compute the lifts that apply to the head of the term (hd1 and hd2)
            // expensive, but shouldn't outlive this block.
            let mut el1 = lft1.as_ref().clone();
            // expensive, but shouldn't outlive this block.
            let mut el2 = lft2.as_ref().clone();
            v1.el(&mut el1)?;
            v2.el(&mut el2)?;
            match (hd1.fterm(&self.set).expect("Tried to lift a locked term"),
                   hd2.fterm(&infos_.set).expect("Tried to lift a locked term")) {
                // case of leaves
                (&FTerm::Atom(a1), &FTerm::Atom(a2)) => match (a1, a2) {
                    (&Constr::Sort(ref s1), &Constr::Sort(ref s2)) => {
                        // Typechecking sorts should produce an empty stack.
                        assert!(v1.is_empty() && v2.is_empty());
                        return enga.sort_cmp(univ, cv_pb, &s1, &s2)
                    },
                    // (Meta n, Meta m) => unreachable!("No Metas!")
                    // (_, _) => return Err(ConvError::NotConvertible),
                    (_, _) => panic!("Atoms should only contain Sort in the checker"),
                },
                // (EVar _, EVar _) => unreachable!("No EVars")

                // 2 indices, known to be bound to no constant.
                (&FTerm::Rel(n), &FTerm::Rel(m)) => {
                    return if el1.reloc_rel(n)? == el2.reloc_rel(m)? {
                        self.convert_stacks(infos_, univ, enga, globals,
                                            &lft1, &lft2, v1, v2, i, s, ctx, ctx_)
                    } else { Err(Box::new(ConvError::NotConvertible)) }
                },
                // 2 constants or 2 defined rels (no locally defined vars in the checker)
                (&FTerm::Flex(fl1), &FTerm::Flex(fl2)) => {
                    // First try intentional equality
                    // TODO: This seems like it might be a sneakily slow step... investigate.
                    let res = if fl1 == fl2 {
                        self.convert_stacks(infos_, univ, enga, globals,
                                            &lft1, &lft2, v1, v2,
                                            i.clone(), s.clone(), ctx, ctx_)
                    } else { Err(Box::new(ConvError::NotConvertible)) };
                    match res {
                        Err(ref o) if **o == ConvError::NotConvertible => {
                            // else the oracle tells which constant is to be expanded.
                            if fl1.oracle_order(&fl2) {
                                match self.unfold_reference(globals, fl1, ctx)?
                                          .map( |(set, def1)| def1.clone(set) ) {
                                    Some(def1) => {
                                        hd1 = v1.whd_stack(self, globals, def1, ctx,
                                                           i.clone(), s.clone())?;
                                    },
                                    None => match infos_.unfold_reference(globals, fl2, ctx_)?
                                                        .map( |(set, def2)|
                                                              def2.clone(set) ) {
                                        Some(def2) => {
                                            hd2 = v2.whd_stack(infos_, globals, def2, ctx_,
                                                               i.clone(), s.clone())?;
                                        },
                                        None => return Err(Box::new(ConvError::NotConvertible)),
                                    },
                                }
                            } else {
                                match infos_.unfold_reference(globals, fl2, ctx_)?
                                            .map( |(set, def2)| def2.clone(set) ) {
                                    Some(def2) => {
                                        hd2 = v2.whd_stack(infos_, globals, def2, ctx_,
                                                           i.clone(), s.clone())?;
                                    },
                                    None => match self.unfold_reference(globals, fl1, ctx)?
                                                      .map( |(set, def1)|
                                                            def1.clone(set) ) {
                                        Some(def1) => {
                                            hd1 = v1.whd_stack(self, globals, def1, ctx,
                                                               i.clone(), s.clone())?;
                                        },
                                        None => return Err(Box::new(ConvError::NotConvertible)),
                                    },
                                }
                            }
                        },
                        // On non-conversion error or success, we are done.
                        o => return o,
                    }
                    // Loop through again.
                },
                (&FTerm::Proj(p1, b1, ref def1), _) => {
                    let s1 = globals.unfold_projection_infos(p1, b1, i.clone())?;
                    v1.push(s1);
                    let def1 = def1.clone(&self.set);
                    hd1 = v1.whd_stack(self, globals, def1,
                                       ctx, i.clone(), s.clone())?;
                    // Loop through and try again with the projection unfolded.
                },
                (_, &FTerm::Proj(p2, b2, ref def2)) => {
                    let s2 = globals.unfold_projection_infos(p2, b2, i.clone())?;
                    v2.push(s2);
                    let def2 = def2.clone(&infos_.set);
                    hd2 = v2.whd_stack(infos_, globals, def2,
                                       ctx_, i.clone(), s.clone())?;
                    // Loop through and try again with the projection unfolded.
                },
                // other constructors
                (&FTerm::Lambda(ref ty1, b1, ref e1), &FTerm::Lambda(ref ty2, b2, ref e2)) => {
                    // Typechecking lambdas should produce an empty stack.
                    // Inconsistency: we tolerate that v1, v2 contain shift and update but
                    // we throw them away
                    assert!(v1.is_empty() && v2.is_empty());
                    let (_, ty1, bd1) = FTerm::dest_flambda(&self.set, Subs::mk_clos,
                                                            ty1, b1, e1, ctx)?;
                    let (_, ty2, bd2) = FTerm::dest_flambda(&infos_.set, Subs::mk_clos,
                                                            ty2, b2, e2, ctx_)?;
                    // FIXME: Ew, non-tail recursion!  Can we do the same trick we do for Proj
                    // somehow?
                    self.ccnv(infos_, univ, enga, globals, ConvPb::Conv, &el1, &el2, ty1, ty2,
                              i.clone(), s.clone(), ctx, ctx_)?;
                    el1.lift()?;
                    el2.lift()?;
                    // Avoid tail recursion in Rust (this is the same as calling ccnv in tail
                    // position).
                    cv_pb = ConvPb::Conv;
                    lft1 = Cow::Owned(el1);
                    lft2 = Cow::Owned(el2);
                    hd1 = bd1;
                    hd2 = bd2;
                    // TODO: v1 and v2 are empty, so probably no need to truncate the stacks, but
                    // we do it anyway because the OCaml implementation does.  We should figure out
                    // whether this is actually necessary, or whether we should retain any
                    // lingering updates and shifts.  This also applies to the top ccnv.
                    v1.clear();
                    v2.clear();
                    // Loop through again.
                },
                (&FTerm::Prod(_, ref c1, ref c2), &FTerm::Prod(_, ref c_1, ref c_2)) => {
                    // Typechecking prods should produce an empty stack.
                    assert!(v1.is_empty() && v2.is_empty());
                    // Luo's system
                    // FIXME: Ew, non-tail recursion!  Can we do the same trick we do for Proj
                    // somehow?
                    let c1 = c1.clone(&self.set);
                    let c_1 = c_1.clone(&infos_.set);
                    self.ccnv(infos_, univ, enga, globals,
                              ConvPb::Conv, &el1, &el2,
                              c1, c_1,
                              i.clone(), s.clone(), ctx, ctx_)?;
                    el1.lift()?;
                    el2.lift()?;
                    // Avoid tail recursion in Rust (this is the same as calling ccnv in tail
                    // position).
                    lft1 = Cow::Owned(el1);
                    lft2 = Cow::Owned(el2);
                    hd1 = c2.clone(&self.set);
                    hd2 = c_2.clone(&infos_.set);
                    // TODO: Figure out stack truncation here (also applies to ccnv above); see
                    // FTerm::Lambda conversion for more details.
                    v1.clear();
                    v2.clear();
                    // Loop through again.
                },
                // Eta-expansion on the fly
                (&FTerm::Lambda(ref ty1, b1, ref e1), _) => {
                    // TODO: Figure out why do we not allow updates or shifts here.
                    if v1.len() != 0 {
                        const E : &'static str = "conversion was given an unreduced term (FLamda)";
                        return Err(Box::new(ConvError::Anomaly(E.into())))
                    }
                    let (_, _, bd1) = FTerm::dest_flambda(&self.set, Subs::mk_clos,
                                                          ty1, b1, e1, ctx)?;
                    v2.eta_expand_stack(ctx_, s.clone());
                    let mut el1 = lft1.into_owned();
                    el1.lift()?;
                    let mut el2 = lft2.into_owned();
                    el2.lift()?;
                    // Avoid tail recursion in Rust (this is the same as calling eqappr in tail
                    // position).
                    cv_pb = ConvPb::Conv;
                    lft1 = Cow::Owned(el1);
                    hd1 = bd1;
                    // No need to clear v1 here, since it's already empty.
                    lft2 = Cow::Owned(el2);
                    // Loop through again.
                },
                (_, &FTerm::Lambda(ref ty2, b2, ref e2)) => {
                    // TODO: Figure out why do we not allow updates or shifts here.
                    if v2.len() != 0 {
                        const E : &'static str = "conversion was given an unreduced term (FLamda)";
                        return Err(Box::new(ConvError::Anomaly(E.into())));
                    }
                    let (_, _, bd2) = FTerm::dest_flambda(&infos_.set, Subs::mk_clos,
                                                          ty2, b2, e2, ctx_)?;
                    v1.eta_expand_stack(ctx, s.clone());
                    let mut el1 = lft1.into_owned();
                    el1.lift()?;
                    let mut el2 = lft2.into_owned();
                    el2.lift()?;
                    // Avoid tail recursion in Rust (this is the same as calling eqappr in tail
                    // position).
                    cv_pb = ConvPb::Conv;
                    lft1 = Cow::Owned(el1);
                    lft2 = Cow::Owned(el2);
                    hd2 = bd2;
                    // No need to clear v2 here, since it's already empty.
                    // Loop through again.
                },
                // only one constant or defined rel (no defined vars in the checker)
                (&FTerm::Flex(fl1), c2) => match self.unfold_reference(globals, fl1, ctx)?
                                                     .map( |(set, def1)| def1.clone(set) ) {
                    Some(def1) => {
                        hd1 = v1.whd_stack(self, globals, def1, ctx, i.clone(), s.clone())?;
                    },
                    None => match *c2 {
                        FTerm::Construct(o) => {
                            let PUniverses(Cons { ind: ref ind2, .. }, _) = **o;
                            // NOTE: We do not catch exactly the same errors that we do in the
                            // OCaml implementation here.  See eta_expand_ind_stack definition for
                            // more information.
                            match Stack::eta_expand_ind_stack(globals,
                                                              &mut infos_.set, &mut self.set,
                                                              ind2, hd2, v2, hd1, v1, ctx_, ctx)? {
                                Some((mut v2, mut v1)) => {
                                    return self.convert_stacks(infos_, univ, enga, globals,
                                                               &lft1, &lft2,
                                                               &mut v1, &mut v2, i, s, ctx, ctx_)
                                },
                                None => return Err(Box::new(ConvError::NotConvertible)),
                            }
                        },
                        _ => return Err(Box::new(ConvError::NotConvertible)),
                    },
                    // Loop through again.
                },
                (c1, &FTerm::Flex(fl2)) => match infos_.unfold_reference(globals, fl2, ctx_)?
                                                       .map( |(set, def2)| def2.clone(set) ) {
                    Some(def2) => {
                        hd2 = v2.whd_stack(infos_, globals, def2, ctx_, i.clone(), s.clone())?;
                    },
                    None => match *c1 {
                        FTerm::Construct(o) => {
                            let PUniverses(Cons { ind: ref ind1, .. }, _) = **o;
                            // NOTE: We do not catch exactly the same errors that we do in the
                            // OCaml implementation here.  See eta_expand_ind_stack definition for
                            // more information.
                            match Stack::eta_expand_ind_stack(globals,
                                                              &mut self.set, &mut infos_.set,
                                                              ind1, hd1, v1, hd2, v2, ctx, ctx_)? {
                                Some((mut v1, mut v2)) => {
                                    return self.convert_stacks(infos_, univ, enga, globals,
                                                               &lft1, &lft2,
                                                               &mut v1, &mut v2, i, s, ctx, ctx_)
                                },
                                None => return Err(Box::new(ConvError::NotConvertible)),
                            }
                        },
                        _ => return Err(Box::new(ConvError::NotConvertible)),
                    },
                    // Loop through again.
                },
                // Inductive types:  MutInd MutConstruct Fix Cofix
                (&FTerm::Ind(o1), &FTerm::Ind(o2)) => {
                    let PUniverses(ref ind1, ref u1) = **o1;
                    let PUniverses(ref ind2, ref u2) = **o2;
                    return if globals.mind_equiv(ind1, ind2) {
                        univ.convert(u1, u2)?;
                        self.convert_stacks(infos_, univ, enga, globals, &lft1, &lft2,
                                            v1, v2, i, s, ctx, ctx_)
                    } else {
                        Err(Box::new(ConvError::NotConvertible))
                    }
                },
                (&FTerm::Construct(o1), &FTerm::Construct(o2)) => {
                    let PUniverses(Cons { ind: ref ind1, idx: j1 }, ref u1) = **o1;
                    let PUniverses(Cons { ind: ref ind2, idx: j2 }, ref u2) = **o2;
                    return if j1 == j2 && globals.mind_equiv(ind1, ind2) {
                        univ.convert(u1, u2)?;
                        self.convert_stacks(infos_, univ, enga, globals, &lft1, &lft2,
                                            v1, v2, i, s, ctx, ctx_)
                    } else {
                        Err(Box::new(ConvError::NotConvertible))
                    }
                },
                // Eta expansion of records
                (&FTerm::Construct(o), _) => {
                    let PUniverses(Cons { ind: ref ind1, .. }, _) = **o;
                    // NOTE: We do not catch exactly the same errors that we do in the
                    // OCaml implementation here.  See eta_expand_ind_stack definition for
                    // more information.
                    match Stack::eta_expand_ind_stack(globals,
                                                      &mut self.set, &mut infos_.set,
                                                      ind1, hd1, v1, hd2, v2, ctx, ctx_)? {
                        Some((mut v1, mut v2)) => {
                            return self.convert_stacks(infos_, univ, enga, globals,
                                                       &lft1, &lft2,
                                                       &mut v1, &mut v2, i, s, ctx, ctx_)
                        },
                        None => return Err(Box::new(ConvError::NotConvertible)),
                    }
                },
                (_, &FTerm::Construct(o)) => {
                    let PUniverses(Cons { ind: ref ind2, .. }, _) = **o;
                    // NOTE: We do not catch exactly the same errors that we do in the
                    // OCaml implementation here.  See eta_expand_ind_stack definition for
                    // more information.
                    match Stack::eta_expand_ind_stack(globals,
                                                      &mut infos_.set, &mut self.set,
                                                      ind2, hd2, v2, hd1, v1, ctx_, ctx)? {
                        Some((mut v2, mut v1)) => {
                            return self.convert_stacks(infos_, univ, enga, globals,
                                                       &lft1, &lft2,
                                                       &mut v1, &mut v2, i, s, ctx, ctx_)
                        },
                        None => return Err(Box::new(ConvError::NotConvertible)),
                    }
                },
                (&FTerm::Fix(o1, n1, ref e1), &FTerm::Fix(o2, n2, ref e2)) => {
                    let Fix(Fix2(ref op1, _), PRec(_, ref tys1, ref cl1)) = **o1;
                    let Fix(Fix2(ref op2, _), PRec(_, ref tys2, ref cl2)) = **o2;
                    if n1 == n2 && op1 == op2 {
                        // op1, tys1, and cl1 should all have the same length, as should
                        // op2, tys2, and cl2, if this term was typechecked.  Therefore,
                        // since op1 == op2, we know tys1.len() == tys2.len() and
                        // cl1.len() == cl2.len().  So we can zip without worrying about
                        // checking that the lengths are the same.
                        let n = cl1.len();
                        for (ty1, ty2) in tys1.iter().zip(tys2.iter()) {
                            let fty1 = e1.mk_clos(&self.set, ty1, ctx)?;
                            let fty2 = e2.mk_clos(&infos_.set, ty2, ctx_)?;
                            // FIXME: Ugh, this is not tail recursive!
                            self.ccnv(infos_, univ, enga, globals, ConvPb::Conv, &el1, &el2,
                                      fty1, fty2, i.clone(), s.clone(), ctx, ctx_)?;
                        }
                        let mut e1 = e1.clone(&self.set); // expensive
                        let mut e2 = e2.clone(&infos_.set); // expensive
                        if let Some(n) = NonZero::new(n) {
                            // TODO: Figure out whether this block should be reachable.  If not, we
                            // should probably assert; if so, we might consider special casing the
                            // None case so we don't have to clone the environments.
                            let n = Idx::new(n)?;
                            e1.liftn(n)?;
                            e2.liftn(n)?;
                            el1.liftn(n)?;
                            el2.liftn(n)?;
                        }
                        for (c1, c2) in cl1.iter().zip(cl2.iter()) {
                            let fc1 = e1.mk_clos(&self.set, c1, ctx)?;
                            let fc2 = e2.mk_clos(&infos_.set, c2, ctx_)?;
                            // FIXME: Ugh, this is not tail recursive!
                            self.ccnv(infos_, univ, enga, globals, ConvPb::Conv, &el1, &el2,
                                      fc1, fc2, i.clone(), s.clone(), ctx, ctx_)?;
                        }
                        return self.convert_stacks(infos_, univ, enga, globals,
                                                   &lft1, &lft2, v1, v2, i, s, ctx, ctx_);
                    } else {
                        return Err(Box::new(ConvError::NotConvertible))
                    }
                },
                (&FTerm::CoFix(o1, n1, ref e1), &FTerm::CoFix(o2, n2, ref e2)) => {
                    let CoFix(_, PRec(_, ref tys1, ref cl1)) = **o1;
                    let CoFix(_, PRec(_, ref tys2, ref cl2)) = **o2;
                    if n1 == n2 && tys1.len() == tys2.len() {
                        // tys1 and cl1 should both have the same length, as should
                        // tys2 and cl2, if this term was typechecked.  Therefore,
                        // since tys1.len() == tys2.len(), we know cl1.len() == cl1.len().
                        // So we can zip without worrying about checking that the lengths
                        // are the same.
                        let n = cl1.len();
                        for (ty1, ty2) in tys1.iter().zip(tys2.iter()) {
                            let fty1 = e1.mk_clos(&self.set, ty1, ctx)?;
                            let fty2 = e2.mk_clos(&infos_.set, ty2, ctx_)?;
                            // FIXME: Ugh, this is not tail recursive!
                            self.ccnv(infos_, univ, enga, globals, ConvPb::Conv, &el1, &el2,
                                      fty1, fty2, i.clone(), s.clone(), ctx, ctx_)?;
                        }
                        let mut e1 = e1.clone(&self.set); // expensive
                        let mut e2 = e2.clone(&infos_.set); // expensive
                        if let Some(n) = NonZero::new(n) {
                            // TODO: Figure out whether this block should be reachable.  If not, we
                            // should probably assert; if so, we might consider special casing the
                            // None case so we don't have to clone the environments.
                            let n = Idx::new(n)?;
                            e1.liftn(n)?;
                            e2.liftn(n)?;
                            el1.liftn(n)?;
                            el2.liftn(n)?;
                        }
                        for (c1, c2) in cl1.iter().zip(cl2.iter()) {
                            let fc1 = e1.mk_clos(&self.set, c1, ctx)?;
                            let fc2 = e2.mk_clos(&infos_.set, c2, ctx_)?;
                            // FIXME: Ugh, this is not tail recursive!
                            self.ccnv(infos_, univ, enga, globals, ConvPb::Conv, &el1, &el2,
                                      fc1, fc2, i.clone(), s.clone(), ctx, ctx_)?;
                        }
                        return self.convert_stacks(infos_, univ, enga, globals,
                                                   &lft1, &lft2, v1, v2, i, s, ctx, ctx_);
                    } else {
                        return Err(Box::new(ConvError::NotConvertible))
                    }
                },
                // Should not happen because both (hd1,v1) and (hd2,v2) are in whnf
                (&FTerm::LetIn(_, _, _, _), _) | (_, &FTerm::LetIn(_, _, _, _)) |
                (&FTerm::Case(_, _, _, _), _) | (_, &FTerm::Case(_, _, _, _)) |
                (&FTerm::CaseT(_, _, _), _) | (_, &FTerm::CaseT(_, _, _)) |
                (&FTerm::App(_, _), _) | (_, &FTerm::App(_, _)) |
                (&FTerm::Clos(_, _), _) | (_, &FTerm::Clos(_, _)) |
                (&FTerm::Lift(_, _), _) | (_, &FTerm::Lift(_, _)) => {
                    panic!("Should not happen because both (hd1,v1) and (hd2,v2) are in whnf")
                },
                // In all other cases, terms are not convertible
                (_, _) => return Err(Box::new(ConvError::NotConvertible)),
            }
        }
    }

    /// Note: stk1 and stk2 must be type-checked beforehand!
    fn convert_stacks<'r, I, S>(&'r mut self, infos_: &'r mut ClosInfos<'id_, 'c, 'b>,
                                univ: &Universes, enga: &Engagement,
                                globals: &'r Globals<'g>,
                                lft1: &Lift, lft2: &Lift,
                                stk1: &Stack<'id, 'a, 'b, I, S>, stk2: &Stack<'id_, 'c, 'b, I, S>,
                                i: I, s: S,
                                ctx: Context<'id, 'a, 'b>,
                                ctx_: Context<'id_, 'c, 'b>) -> ConvResult<()>
        where
            I: Clone + Sync,
            S: Clone + Sync,
    {
        let mut lft1 = lft1.clone(); // expensive, but shouldn't outlive this block.
        let mut lft2 = lft2.clone(); // expensive, but shouldn't outlive this block.
        compare_stacks(
            self, infos_,
            &mut |infos, infos_,
                  globals,
                  (l1, t1), (l2, t2), ctx, ctx_| {
                infos.ccnv(infos_, univ, enga, globals, ConvPb::Conv, l1, l2, t1, t2,
                           i.clone(), s.clone(), ctx, ctx_)
            },
            &mut |globals, ind1, ind2| {
                globals.mind_equiv(ind1, ind2)
            },
            &mut lft1, stk1, &mut lft2, stk2,
            ctx, ctx_,
            globals
        )
    }
}

impl<'b, 'g> Env<'b, 'g> {
    /// Note: t1 and t2 must be type-checked beforehand!
    fn clos_fconv(&mut self, cv_pb: ConvPb, eager_delta: bool,
                      t1: &Constr, t2: &Constr) -> ConvResult<()> {
        let Env { ref mut stratification, ref mut globals, ref mut rel_context } = *self;
        let ref mut rel_context_ = rel_context.clone();
        let univ = stratification.universes();
        let enga = stratification.engagement();
        Set::new( |set| Set::new( |set_| {
            let constr_arenas = Arena::new();
            let constr_arenas_ = Arena::new();
            let constr_arena = constr_arenas.alloc(Arena::with_capacity(0x2000));
            let constr_arena_ = constr_arenas_.alloc(Arena::with_capacity(0x2000));
            let term_arenas = Arena::new();
            let term_arenas_ = Arena::new();
            // (8 * 2^20, just an arbitrary number to start with).
            let term_arena = term_arenas.alloc(Arena::with_capacity(0x800000));
            let term_arena_ = term_arenas_.alloc(Arena::with_capacity(0x800000));
            let ctx = Context::new(term_arena, constr_arena);
            let ctx_ = Context::new(term_arena_, constr_arena_);
            let mut infos =
                Infos::create(set,
                              if eager_delta { Reds::BETADELTAIOTA } else { Reds::BETAIOTAZETA },
                              rel_context.iter_mut())?;
            let mut infos_ =
                Infos::create(set_,
                              if eager_delta { Reds::BETADELTAIOTA } else { Reds::BETAIOTAZETA },
                              rel_context_.iter_mut())?;
            let v1 = t1.inject(&infos.set, ctx)?;
            let v2 = t2.inject(&infos_.set, ctx_)?;
            infos.ccnv(&mut infos_, univ, enga, globals,
                       cv_pb, &Lift::id(), &Lift::id(), v1, v2, (), (), ctx, ctx_)
        } ))
    }

    /// Note: t1 and t2 must be type-checked beforehand!
    fn fconv(&mut self, cv_pb: ConvPb, eager_delta: bool,
             t1: &Constr, t2: &Constr) -> ConvResult<()> {
        if t1.eq(t2) { Ok(()) }
        else { self.clos_fconv(cv_pb, eager_delta, t1, t2) }
    }

    /// Note: t1 and t2 must be type-checked beforehand!
    pub fn conv(&mut self, t1: &Constr, t2: &Constr) -> ConvResult<()> {
        self.fconv(ConvPb::Conv, false, t1, t2)
    }

    /// Note: t1 and t2 must be type-checked beforehand!
    pub fn conv_leq(&mut self, t1: &Constr, t2: &Constr) -> ConvResult<()> {
        self.fconv(ConvPb::Cumul, false, t1, t2)
    }

    /// option for conversion : no compilation for the checker
    ///
    /// Note: t1 and t2 must be type-checked beforehand!
    pub fn vm_conv(&mut self, cv_pb: ConvPb, t1: &Constr, t2: &Constr) -> ConvResult<()> {
        self.fconv(cv_pb, true, t1, t2)
    }

    /// Special-Purpose Reduction

    /// pseudo-reduction rule:
    ///
    /// [hnf_prod_app env s (Prod(_,B)) N --> B[N]
    ///
    /// with an HNF on the first argument to produce a product.
    ///
    /// if this does not work, then we use the string S as part of our
    /// error message.
    ///
    /// NOTE: t must be typechecked beforehand!
    fn hnf_prod_app(&mut self, mut t: Constr, n: &Constr) -> ConvResult<Constr> {
        t.whd_all(self)?;
        match t {
            Constr::Prod(o) => {
                let (_, _, ref b) = *o;
                Ok(b.subst1(n)?)
            },
            _ => Err(Box::new(ConvError::Anomaly("hnf_prod_app: Need a product".into()))),
        }
    }

    /// Pseudo-reduction rule  Prod(x,A,B) a --> B[x\a]
    ///
    /// NOTE: t must be typechecked beforehand!
    pub fn hnf_prod_applist(&mut self, mut t: Constr, nl: &[Constr]) -> ConvResult<Constr> {
        for n in nl.iter().rev() {
            t = self.hnf_prod_app(t, n)?;
        }
        Ok(t)
    }

    /// Dealing with arities
    ///
    /// Recognizing products and arities modulo reduction

    /// NOTE: t1 and t2 must be type-checked beforehand!
    pub fn dest_prod(&mut self, mut c: Constr) -> ConvResult<(Vec<RDecl>, Constr)> {
        let mut m = Vec::new();
        loop {
            c.whd_all(self)?;
            match c {
                Constr::Prod(o) => {
                    let (ref n, ref a, ref c0) = *o;
                    let d = RDecl::LocalAssum(n.clone(), a.clone());
                    self.push_rel(d.clone());
                    m.push(d);
                    c = c0.clone();
                },
                _ => { return Ok((m, c)) }
            }
        }
    }

    /// The same but preserving lets in the context, not internal ones.
    ///
    /// Note: t1 and t2 must be type-checked beforehand!
    pub fn dest_prod_assum(&mut self, mut ty: Constr) -> ConvResult<(Vec<RDecl>, Constr)> {
        let mut l = Vec::new();
        loop {
            ty.whd_allnolet(self)?;
            match ty {
                Constr::Prod(o) => {
                    let (ref x, ref t, ref c) = *o;
                    let d = RDecl::LocalAssum(x.clone(), t.clone());
                    self.push_rel(d.clone());
                    l.push(d);
                    ty = c.clone();
                },
                Constr::LetIn(o) => {
                    let (ref x, ref b, ref t, ref c) = *o;
                    let d = RDecl::LocalDef(x.clone(), b.clone(), ORef(Arc::from(t.clone())));
                    self.push_rel(d.clone());
                    l.push(d);
                    ty = c.clone();
                },
                Constr::Cast(o) => {
                    let (ref c, _, _) = *o;
                    ty = c.clone();
                },
                _ => {
                    let mut ty_ = ty.clone();
                    ty_.whd_all(self)?;
                    if ty_.eq(&ty) { return Ok((l, ty)) }
                    else { ty = ty_; }
                },
            }
        }
    }

    /// Note: t1 and t2 must be type-checked beforehand!
    pub fn dest_lam_assum(&mut self, mut ty: Constr) -> ConvResult<(Vec<RDecl>, Constr)> {
        let mut l = Vec::new();
        loop {
            ty.whd_allnolet(self)?;
            match ty {
                Constr::Lambda(o) => {
                    let (ref x, ref t, ref c) = *o;
                    let d = RDecl::LocalAssum(x.clone(), t.clone());
                    self.push_rel(d.clone());
                    l.push(d);
                    ty = c.clone();
                },
                Constr::LetIn(o) => {
                    let (ref x, ref b, ref t, ref c) = *o;
                    let d = RDecl::LocalDef(x.clone(), b.clone(), ORef(Arc::from(t.clone())));
                    self.push_rel(d.clone());
                    l.push(d);
                    ty = c.clone();
                },
                Constr::Cast(o) => {
                    let (ref c, _, _) = *o;
                    ty = c.clone();
                },
                _ => { return Ok((l, ty)) },
            }
        }
    }

    /// Note: t1 and t2 must be type-checked beforehand!
    pub fn dest_arity(&mut self, c: Constr) -> ConvResult<Arity> {
        let (l, c) = self.dest_prod_assum(c)?;
        match c {
            Constr::Sort(s) => Ok((l, s)),
            _ => Err(Box::new(ConvError::UserError("Not an arity".into()))),
        }
    }
}
