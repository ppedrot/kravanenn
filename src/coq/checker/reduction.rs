use coq::checker::closure::{
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
    Sort,
    SortContents,
};
use std::borrow::{Cow};
use std::iter;
use std::mem;

/// lft_constr_stack_elt
enum ZL<'a, 'b> where 'b: 'a {
    App(Vec<(Lift, FConstr<'a, 'b>)>),
    Proj(&'b Cst, bool, Lift),
    Fix(Lift, FConstr<'a, 'b>, LftConstrStack<'a, 'b>),
    Case(MRef<'b, (CaseInfo, Constr, Constr, Array<Constr>)>, Lift,
         FConstr<'a, 'b>, Vec<FConstr<'a, 'b>>),
}

struct LftConstrStack<'a, 'b>(Vec<ZL<'a, 'b>>) where 'b: 'a;

pub enum ConvError {
    Anomaly(String),
    Env(EnvError),
    Idx(IdxError),
    Univ(UnivError),
    Red(Box<RedError>),
    NotConvertible,
    NotConvertibleVect(usize),
    NotFound,
}

pub type ConvResult<T> = Result<T, ConvError>;

#[derive(Clone,Copy,Debug,Eq,PartialEq)]
pub enum ConvPb {
  Conv,
  Cumul,
}

impl<'a, 'b> ::std::ops::Deref for LftConstrStack<'a, 'b> {
    type Target = Vec<ZL<'a, 'b>>;
    fn deref(&self) -> &Vec<ZL<'a, 'b>> {
        &self.0
    }
}

impl<'a, 'b> ::std::ops::DerefMut for LftConstrStack<'a, 'b> {
    fn deref_mut(&mut self) -> &mut Vec<ZL<'a, 'b>> {
        &mut self.0
    }
}

impl ::std::convert::From<EnvError> for ConvError {
    fn from(e: EnvError) -> Self {
        ConvError::Env(e)
    }
}

impl ::std::convert::From<IdxError> for ConvError {
    fn from(e: IdxError) -> Self {
        ConvError::Idx(e)
    }
}

impl ::std::convert::From<UnivError> for ConvError {
    fn from(e: UnivError) -> Self {
        ConvError::Univ(e)
    }
}

impl ::std::convert::From<Box<RedError>> for ConvError {
    fn from(e: Box<RedError>) -> Self {
        ConvError::Red(e)
    }
}

impl<'a, 'b> LftConstrStack<'a, 'b> {
    fn append(&mut self, mut v: Vec<(Lift, FConstr<'a, 'b>)>) {
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

impl<'a, 'b, Inst, Shft> Stack<'a, 'b, Inst, Shft> {
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

    fn compare_shape(&self, stk: &Self) -> IdxResult<bool> {
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
    fn to_pure(&self, l: &mut Lift,
               ctx: &'a Context<'a, 'b>) -> IdxResult<LftConstrStack<'a, 'b>> {
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
                    stk.append(a.iter().map( |t| (l.clone() /* expensive */, t.clone()))
                                       .collect());
                },
                StackMember::Proj(_, _, p, b, _) => {
                    stk.push(ZL::Proj(p, b, l.clone() /* expensive */ ));
                },
                StackMember::Fix(ref fx, ref a, _) => {
                    let mut lfx = l.clone(); // expensive
                    let pa = a.to_pure(&mut lfx, ctx)?;
                    stk.push(ZL::Fix(lfx, fx.clone(), pa));
                },
                StackMember::CaseT(o, ref env, _) => {
                    let (_, ref p, _, ref br) = **o;
                    stk.push(ZL::Case(o, l.clone() /* expensive */,
                                      env.mk_clos(p, ctx)?, env.mk_clos_vect(br, ctx)?));
                },
                StackMember::Case(o, ref p, ref br, _) => {
                    stk.push(ZL::Case(o, l.clone() /* expensive */, p.clone(),
                                      br.clone() /* expensive */));
                },
            }
        }
        return Ok(stk)
    }

    fn no_arg_available(&self) -> bool {
        for z in self.iter() {
            match *z {
                StackMember::Update(_, _) | StackMember::Shift(_, _) => {},
                StackMember::App(ref v) => { if v.len() != 0 { return false } },
                StackMember::Proj(_, _, _, _, _) | StackMember::Case(_, _, _, _) |
                StackMember::CaseT(_, _, _) | StackMember::Fix(_, _, _) => { return true },
            }
        }
        return true
    }

    fn no_nth_arg_available(&self, mut n: usize) -> bool {
        for z in self.iter() {
            match *z {
                StackMember::Update(_, _) | StackMember::Shift(_, _) => {},
                StackMember::App(ref v) => {
                    n = match n.checked_sub(v.len()) {
                        Some(n) => n,
                        None => { return false },
                    };
                },
                StackMember::Proj(_, _, _, _, _) | StackMember::Case(_, _, _, _) |
                StackMember::CaseT(_, _, _) | StackMember::Fix(_, _, _) => { return true },
            }
        }
        return true
    }

    fn no_case_available(&self) -> bool {
        for z in self.iter() {
            match *z {
                StackMember::Update(_, _) | StackMember::Shift(_, _) | StackMember::App(_) =>
                    {},
                StackMember::Proj(_, _, _, _, _) | StackMember::Case(_, _, _, _) |
                StackMember::CaseT(_, _, _) => { return false },
                StackMember::Fix(_, _, _) => { return true },
            }
        }
        return true
    }

    /// Note: t must be type-checked beforehand!
    fn in_whnf(&self, t: &FConstr<'a, 'b>) -> IdxResult<bool> {
        Ok(match *t.fterm().expect("Tried to lift a locked term") {
            FTerm::LetIn(_, _, _, _) | FTerm::Case(_, _, _, _) | FTerm::CaseT(_, _, _) |
            FTerm::App(_, _) | FTerm::Clos(_, _) | FTerm::Lift(_, _) | FTerm::Cast(_, _, _) =>
                false,
            FTerm::Lambda(_, _, _) => self.no_arg_available(),
            FTerm::Construct(_) => self.no_case_available(),
            FTerm::CoFix(_, _, _) => self.no_case_available(),
            FTerm::Fix(o, n, _) => {
                let Fix(Fix2(ref ri, _), _) = **o;
                // FIXME: Verify that ri[n] in bounds is checked at some point during
                // typechecking.  If not, we must check for it here (we never produce terms
                // that should make it fail the bounds check provided that ri and bds have the
                // same length).
                // TODO: Verify that ri[n] is within usize is checked at some point during
                // typechecking.
                let n = usize::try_from(ri[n])?;
                self.no_nth_arg_available(n)
            },
            FTerm::Flex(_) | FTerm::Prod(_, _, _)/* | FTerm::EVar(_)*/ | FTerm::Ind(_) |
            FTerm::Atom(_) | FTerm::Rel(_) | FTerm::Proj(_, _, _) => true,
        })
    }
}

impl Constr {
    /// Reduction functions

    /// Note: self must be type-checked beforehand!
    pub fn whd_betaiotazeta(self) -> RedResult<Constr> {
        match self {
            Constr::Sort(_) | /* Constr::Var(_) | Constr::Meta(_) | Constr::Evar(_) |*/
            Constr::Const(_) | Constr::Ind(_) | Constr::Construct(_) | Constr::Prod(_) |
            Constr::Lambda(_) | Constr::Fix(_) | Constr::CoFix(_) => Ok(self),
            _ => {
                let mut globals = Globals::default();
                let ref ctx = Context::new();
                let mut infos = Infos::create(Reds::BETAIOTAZETA, &mut globals, iter::empty())?;
                let v = self.inject(ctx)?;
                v.whd_val(&mut infos, ctx)
            }
        }
    }

    /// Note: self must be type-checked beforehand!
    pub fn whd_all<'b, 'g>(self, env: &mut Env<'b, 'g>) -> RedResult<Constr>
        where 'g: 'b,
    {
        match self {
            Constr::Sort(_) | /* Constr::Meta(_) | Constr::Evar(_) |*/
            Constr::Ind(_) | Constr::Construct(_) | Constr::Prod(_) | Constr::Lambda(_) |
            Constr::Fix(_) | Constr::CoFix(_) => Ok(self),
            _ => {
                let Env { ref mut globals, ref mut rel_context, .. } = *env;
                let ref ctx = Context::new();
                let mut infos = Infos::create(Reds::BETADELTAIOTA, globals,
                                              rel_context.iter_mut())?;
                let v = self.inject(ctx)?;
                v.whd_val(&mut infos, ctx)
            }
        }
    }

    /// Note: self must be type-checked beforehand!
    pub fn whd_allnolet<'b, 'g>(self, env: &mut Env<'b, 'g>) -> RedResult<Constr>
        where 'g: 'b,
    {
        match self {
            Constr::Sort(_) | /* Constr::Meta(_) | Constr::Evar(_) |*/
            Constr::Ind(_) | Constr::Construct(_) | Constr::Prod(_) | Constr::Lambda(_) |
            Constr::Fix(_) | Constr::CoFix(_) | Constr::LetIn(_) => Ok(self),
            _ => {
                let Env { ref mut globals, ref mut rel_context, .. } = *env;
                let ref ctx = Context::new();
                let mut infos = Infos::create(Reds::BETADELTAIOTANOLET, globals,
                                              rel_context.iter_mut())?;
                let v = self.inject(ctx)?;
                v.whd_val(&mut infos, ctx)
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
        else { Err(ConvError::NotConvertible) }
    }
}

fn compare_stacks<'a, 'b, I, S, T, F, FMind>
    (f: &mut F, fmind: &mut FMind,
     lft1: &mut Lift, stk1: &Stack<'a, 'b, I, S>,
     lft2: &mut Lift, stk2: &Stack<'a, 'b, I, S>,
     ctx: &'a Context<'a, 'b>,
     env: &mut T) -> ConvResult<()>
    where
        F: FnMut(&mut T, (&Lift, FConstr<'a, 'b>), (&Lift, FConstr<'a, 'b>)) -> ConvResult<()>,
        FMind: FnMut(&T, &Ind, &Ind) -> bool,
{
    /// Prerequisite: call with stacks of the same shape.
    fn cmp_rec<'a, 'b, T, F, FMind>
        (f: &mut F, fmind: &mut FMind,
         pstk1: LftConstrStack<'a, 'b>,
         pstk2: LftConstrStack<'a, 'b>,
         env: &mut T) -> ConvResult<()>
        where
            F: FnMut(&mut T, (&Lift, FConstr<'a, 'b>), (&Lift, FConstr<'a, 'b>)) -> ConvResult<()>,
            FMind: FnMut(&T, &Ind, &Ind) -> bool,
    {
        // The stacks have the same shape, so we don't need to worry about these mismatching.
        for (z1, z2) in pstk1.0.into_iter().zip(pstk2.0.into_iter()) {
            // Not sure why the loop doesn't tail recurse on the first element in OCaml.
            // Presumably, changing the order in which we check these doesn't ruin everything...
            match (z1, z2) {
                (ZL::App(a1), ZL::App(a2)) => {
                    for ((l1, c1), (l2, c2)) in a1.into_iter().zip(a2.into_iter()) {
                        f(env, (&l1, c1), (&l2, c2))?;
                    }
                },
                (ZL::Fix(lfx1, fx1, a1), ZL::Fix(lfx2, fx2, a2)) => {
                    f(env, (&lfx1, fx1), (&lfx2, fx2))?;
                    cmp_rec(f, fmind, a1, a2, env)?;
                },
                (ZL::Proj(_, c1, _), ZL::Proj(_, c2, _)) => {
                    if c1 != c2 { return Err(ConvError::NotConvertible) }
                    // TODO: Figure out why we don't compare lifts here?
                },
                (ZL::Case(o1, l1, p1, br1),
                 ZL::Case(o2, l2, p2, br2)) => {
                    let (ref ci1, _, _, _) = **o1;
                    let (ref ci2, _, _, _) = **o2;
                    if !fmind(env, &ci1.ind, &ci2.ind) {
                        return Err(ConvError::NotConvertible)
                    }
                    f(env, (&l1, p1), (&l2, p2))?;
                    for (c1, c2) in br1.into_iter().zip(br2.into_iter()) {
                        f(env, (&l1, c1), (&l2, c2))?;
                    }
                },
                _ => unreachable!("Stacks should have the same shape."),
            }
        }
        return Ok(())
    }

    if stk1.compare_shape(stk2)? {
        cmp_rec(f, fmind, stk1.to_pure(lft1, ctx)?, stk2.to_pure(lft2, ctx)?, env)
    } else {
        Err(ConvError::NotConvertible)
    }
}

impl Engagement {
    /// Convertibility of sorts
    fn sort_cmp(&self, univ: &Universes, pb: ConvPb, s0: &Sort, s1: &Sort) -> ConvResult<()> {
        match (s0, s1) {
            (&Sort::Prop(c1), &Sort::Prop(c2)) if pb == ConvPb::Cumul => {
                if c1 == SortContents::Pos && c2 == SortContents::Null {
                    return Err(ConvError::NotConvertible)
                }
            },
            (&Sort::Prop(ref c1), &Sort::Prop(ref c2)) => {
                if c1 != c2 {
                    return Err(ConvError::NotConvertible)
                }
            },
            (&Sort::Prop(_), &Sort::Type(_)) => {
                match pb {
                    ConvPb::Cumul => (),
                    _ => return Err(ConvError::NotConvertible),
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
                    return Err(ConvError::NotConvertible)
                }
            },
            (_, _) => return Err(ConvError::NotConvertible),
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

impl<'a, 'b, 'g> Infos<'a, 'b, 'g, FConstr<'a, 'b>> {
    fn unfold_projection_infos<I, S>(&self, p: &'b Cst, b: bool,
                                     i: I) -> ConvResult<StackMember<'a, 'b, I, S>> {
        let pb = self.globals().lookup_projection(p).ok_or(ConvError::NotFound)??;
        // TODO: Verify that npars and arg being within usize is checked at some
        // point during typechecking.
        let npars = usize::try_from(pb.npars).map_err(IdxError::from)?;
        let arg = usize::try_from(pb.arg).map_err(IdxError::from)?;
        Ok(StackMember::Proj(npars, arg, p, b, i))
    }

    /// Conversion between [lft1]term1 and [lft2]term2.
    /// Note: term1 and term2 must be type-checked beforehand!
    fn ccnv<I, S>(&mut self, univ: &Universes, enga: &Engagement, cv_pb: ConvPb,
                  lft1: &Lift, lft2: &Lift, term1: FConstr<'a, 'b>, term2: FConstr<'a, 'b>,
                  i: I, s: S, ctx: &'a Context<'a, 'b>) -> ConvResult<()>
        where
            I: Clone,
            S: Clone,
    {
        self.eqappr(univ, enga, cv_pb,
                    lft1, term1, &mut Stack::new(),
                    lft2, term2, &mut Stack::new(),
                    i, s, ctx)
    }

    /// Conversion between [lft1](hd1 v1) and [lft2](hd2 v2)
    /// Note: term1 and term2 must be type-checked beforehand in the context of stk1 and stk2,
    /// respectively!
    fn eqappr<I, S>(&mut self, univ: &Universes, enga: &Engagement, mut cv_pb: ConvPb,
                    lft1: &Lift, mut hd1: FConstr<'a, 'b>, v1: &mut Stack<'a, 'b, I, S>,
                    lft2: &Lift, mut hd2: FConstr<'a, 'b>, v2: &mut Stack<'a, 'b, I, S>,
                    i: I, s: S, ctx: &'a Context<'a, 'b>) -> ConvResult<()>
        where
            I: Clone,
            S: Clone,
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
            loop {
                hd1 = v1.whd_stack(self, hd1, ctx, i.clone(), s.clone())?;
                hd2 = v2.whd_stack(self, hd2, ctx, i.clone(), s.clone())?;
                // Now, whd_stack on term2 might have modified st1 (due to sharing),
                // and st1 might not be in whnf anymore. If so, we iterate ccnv.
                // FIXME: Actually prove the above maybe?  Or maybe it's not true and this can loop
                // forever.  Alternately, maybe fix this in a less ad hoc way?
                if v1.in_whnf(&hd1)? { break }
            }
            // compute the lifts that apply to the head of the term (hd1 and hd2)
            // expensive, but shouldn't outlive this block.
            let mut el1 = lft1.as_ref().clone();
            // expensive, but shouldn't outlive this block.
            let mut el2 = lft2.as_ref().clone();
            v1.el(&mut el1)?;
            v2.el(&mut el2)?;
            match (hd1.fterm().expect("Tried to lift a locked term"),
                   hd2.fterm().expect("Tried to lift a locked term")) {
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
                        self.convert_stacks(univ, enga, &lft1, &lft2, v1, v2, i, s, ctx)
                    } else { Err(ConvError::NotConvertible) }
                },
                // 2 constants or 2 defined rels (no locally defined vars in the checker)
                (&FTerm::Flex(fl1), &FTerm::Flex(fl2)) => {
                    // First try intentional equality
                    // TODO: This seems like it might be a sneakily slow step... investigate.
                    let res = if fl1 == fl2 {
                        self.convert_stacks(univ, enga, &lft1, &lft2, v1, v2,
                                            i.clone(), s.clone(), ctx)
                    } else { Err(ConvError::NotConvertible) };
                    match res {
                        Err(ConvError::NotConvertible) => {
                            // else the oracle tells which constant is to be expanded.
                            if fl1.oracle_order(&fl2) {
                                match self.unfold_reference(fl1, ctx)?
                                          .map( |def1| def1.clone() ) {
                                    Some(def1) => {
                                        hd1 = v1.whd_stack(self, def1, ctx,
                                                           i.clone(), s.clone())?;
                                    },
                                    None => match self.unfold_reference(fl2, ctx)?
                                                      .map( |def2| def2.clone() ) {
                                        Some(def2) => {
                                            hd2 = v2.whd_stack(self, def2, ctx,
                                                               i.clone(), s.clone())?;
                                        },
                                        None => return Err(ConvError::NotConvertible),
                                    },
                                }
                            } else {
                                match self.unfold_reference(fl2, ctx)?
                                          .map( |def2| def2.clone() ) {
                                    Some(def2) => {
                                        hd2 = v2.whd_stack(self, def2, ctx,
                                                           i.clone(), s.clone())?;
                                    },
                                    None => match self.unfold_reference(fl1, ctx)?
                                                      .map( |def1| def1.clone() ) {
                                        Some(def1) => {
                                            hd1 = v1.whd_stack(self, def1, ctx,
                                                               i.clone(), s.clone())?;
                                        },
                                        None => return Err(ConvError::NotConvertible),
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
                    let s1 = self.unfold_projection_infos(p1, b1, i.clone())?;
                    v1.push(s1);
                    hd1 = v1.whd_stack(self, def1.clone(), ctx, i.clone(), s.clone())?;
                    // Loop through and try again with the projection unfolded.
                },
                (_, &FTerm::Proj(p2, b2, ref def2)) => {
                    let s2 = self.unfold_projection_infos(p2, b2, i.clone())?;
                    v2.push(s2);
                    hd2 = v2.whd_stack(self, def2.clone(), ctx, i.clone(), s.clone())?;
                    // Loop through and try again with the projection unfolded.
                },
                // other constructors
                (&FTerm::Lambda(ref ty1, b1, ref e1), &FTerm::Lambda(ref ty2, b2, ref e2)) => {
                    // Typechecking lambdas should produce an empty stack.
                    // Inconsistency: we tolerate that v1, v2 contain shift and update but
                    // we throw them away
                    assert!(v1.is_empty() && v2.is_empty());
                    let (_, ty1, bd1) = FTerm::dest_flambda(Subs::mk_clos, ty1, b1, e1, ctx)?;
                    let (_, ty2, bd2) = FTerm::dest_flambda(Subs::mk_clos, ty2, b2, e2, ctx)?;
                    // FIXME: Ew, non-tail recursion!  Can we do the same trick we do for Proj
                    // somehow?
                    self.ccnv(univ, enga, ConvPb::Conv, &el1, &el2, ty1, ty2,
                              i.clone(), s.clone(), ctx)?;
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
                    self.ccnv(univ, enga, ConvPb::Conv, &el1, &el2, c1.clone(), c_1.clone(),
                              i.clone(), s.clone(), ctx)?;
                    el1.lift()?;
                    el2.lift()?;
                    // Avoid tail recursion in Rust (this is the same as calling ccnv in tail
                    // position).
                    lft1 = Cow::Owned(el1);
                    lft2 = Cow::Owned(el2);
                    hd1 = c2.clone();
                    hd2 = c_2.clone();
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
                        return Err(
                            ConvError::Anomaly("conversion was given an unreduced term (FLamda)"
                                               .into()));
                    }
                    let (_, _, bd1) = FTerm::dest_flambda(Subs::mk_clos, ty1, b1, e1, ctx)?;
                    v2.eta_expand_stack(ctx, s.clone());
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
                        return Err(
                            ConvError::Anomaly("conversion was given an unreduced term (FLamda)"
                                               .into()));
                    }
                    let (_, _, bd2) = FTerm::dest_flambda(Subs::mk_clos, ty2, b2, e2, ctx)?;
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
                (&FTerm::Flex(fl1), c2) => match self.unfold_reference(fl1, ctx)?
                                                     .map( |def1| def1.clone() ) {
                    Some(def1) => {
                        hd1 = v1.whd_stack(self, def1, ctx, i.clone(), s.clone())?;
                    },
                    None => match *c2 {
                        FTerm::Construct(o) => {
                            let PUniverses(Cons { ind: ref ind2, .. }, _) = **o;
                            // NOTE: We do not catch exactly the same errors that we do in the
                            // OCaml implementation here.  See eta_expand_ind_stack definition for
                            // more information.
                            match Stack::eta_expand_ind_stack(self.globals(),
                                                              ind2, hd2, v2, hd1, v1, ctx)? {
                                Some((mut v2, mut v1)) => {
                                    return self.convert_stacks(univ, enga, &lft1, &lft2,
                                                               &mut v1, &mut v2, i, s, ctx)
                                },
                                None => return Err(ConvError::NotConvertible),
                            }
                        },
                        _ => return Err(ConvError::NotConvertible),
                    },
                    // Loop through again.
                },
                (c1, &FTerm::Flex(fl2)) => match self.unfold_reference(fl2, ctx)?
                                                     .map( |def2| def2.clone() ) {
                    Some(def2) => {
                        hd2 = v2.whd_stack(self, def2, ctx, i.clone(), s.clone())?;
                    },
                    None => match *c1 {
                        FTerm::Construct(o) => {
                            let PUniverses(Cons { ind: ref ind1, .. }, _) = **o;
                            // NOTE: We do not catch exactly the same errors that we do in the
                            // OCaml implementation here.  See eta_expand_ind_stack definition for
                            // more information.
                            match Stack::eta_expand_ind_stack(self.globals(),
                                                              ind1, hd1, v1, hd2, v2, ctx)? {
                                Some((mut v1, mut v2)) => {
                                    return self.convert_stacks(univ, enga, &lft1, &lft2,
                                                               &mut v1, &mut v2, i, s, ctx)
                                },
                                None => return Err(ConvError::NotConvertible),
                            }
                        },
                        _ => return Err(ConvError::NotConvertible),
                    },
                    // Loop through again.
                },
                // Inductive types:  MutInd MutConstruct Fix Cofix
                (&FTerm::Ind(o1), &FTerm::Ind(o2)) => {
                    let PUniverses(ref ind1, ref u1) = **o1;
                    let PUniverses(ref ind2, ref u2) = **o2;
                    return if self.mind_equiv(ind1, ind2) {
                        univ.convert(u1, u2)?;
                        self.convert_stacks(univ, enga, &lft1, &lft2, v1, v2, i, s, ctx)
                    } else {
                        Err(ConvError::NotConvertible)
                    }
                },
                (&FTerm::Construct(o1), &FTerm::Construct(o2)) => {
                    let PUniverses(Cons { ind: ref ind1, idx: j1 }, ref u1) = **o1;
                    let PUniverses(Cons { ind: ref ind2, idx: j2 }, ref u2) = **o2;
                    return if j1 == j2 && self.mind_equiv(ind1, ind2) {
                        univ.convert(u1, u2)?;
                        self.convert_stacks(univ, enga, &lft1, &lft2, v1, v2, i, s, ctx)
                    } else {
                        Err(ConvError::NotConvertible)
                    }
                },
                // Eta expansion of records
                (&FTerm::Construct(o), _) => {
                    let PUniverses(Cons { ind: ref ind1, .. }, _) = **o;
                    // NOTE: We do not catch exactly the same errors that we do in the
                    // OCaml implementation here.  See eta_expand_ind_stack definition for
                    // more information.
                    match Stack::eta_expand_ind_stack(self.globals(),
                                                      ind1, hd1, v1, hd2, v2, ctx)? {
                        Some((mut v1, mut v2)) => {
                            return self.convert_stacks(univ, enga, &lft1, &lft2,
                                                       &mut v1, &mut v2, i, s, ctx)
                        },
                        None => return Err(ConvError::NotConvertible),
                    }
                },
                (_, &FTerm::Construct(o)) => {
                    let PUniverses(Cons { ind: ref ind2, .. }, _) = **o;
                    // NOTE: We do not catch exactly the same errors that we do in the
                    // OCaml implementation here.  See eta_expand_ind_stack definition for
                    // more information.
                    match Stack::eta_expand_ind_stack(self.globals(),
                                                      ind2, hd2, v2, hd1, v1, ctx)? {
                        Some((mut v2, mut v1)) => {
                            return self.convert_stacks(univ, enga, &lft1, &lft2,
                                                       &mut v1, &mut v2, i, s, ctx)
                        },
                        None => return Err(ConvError::NotConvertible),
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
                            let fty1 = e1.mk_clos(ty1, ctx)?;
                            let fty2 = e2.mk_clos(ty2, ctx)?;
                            // FIXME: Ugh, this is not tail recursive!
                            self.ccnv(univ, enga, ConvPb::Conv, &el1, &el2,
                                      fty1, fty2, i.clone(), s.clone(), ctx)?;
                        }
                        let mut e1 = e1.clone(); // expensive
                        let mut e2 = e2.clone(); // expensive
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
                            let fc1 = e1.mk_clos(c1, ctx)?;
                            let fc2 = e2.mk_clos(c2, ctx)?;
                            // FIXME: Ugh, this is not tail recursive!
                            self.ccnv(univ, enga, ConvPb::Conv, &el1, &el2,
                                      fc1, fc2, i.clone(), s.clone(), ctx)?;
                        }
                        return self.convert_stacks(univ, enga, &lft1, &lft2, v1, v2, i, s, ctx);
                    } else {
                        return Err(ConvError::NotConvertible)
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
                            let fty1 = e1.mk_clos(ty1, ctx)?;
                            let fty2 = e2.mk_clos(ty2, ctx)?;
                            // FIXME: Ugh, this is not tail recursive!
                            self.ccnv(univ, enga, ConvPb::Conv, &el1, &el2,
                                      fty1, fty2, i.clone(), s.clone(), ctx)?;
                        }
                        let mut e1 = e1.clone(); // expensive
                        let mut e2 = e2.clone(); // expensive
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
                            let fc1 = e1.mk_clos(c1, ctx)?;
                            let fc2 = e2.mk_clos(c2, ctx)?;
                            // FIXME: Ugh, this is not tail recursive!
                            self.ccnv(univ, enga, ConvPb::Conv, &el1, &el2,
                                      fc1, fc2, i.clone(), s.clone(), ctx)?;
                        }
                        return self.convert_stacks(univ, enga, &lft1, &lft2, v1, v2, i, s, ctx);
                    } else {
                        return Err(ConvError::NotConvertible)
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
                (_, _) => return Err(ConvError::NotConvertible),
            }
        }
    }

    fn convert_stacks<I, S>(&mut self, univ: &Universes, enga: &Engagement,
                            lft1: &Lift, lft2: &Lift,
                            stk1: &Stack<'a, 'b, I, S>, stk2: &Stack<'a, 'b, I, S>,
                            i: I, s: S, ctx: &'a Context<'a, 'b>) -> ConvResult<()>
        where
            I: Clone,
            S: Clone,
    {
        let mut lft1 = lft1.clone(); // expensive, but shouldn't outlive this block.
        let mut lft2 = lft2.clone(); // expensive, but shouldn't outlive this block.
        compare_stacks(
            &mut |infos: &mut Self, (l1, t1), (l2, t2)|
                infos.ccnv(univ, enga, ConvPb::Conv, l1, l2, t1, t2, i.clone(), s.clone(), ctx),
            &mut Self::mind_equiv,
            &mut lft1, stk1, &mut lft2, stk2,
            ctx,
            self
        )
    }
}
