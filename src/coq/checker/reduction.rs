use coq::checker::closure::{
    Context,
    FConstr,
    MRef,
    Stack,
    StackMember,
};
use coq::kernel::esubst::{
    Idx,
    IdxResult,
    Lift,
};
use ocaml::de::{
    Array,
};
use ocaml::values::{
    CaseInfo,
    Constr,
    Cst,
};
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

impl<'a, 'b> LftConstrStack<'a, 'b> {
    pub fn append(&mut self, mut v: Vec<(Lift, FConstr<'a, 'b>)>) {
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
        let mut stk = LftConstrStack(Vec::new());
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
                    stk.push(ZL::Case(o, l.clone() /* expensive */, p.clone(), br.clone()));
                },
            }
        }
        return Ok(stk)
    }
}
