use coq::kernel::esubst::{Idx, IdxError, Lift, IdxResult};
use core::convert::TryFrom;
use core::nonzero::NonZero;
use ocaml::de::{ORef, Array};
use ocaml::values::{
    CoFix,
    Constr,
    Cst,
    Fix,
    Fix2,
    Ind,
    Name,
    PRec,
    PUniverses,
    RDecl,
    Sort,
    SortContents,
};
use std::cell::Cell;
use std::option::{NoneError};
use std::rc::Rc;

#[derive(Clone,Copy)]
pub enum Info {
    Closed,
    Open,
    Unknown,
}

/// Exception raised if a variable lookup is out of range.
pub enum SubstError {
    LocalOccur,
    Idx(IdxError),
}

pub struct Substituend<A> {
    info: Cell<Info>,
    it: A,
}

pub type Arity = (Vec<RDecl>, ORef<Sort>);

impl<A> Substituend<A> {
    pub fn make(c: A) -> Self {
        Substituend {
            info: Cell::new(Info::Unknown),
            it: c,
        }
    }
}

impl ::std::convert::From<IdxError> for SubstError {
    fn from(e: IdxError) -> Self {
        SubstError::Idx(e)
    }
}

impl<'a> Substituend<&'a Constr> {
    /// 1st : general case
    pub fn lift(&self, depth: Idx) -> IdxResult<Constr> {
        match self.info.get() {
            Info::Closed => Ok(self.it.clone()),
            Info::Open => self.it.lift(depth),
            Info::Unknown => {
                self.info.set(if self.it.closed0()? { Info::Closed } else { Info::Open });
                // Recursion is okay here since it can only loop once.
                self.lift(depth)
            },
        }
    }
}

impl Constr {
    /// Constructions as implemented

    pub fn strip_outer_cast(&self) -> &Self {
        let mut c = self;
        while let Constr::Cast(ref o) = *c {
            let (ref c_, _, _) = **o;
            c = c_;
        }
        c
    }

    /// Warning: returned argument order is reversed from the OCaml implementation!
    ///
    /// We could also consider a VecDeque, but we only ever append one way so it seems like a
    /// waste...
    pub fn collapse_appl<'a>(&'a self, cl: &'a [Self]) -> (&Self, Vec<&Self>) {
        // FIXME: Consider a non-allocating version that works as an intrusive iterator, or a
        // reversed iterator; both would suffice for our purposes here.
        let mut f = self;
        // Argument order is reversed, so extending to the right is prepending.
        let mut cl2: Vec<&Self> = cl.iter().collect();
        while let Constr::App(ref o) = *f.strip_outer_cast() {
            let (ref g, ref cl1) = **o;
            f = g;
            cl2.extend(cl1.iter().rev());
        }
        (f, cl2)
    }

    /// This method has arguments in the same order as the OCaml.
    pub fn decompose_app(&self) -> (&Self, Vec<&Self>) {
        if let Constr::App(ref o) = *self {
            let (ref f, ref cl) = **o;
            let (f, mut cl) = f.collapse_appl(cl);
            cl.reverse();
            (f, cl)
        } else {
            (self, Vec::new())
        }
    }

    pub fn applist(self, l: Vec<Constr>) -> Constr {
        Constr::App(ORef(Rc::from((self, Array(Rc::from(l))))))
    }

    /// Functions for dealing with Constr terms

    /// Occurring

    pub fn iter_with_binders<T, G, F, E>(&self, g: G, f: F, l: &T) -> Result<(), E>
        where
            T: Clone,
            G: Fn(&mut T) -> Result<(), E>,
            F: Fn(&Constr, &T) -> Result<(), E>,
    {
        Ok(match *self {
            Constr::Rel(_) | Constr::Sort(_) | Constr::Const(_) | Constr::Ind(_)
            | Constr::Construct(_) => (),
            Constr::Cast(ref o) => {
                let (ref c, _, ref t) = **o;
                f(c, l)?;
                f(t, l)?;
            },
            Constr::Prod(ref o) => {
                let (_, ref t, ref c) = **o;
                f(t, l)?;
                let mut l = l.clone(); // expensive
                g(&mut l)?;
                f(c, &l)?;
            },
            Constr::Lambda(ref o) => {
                let (_, ref t, ref c) = **o;
                f(t, l)?;
                let mut l = l.clone(); // expensive
                g(&mut l)?;
                f(c, &l)?;
            },
            Constr::LetIn(ref o) => {
                let (_, ref b, ref t, ref c) = **o;
                f(b, l)?;
                f(t, l)?;
                let mut l = l.clone(); // expensive
                g(&mut l)?;
                f(c, &l)?;
            },
            Constr::App(ref o) => {
                let (ref c, ref al) = **o;
                f(c, l)?;
                for x in al.iter() {
                    f(x, l)?;
                }
            },
            // | Evar (e,al) -> Array.iter (f n) l,
            Constr::Case(ref o) => {
                let (_, ref p, ref c, ref bl) = **o;
                f(p, l)?;
                f(c, l)?;
                for x in bl.iter() {
                    f(x, l)?;
                }
            },
            Constr::Fix(ref o) => {
                let Fix(_, PRec(_, ref tl, ref bl)) = **o;
                let len = tl.len();
                for x in tl.iter() {
                    f(x, l)?;
                }
                let mut l = l.clone(); // expensive
                for _ in 0..len {
                    g(&mut l)?;
                }
                for x in bl.iter() {
                    f(x, &l)?;
                }
            },
            Constr::CoFix(ref o) => {
                let CoFix(_, PRec(_, ref tl, ref bl)) = **o;
                let len = tl.len();
                for x in tl.iter() {
                    f(x, l)?;
                }
                let mut l = l.clone(); // expensive
                for _ in 0..len {
                    g(&mut l)?;
                }
                for x in bl.iter() {
                    f(x, &l)?;
                }
            },
            Constr::Proj(ref o) => {
                let (_, ref c) = **o;
                f(c, l)?;
            },
            // Constr::Meta(_) | Constr::Var(_) | Constr::Evar(_) => unreachable!("")
        })
    }


    /// (closedn n M) raises LocalOccur if a variable of height greater than n
    /// occurs in M, returns () otherwise
    fn closed_rec(&self, n: &i64) -> Result<(), SubstError> {
        match *self {
            Constr::Rel(m) if m > *n => Err(SubstError::LocalOccur),
            _ => self.iter_with_binders(|i| {
                *i = i.checked_add(1).ok_or(SubstError::Idx(IdxError::from(NoneError)))?;
                return Ok(())
            }, Self::closed_rec, n),
        }
    }

    pub fn closedn(&self, n: i64) -> IdxResult<bool> {
        match self.closed_rec(&n) {
            Ok(()) => Ok(true),
            Err(SubstError::LocalOccur) => Ok(false),
            Err(SubstError::Idx(e)) => Err(e),
        }
    }

    /// [closed0 M] is true iff [M] is a (deBruijn) closed term
    pub fn closed0(&self) -> IdxResult<bool> {
        self.closedn(0)
    }

    /// Lifting
    pub fn map_constr_with_binders<T, G, F, E>(&self, g: G, f: F, l: &T) -> Result<Constr, E>
        where
            T: Clone,
            G: Fn(&mut T) -> Result<(), E>,
            F: Fn(&Constr, &T) -> Result<Constr, E>,
    {
        Ok(match *self {
            Constr::Rel(_) | Constr::Sort(_) | Constr::Const(_) | Constr::Ind(_)
            | Constr::Construct(_) => self.clone(),
            Constr::Cast(ref o) => {
                let (ref c, k, ref t) = **o;
                let c = f(c, l)?;
                let t = f(t, l)?;
                Constr::Cast(ORef(Rc::from((c, k, t))))
            },
            Constr::Prod(ref o) => {
                let (ref na, ref t, ref c) = **o;
                let t = f(t, l)?;
                let mut l = l.clone(); // expensive
                g(&mut l)?;
                let c = f(c, &l)?;
                Constr::Prod(ORef(Rc::from((na.clone(), t, c))))
            },
            Constr::Lambda(ref o) => {
                let (ref na, ref t, ref c) = **o;
                let t = f(t, l)?;
                let mut l = l.clone(); // expensive
                g(&mut l)?;
                let c = f(c, &l)?;
                Constr::Lambda(ORef(Rc::from((na.clone(), t, c))))
            },
            Constr::LetIn(ref o) => {
                let (ref na, ref b, ref t, ref c) = **o;
                let b = f(b, l)?;
                let t = f(t, l)?;
                let mut l = l.clone(); // expensive
                g(&mut l)?;
                let c = f(c, &l)?;
                Constr::LetIn(ORef(Rc::from((na.clone(), b, t, c))))
            },
            Constr::App(ref o) => {
                let (ref c, ref al) = **o;
                let c = f(c, l)?;
                // expensive -- allocates a Vec
                let al: Result<Vec<_>, _> = al.iter().map( |x| f(x, l) ).collect();
                Constr::App(ORef(Rc::from((c, Array(Rc::from(al?))))))
            },
            // | Evar (e,al) -> Evar (e, Array.map (f l) al)
            Constr::Case(ref o) => {
                let (ref ci, ref p, ref c, ref bl) = **o;
                let p = f(p, l)?;
                let c = f(c, l)?;
                // expensive -- allocates a Vec
                let bl: Result<Vec<_>, _> = bl.iter().map( |x| f(x, l) ).collect();
                Constr::Case(ORef(Rc::from((ci.clone(), p, c, Array(Rc::from(bl?))))))
            },
            Constr::Fix(ref o) => {
                let Fix(ref ln, PRec(ref lna, ref tl, ref bl)) = **o;
                let len = tl.len();
                // expensive -- allocates a Vec
                let tl: Result<Vec<_>, _> = tl.iter().map( |x| f(x, l) ).collect();
                let mut l = l.clone(); // expensive
                for _ in 0..len {
                    g(&mut l)?;
                }
                // expensive -- allocates a Vec
                let bl: Result<Vec<_>, _> = bl.iter().map( |x| f(x, &l) ).collect();
                Constr::Fix(ORef(Rc::from(Fix(ln.clone(),
                                              PRec(lna.clone(),
                                                   Array(Rc::from(tl?)),
                                                   Array(Rc::from(bl?)))))))
            },
            Constr::CoFix(ref o) => {
                let CoFix(ln, PRec(ref lna, ref tl, ref bl)) = **o;
                let len = tl.len();
                // expensive -- allocates a Vec
                let tl: Result<Vec<_>, _> = tl.iter().map( |x| f(x, l) ).collect();
                let mut l = l.clone(); // expensive
                for _ in 0..len {
                    g(&mut l)?;
                }
                // expensive -- allocates a Vec
                let bl: Result<Vec<_>, _> = bl.iter().map( |x| f(x, &l) ).collect();
                Constr::CoFix(ORef(Rc::from(CoFix(ln.clone(),
                                                  PRec(lna.clone(),
                                                       Array(Rc::from(tl?)),
                                                       Array(Rc::from(bl?)))))))
            },
            Constr::Proj(ref o) => {
                let (ref p, ref c) = **o;
                let c = f(c, l)?;
                Constr::Proj(ORef(Rc::from((p.clone(), c))))
            },
            // Constr::Meta(_) | Constr::Var(_) | Constr::Evar(_) => unreachable!("")
        })
    }

    /// The generic lifting function
    pub fn exliftn(&self, el: &Lift) -> IdxResult<Constr> {
        match *self {
            Constr::Rel(i) =>
                Ok(Constr::Rel(i32::from(el.reloc_rel(Idx::new(NonZero::new(i)?)?)?) as i64)),
            _ => self.map_constr_with_binders(Lift::lift, Self::exliftn, el)
        }
    }

    /// Lifting the binding depth across k bindings

    pub fn liftn(&self, k: Idx, n: Idx) -> IdxResult<Constr> {
        let mut el = Lift::id();
        el.shift(k)?;
        if let Some(n) = n.checked_sub(Idx::ONE).expect("n > 0 - 1 ≥ 0") {
            el.liftn(n)?;
        }
        if el.is_id() {
            Ok(self.clone())
        } else {
            self.exliftn(&el)
        }
    }

    pub fn lift(&self, k: Idx) -> IdxResult<Constr> {
        self.liftn(k, Idx::ONE)
    }

    /// Substituting

    fn substrec(&self,
                &(depth, ref lamv): &(Option<Idx>, &[Substituend<&Constr>])) -> IdxResult<Constr> {
        match *self {
            Constr::Rel(k_) => {
                // FIXME: For below, ensure u32 to usize is always a valid cast.
                let d = depth.map(u32::from).unwrap_or(0) as usize;
                // NOTE: This can only fail if we compile with addresses under 64 bits.
                let k = usize::try_from(k_)?;
                // After the above, we know k is a valid non-negative i64.
                if k <= d {
                    Ok(self.clone())
                } else if let Some(sub) = lamv.get(k - d - 1) {
                    // Note that k - d above is valid (and > 0) because 0 ≤ d < k;
                    // therefore, 0 ≤ k - depth - 1, so that is valid.
                    // Also, the unwrap() below is granted because 0 < k.
                    // FIXME: There is a better way of dealing with this.
                    sub.lift(depth.unwrap())
                } else {
                    // k - lamv.len() is valid (and > 0) because if lamv.get(k - d - 1) = None,
                    // lamv.len() ≤ k - d - 1 < k - d ≤ k (i.e. lamv.len() < k), so
                    // 0 < k - lamv.len() (k - lamv.len() is positive).
                    // Additionally, since we know 0 < lamv.len() < k, and k is a valid positive
                    // i64, lamv.len() is also a valid positive i64.
                    // So the cast is valid.
                    Ok(Constr::Rel(k_ - lamv.len() as i64))
                }
            },
            _ => self.map_constr_with_binders(
                |&mut (ref mut depth, _)| {
                    *depth = match *depth {
                        None => Some(Idx::ONE),
                        Some(depth) => Some(depth.checked_add(Idx::ONE)?),
                    };
                    Ok(())
                },
                Self::substrec,
                &(depth, lamv)
            )
        }
    }

    /// (subst1 M c) substitutes M for Rel(1) in c
    /// we generalise it to (substl [M1,...,Mn] c) which substitutes in parallel
    /// M1,...,Mn for respectively Rel(1),...,Rel(n) in c
    pub fn substn_many(&self, lamv: &[Substituend<&Constr>], n: Option<Idx>) -> IdxResult<Constr> {
        let lv = lamv.len();
        if lv == 0 { return Ok(self.clone()) }
        else { self.substrec(&(n, lamv)) }
    }

    pub fn substnl(&self, laml: &[Constr], n: Option<Idx>) -> IdxResult<Constr> {
        let lamv: Vec<_> = laml.iter().map(Substituend::make).collect();
        self.substn_many(&lamv, n)
    }

    pub fn substl(&self, laml: &[Constr]) -> IdxResult<Constr> {
        self.substnl(laml, None)
    }

    pub fn subst1(&self, lam: &Constr) -> IdxResult<Constr> {
        let lamv = [Substituend::make(lam)];
        self.substn_many(&lamv, None)
    }

    /// Iterate lambda abstractions

    /* /// compose_lam [x1:T1;..;xn:Tn] b = [x1:T1]..[xn:Tn]b
    pub fn compose_lam<I>(&self, l: I)
        where I: Iterator<Elem=&ORef<(Name, Constr, Constr)>> {
    } */
    /* val decompose_lam : constr -> (name * constr) list * constr */
    /*
    let compose_lam l b =
      let rec lamrec = function
        | ([], b)       -> b
        | ((v,t)::l, b) -> lamrec (l, Lambda (v,t,b))
      in
      lamrec (l,b) */

    /// Transforms a lambda term [x1:T1]..[xn:Tn]T into the pair
    /// ([(x1,T1);...;(xn,Tn)],T), where T is not a lambda
    ///
    /// (For technical reasons, we carry around the nested constructor as well, but we never need
    /// it).
    pub fn decompose_lam(&self) -> (Vec<&ORef<(Name, Constr, Constr)>>, &Constr) {
        let mut l = Vec::new();
        let mut c = self;
        loop {
            match *c {
                Constr::Lambda(ref o) => {
                    let (/*ref x, ref t*/_, _, ref c_) = **o;
                    /* l.push((x, t)); */
                    l.push(o);
                    c = c_;
                },
                Constr::Cast(ref o) => {
                    let (ref c_, _, _) = **o;
                    c = c_;
                },
                _ => {
                    return (l, c)
                }
            }
        }
    }

    /// Alpha conversion functions

    /// alpha conversion : ignore print names and casts
    pub fn compare<F>(&self, t2: &Self, f: F) -> bool
        where F: Fn(&Self, &Self) -> bool,
    {
        // FIXME: This is (in some cases) unnecessarily tail recursive.  We could reduce the amount
        // of recursion required (and the likelihood that we'll get a stack overflow) by making the
        // function slightly less generic.
        match (self, t2) {
            (&Constr::Rel(n1), &Constr::Rel(n2)) => n1 == n2,
            // | Meta m1, Meta m2 -> Int.equal m1 m2
            // | Var id1, Var id2 -> Id.equal id1 id2
            (&Constr::Sort(ref s1), &Constr::Sort(ref s2)) => s1.compare(s2),
            (&Constr::Cast(ref o1), _) => {
                let (ref c1, _, _) = **o1;
                f(c1, t2)
            },
            (_, &Constr::Cast(ref o2)) => {
                let (ref c2, _, _) = **o2;
                f(self, c2)
            },
            (&Constr::Prod(ref o1), &Constr::Prod(ref o2)) => {
                let (_, ref t1, ref c1) = **o1;
                let (_, ref t2, ref c2) = **o2;
                f(t1, t2) && f(c1, c2)
            },
            (&Constr::Lambda(ref o1), &Constr::Lambda(ref o2)) => {
                let (_, ref t1, ref c1) = **o1;
                let (_, ref t2, ref c2) = **o2;
                f(t1, t2) && f(c1, c2)
            },
            (&Constr::LetIn(ref o1), &Constr::LetIn(ref o2)) => {
                let (_, ref b1, ref t1, ref c1) = **o1;
                let (_, ref b2, ref t2, ref c2) = **o2;
                f(b1, b2) && f(t1, t2) && f(c1, c2)
            },
            (&Constr::App(ref o1), &Constr::App(ref o2)) => {
                let (ref c1, ref l1) = **o1;
                let (ref c2, ref l2) = **o2;
                if l1.len() == l2.len() {
                    f(c1, c2) && l1.iter().zip(l2.iter()).all( |(x, y)| f(x, y) )
                } else {
                    // It's really sad that we have to allocate to perform this equality check in
                    // linear time...
                    // (we actually shouldn't, since we should be able to modify the nodes in-place
                    // in order to reuse the existing memory, but fixing this might be more trouble
                    // than it's worth).
                    // FIXME: Alternative: a reversed iterator may be doable quite efficiently
                    // (without allocating), especially since we don't really need to go in forward
                    // order to do equality checks...
                    let (h1, l1) = c1.collapse_appl(&***l1);
                    let (h2, l2) = c2.collapse_appl(&***l2);
                    // We currently check in the opposite order from the OCaml, since we use the
                    // reversed method.  This shouldn't matter in terms of results, but it might
                    // affect performance... we could also iterate in reverse.
                    if l1.len() == l2.len() {
                        f(h1, h2) && l1.iter().zip(l2.iter()).all( |(x, y)| f(x, y) )
                    } else { false }
                }
            },
            // | Evar (e1,l1), Evar (e2,l2) -> Int.equal e1 e2 && Array.equal f l1 l2
            (&Constr::Const(ref o1), &Constr::Const(ref o2)) => {
                let ref c1 = **o1;
                let ref c2 = **o2;
                c1.eq(c2, Cst::eq_con_chk)
            },
            (&Constr::Ind(ref c1), &Constr::Ind(ref c2)) => c1.eq(c2, Ind::eq_ind_chk),
            (&Constr::Construct(ref o1), &Constr::Construct(ref o2)) => {
                let PUniverses(ref i1, ref u1) = **o1;
                let PUniverses(ref i2, ref u2) = **o2;
                i1.idx == i2.idx && i1.ind.eq_ind_chk(&i2.ind) && u1 == u2
            },
            (&Constr::Case(ref o1), &Constr::Case(ref o2)) => {
                let (_, ref p1, ref c1, ref bl1) = **o1;
                let (_, ref p2, ref c2, ref bl2) = **o2;
                f(p1, p2) && f(c1, c2) &&
                bl1.len() == bl2.len() && bl1.iter().zip(bl2.iter()).all( |(x, y)| f(x, y))
            },
            (&Constr::Fix(ref o1), &Constr::Fix(ref o2)) => {
                let Fix(Fix2(ref ln1, i1), PRec(_, ref tl1, ref bl1)) = **o1;
                let Fix(Fix2(ref ln2, i2), PRec(_, ref tl2, ref bl2)) = **o2;
                i1 == i2 &&
                ln1.len() == ln2.len() && ln1.iter().zip(ln2.iter()).all( |(x, y)| x == y) &&
                tl1.len() == tl2.len() && tl1.iter().zip(tl2.iter()).all( |(x, y)| f(x, y) ) &&
                bl1.len() == bl2.len() && bl1.iter().zip(bl2.iter()).all( |(x, y)| f(x, y) )
            },
            (&Constr::CoFix(ref o1), &Constr::CoFix(ref o2)) => {
                let CoFix(ln1, PRec(_, ref tl1, ref bl1)) = **o1;
                let CoFix(ln2, PRec(_, ref tl2, ref bl2)) = **o2;
                ln1 == ln2 &&
                tl1.len() == tl2.len() && tl1.iter().zip(tl2.iter()).all( |(x, y)| f(x, y) ) &&
                bl1.len() == bl2.len() && bl1.iter().zip(bl2.iter()).all( |(x, y)| f(x, y) )
            },
            (&Constr::Proj(ref o1), &Constr::Proj(ref o2)) => {
                let (ref p1, ref c1) = **o1;
                let (ref p2, ref c2) = **o2;
                p1.equal(p2) && f(c1, c2)
            },
            (_, _) => false,
        }
    }

    pub fn eq(&self, n: &Self) -> bool {
        self as *const _ == n as *const _ ||
        self.compare(n, Self::eq)
    }
}

impl Sort {
    fn compare(&self, s2: &Self) -> bool {
        match (self, s2) {
            (&Sort::Prop(c1), &Sort::Prop(c2)) => {
                match (c1, c2) {
                    (SortContents::Pos, SortContents::Pos) |
                    (SortContents::Null, SortContents::Null) => true,
                    (SortContents::Pos, SortContents::Null) => false,
                    (SortContents::Null, SortContents::Pos) => false,
                }
            },
            (&Sort::Type(ref u1), &Sort::Type(ref u2)) => u1 == u2,
            (&Sort::Prop(_), &Sort::Type(_)) => false,
            (&Sort::Type(_), &Sort::Prop(_)) => false,
        }
    }
}

impl<T> PUniverses<T> {
    fn eq<F>(&self, &PUniverses(ref c2, ref u2): &Self, f: F) -> bool
        where F: Fn(&T, &T) -> bool,
    {
        let PUniverses(ref c1, ref u1) = *self;
        u1 == u2 && f(c1, c2)
    }
}
