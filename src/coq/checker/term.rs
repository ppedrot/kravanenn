use coq::kernel::esubst::{Idx, IdxError, Lift, IdxResult};
use core::convert::TryFrom;
use core::nonzero::NonZero;
use ocaml::de::{ORef, Array};
use ocaml::values::{
    CoFix,
    Constr,
    Fix,
    Name,
    PRec,
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
}
