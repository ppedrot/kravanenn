use ocaml::de::{ORef, Array};
use ocaml::values::{
    CoFix,
    Constr,
    Fix,
    Name,
    PRec,
};
use std::rc::Rc;
use coq::kernel::esubst::{Idx, Lift, IdxResult};
use core::nonzero::NonZero;

impl Constr {
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
    pub fn decompose_lam(&self) -> (Vec<ORef<(Name, Constr, Constr)>>, &Constr) {
        let mut l = Vec::new();
        let mut c = self;
        loop {
            match *c {
                Constr::Lambda(ref o) => {
                    let (/*ref x, ref t*/_, _, ref c_) = **o;
                    /* l.push((x, t)); */
                    l.push(o.clone());
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
}
