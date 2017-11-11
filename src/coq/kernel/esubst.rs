use std::borrow::{Borrow};
use std::convert::{TryFrom};
use std::num::{TryFromIntError};
use std::option::{NoneError};
use core::nonzero::{NonZero, Zeroable};

/*

For my own clarification, an intro to De Bruijn indices and explicit substitutions:

- a ⋅ s ≡ what you get when you try to substitute a for the first De Bruijn index
  in s.

  id ≡ identity substitution: De Bruijn indices go to themselves.

  (λa)b →β a[b ⋅ id]

  1[c ⋅ s] → c (1 is the De Bruijn index 1)

  (cd)[s] → (c[s])(d[s])

*/

// An Idx is guaranteed to have positive (nonzero) i32.
#[derive(Clone,Debug,Copy,PartialEq)]
pub struct Idx(i32);

#[derive(Clone,Debug,Copy)]
pub struct IdxError(());

pub type IdxResult<T> = Result<T, IdxError>;

impl ::std::convert::From<Idx> for i32 {
    fn from(idx: Idx) -> i32 {
        idx.0
    }
}

impl ::std::convert::From<NoneError> for IdxError {
    fn from(_: NoneError) -> Self {
        IdxError(())
    }
}

impl ::std::convert::From<TryFromIntError> for IdxError {
    fn from(_: TryFromIntError) -> Self {
        IdxError(())
    }
}

impl Idx {
    pub fn new<T>(x: NonZero<T>) -> Result<Idx, /*<i32 as TryFrom<u32>>::Error*/IdxError> where i32: TryFrom<T>, T: Zeroable {
        match i32::try_from(x.get()) {
            // The 0 case should not happen, but since try_from is a safe trait it's hard to enforce this
            // (someone could provide a stupid implementation that didn't map 0 to 0).  Anyway, the
            // purpose of the NonZero in the argument is to have people check for zero ahead of
            // time.
            Ok(i) if i > 0 => Ok(Idx(i)),
            _ => Err(IdxError(())),
        }
    }

    pub const ONE : Self = Idx(1);

    pub fn checked_add(self, o: Idx) -> IdxResult<Idx> {
        // Must be positive since both Idxs are positive.
        Ok(Idx(self.0.checked_add(o.0)?))
    }

    pub fn checked_sub(self, o: Idx) -> IdxResult<Option<Idx>> {
        // Both self.0 and o.0 are positive i32s, so subtracting one from the other definitely does
        // not overflow.
        match self.0 - o.0 {
            i if i > 0 => Ok(Some(Idx(i))),
            0 => Ok(None),
            _ => Err(IdxError(())),
        }
    }
}

/// Explicit substitutions of type [T], where I : Borrow<[T]>.
///
/// NOTE: This differs from the OCaml's implementation because instead of representing
/// this as a linked list of subs, we represent a set of substitutions as a vector that
/// terminates in a bounded identity.  This reduces sharing but significantly decreases
/// allocations and indirection, and makes in-place mutation easier.  We will see
/// whether this turns out to be worthwhile.
#[derive(Clone,Debug)]
pub struct Subs<I> {
    /// Substitution operations (applied in order from right to left).
    ops: Vec<Op<I>>,
    /// ESID(n)             = %n END   bounded identity
    id: Idx,
}

#[derive(Clone,Debug)]
enum Op<I> {
    /// CONS([|t1..tn|],S)  = (S.t1...tn)    parallel substitution
    ///   (beware of the order: indice 1 is substituted by tn)
    Cons(I),
    /// SHIFT(n,S)          = (^n o S) terms in S are relocated with n vars
    Shift(Idx),
    /// LIFT(n,S)           = (%n S) stands for ((^n o S).n...1)
    ///   (corresponds to S crossing n binders)
    Lift(Idx),
}

#[derive(Copy,Clone,Debug)]
pub enum Expr<T> {
    /// Variable is substituted by value (i.e. the value must be shifted
    /// by some number of binders).
    Val(T),
    /// Variable relocated at index; `None` if the variable points inside
    /// the substitution and `Some(k)` if it points k bindings beyond
    /// the substitution.
    Var(Option<Idx>),
}

// TODO: investigate whether when using vectors in Rust, the extra checks
// here to avoid pushing onto it are actually worthwhile (since we won't
// trigger GC and don't allocate too frequently for vectors, and
// don't do much pointer chasing either).
impl<I> Subs<I> {
    pub fn id(idx: Idx) -> Self {
        Subs { ops: Vec::new(), id: idx }
    }

    fn push(&mut self, o: Op<I>) -> IdxResult<()> {
        // TODO: Verify that u32 to usize is a safe upcast.
        if self.ops.len() == u32::max_value() as usize {
            // ops can never be larger than u32::MAX.
            return Err(IdxError(()));
        }
        self.ops.push(o);
        Ok(())
    }

    pub fn cons<T>(&mut self, x: I) -> IdxResult<()>
        where I: Borrow<[T]> {
        // Don't bother cons-ing an empty substitution list.
        if x.borrow().len() > 0 {
            return self.push(Op::Cons(x));
        }
        Ok(())
    }

    pub fn shift(&mut self, n: Idx) -> IdxResult<()> {
        if let Some(&mut Op::Shift(ref mut k)) = self.ops.last_mut() {
            // Coalesce shifts with shifts.
            *k = Idx(k.0.checked_add(n.0)?);
            return Ok(())
        }
        return self.push(Op::Shift(n))
    }

    pub fn liftn(&mut self, n: Idx) -> IdxResult<()> {
        match self.ops.last_mut() {
            None => {
                // Coalesce ids with lifts
                self.id = Idx(self.id.0.checked_add(n.0)?);
                return Ok(())
            },
            Some(&mut Op::Lift(ref mut p)) => {
                // Coalesce lifts with lifts
                *p = Idx(p.0.checked_add(n.0)?);
                return Ok(())
            },
            _ => {},
        }
        return self.push(Op::Lift(n))
    }

    pub fn lift(&mut self) -> IdxResult<()> {
        // TODO: See if it's worthwhile factoring out the n > 0 check as is done in the OCaml
        // implementation.
        // The OCaml implementation presumably does it to avoid the branch, but is it
        // really a bottleneck?
        self.liftn(Idx(1))
    }

    /// [shift_cons(k,s,[|t1..tn|])] builds (^k s).t1..tn
    pub fn shift_cons<T>(&mut self, k: Idx, t: I) -> IdxResult<()>
        where I: Borrow<[T]>
    {
        /* // Don't bother shifting by 0
        if k > 0 {
            if let Some(&mut Op::Shift(ref mut n)) = &mut *self.ops.last_mut() {
                // Coalesce shifts with shifts.
                *n += k;
            } else {
                self.ops.push(Op::Shift(k + n));
            }
        } */
        // TODO: Figure out why the above is inlined in OCaml?  Rust will probably inline it anyway.
        self.shift(k)?;
        // TODO: Figure out why the below must be inlined?  Because it saves a branch, I guess?
        // But is this even a branch we can reliably save, if we're trying to avoid allocation?
        // self.push(Op::Cons(t))
        self.cons(t)
    }

    /// [expand_rel k subs] expands de Bruijn [k] in the explicit substitution
    /// [subs]. The result is either (Inl(lams,v)) when the variable is
    /// substituted by value [v] under lams binders (i.e. v *has* to be
    /// shifted by lams), or (Inr (k',p)) when the variable k is just relocated
    /// as k'; p is None if the variable points inside subs and Some(k) if the
    /// variable points k bindings beyond subs (cf argument of ESID).
    pub fn expand_rel<T>(&self, k: Idx) -> IdxResult<(Idx, Expr<&T>)>
        where I: Borrow<[T]>
    {
        let mut lams = 0i64;
        let mut k = k.0;
        // INVARIANT: 0 < k ≤ i32::MAX.
        // INVARIANT: after x iterations through the loop, lams ≤ x * i32::MAX, and 0 < k ≤ i32::MAX
        for op in self.ops.iter().rev() {
            match *op {
                Op::Cons(ref def) => {
                    let def = def.borrow();
                    let len = def.len();
                    // TODO: Verify that i32 to usize is a safe upcast.
                    match len.checked_sub(k as usize) {
                        Some(i) => {
                            // 0 ≤ len - k, and 1 ≤ k (so -k ≤ -1 and len-k ≤ len-1)
                            // 0 ≤ len - k ≤ len - 1 < len
                            // 0 ≤ i < len
                            return Ok((Idx(i32::try_from(lams)?), Expr::Val(&def[i])))
                        },
                        None => {
                            // len - k < 0, and k ≤ i32::MAX
                            // 0 < k - len, and
                            //   0 < k - len ≤ i32::MAX - len ≤ i32::MAX
                            // Cast is valid for sure since len < k ≤ i32::MAX.
                            k -= len as i32;
                            // 0 < k ≤ i32::MAX
                        },
                    }
                },
                // NOTE: n.0 ≥ 0
                Op::Lift(n) => if n.0 < k {
                    // 0 < k ≤ i32::MAX and 0 < k - n.0, and 0 ≤ n.0 ≤ i32::MAX
                    // Cast is valid because i32 to i64 always is.
                    lams += n.0 as i64;
                    // 0 < k - n.0 ≤ i32::MAX - n.0 ≤ i32::MAX
                    k -= n.0;
                    // 0 < k ≤ i32::MAX
                } else {
                    // 0 < k ≤ i32::MAX
                    return Ok((Idx(k), Expr::Var(None)))
                },
                Op::Shift(n) => {
                    // 0 ≤ n.0 ≤ i32::MAX
                    // Cast is valid for sure since i32 to i64 always is.
                    lams += n.0 as i64;
                },
            }
            // Since we never add more than i32::MAX to lams in a loop iteration, and ops.len() ≤ u32::MAX,
            // lams can never exceed i32::MAX * u32::MAX = (2^31 - 1) * (2^32 - 1) < i64::MAX.
        }
        // lams ≤ i32::MAX * u32::MAX and k ≤ i32::MAX
        // lams + k ≤ i32::MAX * (u32::MAX + 1) = (2^31 - 1) * 2^32 < i64::MAX
        // Cast of k to i64 is valid since u32 to i64 always is.
        // if self.id.0 < k, then 0 < k - self.id.0 ≤ i32::MAX.
        Ok((Idx(i32::try_from(lams + k as i64)?), Expr::Var(if self.id.0 < k { Some(Idx(k - self.id.0)) } else { None })))
    }

    /* /// Composition of substitutions: [comp mk_clos s1 s2] computes a
    /// substitution equivalent to applying s2 then s1. Argument
    /// mk_clos is used when a closure has to be created, i.e. when
    /// s1 is applied on an element of s2.
    /* pub fn comp(&mut self, mk_clos: (&mut T, &mut Subs) -> (), s: Subs<I>)
        where I: BorrowMut<[T]>
    {

    } */
    pub fn comp(mk_clos: (&mut T, &mut Subs) -> (), s1: Self, s2: Self) -> Self {
        let mut s;
        // 3 cases:
        // 1. s1 = CONS.  3 subcases:
        //   i. s2 = CONS.  Then CArray (new)
        //   ii. s2 = SHIFT.  Then reduce (recurse), SHIFT (new) or CONS (new)
        //   iii. s2 = LIFT.  Then always CONS (new) and sometimes LIFT (new) or CONS (new).
        // 2. s1 = LIFT.  3 subcases:
        //   i. s2 = SHIFT.  Then SHIFT (new, if k ≠ 0) and sometimes SHIFT (new) or LIFT (new).
        let mut is1 = s1.ops.iter().rev();
        let mut is2 = s2.ops.iter().rev();
        loop {
            if let Some(v2) = is2.next() {
                if let Some(v1) = is1.next() {
                    match (*v1, *v2) {
                        Op::Shift(k) => {
                            // Shift after applying comp
                            subs_shift(self.);
                        }
                    }
                } else {
                    return Subs { ops: s2.ops, idx: s2.idx }
                }
            } else {
                return Subs { ops: s1.ops, idx: s1.idx };
            }
            if let Some(v1) = s1.
        }
    } */
/*let rec comp mk_cl s1 s2 =
  match (s1, s2) with
    | _, ESID _ -> s1
    | ESID _, _ -> s2
    | SHIFT(k,s), _ -> subs_shft(k, comp mk_cl s s2)
    | _, CONS(x,s') ->
        CONS(CArray.Fun1.map (fun s t -> mk_cl(s,t)) s1 x, comp mk_cl s1 s')
    | CONS(x,s), SHIFT(k,s') ->
        let lg = Array.length x in
        if k == lg then comp mk_cl s s'
        else if k > lg then comp mk_cl s (SHIFT(k-lg, s'))
        else comp mk_cl (CONS(Array.sub x 0 (lg-k), s)) s'
    | CONS(x,s), LIFT(k,s') ->
        let lg = Array.length x in
        if k == lg then CONS(x, comp mk_cl s s')
        else if k > lg then CONS(x, comp mk_cl s (LIFT(k-lg, s')))
        else
          CONS(Array.sub x (lg-k) k,
               comp mk_cl (CONS(Array.sub x 0 (lg-k),s)) s')
    | LIFT(k,s), SHIFT(k',s') ->
        if k<k'
        then subs_shft(k, comp mk_cl s (subs_shft(k'-k, s')))
        else subs_shft(k', comp mk_cl (subs_liftn (k-k') s) s')
    | LIFT(k,s), LIFT(k',s') ->
        if k<k'
        then subs_liftn k (comp mk_cl s (subs_liftn (k'-k) s'))
        else subs_liftn k' (comp mk_cl (subs_liftn (k-k') s) s')
val comp : ('a subs * 'a -> 'a) -> 'a subs -> 'a subs -> 'a subs*/

/*let rec exp_rel lams k subs =
  match subs with
    | CONS (def,_) when k <= Array.length def
                           -> Inl(lams,def.(Array.length def - k))
    | CONS (v,l)           -> exp_rel lams (k - Array.length v) l
    | LIFT (n,_) when k<=n -> Inr(lams+k,None)
    | LIFT (n,l)           -> exp_rel (n+lams) (k-n) l
    | SHIFT (n,s)          -> exp_rel (n+lams) k s
    | ESID n when k<=n     -> Inr(lams+k,None)
    | ESID n               -> Inr(lams+k,Some (k-n))

let expand_rel k subs = exp_rel 0 k subs*/

    /// Tests whether a substitution is equal to the identity
    pub fn is_id<T>(&self) -> bool
        where I: Borrow<[T]>
    {
        !self.ops.iter().any( |op| match *op {
            Op::Lift(_) => false,
            // NOTE: The below cannot happen with the current interface.
            // Op::Shift(Idx(0)) => false,
            // Op::Cons(ref x) => x.borrow().len() > 0,
            _ => true
        })
    }
}

pub type SubsV<T> = Subs<Vec<T>>;

/* (** {6 Compact representation } *)
(** Compact representation of explicit relocations
    - [ELSHFT(l,n)] == lift of [n], then apply [lift l].
    - [ELLFT(n,l)] == apply [l] to de Bruijn > [n] i.e under n binders. *)
type lift = private
  | ELID
  | ELSHFT of lift * int
  | ELLFT of int * lift

val el_id : lift
val el_shft : int -> lift -> lift
val el_liftn : int -> lift -> lift
val el_lift : lift -> lift
val reloc_rel : int -> lift -> int
val is_lift_id : lift -> bool
    */
#[derive(Debug,Clone)]
pub struct Lift {
    lifts: Vec<i32>,
}

impl Lift {
    pub fn id() -> Self {
        Lift { lifts: Vec::new(), }
    }

    fn push(&mut self, o: i32) -> IdxResult<()> {
        // TODO: Verify that u32 to usize is a safe upcast.
        if self.lifts.len() == u32::max_value() as usize {
            // lifts can never be larger than u32::MAX.
            return Err(IdxError(()));
        }
        self.lifts.push(o);
        Ok(())
    }

    pub fn shift(&mut self, n: Idx) -> IdxResult<()> {
        if let Some(k) = self.lifts.last_mut() {
            // Coalesce shifts with shifts.
            *k = k.checked_add(n.0)?;
            return Ok(())
        }
        return self.push(n.0)
    }

    pub fn liftn(&mut self, n: Idx) -> IdxResult<()> {
        match self.lifts.last_mut() {
            None => {
                // Lifts don't change ids
                return Ok(())
            },
            Some(&mut ref mut p) if *p < 0 => {
                // Coalesce lifts with lifts
                let p_ = p.checked_sub(n.0)?;
                return if p_ > i32::min_value() {
                    // We need to make sure -p_ is still in range for
                    // i32.
                    *p = p_;
                    Ok(())
                } else {
                    Err(IdxError(()))
                }
            },
            _ => {},
        }
        // n.0 is positive so making it negative is in bounds for sure.
        return self.push(-n.0)
    }

    pub fn lift(&mut self) -> IdxResult<()> {
        self.liftn(Idx(1))
    }

    pub fn is_id(&self) -> bool {
        !self.lifts.iter().any( |i| *i > 0)
    }

    pub fn reloc_rel(&self, n: Idx) -> IdxResult<Idx> {
        let mut n = n.0 as i64;
        let mut lams = 0 as i64;
        // INVARIANT: after x iterations through the loop, 0 ≤ lams, 0 < n, and 0 < lams + n ≤ (x + 1) * i32::MAX.
        // Basic idea: after every iteration of the loop, either only one of lams and n have been
        // increased by at most i32::MAX, or one has been increased by i32::MAX and the other
        // decreased by i32::MAX, such that neither goes negative.  Therefore, the net sum of the
        // two is always ≤ (x + 1) * i32::MAX and neither is ever larger than x * i32::MAX.
        for k in self.lifts.iter().rev() {
            if *k < 0 {
                // Lift
                // Addition here safe because positive i64 plus negative i64 is always in bounds.
                let n_ = n + *k as i64;
                if n_ <= 0 {
                    // 0 ≤ lams, 0 < n, and 0 < lams + n ≤ i32::MAX * (u32::MAX - 1 + 1) = (2^31 - 1) * (2^32 - 1) < i64::MAX
                    return Ok(Idx(i32::try_from(lams + n)?))
                } else {
                    // 0 ≤ k ≤ i32::MAX, 0 ≤ lams, and 0 < n
                    //   0 < n + k ≤ lams + n + k ≤ (x + 1) * i32::MAX + i32::MAX
                    // 0 < n_ and 0 ≤ lams < lams - k and 0 < lams + n = lams - k + n + k ≤ (x + 1) * i32::MAX
                    // 0 < lams - k + n_ ≤ (x + 1) * i32::MAX
                    n = n_;
                    // 0 < lams - k + n ≤ (x + 1) * i32::MAX, and 0 < lams - k < lams - k + n ≤ (x + 1) * i32::MAX < i64::MAX
                    lams -= *k as i64;
                    // 0 < lams + n ≤ (x + 1) * i32::MAX, and 0 < lams < lams + n ≤ (x + 1) * i32::MAX < i64::MAX
                }
            } else {
                // 0 ≤ k ≤ i32::MAX
                // Cast is valid for sure since i32 to i64 always is.
                // 0 < n + k ≤ lams + n + k ≤ (x + 1) * i32::MAX + i32::MAX = (x + 2) * i32::MAX < i64::MAX
                n += *k as i64;
                // 0 < lams + n ≤ (x + 2) * i32::MAX, 0 < n, and 0 ≤ lams.
            }
            // Since we never add more than i32::MAX to lams in a loop iteration, and lifts.len() ≤ u32::MAX,
            // n + lams can never exceed i32::MAX * (u32::MAX + 1) = (2^31 - 1) * 2^32 < i64::MAX.
        }
        // lams ≤ i32::MAX * u32::MAX and n ≤ i32::MAX
        // lams + n ≤ i32::MAX * (u32::MAX + 1) = (2^31 - 1) * 2^32 < i64::MAX
        Ok(Idx(i32::try_from(lams + n)?))
    }
    /* pub fn shift(&mut self, n: usize) -> Result<(), TryFromIntError> {

    } */

// let el_id = ELID
// (* compose a relocation of magnitude n *)
// let rec el_shft_rec n = function
//   | ELSHFT(el,k) -> el_shft_rec (k+n) el
//   | el           -> ELSHFT(el,n)
// let el_shft n el = if Int.equal n 0 then el else el_shft_rec n el
//
// (* cross n binders *)
// let rec el_liftn_rec n = function
//   | ELID        -> ELID
//   | ELLFT(k,el) -> el_liftn_rec (n+k) el
//   | el          -> ELLFT(n, el)
// let el_liftn n el = if Int.equal n 0 then el else el_liftn_rec n el
//
// let el_lift el = el_liftn_rec 1 el
//
// (* relocation of de Bruijn n in an explicit lift *)
// let rec reloc_rel n = function
//   | ELID -> n
//   | ELLFT(k,el) ->
//       if n <= k then n else (reloc_rel (n-k) el) + k
//   | ELSHFT(el,k) -> (reloc_rel (n+k) el)
//
// let rec is_lift_id = function
//   | ELID -> true
//   | ELSHFT(e,n) -> Int.equal n 0 && is_lift_id e
//   | ELLFT (_,e) -> is_lift_id e
//

}
