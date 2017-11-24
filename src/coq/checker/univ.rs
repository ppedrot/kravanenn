use coq::kernel::names::{
    HDp,
};
use coq::lib::hashcons::{Table, HashconsedType};
use coq::lib::hashset::combine;
use ocaml::de::{
    ORef,
};
use ocaml::values::{
    Expr,
    HList,
    Instance,
    Int,
    Level,
    RawLevel,
    Univ,
};
use std::borrow::{Cow};
use std::collections::HashMap;
use std::sync::{Arc};

/// Comparison on this type is pointer equality
struct CanonicalArc {
    univ: Level,
    lt: Vec<Level>,
    le: Vec<Level>,
    rank: Int,
    predicative: bool,
}

#[derive(Clone,Copy,Debug,Eq,PartialEq)]
enum FastOrder {
    Eq,
    Lt,
    Le,
    NLe,
}

/// A Level.t is either an alias for another one, or a canonical one,
/// for which we know the universes that are above
enum UnivEntry {
  Canonical(CanonicalArc),
  Equiv(Level),
}

pub struct Universes(UMap<UnivEntry>);

pub struct LevelMap();

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum UnivError {
    Anomaly(String),
}

// type LMap<T> = HashMap<Level, T>;

type UMap<T> = HashMap<Level, T>;

pub type Hlevel = Table<Level, HDp>;

pub type Hexpr = Table<Expr, Hlevel>;

pub type Huniv = Table<Univ, Hexpr>;

pub type UnivResult<T> = Result<T, UnivError>;

pub trait Hashconsed<U> {
    fn hash(&self) -> i64;
    fn eq(&self, &Self) -> bool;
    fn hcons<'a>(&'a self, &'a U) -> Cow<'a, Self>
        where Self: ToOwned;
}

impl<T, U> HashconsedType<U> for HList<T>
    where
        T: Hashconsed<U>,
        T: Clone,
{
    fn hash(&self) -> i64 {
        match *self {
            HList::Nil => 0,
            HList::Cons(ref o) => {
                let (_, h, _) = **o;
                h
            },
        }
    }

    fn eq(&self, l2: &Self) -> bool {
        match (self, l2) {
            (&HList::Nil, &HList::Nil) => true,
            (&HList::Cons(ref o1), &HList::Cons(ref o2)) => {
                let (ref x1, _, ref l1) = **o1;
                let (ref x2, _, ref l2) = **o2;
                x1 as *const _ == x2 as *const _ && &*l1 as *const _ == &*l2 as *const _
            },
            (_, _) => false,
        }
    }

    fn hashcons<'a, 'b>(&'b self, u: &'a U) -> Cow<'b, Self>
    {
        // FIXME: Should these terms be new each time, or should we try to get more sharing?
        match *self {
            HList::Nil => Cow::Owned(HList::Nil),
            HList::Cons(ref o) => {
                let (ref x, h, ref l) = **o;
                let x = x.hcons(u);
                Cow::Owned(HList::Cons(ORef(Arc::new((x.into_owned(), h, l.to_owned())))))
            },
        }
    }
}

/// Note: the OCaml is needlessly generic over T.  At the end of the day, we only use HList with
/// Univ.
impl<T> HList<T>
{
    fn hash(&self) -> i64 {
        match *self {
            HList::Nil => 0,
            HList::Cons(ref o) => {
                let (_, h, _) = **o;
                h
            },
        }
    }

    /* fn hashcons<F>(&self, hc: F) -> Cow<Self>
        where
            F: Fn(&T) -> Cow<T>,
            T: Clone,
    {
        match *self {
            HList::Nil => Cow::Borrowed(self),
            HList::Cons(ref o) => {
                let (ref x, h, ref l) = **o;
                match self.hc(l) {
                    Cow::Owned(x) => Cow::Owned(HList::Cons(x, h, l.to_owned())),
                    Cow::Borrowed(x) => Cow::Borrowed(self),
                }
             },
        }
    } */

    /// No recursive call: the interface guarantees that all HLists from this
    /// program are already hashconsed. If we get some external HList, we can
    /// still reconstruct it by traversing it entirely.
    fn hcons<'a, U>(&'a self, u: &'a Table<HList<T>, U>) -> Cow<'a, Self>
        where
            T: Hashconsed<U>,
            T: Clone,
    {
        u.hcons(self)
    }

    fn nil() -> Self {
        HList::Nil
    }

    fn cons<'a, U>(x: T, l: Self, u: &'a Table<HList<T>, U>) -> Self
        where
            T: Hashconsed<U>,
            T: Clone,
    {
        let h = x.hash();
        let hl = match l {
            HList::Nil => 0,
            HList::Cons(ref o) => {
                let (_, h, _) = **o;
                h
            },
        };
        let h = combine::combine(h, hl);
        HList::Cons(ORef(Arc::new((x, h, l)))).hcons(u).into_owned()
    }

    fn for_all2<F>(&self, l2: &Self, f: F) -> bool
        where
            F: Fn(&T, &T) -> bool,
    {
        let mut l1 = self.iter();
        let mut l2 = l2.iter();
        loop {
            match (l1.next(), l2.next()) {
                (None, None) => return true,
                (Some(x1), Some(x2)) => { if !f(x1, x2) { return false } },
                (_, _) => return false,
            }
        }
    }
    /* let nil = Nil
  let cons x l =
    let h = M.hash x in
    let hl = match l with Nil -> 0 | Cons (_, h, _) -> h in
    let h = Hashset.Combine.combine h hl in
    hcons (Cons (x, h, l))*/
    /*fn cons(&self, x: &T, l: &Self) -> Cow<Self> {
        let h = Expr.HExpr
        match *self {
            l
        }
  let cons x l =
    let h = M.hash x in
    let hl = match l with Nil -> 0 | Cons (_, h, _) -> h in
    let h = Hashset.Combine.combine h hl in
    hcons (Cons (x, h, l))
    }

  let hcons = Hashcons.simple_hcons Hcons.generate Hcons.hcons M.hcons
  (** No recursive call: the interface guarantees that all HLists from this
      program are already hashconsed. If we get some external HList, we can
      still reconstruct it by traversing it entirely. *)
  let nil = Nil
  let cons x l =
    let h = M.hash x in
    let hl = match l with Nil -> 0 | Cons (_, h, _) -> h in
    let h = Hashset.Combine.combine h hl in
    hcons (Cons (x, h, l))*/
}


impl RawLevel {
    fn equal(&self, y: &Self) -> bool {
        self as *const _ == y as *const _ ||
            match (self, y) {
                (&RawLevel::Prop, &RawLevel::Prop) => true,
                (&RawLevel::Set, &RawLevel::Set) => true,
                (&RawLevel::Level(n, ref d), &RawLevel::Level(n_, ref d_)) =>
                    n == n_ && d.equal(&**d_),
                (&RawLevel::Var(n), &RawLevel::Var(n_)) => n == n_,
                (_, _) => false,
            }
    }

    fn hcons<'a>(&'a self, u: &'a HDp) -> Cow<'a, RawLevel> {
        match *self {
            RawLevel::Prop => Cow::Borrowed(self),
            RawLevel::Set => Cow::Borrowed(self),
            RawLevel::Level(n, ref d) => {
                let d_ = d.hcons(u);
                if &*d_ as *const _ == &**d as *const _ { Cow::Borrowed(self) } else {
                    Cow::Owned(RawLevel::Level(n, ORef(Arc::new(d_.into_owned()))))
                }
            },
            RawLevel::Var(_) => Cow::Borrowed(self),
        }
    }

    fn hequal(&self, y: &Self) -> bool {
        self as *const _ == y as *const _ ||
        match (self, y) {
            (&RawLevel::Prop, &RawLevel::Prop) => true,
            (&RawLevel::Set, &RawLevel::Set) => true,
            (&RawLevel::Level(n, ref d), &RawLevel::Level(n_, ref d_)) =>
                n == n_ && &**d as *const _ == &**d_ as *const _,
            (&RawLevel::Var(n), &RawLevel::Var(n_)) => n == n_,
            _ => false,
        }
    }

    fn hash(&self) -> i64 {
        match *self {
            RawLevel::Prop => combine::combinesmall(1, 0),
            RawLevel::Set => combine::combinesmall(1, 1),
            RawLevel::Var(n) => combine::combinesmall(2, n),
            RawLevel::Level(n, ref d) =>
                combine::combinesmall(3, combine::combine(n, d.hash()))
        }
    }
}

/// Hashcons on levels + their hash
impl HashconsedType<HDp> for Level {
    fn eq(&self, y: &Self) -> bool {
        self.hash == y.hash && self.data.hequal(&y.data)
    }

    fn hash(&self) -> i64 {
        self.hash
    }

    fn hashcons(&self, u: &HDp) -> Cow<Self> {
        let data_ = self.data.hcons(u);

        if &self.data as *const _ == &*data_ as *const _ { Cow::Borrowed(self) } else {
            Cow::Owned(Level {
                hash: self.hash,
                data: data_.into_owned(),
            })
        }
    }
    // let eq x y = x.hash == y.hash && RawLevel.hequal x.data y.data
    // let hash x = x.hash
    // let hashcons () x =
    //   let data' = RawLevel.hcons x.data in
    //   if x.data == data' then x else { x with data = data' }
}

impl Level {
    pub fn equal(&self, y: &Self) -> bool {
        self as *const _ == y as *const _ ||
        self.hash == y.hash &&
        self.data.equal(&y.data)
    }

    fn hash(&self) -> i64 {
        self.hash
    }

    fn hcons<'a>(&'a self, u: &'a Hlevel) -> Cow<'a, Self> {
        // <List::<Str> as HashconsedType::<(Table::<List<Str>, Table<Str, ()>>, (), Baz)>>::hashcons(&dp, &(foo2, (), FOO))
        // self.hashcons(&(u, (), Hstring::hcons))
        u.hcons(self)
        // dp.hashcons::<Table::<Str, ()>>(&(foo2, Foo::hcons))
    }
}

/// For use in UMap.
/// TODO: Consider replacing this with a LevelKey wrapper, once it's been ascertained that this
/// won't cause problems.
impl PartialEq for Level {
    fn eq(&self, v: &Self) -> bool {
        // Comparison equals 0 for RawLevels and Levels is the same as equality.
        self.equal(v)
    }
}

/// For use in UMap.
/// TODO: Consider replacing this with a LevelKey wrapper, once it's been ascertained that this
/// won't cause problems.
impl Eq for Level {}

/// For use in UMap.
/// TODO: Consider replacing this with a LevelKey wrapper, once it's been ascertained that this
/// won't cause problems.
impl ::std::hash::Hash for Level {
    fn hash<H>(&self, state: &mut H)
        where
            H: ::std::hash::Hasher,
    {
        // Just write the hash directly to the state... note that if this isn't a dummy hasher,
        // this will try to scramble the hash, which is possibly not a good thing for collisions.
        state.write_i64(self.hash());
    }
}

impl HashconsedType<Hlevel> for Expr {
    fn hashcons(&self, u: &Hlevel) -> Cow<Self> {
        let Expr(ref b, n) = *self;
        let b_ = b.hcons(u);
        if &*b_ as *const _ == b as *const _ { Cow::Borrowed(self) } else {
            Cow::Owned(Expr(b_.into_owned(), n))
        }
    }

    fn eq(&self, l2: &Self) -> bool {
        self as *const _ == l2 as *const _ ||
        match (self, l2) {
            (&Expr(ref b, n), &Expr(ref b_, n_)) =>
                b as *const _ == b_ as *const _ && n == n_,
        }
    }

    fn hash(&self) -> i64 {
        let Expr(ref x, n) = *self;
        // FIXME: check overflow
        n + x.hash()
    }
    //   type t = _t
    //   type u = Level.t -> Level.t
    //   let hashcons hdir (b,n as x) =
	// let b' = hdir b in
	//   if b' == b then x else (b',n)
    //   let eq l1 l2 =
    //     l1 == l2 ||
    //     match l1,l2 with
	// | (b,n), (b',n') -> b == b' && n == n'

    //   let hash (x, n) = n + Level.hash x
}

/* impl<T> PartialEq for HList<T> {
    fn eq(&self, l2: &Self) -> bool {
        match (self, l2) {
            (&HList::Nil, &HList::Nil) => true,
            (&HList::Cons(ref x1, _, ref l1), &HList::Cons(ref x2, _, ref l2)) =>
                x1 as *const _ == x2 as *const _ &&
                l1 as *const _ == l2 as *const _,
            _ => false,
        }
    }
} */

/*trait HashedList<M> where M: HashConsed {
    fn
}
sig
  type t = private Nil | Cons of M.t * int * t
  val nil : t
  val cons : M.t -> t -> t
end =
struct
  type t = Nil | Cons of M.t * int * t
  module Self =
  struct
    type _t = t
    type t = _t
    type u = (M.t -> M.t)
    let hash = function Nil -> 0 | Cons (_, h, _) -> h
    let eq l1 l2 = match l1, l2 with
    | Nil, Nil -> true
    | Cons (x1, _, l1), Cons (x2, _, l2) -> x1 == x2 && l1 == l2
    | _ -> false
    let hashcons hc = function
    | Nil -> Nil
    | Cons (x, h, l) -> Cons (hc x, h, l)
  end
  module Hcons = Hashcons.Make(Self)
  let hcons = Hashcons.simple_hcons Hcons.generate Hcons.hcons M.hcons
  (** No recursive call: the interface guarantees that all HLists from this
      program are already hashconsed. If we get some external HList, we can
      still reconstruct it by traversing it entirely. *)
  let nil = Nil
  let cons x l =
    let h = M.hash x in
    let hl = match l with Nil -> 0 | Cons (_, h, _) -> h in
    let h = Hashset.Combine.combine h hl in
    hcons (Cons (x, h, l))
end*/

impl<T> HList<T> {
    /*fn map(&self) {
        match *self {
            HList::Nil => Nil,
            HList::Cons(ref x, _, ref l) =>
        }
        self.cons()
    }*/
  /*let rec map f = function
  | Nil -> nil
  | Cons (x, _, l) -> cons (f x) (map f l)

  let smartmap = map*/

}

impl CanonicalArc {
    /// [compare_neq] : is [arcv] in the transitive upward closure of [arcu] ?

    /// In [strict] mode, we fully distinguish between LE and LT, while in
    /// non-strict mode, we simply answer LE for both situations.
    ///
    /// If [arcv] is encountered in a LT part, we could directly answer
    /// without visiting unneeded parts of this transitive closure.
    /// In [strict] mode, if [arcv] is encountered in a LE part, we could only
    /// change the default answer (1st arg [c]) from NLE to LE, since a strict
    /// constraint may appear later. During the recursive traversal,
    /// [lt_done] and [le_done] are universes we have already visited,
    /// they do not contain [arcv]. The 4rd arg is [(lt_todo,le_todo)],
    /// two lists of universes not yet considered, known to be above [arcu],
    /// strictly or not.
    ///
    /// We use depth-first search, but the presence of [arcv] in [new_lt]
    /// is checked as soon as possible : this seems to be slightly faster
    /// on a test.
    ///
    /// The universe should actually be in the universe map, or else it will return an error.
    fn fast_compare_neq(&self, arcv: &Self, strict: bool, g: &Universes) -> UnivResult<FastOrder> {
        // [c] characterizes whether arcv has already been related
        // to arcu among the lt_done,le_done universe
        let mut c = FastOrder::NLe;
        let mut lt_done = Vec::new();
        let mut le_done = Vec::new();
        let mut lt_todo : Vec<&CanonicalArc> = Vec::new();
        let mut le_todo = vec![self];
        loop {
            if let Some(arc) = lt_todo.pop() {
                if !lt_done.iter().any( |&arc_| arc as *const _ == arc_ as *const _) {
                    for u in arc.le.iter() {
                        let arc = u.repr(g)?;
                        if arc as *const _ == arcv as *const _ {
                            return Ok(if strict { FastOrder::Lt } else { FastOrder::Le })
                        } else {
                            lt_todo.push(arc);
                        }
                    }
                    for u in arc.lt.iter() {
                        let arc = u.repr(g)?;
                        if arc as *const _ == arcv as *const _ {
                            return Ok(if strict { FastOrder::Lt } else { FastOrder::Le })
                        } else {
                            lt_todo.push(arc);
                        }
                    }
                    lt_done.push(arc);
                }
            } else if let Some(arc) = le_todo.pop() {
                // lt_todo = []
                if arc as *const _ == arcv as *const _ {
                    // No need to continue inspecting universes above arc;
                    // if arcv is strictly above arc, then we would have a cycle.
                    // But we cannot answer LE yet, a stronger constraint may
                    // come later from [le_todo].
                    if strict {
                        c = FastOrder::Le;
                    } else {
                        return Ok(FastOrder::Le);
                    }
                } else {
                    if !(lt_done.iter().any( |&arc_| arc as *const _ == arc_ as *const _) ||
                         le_done.iter().any( |&arc_| arc as *const _ == arc_ as *const _)) {
                        for u in arc.lt.iter() {
                            let arc = u.repr(g)?;
                            if arc as *const _ == arcv as *const _ {
                                return Ok(if strict { FastOrder::Lt } else { FastOrder::Le })
                            } else {
                                lt_todo.push(arc);
                            }
                        }
                        // Cannot use .extend here because we need to fail fast on failure.  There
                        // is probably a better way to deal with this.
                        for u in arc.le.iter() {
                            le_todo.push(u.repr(g)?);
                        }
                        le_done.push(arc);
                    }
                }
            } else {
                // lt_todo = [], le_todo = []
                return Ok(c)
            }
        }
    }

    // /// The universe should actually be in the universe map, or else it will return an error.
    // fn fast_compare(&self, arcv: &Self, g: &Universes) -> UnivResult<FastOrder> {
    //     if self as *const _ == arcv as *const _ { Ok(FastOrder::Eq) }
    //     else { self.fast_compare_neq(arcv, true, g) }
    // }

    /// The universe should actually be in the universe map, or else it will return an error.
    fn is_leq(&self, arcv: &Self, g: &Universes) -> UnivResult<bool> {
        Ok(self as *const _ == arcv as *const _ ||
           match self.fast_compare_neq(arcv, false, g)? {
               FastOrder::NLe => false,
               FastOrder::Eq | FastOrder::Le | FastOrder::Lt => true,
           })
    }

    /// The universe should actually be in the universe map, or else it will return an error.
    fn is_lt(&self, arcv: &Self, g: &Universes) -> UnivResult<bool> {
        if self as *const _ == arcv as *const _ {
            Ok(false)
        } else {
            self.fast_compare_neq(arcv, true, g).map( |c| match c {
                FastOrder::Lt => true,
                FastOrder::Eq | FastOrder::Le | FastOrder::NLe => false,
            })
        }
    }

    fn is_prop(&self) -> bool {
        self.univ.is_prop()
    }

    fn is_set(&self) -> bool {
        self.univ.is_set()
    }
}

impl Level {
    fn is_prop(&self) -> bool {
        match self.data {
            RawLevel::Prop => true,
            _ => false,
        }
    }

    fn is_set(&self) -> bool {
        match self.data {
            RawLevel::Set => true,
            _ => false,
        }
    }

    /// Worked out elsewhere; if this is wrong, we can figure out another way to get this value.
    const PROP : Self = Level { hash: 7, data: RawLevel::Prop };
    const SET : Self = Level { hash: 8, data: RawLevel::Prop };

    /// Every Level.t has a unique canonical arc representative

    /// repr : universes -> Level.t -> canonical_arc
    /// canonical representative : we follow the Equiv links
    /// The universe should actually be in the universe map, or else it will return an error.
    /// Also note: if the map universe map contains Equiv cycles, this will loop forever!
    fn repr<'a>(&'a self, g: &'a Universes) -> UnivResult<&CanonicalArc> {
        let mut u = self;
        loop {
            match g.0.get(u) {
                Some(&UnivEntry::Equiv(ref v)) => { u = v },
                Some(&UnivEntry::Canonical(ref arc)) => return Ok(arc),
                None =>
                    return Err(UnivError::Anomaly(format!("Univ.repr: Universe {:?} undefined",
                                                          u))),
            }
        }
    }

    /// Invariants : compare(u,v) = EQ <=> compare(v,u) = EQ
    ///              compare(u,v) = LT or LE => compare(v,u) = NLE
    ///              compare(u,v) = NLE => compare(v,u) = NLE or LE or LT
    ///
    /// Adding u>=v is consistent iff compare(v,u) # LT
    ///  and then it is redundant iff compare(u,v) # NLE
    /// Adding u>v is consistent iff compare(v,u) = NLE
    ///  and then it is redundant iff compare(u,v) = LT

    /// Universe checks [check_eq] and [check_leq], used in coqchk

    /// First, checks on universe levels

    /// The universe should actually be in the universe map, or else it will return an error.
    fn check_equal(&self, v: &Level, g: &Universes) -> UnivResult<bool> {
        let arcu = self.repr(g)?;
        let arcv = v.repr(g)?;
        Ok(arcu as *const _ == arcv as *const _)
    }

    /// The universe should actually be in the universe map, or else it will return an error.
    fn check_eq(&self, v: &Level, g: &Universes) -> UnivResult<bool> {
        Ok(self as *const _ == v as *const _ ||
           self.check_equal(v, g)?)
    }

    /// The universe should actually be in the universe map, or else it will return an error.
    fn check_smaller(&self, v: &Self, strict: bool, g: &Universes) -> UnivResult<bool> {
        let arcu = self.repr(g)?;
        let arcv = v.repr(g)?;
        if strict {
            arcu.is_lt(arcv, g)
        } else {
            Ok(arcu.is_prop()
               || (arcu.is_set() && arcv.predicative)
               || (arcu.is_leq(arcv, g)?))
        }
    }
}

impl Expr {
    /// Worked out elsewhere; if this is wrong, we can figure out another way to get this value.
    const PROP : Self = Expr(Level::PROP, 0);

    fn hcons<'a>(&'a self, u: &'a Hexpr) -> Cow<'a, Self> {
        // <List::<Str> as HashconsedType::<(Table::<List<Str>, Table<Str, ()>>, (), Baz)>>::hashcons(&dp, &(foo2, (), FOO))
        // self.hashcons(&(u, (), Hstring::hcons))
        u.hcons(self)
        // dp.hashcons::<Table::<Str, ()>>(&(foo2, Foo::hcons))
    }

    /* fn eq(&self, y: &Self) -> bool {
        self as *const _ == y as *const _ ||
        {
            let Expr(ref u, n) = *self;
            let Expr(ref v, n_) = *y;
            n == n_ && u.equal(v)
        }
    } */

    // let hcons =
    //   Hashcons.simple_hcons H.generate H.hcons Level.hcons
    // let hash = ExprHash.hash
    // let eq x y = x == y ||
    //   (let (u,n) = x and (v,n') = y in
    //      Int.equal n n' && Level.equal u v)

    fn equal(&self, y: &Self) -> bool {
        let Expr(ref u, n) = *self;
        let Expr(ref v, n_) = *y;
        n == n_ && u.equal(v)
    }

    fn map<'a, F>(&'a self, f: F, u: &'a Hexpr) -> Cow<'a, Self>
        where
            F: for<'b> Fn(&'b Level) -> Cow<'b, Level>,
    {
        let Expr(ref v, n) = *self;
        let v_ = f(v);
        match v_ {
            Cow::Borrowed(_) => Cow::Borrowed(self), // Has to be the same
            Cow::Owned(v_) => {
                // Bellow is impossible because we don't have a pointer to a Level, but an actual
                // Level.
                /* if v_ as *const _ == v as *const _ { Cow::Borrowed(self) }
                else */if v_.is_prop() && n != 0 {
                    // No choice but into_owned here.
                    Cow::Owned(Expr(Level::SET, n).hcons(u).into_owned())
                } else {
                    // Again, no choice but into_owned here.
                    Cow::Owned(Expr(v_, n).hcons(u).into_owned())
                }
            }
        }
        // let map f (v, n as x) =
        //   let v' = f v in
	    // if v' == v then x
	    // else if Level.is_prop v' && n != 0 then
	    //   hcons (Level.set, n)
	    // else hcons (v', n)
    }

    /// The universe should actually be in the universe map, or else it will return an error.
    fn check_equal(&self, y: &Self, g: &Universes) -> UnivResult<bool> {
        Ok(self as *const _ == y as *const _ || {
            let Expr(ref u, n) = *self;
            let Expr(ref v, m) = *y;
            n == m && u.check_equal(v, g)?
        })
    }

    /// The universe should actually be in the universe map, or else it will return an error.
    fn check_smaller(&self, &Expr(ref v, m): &Self, g: &Universes) -> UnivResult<bool> {
        let Expr(ref u, n) = *self;
        if n <= m {
            u.check_smaller(v, false, g)
        } else if n - m == 1 {
            // n - m is valid, because n > m, so 0 < n - m ≤ n ≤ i64::MAX.
            u.check_smaller(v, true, g)
        } else {
            Ok(false)
        }
    }

    /// The universe should actually be in the universe map, or else it will return an error.
    fn exists_bigger(&self, l: &Univ, g: &Universes) -> UnivResult<bool> {
        // NOTE: We don't just use any / all because we want to propagate errors; there may be a
        // way to do both somehow.
        for ul_ in l.iter() {
            if self.check_smaller(ul_, g)? { return Ok(true) }
        }
        return Ok(false)
    }
}

impl Univ {
    pub fn equal(&self, y: &Self) -> bool {
        self as *const _ == y as *const _ ||
        self.hash() == y.hash() &&
        self.for_all2(y, Expr::equal)
    }
    /*let equal x y = x == y ||
    (Huniv.hash x == Huniv.hash y &&
       Huniv.for_all2 Expr.equal x y)*/

    pub fn is_type0m(&self) -> bool {
        // I believe type0m is:
        //    Cons (({ hash = 7; data = Prop }, 0), 459193, Nil)
        // Details worked out elsewhere; if they're wrong, we can fgure out something else.
        match *self {
            HList::Nil => false,
            HList::Cons(ref o) => {
                let (ref x, h, ref l) = **o;
                h == 459193 &&
                x.equal(&Expr::PROP) &&
                if let HList::Nil = *l { true } else { false }
            }
        }
    }

    /// Then, checks on universes
    /// The universe should actually be in the universe map, or else it will return an error.
    fn check_eq_univs(&self, l2: &Self, g: &Universes) -> UnivResult<bool> {
        // NOTE: We don't just use any / all because we want to propagate errors; there may be a
        // way to do both somehow.
        let exists = |x1: &Expr, l: &Univ| {
            for x2 in l.iter() {
                if x1.check_equal(x2, g)? { return Ok(true) }
            }
            Ok(false)
        };
        for x1 in self.iter() {
            if !exists(x1, l2)? { return Ok(false) }
        }
        for x2 in l2.iter() {
            if !exists(x2, self)? { return Ok(false) }
        }
        return Ok(true)
    }

    /// The universe should actually be in the universe map, or else it will return an error.
    pub fn check_eq(&self, v: &Self, g: &Universes) -> UnivResult<bool> {
        Ok(self as *const _ == v as *const _ ||
           self.check_eq_univs(v, g)?)
    }

    /// The universe should actually be in the universe map, or else it will return an error.
    fn real_check_leq(&self, v: &Self, g: &Universes) -> UnivResult<bool> {
        // NOTE: We don't just use any / all because we want to propagate errors; there may be a
        // way to do both somehow.
        for ul in self.iter() {
            if !ul.exists_bigger(v, g)? { return Ok(false) }
        }
        return Ok(true)
    }

    /// The universe should actually be in the universe map, or else it will return an error.
    pub fn check_leq(&self, v: &Self, g: &Universes) -> UnivResult<bool> {
        Ok(self as *const _ == v as *const _ ||
           self.is_type0m() ||
           self.check_eq_univs(v, g)? ||
           self.real_check_leq(v, g)?)
    }
}

impl Instance {
    pub fn equal(&self, u: &Self) -> bool {
        self as *const _ == u as *const _ ||
        (self.is_empty() && u.is_empty()) ||
        (/* Necessary as universe instances might come from different modules and
            unmarshalling doesn't preserve sharing */
         self.len() == u.len() && self.iter().zip(u.iter()).all( |(x, y)| x.equal(y)))
    }

    /// The universe should actually be in the universe map, or else it will return an error.
    pub fn check_eq(&self, t2: &Instance, g: &Universes) -> UnivResult<bool> {
        if self as *const _ == t2 as *const _ { return Ok(true) }
        if self.len() != t2.len() { return Ok(false) }
        // NOTE: We don't just use any / all because we want to propagate errors; there may be a
        // way to do both somehow.
        for (u, v) in self.iter().zip(t2.iter()) {
            if !u.check_eq(v, g)? {
                return Ok(false)
            }
        }
        return Ok(true)
    }

    /// Substitution functions

    /// Substitute instance inst for ctx in csts

    /*fn subst_instance_level(s, l) {
        match l.level.data {
        }
    }*/

    pub fn subst_instance(&self, i: &Instance) -> Cow<Instance> {
        panic!("")

    }

    pub fn subst_universe(&self, u: &Univ) -> Cow<Univ> {
        panic!("")
    }

/*val subst_instance_instance : universe_instance -> universe_instance -> universe_instance
val subst_instance_universe : universe_instance -> universe -> universe
    let subst_instance_level s l =
      match l.Level.data with
      | Level.Var n -> s.(n)
      | _ -> l

    let subst_instance_instance s i =
      Array.smartmap (fun l -> subst_instance_level s l) i

    let subst_instance_universe s u =
      let f x = Universe.Expr.map (fun u -> subst_instance_level s u) x in
      let u' = Universe.smartmap f u in
        if u == u' then u
        else Universe.sort u'*/
}
