use ocaml::values::{
    Expr,
    HList,
    Instance,
    Int,
    Level,
    RawLevel,
    Univ,
};
use std::collections::HashMap;

/// Comparison on this type is pointer equality
/// FIXME: Make the above comment true.
#[derive(PartialEq,Eq)]
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

// type LMap<T> = HashMap<Level, T>;

type UMap<T> = HashMap<Level, T>;

/// A Level.t is either an alias for another one, or a canonical one,
/// for which we know the universes that are above
enum UnivEntry {
  Canonical(CanonicalArc),
  Equiv(Level),
}

pub struct Universes(UMap<UnivEntry>);

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum UnivError {
    Anomaly(String),
}

pub type UnivResult<T> = Result<T, UnivError>;

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
                        // FIXME: Pointer equality (depends on sharing)
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
                // FIXME: Pointer equality (depends on sharing)
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
                            // FIXME: Pointer equality (depends on sharing)
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
    //     // FIXME: Pointer equality (depends on sharing)
    //     if self as *const _ == arcv as *const _ { Ok(FastOrder::Eq) }
    //     else { self.fast_compare_neq(arcv, true, g) }
    // }

    /// The universe should actually be in the universe map, or else it will return an error.
    fn is_leq(&self, arcv: &Self, g: &Universes) -> UnivResult<bool> {
        // FIXME: Pointer equality (depends on sharing)
        Ok(self as *const _ == arcv as *const _ ||
           match self.fast_compare_neq(arcv, false, g)? {
               FastOrder::NLe => false,
               FastOrder::Eq | FastOrder::Le | FastOrder::Lt => true,
           })
    }

    /// The universe should actually be in the universe map, or else it will return an error.
    fn is_lt(&self, arcv: &Self, g: &Universes) -> UnivResult<bool> {
        // FIXME: Pointer equality (depends on sharing)
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
        // FIXME: Pointer equality (depends on sharing)
        Ok(arcu as *const _ == arcv as *const _)
    }

    /// The universe should actually be in the universe map, or else it will return an error.
    pub fn check_eq(&self, v: &Level, g: &Universes) -> UnivResult<bool> {
        // FIXME: Pointer equality (depends on sharing)
        // t1 == t2 ||
        self.check_equal(v, g)
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

    /// The universe should actually be in the universe map, or else it will return an error.
    pub fn check_equal(&self, y: &Self, g: &Universes) -> UnivResult<bool> {
        // FIXME: Pointer equality (depends on sharing)
        // self == y
        let Expr(ref u, n) = *self;
        let Expr(ref v, m) = *y;
        Ok(n == m && u.check_equal(v, g)?)
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
    pub fn is_type0m(&self) -> bool {
        // I believe type0m is:
        //    Cons (({ hash = 7; data = Prop }, 0), 459193, Nil)
        // Details worked out elsewhere; if they're wrong, we can fgure out something else.
        match *self {
            HList::Nil => false,
            HList::Cons(ref o) => {
                let (ref x, h, ref l) = **o;
                h == 459193 &&
                *x == Expr::PROP &&
                *l == HList::Nil
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
        // FIXME: Not entirely clear that u == v is a shortcut in this case, since we want pointer
        // equality for Level.equal (which is part of Expr.equal, which is part of Universe.equal).
        // So for now we just skip the equality check.
        /* u == v || */
        self.check_eq_univs(v, g)
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
        // FIXME: Not entirely clear that u == v is a shortcut in this case (see check_eq for
        // details), so we skip it.
        // self == v ||
        Ok(self.is_type0m() ||
           self.check_eq_univs(v, g)? ||
           self.real_check_leq(v, g)?)
    }
}

impl Instance {
    /// The universe should actually be in the universe map, or else it will return an error.
    pub fn check_eq(&self, t2: &Instance, g: &Universes) -> UnivResult<bool> {
        // FIXME: Pointer equality (depends on sharing)
        // t1 == t2 ||
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
}
