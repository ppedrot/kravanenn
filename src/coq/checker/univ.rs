use ocaml::values::{
    Instance,
    Int,
    Level,
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

// type LMap<T> = HashMap<Level, T>;

type UMap<T> = HashMap<Level, T>;

/// A Level.t is either an alias for another one, or a canonical one,
/// for which we know the universes that are above
enum UnivEntry {
  Canonical(CanonicalArc),
  Equiv(Level),
}

pub struct Universes(UMap<UnivEntry>);

pub enum UnivError {
    Anomaly(String),
}

pub type UnivResult<T> = Result<T, UnivError>;

impl Level {
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

    /// First, checks on universe levels
    fn check_equal(&self, v: &Level, g: &Universes) -> UnivResult<bool> {
        let arcu = self.repr(g)?;
        let arcv = v.repr(g)?;
        // FIXME: Pointer equality (depends on sharing)
        Ok(arcu == arcv)
    }

    pub fn check_eq(&self, v: &Level, g: &Universes) -> UnivResult<bool> {
        // FIXME: Pointer equality (depends on sharing)
        // t1 == t2 ||
        self.check_equal(v, g)
    }
}

impl Universes {
    /// Universe checks [check_eq] and [check_leq], used in coqchk

    /// Then, checks on universes
    pub fn check_eq(&self, t1: &Instance, t2: &Instance) -> UnivResult<bool> {
        // FIXME: Pointer equality (depends on sharing)
        // t1 == t2 ||
        if t1.len() != t2.len() { return Ok(false) }
        for (u, v) in t1.iter().zip(t2.iter()) {
            if !u.check_eq(v, self)? {
                return Ok(false)
            }
        }
        return Ok(true)
    }
}
