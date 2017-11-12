use std::collections::HashMap;
use ocaml::values::{
    // Int,
    Level,
};

/* /// Comparison on this type is pointer equality
struct CanonicalArc {
    univ: Level,
    lt: Vec<Level>,
    le: Vec<Level>,
    rank: Int,
    predicative: bool,
} */

// type LMap<T> = HashMap<Level, T>;

type UMap<T> = HashMap<Level, T>;

enum UnivEntry {
  // Canonical(CanonicalArc),
  // Equiv(Level),
}

pub struct Universes(UMap<UnivEntry>);
