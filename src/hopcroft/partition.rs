use std::vec::Vec;
use std::iter::IntoIterator;

#[derive(Copy, Clone)]
pub struct Set(usize);

struct Info {
  /// index of the first element of a partition
  first : usize,
  /// successor index of the last element of a partition
  last : usize,
  /// index of the last marked element of a partition
  marked : usize,
}

pub struct Partition {
  /// data relative to each partition
  partinfo : Vec<Info>,
  /// associate a partition to an element
  index : Box<[Set]>,
  /// contain elements in a contiguous way w.r.t. partitions
  elements : Box<[usize]>,
  /// keep the location of an element in [elements]
  location : Box<[usize]>,
}

impl Set {

pub fn to_usize (i : Set) -> usize { let Set(i) = i; i }

pub fn of_usize (i : usize) -> Set { Set(i) }

}

impl Partition {

fn initial_size (n : usize) -> usize { n / 100 }

/// Create a new partition holding `n` elements. All elements are initially
/// member of the same partition.
pub fn new (n : usize) -> Partition {
  let mut partinfo = Vec::with_capacity(Partition::initial_size(n));
  let mut index = Vec::with_capacity(n);
  let mut elements = Vec::with_capacity(n);
  let mut location = Vec::with_capacity(n);
  partinfo.push(Info { first : 0, last : n, marked : 0 });
  for i in 0..n {
    index.push(Set(0));
    elements.push(i);
    location.push(i);
  }
  Partition {
    partinfo : partinfo,
    index : index.into_boxed_slice(),
    elements : elements.into_boxed_slice(),
    location : location.into_boxed_slice(),
  }
}

/// Number of partitions held by the datastructure.
pub fn len (p : &Partition) -> usize { Vec::len(&p.partinfo) }

/// Number of elements in a partition.
pub fn size (p : &Partition, i : Set) -> usize {
  let Set(i) = i;
  let ref info = p.partinfo[i];
  info.last - info.first
}

/// Return the partition an element is in.
pub fn partition(p : &Partition, n : usize) -> Set { p.index[n] }

}

// struct PartitionIter {
//   off : usize,
//   max : usize,
// }

// impl Iterator for PartitionIter  {
//   fn next (&mut self) -> Option<PartitionIter> {
//     if self.max == self.off { None } else {
//   }
// }
// 
// impl <'a> IntoIterator for &'a Partition {
//   type Item = usize;
//   type IntoIter = PartitionIter;
// }

impl Partition {
/*

let iter s f t =
  let fst = uget t.first s in
  let lst = uget t.last s in
  for i = fst to lst - 1 do
    f (uget t.elements i);
  done

let fold s f t accu =
  let fst = uget t.first s in
  let lst = uget t.last s in
  let rec fold accu i =
    if lst <= i then accu
    else fold (f (uget t.elements i) accu) (succ i)
  in
  fold accu fst

let iter_all f t =
  for i = 0 to t.partitions do f i; done

let fold_all f t accu =
  let rec fold accu i =
    if t.partitions <= i then accu
    else fold (f i accu) (succ i)
  in
  fold accu 0

let next i t =
  if uget t.last (uget t.index i) < uget t.location i then -1
  else uget t.elements (succ (uget t.location i))
*/

/// Split a partition between marked and unmarked elements. If this creates a
/// new partition, it is returned. Otherwise it returns `None`.
pub fn split (p : &mut Partition, i : Set) -> Option<Set> {
  let Set(i) = i;
  let new = {
    let info = &mut p.partinfo[i];
    if info.marked == info.last { info.marked = info.first; return None; }
    if info.marked == info.first { return None; }
    let ninfo = Info {
      first : info.first,
      last : info.marked,
      marked : info.first,
    };
    info.first = info.marked;
    ninfo
  };
  let len = p.partinfo.len() + 1;
  for i in new.first..new.last {
    p.index[p.elements[i]] = Set(len);
  }
  p.partinfo.push(new);
  Some (Set(len))
}

pub fn mark(p : &mut Partition, i : usize) {
  let Set(set) = p.index[i];
  let loc = p.location[i];
  let mark = p.partinfo[set].marked;
  if mark <= loc {
    p.elements[loc] = p.elements[mark];
    p.location[p.elements[loc]] = loc;
    p.elements[mark] = i;
    p.partinfo[set].marked = mark + 1;
  }
}

pub fn is_marked (p : &Partition, i : Set) -> bool {
  let Set(i) = i;
  let ref info = p.partinfo[i];
  info.marked != info.first
}

pub fn choose(p : &Partition, i : Set) -> usize {
  let Set(i) = i;
  p.elements[p.partinfo[i].first]
}

/*

let choose s t = uget t.elements (uget t.first s)

let represent s = s

*/

}
