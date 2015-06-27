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
pub fn len (&self) -> usize { Vec::len(&self.partinfo) }

/// Number of elements in a partition.
pub fn size (&self, i : Set) -> usize {
  let Set(i) = i;
  let ref info = self.partinfo[i];
  info.last - info.first
}

/// Return the partition an element is in.
pub fn partition(&self, n : usize) -> Set { self.index[n] }

}

pub struct PartitionIter {
  off : usize,
  max : usize,
}

impl Iterator for PartitionIter {
  type Item = Set;
  fn next (&mut self) -> Option<Set> {
    if self.max == self.off { None } else {
      let ans = self.off;
      self.off = self.off + 1;
      Some(Set(ans))
    }
  }
}

impl <'a> IntoIterator for &'a Partition {
  type Item = Set;
  type IntoIter = PartitionIter;
  fn into_iter(self) -> PartitionIter { PartitionIter { off : 0, max : self.len() } }
}

pub struct SetIter<'a> {
  off : usize,
  max : usize,
  ptr : &'a[usize],
}

impl <'a> Iterator for SetIter<'a> {
  type Item = usize;
  fn next (&mut self) -> Option<usize> {
    if self.max == self.off { None } else {
      let ans = self.ptr[self.off];
      self.off = self.off + 1;
      Some(ans)
    }
  }
}

impl <'a> Partition {

pub fn class(&'a self, i : Set) -> SetIter<'a> {
  let Set(i) = i;
  let ref info = self.partinfo[i];
  SetIter {
    off : info.first,
    max : info.last,
    ptr : self.elements.as_ref(),
  }
}

}

impl Partition {

/// Split a partition between marked and unmarked elements. If this creates a
/// new partition, it is returned. Otherwise it returns `None`.
pub fn split (&mut self, i : Set) -> Option<Set> {
  let Set(i) = i;
  let new = {
    let info = &mut self.partinfo[i];
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
  let len = self.partinfo.len() + 1;
  for i in new.first..new.last {
    self.index[self.elements[i]] = Set(len);
  }
  self.partinfo.push(new);
  Some (Set(len))
}

pub fn mark(&mut self, i : usize) {
  let Set(set) = self.index[i];
  let loc = self.location[i];
  let mark = self.partinfo[set].marked;
  if mark <= loc {
    self.elements[loc] = self.elements[mark];
    self.location[self.elements[loc]] = loc;
    self.elements[mark] = i;
    self.partinfo[set].marked = mark + 1;
  }
}

pub fn is_marked (&self, i : Set) -> bool {
  let Set(i) = i;
  let ref info = self.partinfo[i];
  info.marked != info.first
}

pub fn choose(&self, i : Set) -> usize {
  let Set(i) = i;
  self.elements[self.partinfo[i].first]
}

/*

let choose s t = uget t.elements (uget t.first s)

let represent s = s

*/

}
