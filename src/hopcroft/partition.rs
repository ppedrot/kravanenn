use std::vec::Vec;
use std::iter::IntoIterator;
use std::marker::PhantomData;

pub struct Set<T>(usize, PhantomData<*const T>);

impl<T> Copy for Set<T> {}
impl<T> Clone for Set<T> { fn clone(&self) -> Set<T> { *self } }

struct Info {
  /// index of the first element of a partition
  first : usize,
  /// successor index of the last element of a partition
  last : usize,
  /// index of the last marked element of a partition
  marked : usize,
}

pub struct Partition<T> {
  /// data relative to each partition
  partinfo : Vec<Info>,
  /// associate a partition to an element
  index : Box<[Set<T>]>,
  /// contain elements in a contiguous way w.r.t. partitions
  elements : Box<[usize]>,
  /// keep the location of an element in [elements]
  location : Box<[usize]>,
}

impl<T> Set<T> {

pub fn to_usize (i : Set<T>) -> usize { let Set(i, _) = i; i }

pub fn of_usize (i : usize) -> Set<T> {
  Set(i, PhantomData)
}

}

fn initial_size (n : usize) -> usize { n / 100 }

impl<T> Partition<T> {

/// Create a new partition holding `n` elements. All elements are initially
/// member of the same partition.
pub fn new (n : usize) -> Partition<T> {
  let mut partinfo = Vec::with_capacity(initial_size(n));
  let mut index = Vec::with_capacity(n);
  let mut elements = Vec::with_capacity(n);
  let mut location = Vec::with_capacity(n);
  partinfo.push(Info { first : 0, last : n, marked : 0 });
  for i in 0..n {
    index.push(Set::of_usize(0));
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
pub fn size (&self, i : Set<T>) -> usize {
  let Set(i, _) = i;
  let ref info = self.partinfo[i];
  info.last - info.first
}

/// Return the partition an element is in.
pub fn partition(&self, n : usize) -> Set<T> { self.index[n].clone() }

}

pub struct PartitionIter<T> {
  off : usize,
  max : usize,
  phantom : PhantomData<*const T>,
}

impl<T> Iterator for PartitionIter<T> {
  type Item = Set<T>;
  fn next (&mut self) -> Option<Set<T>> {
    if self.max == self.off { None } else {
      let ans = self.off;
      self.off = self.off + 1;
      Some(Set::of_usize(ans))
    }
  }
}

impl<'a, T> IntoIterator for &'a Partition<T> {
  type Item = Set<T>;
  type IntoIter = PartitionIter<T>;
  fn into_iter(self) -> PartitionIter<T> {
    PartitionIter { off : 0, max : self.len(), phantom : PhantomData }
  }
}

pub struct SetIter<'a, T> {
  off : usize,
  max : usize,
  ptr : &'a[usize],
  phantom : PhantomData<*const T>,
}

impl <'a, T> Iterator for SetIter<'a, T> {
  type Item = usize;
  fn next (&mut self) -> Option<usize> {
    if self.max == self.off { None } else {
      let ans = self.ptr[self.off];
      self.off = self.off + 1;
      Some(ans)
    }
  }
}

impl <'a, T> Partition<T> {

pub fn class(&'a self, i : Set<T>) -> SetIter<'a, T> {
  let Set(i, _) = i;
  let ref info = self.partinfo[i];
  SetIter {
    off : info.first,
    max : info.last,
    ptr : self.elements.as_ref(),
    phantom : PhantomData,
  }
}

}

impl<T> Partition<T> {

/// Split a partition between marked and unmarked elements. If this creates a
/// new partition, it is returned. Otherwise it returns `None`.
pub fn split (&mut self, i : Set<T>) -> Option<Set<T>> {
  let Set(i, _) = i;
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
    self.index[self.elements[i]] = Set::of_usize(len);
  }
  self.partinfo.push(new);
  Some (Set::of_usize(len))
}

pub fn mark(&mut self, i : usize) {
  let Set(set, _) = self.index[i];
  let loc = self.location[i];
  let mark = self.partinfo[set].marked;
  if mark <= loc {
    self.elements[loc] = self.elements[mark];
    self.location[self.elements[loc]] = loc;
    self.elements[mark] = i;
    self.partinfo[set].marked = mark + 1;
  }
}

pub fn is_marked(&self, i : Set<T>) -> bool {
  let Set(i, _) = i;
  let ref info = self.partinfo[i];
  info.marked != info.first
}

pub fn choose(&self, i : Set<T>) -> usize {
  let Set(i, _) = i;
  self.elements[self.partinfo[i].first]
}

}
