use ocaml::de::{ORef, Seed};
use ocaml::values::{
    Int,
    CMap,
    Map,
};
use serde;
use std::collections::{HashMap};
use std::hash::{Hash};

// An iterator specialized to CMaps.
pub struct CMapIter<'a, K, V> where K: 'a, V: 'a {
    stack: Vec<&'a ORef<(CMap<K, V>, K, V, CMap<K, V>, Int)>>,
    node: &'a CMap<K, V>,
}

impl<'a, K, V> CMapIter<'a, K, V> {
    // TODO: Consider using height for size hint somehow (tree is balanced, so should be useful).
    fn new(node: &'a CMap<K, V>) -> Self {
        CMapIter {
            stack: Vec::new(),
            node: node,
        }
    }
}

impl<'a, K, V> Iterator for CMapIter<'a, K, V> {
    type Item = (&'a K, &'a V);

    // Note: order preserving (inorder traversal), though this isn't actually useful to us right
    // now.
    // Also note: if there were a cycle (which there shouldn't be) in the original Map,
    // this could loop forever.  But if used as intended (from a DeserializeSeed), this is unlikely
    // to happen, since DeserializeSeed will already loop forever in that case...
    fn next(&mut self) -> Option<(&'a K, &'a V)> {
        loop {
            match *self.node {
                CMap::Nil => {
                    let node = if let Some(node) = self.stack.pop() { node } else { return None };
                    let (_, ref k, ref v, ref right, _) = **node;
                    self.node = right;
                    return Some((k, v))
                },
                CMap::Node(ref node) => {
                    let (ref left, _, _, _, _) = **node;
                    self.stack.push(node);
                    self.node = left;
                },
            }
        }
    }
}

impl<K, V> CMap<K, V> {
    pub fn iter<'a>(&'a self) -> CMapIter<'a, K, V> {
        CMapIter::new(self)
    }
}

impl<'de, K, V> serde::de::DeserializeState<'de, Seed<'de>> for Map<K, V>
    where K: Hash + Eq + Clone + Send + Sync + 'static,
          V: Send + Sync + Clone + 'static,
          K: serde::de::DeserializeState<'de, Seed<'de>>,
          V: serde::de::DeserializeState<'de, Seed<'de>>,
{
    fn deserialize_state<'seed, D>(seed: &'seed mut Seed<'de>, deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::de::Deserializer<'de>,
    {
        // Lazy: we just deserialize the CMap, then add everything to a HashMap.
        let cmap: CMap<K, V> = CMap::deserialize_state(seed, deserializer)?;
        Ok(Map(cmap.iter().map( |(k, v)| (k.clone(), v.clone())).collect()))
    }
}

impl<K, V> ::std::ops::Deref for Map<K, V> where K: Hash + Eq {
    type Target = HashMap<K, V>;
    fn deref(&self) -> &HashMap<K, V> {
        &self.0
    }
}

impl<K, V> ::std::ops::DerefMut for Map<K, V> where K: Hash + Eq {
    fn deref_mut(&mut self) -> &mut HashMap<K, V> {
        &mut self.0
    }
}
