extern crate parking_lot;
#[macro_use]
extern crate trait_group;

use std::mem;
use std::sync::Arc;
use std::ops::{Index, IndexMut};
use std::sync::atomic::{AtomicBool, Ordering};
use parking_lot::{RwLock, RwLockWriteGuard, RwLockReadGuard};

use std::fmt::{self, Debug};

trait_group! {
    pub trait Key: PartialEq + Clone + Debug + AsRef<[u8]>
}

trait_group! {
    pub trait Val: PartialEq + Clone + Debug
}

#[derive(PartialEq, Clone)]
pub enum Child<K, V>
    where K: Key, V: Val {
    Trie(Trie<K, V>),
    Leaf {
        key: K,
        val: V,
    },
    None,
}

enum RemoveResult<K, V>
    where K: Key, V: Val {
    Done,
    Clear,
    PassUp(Child<K, V>),
}

#[derive(PartialEq)]
pub struct Children<K, V>([Child<K, V>; 16])
    where K: Key, V: Val;

impl<K, V> Index<usize> for Children<K, V>
    where K: Key, V: Val {
    type Output = Child<K, V>;
    fn index<'a>(&'a self, index: usize) -> &'a Self::Output {
        &self.0[index]
    }
}

impl<K, V> IndexMut<usize> for Children<K, V>
    where K: Key, V: Val {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.0[index]
    }
}

pub struct Trie<K, V>
    where K: Key, V: Val {
    children: Arc<RwLock<Children<K, V>>>,
    cow: Arc<AtomicBool>,
}

impl<K, V> PartialEq for Trie<K, V>
    where K: Key, V: Val {
    fn eq(&self, other: &Self) -> bool {
        *self.readable_children() == *other.readable_children()
    }
}

impl<K, V> Clone for Trie<K, V>
    where K: Key, V: Val {
    fn clone(&self) -> Self {
        self.cow.store(true, Ordering::Relaxed);
        Trie {
            children: self.children.clone(),
            cow: self.cow.clone(),
        }
    }
}

impl<K, V> Children<K, V>
    where K: Key, V: Val {
    pub fn new() -> Self {
        Children(
            [Child::None, Child::None, Child::None, Child::None,
             Child::None, Child::None, Child::None, Child::None,
             Child::None, Child::None, Child::None, Child::None,
             Child::None, Child::None, Child::None, Child::None])
    }
    fn take(&mut self, i: usize) -> Child<K, V> {
        mem::replace(&mut self.0[i], Child::None)
    }
    fn singleton_idx(&self) -> Option<usize> {
        let mut singleton = None;
        for i in 0..16 {
            if let Child::None = self.0[i] {
            } else if singleton == None {
                singleton = Some(i);
            } else {
                return None
            }
        }
        singleton
    }
    fn singleton_leaf(&mut self) -> Option<Child<K, V>> {
        self.singleton_idx().and_then(|i| {
            match self.0[i] {
                Child::Leaf{ .. } => Some(self.take(i)),
                _ => None,
            }
        })
    }
    fn singleton(&mut self) -> bool {
        self.singleton_idx().is_some()
    }
}


impl<K, V> Trie<K, V>
    where K: Key, V: Val {
    pub fn new() -> Self {
        Trie {
            children: Arc::new(RwLock::new(Children::new())),
            cow: Arc::new(AtomicBool::new(false)),
        }
    }

    pub fn new_cow(cow: Arc<AtomicBool>) -> Self {
        Trie {
            children: Arc::new(RwLock::new(Children::new())),
            cow: cow,
        }
    }

    fn put(&mut self, idx: usize, child: Child<K, V>, cow: Arc<AtomicBool>) {
        self.writable_children(cow)[idx] = child;
    }

    fn new_from(
        akey: K,
        aval: V,
        bkey: K,
        bval: V,
        depth: usize,
        cow: Arc<AtomicBool>) -> Self
    {
        let mut trie = Trie::new();
        let na = nibble(akey.as_ref(), depth);
        let nb = nibble(bkey.as_ref(), depth);
        if na == nb {
            let newtrie = Trie::new_from(
                akey,
                aval,
                bkey,
                bval,
                depth + 1,
                cow.clone());
            trie.put(na, Child::Trie(newtrie), cow);
        } else {
            trie.put(na, Child::Leaf { key: akey, val: aval }, cow.clone());
            trie.put(nb, Child::Leaf { key: bkey, val: bval }, cow);
        }
        trie
    }

    pub fn writable_children(&mut self, cow: Arc<AtomicBool>)
                             -> RwLockWriteGuard<Children<K, V>> {
        if self.cow.load(Ordering::Relaxed) {
            // copy the children
            let mut newchildren = Children::new();
            {
                let children = self.readable_children();
                for i in 0..16 {
                    newchildren[i] = children[i].clone()
                }
            }
            *self = Trie {
                children: Arc::new(RwLock::new(newchildren)),
                cow: cow,
            }
        }
        self.children.write()
    }

    pub fn readable_children(&self) -> RwLockReadGuard<Children<K, V>> {
        self.children.read()
    }

    pub fn insert(&mut self, key: K, val: V) {
        self.insert_depth(key, val, 0, Arc::new(AtomicBool::new(false)))
    }

    fn insert_depth(&mut self, key: K, val: V, depth: usize, cow: Arc<AtomicBool>) {
        let i = nibble(key.as_ref(), depth);
        let ref mut child = self.writable_children(cow.clone())[i];
        match *child {
            Child::None => *child = Child::Leaf { key: key, val: val },
            Child::Leaf { .. } => {
                let oldleaf = mem::replace(child, Child::None);
                if let Child::Leaf { key: leafkey, val: leafval } = oldleaf {
                    if leafkey == key {
                        *child = Child::Leaf { key: key, val: val }
                    } else {
                        *child = Child::Trie(Trie::new_from(leafkey,
                                                            leafval,
                                                            key,
                                                            val,
                                                            depth + 1,
                                                            cow));
                    }
                } else {
                    unreachable!();
                }
            },
            Child::Trie(ref mut trie) => {
                trie.insert_depth(key, val, depth + 1, cow);
            }
        }
    }

    pub fn remove(&mut self, key: &K) {
        self.remove_depth(key, 0, Arc::new(AtomicBool::new(false)));
    }

    fn remove_depth(
        &mut self,
        key: &K,
        depth: usize,
        cow: Arc<AtomicBool>) -> RemoveResult<K, V>
    {
        let i = nibble(key.as_ref(), depth);
        let ref mut writelock = self.writable_children(cow.clone());
        let result = match writelock[i] {
            Child::Leaf { key: ref leafkey, .. } if key == leafkey => {
                RemoveResult::Clear
            },
            Child::None | Child::Leaf{ .. } => RemoveResult::Done,
            Child::Trie(ref mut trie) => {
                match trie.remove_depth(key, depth + 1, cow) {
                    RemoveResult::PassUp(passed) => RemoveResult::PassUp(passed),
                    _ => RemoveResult::Done,
                }
            }
        };
        // Enact the change and cascade up if producing singleton tries
        match result {
            RemoveResult::Done => RemoveResult::Done,
            RemoveResult::Clear => {
                writelock[i] = Child::None;
                match writelock.singleton_leaf() {
                    Some(single) => {
                        RemoveResult::PassUp(single)
                    }
                    None => RemoveResult::Done,
                }
            }
            RemoveResult::PassUp(passed) => {
                if writelock.singleton() {
                    RemoveResult::PassUp(passed)
                } else {
                    writelock[i] = passed;
                    RemoveResult::Done
                }
            }
        }
    }

    pub fn get(&self, key: &K) -> Option<V> {
        self.get_depth(key, 0)
    }

    pub fn get_depth(&self, key: &K, depth: usize) -> Option<V> {
        let i = nibble(key.as_ref(), depth);
        match self.readable_children()[i] {
            Child::Leaf { key: ref leafkey, ref val } if leafkey == key =>
                Some(val.clone()),
            Child::Leaf { .. } | Child::None => None,
            Child::Trie(ref trie) => trie.get_depth(key, depth + 1)
        }
    }

    pub fn update<U>(&mut self, key: &K, update: U) where U: Fn(&V) -> V {
        self.update_depth(key, update, 0, Arc::new(AtomicBool::new(false)))
    }

    pub fn update_depth<U>(
        &mut self, key: &K, update: U, depth: usize, cow: Arc<AtomicBool>
    ) where U: Fn(&V) -> V {
        let i = nibble(key.as_ref(), depth);
        let ref mut writelock = self.writable_children(cow.clone());
        match writelock[i] {
            Child::Leaf { key: ref leafkey, ref mut val } if leafkey == key =>
                *val = update(val),
            Child::Leaf { .. } | Child::None => (),
            Child::Trie(ref mut trie) => trie.update_depth(key, update, depth + 1, cow)
        }
    }


    // test use only
    fn _empty(&self) -> bool {
        let children = self.readable_children();
        for i in 0..16 {
            if let Child::None = children[i] {
            } else {
                return false
            }
        }
        true
    }

    pub fn union(&self, other: &Trie<K, V>) -> Trie<K, V> {
        self.union_depth(other, 0, Arc::new(AtomicBool::new(false)))
    }

    fn union_depth(
        &self,
        other: &Trie<K, V>,
        depth: usize,
        cow: Arc<AtomicBool>
    ) -> Trie<K, V> {
        let mut union = Trie::new_cow(cow.clone());
        {
            let a = self.readable_children();
            let b = other.readable_children();
            let mut c = union.writable_children(cow.clone());
            for i in 0..16 {
                if a[i] == b[i] {
                    c[i] == a[i].clone();
                } else {
                    c[i] = match (&a[i], &b[i]) {
                        (&Child::None, &Child::None) => Child::None,

                        (&Child::Leaf { ref key, ref val }, &Child::None) |
                        (&Child::None, &Child::Leaf { ref key, ref val }) =>
                            Child::Leaf { key: key.clone(), val: val.clone() },

                        (&Child::Trie(ref trie), &Child::None) |
                        (&Child::None, &Child::Trie(ref trie)) =>
                            Child::Trie(trie.clone()),

                        (&Child::Leaf { key: ref akey, val: ref aval },
                         &Child::Leaf { key: ref bkey, val: ref bval }) =>
                            Child::Trie(Trie::new_from(
                                akey.clone(),
                                aval.clone(),
                                bkey.clone(),
                                bval.clone(),
                                depth + 1,
                                cow.clone())),

                        (&Child::Leaf { ref key, ref val }, &Child::Trie(ref trie)) |
                        (&Child::Trie(ref trie), &Child::Leaf { ref key, ref val }) => {
                            let mut trie = trie.clone();
                            trie.insert_depth(
                                key.clone(),
                                val.clone(),
                                depth + 1,
                                cow.clone());
                            Child::Trie(trie)
                        },

                        (&Child::Trie(ref a), &Child::Trie(ref b)) =>
                            Child::Trie(a.union_depth(b, depth + 1, cow.clone())),
                    }
                }
            }
        }
        union
    }
}

/// Gets the nibble at position i
pub fn nibble(key: &[u8], i: usize) -> usize {
    if i % 2 == 0 {
        (key[i / 2] & 0b1111) as usize
    } else {
        (key[i / 2] >> 4) as usize
    }
}

impl<K, V> fmt::Debug for Child<K, V>
    where K: Key, V: Val {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match *self {
            Child::Leaf { ref val, .. } => {
                write!(f, "{:#?}", val)
            },
            Child::Trie(ref t) => {
                write!(f, "{:#?}", t)
            },
            _ => Ok(()),
        }
    }
}

impl<K, V> fmt::Debug for Children<K, V>
    where K: Key, V: Val {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        try!(write!(f, "[ "));
        for i in 0..16 {
            if let Child::None = self.0[i] {
            } else {
                try!(write!(f, "{:?} ", self.0[i]));
            }
        }
        try!(write!(f, "]"));
        Ok(())
    }
}

impl<K, V> fmt::Debug for Trie<K, V>
    where K: Key, V: Val {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "{:#?}", *self.readable_children())
    }
}

#[cfg(test)]
mod tests {
    use super::Trie;
    use std::hash::{Hash, Hasher, SipHasher};
    extern crate byteorder;
    use self::byteorder::{WriteBytesExt, BigEndian};

    fn hash(i: usize) -> [u8; 8] {
        let mut h = SipHasher::new();
        i.hash(&mut h);
        let mut vec: Vec<u8> = vec![];
        vec.write_u64::<BigEndian>(h.finish()).unwrap();
        let mut key = [0u8; 8];
        for i in 0..8 {
            key[i] = vec[i]
        }
        key
    }

    #[test]
    fn insert_one() {
        let mut trie = Trie::<[u8; 8], &'static str>::new();
        trie.insert([0; 8], "wonk");
        assert_eq!(trie.get(&[0; 8]), Some("wonk"));
        assert_eq!(trie.get(&[1; 8]), None);
    }

    #[test]
    fn lotsakeys() {
        let lots = 100_000;
        let mut trie = Trie::<[u8; 8], usize>::new();
        for i in 0..lots {
            trie.insert(hash(i), i);
        }
        for i in 0..lots {
            assert_eq!(trie.get(&hash(i)), Some(i));
        }
    }

    #[test]
    fn removal() {
        let lots = 100_000;
        let mut trie = Trie::<[u8; 8], usize>::new();
        for i in 0..lots {
            trie.insert(hash(i), i);
        }

        for i in 0..lots {
            if i % 2 == 0 {
                trie.remove(&hash(i));
            }
        }

        for i in 0..lots {
            if i % 2 == 0 {
                assert_eq!(trie.get(&hash(i)), None);
            } else {
                assert_eq!(trie.get(&hash(i)), Some(i));
            }
        }
    }

    #[test]
    fn remove_all() {

        let lots = 100_000;

        let mut trie = Trie::<[u8; 8], usize>::new();
        for i in 0..lots {
            trie.insert(hash(i), i as usize);
        }

        for i in 0..lots {
            trie.remove(&hash(i));
        }

        for i in 0..lots {
            assert_eq!(trie.get(&hash(i)), None);
        }

        assert!(trie._empty());
    }

    #[test]
    fn update() {
        let lots = 100_000;
        let mut trie = Trie::<[u8; 8], usize>::new();
        for i in 0..lots {
            trie.insert(hash(i), i);
        }
        for i in 0..lots {
            trie.update(&hash(i), |x| x + 1);
        }
        for i in 0..lots {
            assert_eq!(trie.get(&hash(i)), Some(i + 1));
        }
    }

    #[test]
    fn tries_in_a_trie() {
        let mut trietrie = Trie::<[u8; 8], Trie<[u8; 8], usize>>::new();
        let many = 1000;

        for i in 0..many {
            let mut trie = Trie::<[u8; 8], usize>::new();
            for o in 0..many {
                trie.insert(hash(o), o * i);
            }
            trietrie.insert(hash(i), trie);
        }

        for i in 0..many {
            for o in 0..many {
                assert_eq!(trietrie.get(&hash(i)).unwrap().get(&hash(o)),
                           Some(o * i));
            }
        }
    }

    #[test]
    fn union() {
        let lots = 100_000;
        let mut a = Trie::<[u8; 8], usize>::new();
        let mut b = Trie::<[u8; 8], usize>::new();
        for i in 0..lots {
            if i % 2 == 0 {
                a.insert(hash(i), i);
            } else {
                b.insert(hash(i), i);
            }
        }

        let union = a.union(&b);

        for i in 0..lots {
            assert_eq!(union.get(&hash(i)), Some(i));
            if i % 2 == 0 {
                assert_eq!(a.get(&hash(i)), Some(i));
                assert_eq!(b.get(&hash(i)), None);
            } else {
                assert_eq!(a.get(&hash(i)), None);
                assert_eq!(b.get(&hash(i)), Some(i));
            }
        }
    }

    #[test]
    fn copy_on_write() {
        let mut a = Trie::<[u8; 8], usize>::new();

        let junk = 100_000;
        for i in 0..junk {
            a.insert(hash(i + 10000), 999);
        }

        a.insert(hash(1), 10);
        a.insert(hash(2), 20);

        let mut b = a.clone();

        b.insert(hash(1), 11);
        b.insert(hash(3), 30);

        let mut c = b.clone();

        c.insert(hash(1), 111);

        assert_eq!(a.get(&hash(1)), Some(10));
        assert_eq!(a.get(&hash(2)), Some(20));
        assert_eq!(a.get(&hash(3)), None);

        assert_eq!(b.get(&hash(1)), Some(11));
        assert_eq!(b.get(&hash(2)), Some(20));
        assert_eq!(b.get(&hash(3)), Some(30));

        assert_eq!(c.get(&hash(1)), Some(111));

        // change old values
        a.insert(hash(1), 1111);

        assert_eq!(a.get(&hash(1)), Some(1111));
        assert_eq!(b.get(&hash(1)), Some(11));
        assert_eq!(c.get(&hash(1)), Some(111));
    }

    #[test]
    fn copy_on_write_remove() {
        let mut a = Trie::<[u8; 8], usize>::new();

        let lots = 100_000;
        for i in 0..lots {
            a.insert(hash(i), i);
        }

        let mut b = a.clone();

        b.remove(&hash(0));
        b.remove(&hash(1));

        let mut c = b.clone();

        c.remove(&hash(2));

        assert_eq!(a.get(&hash(0)), Some(0));
        assert_eq!(a.get(&hash(1)), Some(1));
        assert_eq!(a.get(&hash(2)), Some(2));

        assert_eq!(b.get(&hash(0)), None);
        assert_eq!(b.get(&hash(1)), None);
        assert_eq!(b.get(&hash(2)), Some(2));

        assert_eq!(c.get(&hash(0)), None);
        assert_eq!(c.get(&hash(1)), None);
        assert_eq!(c.get(&hash(2)), None);

    }
}
