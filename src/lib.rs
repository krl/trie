extern crate parking_lot;

use std::mem;
use std::sync::Arc;
use std::ops::{Index, IndexMut};
use std::sync::atomic::{AtomicBool, // Ordering
};
use parking_lot::RwLock;

use std::fmt::{self, Debug};

#[derive(Clone)]
enum Child<K, V> {
    Trie(Trie<K, V>),
    Leaf {
        key: K,
        val: V,
    },
    None,
}

struct Children<K, V>([Child<K, V>; 16]);

impl<K, V> Index<usize> for Children<K, V> {
    type Output = Child<K, V>;
    fn index<'a>(&'a self, index: usize) -> &'a Self::Output {
        &self.0[index]
    }
}

impl<K, V> IndexMut<usize> for Children<K, V> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.0[index]
    }
}

impl<K, V> Children<K, V> {
    fn take(&mut self, i: usize) -> Child<K, V> {
        mem::replace(&mut self.0[i], Child::None)
    }
}

#[derive(Clone)]
pub struct Trie<K, V> {
    children: Arc<RwLock<Children<K, V>>>,
    cow: Arc<AtomicBool>,
}

impl<K, V> Children<K, V> {
    pub fn new() -> Self {
        Children(
            [Child::None, Child::None, Child::None, Child::None,
             Child::None, Child::None, Child::None, Child::None,
             Child::None, Child::None, Child::None, Child::None,
             Child::None, Child::None, Child::None, Child::None])
    }
}

impl<K, V> Trie<K, V>
    where K: PartialEq + AsRef<[u8]> + Debug + Clone,
          V: Clone + Debug {
    pub fn new() -> Self {
        Trie {
            children: Arc::new(RwLock::new(Children::new())),
            cow: Arc::new(AtomicBool::new(false)),
        }
    }

    fn put(&self, idx: usize, child: Child<K, V>) {
        self.children.write()[idx] = child;
    }

    fn new_from(akey: K, aval: V, bkey: K, bval: V, depth: usize) -> Self {
        let trie = Trie::new();
        let na = nibble(akey.as_ref(), depth);
        let nb = nibble(bkey.as_ref(), depth);
        if na == nb {
            let newtrie = Trie::new_from(akey, aval, bkey, bval, depth + 1);
            trie.put(na, Child::Trie(newtrie));
        } else {
            trie.put(na, Child::Leaf { key: akey, val: aval });
            trie.put(nb, Child::Leaf { key: bkey, val: bval });
        }
        trie
    }

    // fn ensure_writable(&mut self, cow: Arc<AtomicBool>) {
    //     if self.cow.load(Ordering::Relaxed) {
    //         // copy the children
    //         let mut newchildren = Children::new();
    //         {
    //             let children = self.children.read();
    //             for i in 0..16 {
    //                 newchildren[i] = children[i].clone()
    //             }
    //         }
    //         *self = Trie {
    //             children: Arc::new(RwLock::new(newchildren)),
    //             cow: cow,
    //         }
    //     }
    // }

    pub fn insert(&mut self, key: K, val: V) {
        self.insert_depth(key, val, 0)
    }

    fn insert_depth(&mut self, key: K, val: V, depth: usize) {
        let i = nibble(key.as_ref(), depth);
        let ref mut child = self.children.write()[i];
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
                                                            depth + 1));
                    }
                } else {
                    unreachable!();
                }
            },
            Child::Trie(ref mut trie) => {
                trie.insert_depth(key, val, depth + 1);
            }
        }
    }

    pub fn remove(&mut self, key: &K) {
        self.remove_depth(key, 0);
    }

    fn remove_depth(&mut self, key: &K, depth: usize) -> Option<Child<K, V>> {
        let i = nibble(key.as_ref(), depth);
        {
            let mut writelock = self.children.write();
            let ref mut child = writelock[i];
            let mut overwrite = None;
            match *child {
                Child::Leaf { key: ref leafkey, .. } if key == leafkey => {
                    overwrite = Some(Child::None)
                },
                Child::None | Child::Leaf{ .. } => (),
                Child::Trie(ref mut trie) => {
                    overwrite = trie.remove_depth(key, depth + 1);
                }
            }
            overwrite.map(|c| { *child = c });
        }
        if depth > 0 {
            let mut singleton = None;
            let mut children = self.children.write();
            for i in 0..16 {
                if let Child::None = children[i] {
                } else if singleton == None {
                    singleton = Some(i);
                } else {
                    return None
                }
            }
            singleton.map(|idx| {
                children.take(idx)
            })
        } else {
            None
        }
    }

    pub fn get(&self, key: &K) -> Option<V> {
        self.get_depth(key, 0)
    }

    pub fn get_depth(&self, key: &K, depth: usize) -> Option<V> {
        let i = nibble(key.as_ref(), depth);
        match self.children.read()[i] {
            Child::Leaf { key: ref leafkey, ref val } if leafkey == key =>
                Some(val.clone()),
            Child::Leaf { .. } | Child::None => None,
            Child::Trie(ref trie) => trie.get_depth(key, depth + 1)
        }
    }

    // test use only
    fn _empty(&self) -> bool {
        let children = self.children.read();
        for i in 0..16 {
            if let Child::None = children[i] {
            } else {
                return false
            }
        }
        true
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
    where K: Debug, V: Debug {
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
    where K: Debug, V: Debug {
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
    where K: Debug, V: Debug {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "{:#?}", *self.children.read())
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

    // #[test]
    // fn removal() {
    //     let lots = 100_000;
    //     let mut trie = Trie::<[u8; 8], usize>::new();
    //     for i in 0..lots {
    //         trie.insert(hash(i), i);
    //     }

    //     for i in 0..lots/2 {
    //         trie.remove(&hash(i*2));
    //     }

    //     for i in 0..lots {
    //         if i % 2 == 0 {
    //             assert_eq!(trie.get(&hash(i)), None);
    //         } else {
    //             assert_eq!(trie.get(&hash(i)), Some(i));
    //         }
    //     }
    // }

    #[test]
    fn remove_all() {
        let from = 17;
        let lots = 20;
        let mut trie = Trie::<[u8; 8], usize>::new();
        for i in from..lots {
            trie.insert(hash(i), i as usize);
        }

        println!("ALL: {:?}", trie);

        for i in from..lots {
            trie.remove(&hash(i));
            println!("removed {} {:?}", i, trie);
        }

        for i in from..lots {
            assert_eq!(trie.get(&hash(i)), None);
        }

        println!("leftovers:\n{:#?}", trie);

        assert!(trie._empty());
    }

    // #[test]
    // fn copy_on_write() {
    //     let mut a = Trie::<[u8; 8], usize>::new();

    //     let junk = 100_000;
    //     for i in 0..junk {
    //         a.insert(hash(i + 10000), 999);
    //     }

    //     a.insert(hash(1), 10);
    //     a.insert(hash(2), 20);

    //     let mut b = a.clone();

    //     b.insert(hash(1), 11);
    //     b.insert(hash(3), 30);

    //     let mut c = b.clone();

    //     c.insert(hash(1), 111);

    //     assert_eq!(*a.get(hash(1)).unwrap(), 10);
    //     assert_eq!(*a.get(hash(2)).unwrap(), 20);
    //     assert_eq!(a.get(hash(3)), None);

    //     assert_eq!(*b.get(hash(1)).unwrap(), 11);
    //     assert_eq!(*b.get(hash(2)).unwrap(), 20);
    //     assert_eq!(*b.get(hash(3)).unwrap(), 30);

    //     assert_eq!(*c.get(hash(1)).unwrap(), 111);

    //     // change old values
    //     a.insert(hash(1), 1111);

    //     assert_eq!(*a.get(hash(1)).unwrap(), 1111);
    //     assert_eq!(*b.get(hash(1)).unwrap(), 11);
    //     assert_eq!(*c.get(hash(1)).unwrap(), 111);
    // }
}
