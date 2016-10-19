extern crate parking_lot;

use std::mem;
use std::ops::{Deref, DerefMut, Index, IndexMut};
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::fmt::{self, Debug};
use parking_lot::RwLock;

#[derive(Debug, Clone)]
enum Child<K, V> {
    Trie(Trie<K, V>),
    Leaf {
        key: K,
        val: V,
    },
    None,
}

struct Children<K, V>([Child<K, V>; 16]);

enum RemoveResult {
    Empty,
    Ok,
    Noop,
}

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
    fn empty(&self) -> bool {
        for i in 0..16 {
            if let Child::None = self.0[i] {
            } else {
                return false
            }
        }
        true
    }
    fn remove(&mut self, i: usize) -> Child<K, V> {
        mem::replace(&mut self.0[i], Child::None)
    }
}

#[derive(Debug)]
struct Cursor<'a, K, V>
    where V: 'a, K: 'a
{
    trie: &'a Trie<K, V>,
    pos: usize,
}

struct Trie<K, V> {
    cow: Arc<AtomicBool>,
    children: Arc<RwLock<Children<K, V>>>,
}

impl<K, V> Clone for Trie<K, V> {
    fn clone(&self) -> Self {
        self.cow.store(true, Ordering::Relaxed);
        Trie {
            cow: self.cow.clone(),
            children: self.children.clone(),
        }
    }
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
    pub fn ensure_writable(&mut self, cow: Arc<AtomicBool>) {
        if self.cow.load(Ordering::Relaxed) {
            // copy the children
            let mut newchildren = Children::new();
            {
                let children = self.children.deref().read();
                for i in 0..16 {
                    newchildren[i] = children[i].clone()
                }
            }
            *self = Trie {
                children: Arc::new(RwLock::new(newchildren)),
                cow: cow,
            }
        }
    }

    fn insert(&mut self, key: K, val: V) {
        let branch = self.branch(&key);
        let last = branch.last().expect("no zero length branches");
        let mut children = last.trie.children.write();
        let ref mut child = children[last.pos];
        match *child {
            Child::None => {
                *child = Child::Leaf { key: key, val: val }
            },
            _ => unimplemented!(),
        }
    }

    fn get(&self, key: &K) -> Option<V> {
        let branch = self.branch(&key);
        let last = branch.last().expect("no zero length branches");
        let children = last.trie.children.read();
        match children[last.pos] {
            Child::Leaf { key: ref leafkey, val: ref val }
            if leafkey == key => Some(val.clone()),
            _ => None

        }
    }

    fn branch<'a>(&'a self, key: &K) -> Vec<Cursor<'a, K, V>> {
        let mut branch = vec![];
        self.branch_depth(key, 0, &mut branch);
        branch
    }

    fn branch_depth<'a>(&'a self,
                        key: &K,
                        depth: usize,
                        branch: &mut Vec<Cursor<'a, K,V>>) {
        let i = nibble(key.as_ref(), depth);
        branch.push(Cursor { trie: &self, pos: i});
    }

    fn empty(&self) -> bool {
        let children = self.children.read();
        for i in 0..16 {
            if let Child::None = children[i] {
            } else {
                return false
            }
        }
        true
    }

    fn singleton(&self) -> Option<usize> {
        let children = self.children.read();
        let mut pos = None;
        for i in 0..16 {
            if let Child::None = children[i] {
            } else if pos == None {
                pos = Some(i)
            } else {
                return None
            }
        }
        pos
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

impl<K, V> fmt::Debug for Children<K, V>
    where K: Debug, V: Debug {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        for i in 0..16 {
            if let Child::None = self.0[i] {
            } else {
                write!(f, "\n{}: {:#?}", i, self.0[i]);
            }
        }
        Ok(())
    }
}

impl<K, V> fmt::Debug for Trie<K, V>
    where K: Debug, V: Debug {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "{:#?}", *self.children.deref().read())
    }
}

#[cfg(test)]
mod tests {
    use super::{Trie, nibble};
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
        let lots = 5;
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
    //         trie.remove(hash(i*2));
    //     }

    //     for i in 0..lots {
    //         if i % 2 == 0 {
    //             assert_eq!(trie.get(hash(i)), None);
    //         } else {
    //             assert_eq!(*trie.get(hash(i)).unwrap(), i);
    //         }
    //     }
    // }

    // #[test]
    // fn remove_all() {
    //     let lots = 20;
    //     let mut trie = Trie::<[u8; 8], usize>::new();
    //     for i in 0..lots {
    //         trie.insert(hash(i), i as usize);
    //     }

    //     for i in 0..lots {
    //         trie.remove(hash(i));
    //         println!("\n{:#?}", trie);
    //     }

    //     for i in 0..lots {
    //         assert_eq!(trie.get(hash(i)), None);
    //     }

    //     assert!((*trie.children).borrow().empty());
    // }

    // #[test]
    // fn temp() {
    //     let mut a = Trie::<[u8; 8], usize>::new();
    //     a.insert(hash(18), 18);
    //     a.insert(hash(19), 19);
    //     println!("1: {:#?}", a);
    //     a.remove(hash(18));
    //     println!("2: {:#?}", a);
    //     a.remove(hash(19));
    //     println!("3: {:#?}", a);
    // }

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
