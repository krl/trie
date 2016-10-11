extern crate content;

use content::Hash;
use std::mem;
use std::ops::{Deref, DerefMut, Index, IndexMut};
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::fmt::{self, Debug};
use std::cell::RefCell;

#[derive(Debug, Clone)]
enum Child<K, V> {
    Trie(Trie<K, V>),
    Leaf {
        key: K,
        val: Arc<V>,
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

struct Trie<K, V> {
    cow: Arc<AtomicBool>,
    children: Arc<RefCell<Children<K, V>>>,
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

pub trait Nibbles {
    fn nibble(&self, i: usize) -> usize;
}

impl<K, V> Trie<K, V>
    where K: PartialEq + Nibbles + Debug + Clone,
          V: Clone + Debug {
    pub fn new() -> Self {
        Trie {
            children: Arc::new(RefCell::new(Children::new())),
            cow: Arc::new(AtomicBool::new(false)),
        }
    }
    pub fn ensure_writable(&mut self, cow: Arc<AtomicBool>) {
        if self.cow.load(Ordering::Relaxed) {
            // copy the children
            let mut newchildren = Children::new();
            {
                let children = self.children.deref().borrow();
                for i in 0..16 {
                    newchildren[i] = children[i].clone()
                }
            }
            *self = Trie {
                children: Arc::new(RefCell::new(newchildren)),
                cow: cow,
            }
        }
    }
    fn insert(&mut self, key: K, val: V) {
        let cow;

        let mut path = vec![];
        for i in 0..4 {
            path.push(key.nibble(i));
        }
        println!("inserting {:?}, {:?}", val, path);

        if self.cow.load(Ordering::Relaxed) {
            cow = Arc::new(AtomicBool::new(false));
        } else {
            cow = self.cow.clone();
        }
        self.insert_depth(key, Arc::new(val), 0, cow)
    }
    fn insert_depth(&mut self,
                    key: K,
                    val: Arc<V>,
                    depth: usize,
                    new_cow: Arc<AtomicBool>) {
        self.ensure_writable(new_cow.clone());
        let i = key.nibble(depth);
        let ref mut child = self.children.deref().borrow_mut()[i];
        match *child {
            // insert
            Child::None => *child = Child::Leaf { key: key, val: val },
            Child::Leaf { .. } => {
                let oldleaf = mem::replace(child, Child::None);
                if let Child::Leaf{ key: oldkey, val: oldval } = oldleaf {
                    if oldkey == key {
                        // overwrite
                        *child = Child::Leaf { key: key, val: val }
                    } else {
                        // split into new trie node
                        let mut trie = Trie::new();
                        trie.insert_depth(key, val, depth + 1, new_cow.clone());
                        trie.insert_depth(oldkey, oldval, depth + 1, new_cow);
                        *child = Child::Trie(trie);
                    }
                } else {
                    // already matched as a leaf
                    unreachable!();
                }
            },
            Child::Trie(ref mut trie) => {
                trie.insert_depth(key, val, depth + 1, new_cow);
            }
        }
    }

    fn remove(&mut self, key: K) {
        let cow;
        if self.cow.load(Ordering::Relaxed) {
            cow = Arc::new(AtomicBool::new(false));
        } else {
            cow = self.cow.clone();
        }
        self.remove_depth(key, 0, cow)
    }
    fn remove_depth(&mut self,
                    key: K,
                    depth: usize,
                    new_cow: Arc<AtomicBool>) {
        self.ensure_writable(new_cow.clone());
        let i = key.nibble(depth);

        let ref mut child = self.children.deref().borrow_mut()[i];
        let mut newchild;
        match *child {
            Child::Leaf { key: ref leafkey, .. } if leafkey == &key => {
                newchild = Child::None;
            },
            Child::None | Child::Leaf { .. } => return (),
            Child::Trie(ref mut trie) => {
                return trie.remove_depth(key, depth + 1, new_cow);
            }
        }
        *child = newchild;
        // Check if the removal left this node as a singleton.
        // match self.singleton() {
        //     Some(i) => newchild = cloned.move_out(i),
        //     None => newchild = Child::Trie(cloned),
        // }
    }

    fn move_out(self, i: usize) -> Child<K, V> {
        self.children.borrow_mut().remove(i)
    }

    fn singleton(&self) -> Option<usize> {
        let mut children = self.children.deref().borrow_mut();
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

    fn get(&self, key: K) -> Option<Arc<V>> {
        self.get_depth(key, 0)
    }

    fn get_depth(&self, key: K, depth: usize) -> Option<Arc<V>> {
        let i = key.nibble(depth);
        let ref child = self.children.deref().borrow()[i];
        match *child {
            Child::None => None,
            Child::Trie(ref trie) => trie.get_depth(key, depth + 1),
            Child::Leaf { key: ref leafkey, ref val } if leafkey == &key => {
                Some(val.clone())
            },
            Child::Leaf { .. } => None,
        }
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
        write!(f, "{:#?}", self.children.deref().borrow())
    }
}

#[cfg(test)]
mod tests {
    use super::{Trie, Nibbles, nibble};
    use std::hash::{Hash, Hasher, SipHasher};
    extern crate byteorder;
    use self::byteorder::{WriteBytesExt, BigEndian};

    impl Nibbles for &'static str {
        fn nibble(&self, i: usize) -> usize {
            nibble(self.as_ref(), i)
        }
    }

    impl Nibbles for [u8; 8] {
        fn nibble(&self, i: usize) -> usize {
            nibble(&self[..], i)
        }
    }

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
    fn lotsakeys() {
        let lots = 100_000;
        let mut trie = Trie::<[u8; 8], usize>::new();
        for i in 0..lots {
            trie.insert(hash(i), i);
        }

        for i in 0..lots {
            assert_eq!(*trie.get(hash(i)).unwrap(), i);
        }
    }

    #[test]
    fn removal() {
        let lots = 100_000;
        let mut trie = Trie::<[u8; 8], usize>::new();
        for i in 0..lots {
            trie.insert(hash(i), i);
        }

        for i in 0..lots/2 {
            trie.remove(hash(i*2));
        }

        for i in 0..lots {
            if i % 2 == 0 {
                assert_eq!(trie.get(hash(i)), None);
            } else {
                assert_eq!(*trie.get(hash(i)).unwrap(), i);
            }
        }
    }

    #[test]
    fn remove_all() {
        let lots = 20;
        let mut trie = Trie::<[u8; 8], usize>::new();
        for i in 0..lots {
            trie.insert(hash(i), i as usize);
        }

        for i in 0..lots {
            trie.remove(hash(i));
            println!("\n{:#?}", trie);
        }

        for i in 0..lots {
            assert_eq!(trie.get(hash(i)), None);
        }

        assert!((*trie.children).borrow().empty());
    }

    #[test]
    fn temp() {
        let mut a = Trie::<[u8; 8], usize>::new();
        a.insert(hash(18), 18);
        a.insert(hash(19), 19);
        println!("1: {:#?}", a);
        a.remove(hash(18));
        println!("2: {:#?}", a);
        a.remove(hash(19));
        println!("3: {:#?}", a);
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

        assert_eq!(*a.get(hash(1)).unwrap(), 10);
        assert_eq!(*a.get(hash(2)).unwrap(), 20);
        assert_eq!(a.get(hash(3)), None);

        assert_eq!(*b.get(hash(1)).unwrap(), 11);
        assert_eq!(*b.get(hash(2)).unwrap(), 20);
        assert_eq!(*b.get(hash(3)).unwrap(), 30);

        assert_eq!(*c.get(hash(1)).unwrap(), 111);

        // change old values
        a.insert(hash(1), 1111);

        assert_eq!(*a.get(hash(1)).unwrap(), 1111);
        assert_eq!(*b.get(hash(1)).unwrap(), 11);
        assert_eq!(*c.get(hash(1)).unwrap(), 111);
    }
}
