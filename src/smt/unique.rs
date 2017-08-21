use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::rc::{Rc,Weak};
use std::hash::{Hash,Hasher};
use std::cell::RefCell;
use std::fmt::{Debug,Formatter,Error};
use std::borrow::Borrow;
use std::ops::Deref;

#[derive(Clone)]
pub struct UniqueRef<U : Hash + Eq>(Rc<UniqueEntry<U>>);

pub struct Uniquer<U : Hash + Eq> {
    map: Rc<RefCell<HashMap<U,Weak<UniqueEntry<U>>>>>
}

struct UniqueEntry<U : Hash + Eq> {
    map: Weak<RefCell<HashMap<U,Weak<UniqueEntry<U>>>>>,
    elem: U
}

impl<U : Hash + Eq + Clone> Uniquer<U> {
    pub fn new() -> Uniquer<U> {
        Uniquer { map: Rc::new(RefCell::new(HashMap::new())) }
    }
    pub fn get(&self,key: U) -> UniqueRef<U> {
        match self.map.try_borrow_mut() {
            Err(_) => panic!("Uniquer internal error"),
            Ok(ref mut mp) => match mp.entry(key.clone()) {
                Entry::Vacant(e) => {
                    let r = Rc::new(UniqueEntry { map: Rc::downgrade(&self.map),
                                                  elem: key });
                    let w = Rc::downgrade(&r);
                    e.insert(w);
                    UniqueRef(r)
                },
                Entry::Occupied(mut e) => {
                    match Weak::upgrade(e.get()) {
                        None => {
                            let r = Rc::new(UniqueEntry { map: Rc::downgrade(&self.map),
                                                          elem: key });
                            let w = Rc::downgrade(&r);
                            e.insert(w);
                            UniqueRef(r)
                        },
                        Some(re) => UniqueRef(re.clone())
                    }
                }
            }
        }
    }
}

impl<U : Hash + Eq> Drop for UniqueEntry<U> {
    fn drop(&mut self) {
        match self.map.upgrade() {
            None => {},
            Some(mp) => match mp.try_borrow_mut() {
                Err(_) => panic!("Cannot change map"),
                Ok(ref mut rmp) => { rmp.remove(&self.elem); }
            }
        }
    }
}

impl<U : Hash + Eq> UniqueRef<U> {
    pub fn get<'a>(&'a self) -> &'a U {
        let UniqueRef(ref r) = *self;
        &r.elem
    }
}

impl<U : Hash + Eq> PartialEq for UniqueRef<U> {
    fn eq(&self,oth: &UniqueRef<U>) -> bool {
        let UniqueRef(ref r1) = *self;
        let UniqueRef(ref r2) = *oth;
        Rc::ptr_eq(r1,r2)
    }
}

impl<U : Hash + Eq> Eq for UniqueRef<U> {}

impl<U : Hash + Eq + Debug> Debug for UniqueRef<U> {
    fn fmt(&self, f: &mut Formatter) -> Result<(),Error> {
        let UniqueRef(ref r) = *self;
        r.elem.fmt(f)
    }
}

impl<U : Hash + Eq> Hash for UniqueRef<U> {
    fn hash<H>(&self,state: &mut H) where H : Hasher {
        let UniqueRef(ref r) = *self;
        (Rc::borrow(r) as *const UniqueEntry<U>).hash(state)
    }
}

impl<U : Hash + Eq> AsRef<U> for UniqueRef<U> {
    fn as_ref(&self) -> &U {
        let UniqueRef(ref r) = *self;
        &r.elem
    }
}

impl<U : Hash + Eq> Deref for UniqueRef<U> {
    type Target = U;
    fn deref(&self) -> &U {
        let UniqueRef(ref r) = *self;
        &r.elem
    }
}
