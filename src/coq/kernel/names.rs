use std::collections::HashMap;

use ocaml::values::{
    Cst,
    Ind,
    Kn,
    Mp,
    Proj,
};

pub type MutInd = Cst;

impl PartialEq for Cst {
    // FIXME: This is a not very nice hack to make sure we have the correct equality for the
    // current HashMaps.  You probably shouldn't rely on this for regular equality.
    fn eq(&self, o: &Self) -> bool {
        self.user_equal(o)
    }
}

impl MutInd {
    pub fn canonical(&self) -> &Kn {
        match *self {
            Cst::Same(ref kn) => kn,
            Cst::Dual(ref o) => {
                let (_, ref kn) = **o;
                kn
            },
        }
    }

    pub fn user(&self) -> &Kn {
        match *self {
            Cst::Same(ref kn) => kn,
            Cst::Dual(ref o) => {
                let (ref kn, _) = **o;
                kn
            },
        }
    }

    pub fn user_equal(&self, y: &Self) -> bool {
        self as *const _ == y as *const _ || self.user() == y.user()
    }

    pub fn canonical_equal(&self, y: &Self) -> bool {
        self as *const _ == y as *const _ || self.canonical() == y.canonical()
    }

    pub fn eq_mind_chk(&self, y: &Self) -> bool {
        self.user_equal(y)
    }
}

impl Cst {
    pub fn eq_con_chk(&self, y: &Self) -> bool {
        self.user_equal(y)
    }
}

impl Ind {
    pub fn eq_ind_chk(&self, y: &Self) -> bool {
        self.pos == y.pos && self.name.eq_mind_chk(&y.name)
    }
}

impl Proj {
    pub fn equal(&self, y: &Self) -> bool {
        self.0.canonical_equal(&y.0) && self.1 == y.1
    }
}

pub type MpMap<T> = HashMap<Mp, T>;

pub type KnMap<T> = HashMap<Kn, T>;

/// Note: this should be MutInd.UserOrd
pub type MindMapEnv<'b, T> = HashMap<&'b MutInd, T>;

/// Note: this should be Constant.UserOrd
pub type CMapEnv<T> = HashMap<Cst, T>;
