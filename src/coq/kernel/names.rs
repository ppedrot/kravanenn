use std::collections::HashMap;

use ocaml::values::{
    Cst,
    Kn,
    Mp,
};

pub type MutInd = Cst;

pub type MpMap<T> = HashMap<Mp, T>;

pub type KnMap<T> = HashMap<Kn, T>;

/// Note: this should be MutInd.UserOrd
pub type MindMapEnv<'b, T> = HashMap<&'b MutInd, T>;

/// Note: this should be Constant.UserOrd
pub type CMapEnv<T> = HashMap<Cst, T>;
