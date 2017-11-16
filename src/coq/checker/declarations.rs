use ocaml::de::{
    ORef,
};
use ocaml::values::{
    Constr,
    Mp,
    MpResolver,
    Substituted,
    UId,
};
use std::collections::{HashMap};

struct UMap<'b>(HashMap<Mp, &'b MpResolver>, HashMap<&'b UId, &'b MpResolver>);

impl<'b> UMap<'b> {
    pub fn mps<'c>(&mut self, _c: &'c mut ORef<Constr>) -> Constr {
        unimplemented!("mp substitution not yet implemented")
    }
}

impl<T> Substituted<ORef<T>> {
    fn force<'b, F>(&mut self, _fsubst: F)
        where F: for<'c> FnOnce(&mut UMap<'b>, &'c mut ORef<T>) -> T,
              T: Clone,
    {
        let Substituted { ref mut subst, value: ref mut _value } = *self;
        if subst.len() != 0 {
            unimplemented!("Module substitutions are yet implemented")
        }
    }
}

impl Substituted<ORef<Constr>> {
    pub fn force_constr(&mut self) {
        self.force(UMap::mps)
    }
}
