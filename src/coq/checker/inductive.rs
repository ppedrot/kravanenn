use coq::checker::environ::{
    Env,
};
use coq::checker::reduction::{
    ConvResult,
};
use ocaml::values::{
    Constr,
    Ind,
    PUniverses,
};

/// Extracting an inductive type from a construction

impl Constr {
    /// This API is weird; it mutates self in place.  This is done in order to allow the argument
    /// vector returned by find_rectype to point inside of self.  We could avoid this in various
    /// ways (including not allocating a vector at all) but the best solutions probably look more
    /// like this, so we just bite the bullet.
    ///
    /// Returns None if this does not reduce to an application of an inductive type.
    ///
    /// self should be typechecked beforehand!
    pub fn find_rectype(&mut self, env: &mut Env) ->
        ConvResult<Option<(&PUniverses<Ind>, Vec<&Constr>)>>
    {
        // TODO: If everything applied to reverse-order arg lists, we could use a more efficient
        // method here and use an iterator instead of allocating a Vec.
        self.whd_all(env)?;
        let (t, l) = self.decompose_app();
        Ok(match *t {
            Constr::Ind(ref o) => Some((&**o, l)),
            _ => None
        })
    }
}
