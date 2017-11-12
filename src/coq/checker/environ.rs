use ocaml::values::{
    Cb,
    Cst,
    // Engagement,
    IndPack,
    // Kn,
    // ModType,
    // Module,
    ProjBody,
    // Rctxt,
    // VoDigest,
};
/* use coq::checker::univ::{
    Universes,
}; */
use coq::kernel::names::{
    CMapEnv,
    // KnMap,
    MindMapEnv,
    // MpMap,
    MutInd,
};

/// Environments

pub struct Globals<'b> {
    constants: CMapEnv<&'b Cb>,
    inductives: MindMapEnv<'b, &'b IndPack>,
    // inductives_eq: KnMap<Kn>,
    // modules: MpMap<Module>,
    // modtypes: MpMap<ModType>,
}

pub struct Stratification {
    // universes: Universes,
    // enga: Engagement,
}

pub struct Env<'b> {
    globals: Globals<'b>,
    // rel_context: Rctxt,
    // stratification: Stratification,
    // imports: MpMap<VoDigest>,
}

/* const EMPTY_ENV : Env = {
    env_globals: Globals {
        constants:
        inductives:

    }
} */

pub enum EnvError {
    Anomaly(String),
}

pub type EnvResult<T> = Result<T, EnvError>;

impl<'b> Env<'b> {
    /// Constants

    /// Global constants
    pub fn lookup_constant(&self, c: &Cst) -> Option<&'b Cb> {
        self.globals.constants.get(c).map( |&c| c)
    }

    pub fn lookup_projection(&self, p: &Cst) -> Option<EnvResult<&'b ProjBody>> {
        // NOTE: Altered from OCaml implementation to not require p to be a Proj, since sometimes
        // we only have a constant (for instance, when checking a projection invented for eta
        // expansion of primitive records).
        self.lookup_constant(&p)
           .map( |p| p.proj.as_ref().ok_or_else( || {
               let e = "lookup_projection: constant is not a projection";
               EnvError::Anomaly(e.into())
           }))
    }

    /// Inductives

    pub fn lookup_mind(&self, kn: &MutInd) -> Option<&'b IndPack> {
        self.globals.inductives.get(kn).map( |&v| v )
    }
}
