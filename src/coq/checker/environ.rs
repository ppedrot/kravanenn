use ocaml::values::{
    // Cb,
    // Engagement,
    IndPack,
    // Kn,
    // ModType,
    // Module,
    // Rctxt,
    // VoDigest,
};
/* use coq::checker::univ::{
    Universes,
}; */
use coq::kernel::names::{
    // CMapEnv,
    // KnMap,
    MindMapEnv,
    // MpMap,
    MutInd,
};

/// Environments

pub struct Globals<'b> {
    // constants: CMapEnv<Cb>,
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

impl<'b> Env<'b> {
    pub fn lookup_mind(&self, kn: &MutInd) -> Option<&'b IndPack> {
        self.globals.inductives.get(kn).map( |&v| v )
    }
}
