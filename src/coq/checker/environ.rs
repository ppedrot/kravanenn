use coq::checker::univ::{
    Huniv,
    SubstError,
    Universes,
};
use coq::kernel::names::{
    CMapEnv,
    KnKey,
    KnMap,
    KnUser,
    MindMapEnv,
    // MpMap,
    MutInd,
};
use ocaml::values::{
    Cb,
    Constr,
    Cst,
    CstDef,
    Engagement,
    Ind,
    IndPack,
    Kn,
    // ModType,
    // Module,
    ProjBody,
    PUniverses,
    // Rctxt,
    RDecl,
    // VoDigest,
};
use std::borrow::Cow;

/// Environments

#[derive(Default)]
pub struct Globals<'g> {
    constants: CMapEnv<'g, &'g Cb>,
    inductives: MindMapEnv<'g, &'g IndPack>,
    inductives_eq: KnMap<'g, Kn>,
    /// Hash-consed universe table.
    univ_hcons_tbl: Huniv,
    // modules: MpMap<Module>,
    // modtypes: MpMap<ModType>,
}

pub struct Stratification {
    universes: Universes,
    enga: Engagement,
}

pub struct Env<'b, 'g> where 'g: 'b {
    /// Will let us easily keep the globals the same (without copying) while recreating the
    /// rel_context.  We want to divorce the rel_context lifetimes from the global lifetimes
    /// so we can drop the Env without unifying the lifetime of the globals with it.
    pub globals: &'b mut Globals<'g>,
    /// NOTE: We will probably make this something we clone somewhat regularly, since we often
    /// want to keep the rest of the Env the same but mutate the Rctxt.  So we might make this
    /// into a &'r mut Rctx<'b> or something.
    /// NOTE: We currently use Vec<RDecl> instead of RCtxt, just because it's somewhat easier
    /// to deal with.  We can always change it later.
    pub rel_context: &'b mut Vec<RDecl>,
    pub stratification: Stratification,
    // imports: MpMap<VoDigest>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ConstEvaluationResult {
    NoBody,
    Opaque,
    Subst(SubstError),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum EnvError {
    Anomaly(String),
    NotEvaluableConst(ConstEvaluationResult),
}

pub type EnvResult<T> = Result<T, EnvError>;

impl ::std::convert::From<SubstError> for ConstEvaluationResult {
    fn from(e: SubstError) -> Self {
        ConstEvaluationResult::Subst(e)
    }
}

impl<'g> Globals<'g> where {
    /// Constants

    /// Global constants
    pub fn lookup_constant(&self, c: &Cst) -> Option<&'g Cb> {
        self.constants.get(&KnUser(c)).map( |&cb| cb )
    }

    pub fn constant_value(&self, o: &PUniverses<Cst>) ->
        Option<Result<Cow<'g, Constr>, ConstEvaluationResult>>
    {
        let PUniverses(ref kn, ref u) = *o;
        self.lookup_constant(kn)
            .and_then( |cb| {
                Some(match cb.body {
                    CstDef::Def(ref l_body) => {
                        // l_body is lazily initialized, and this is the only place that tries to
                        // force it.
                        let b = l_body.get_or_create( |mut l_body| {
                            l_body.force_constr();
                            if cb.polymorphic {
                                // FIXME: Why do we do this twice?
                                l_body.force_constr();
                            }
                            l_body.value
                        });
                        if cb.polymorphic {
                            match b.subst_instance(u, &self.univ_hcons_tbl) {
                                Ok(b) => Ok(b),
                                Err(e) => Err(ConstEvaluationResult::Subst(e)),
                            }
                        } else {
                            Ok(Cow::Borrowed(&**b))
                        }
                    },
                    CstDef::OpaqueDef(_) =>
                        Err(ConstEvaluationResult::NoBody),
                    CstDef::Undef(_) =>
                        Err(ConstEvaluationResult::Opaque),
                })
            })
    }

    pub fn lookup_projection(&self, p: &Cst) -> Option<EnvResult<&ProjBody>> {
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

    /// Mutual Inductives
    fn scrape_mind<'a>(&'a self, kn: &'a Kn) -> &'a Kn {
        self.inductives_eq.get(&KnKey(kn)).unwrap_or(kn)
    }

    pub fn mind_equiv(&self, ind1: &Ind, ind2: &Ind) -> bool {
        ind1.pos == ind2.pos &&
        self.scrape_mind(ind1.name.user()).equal(self.scrape_mind(ind2.name.user()))
    }

    pub fn lookup_mind(&self, kn: &MutInd) -> Option<&'g IndPack>
    {
        self.inductives.get(&KnUser(kn)).map( |&v| v )
    }
}

impl Stratification {
    pub fn universes(&self) -> &Universes {
        &self.universes
    }

    pub fn engagement(&self) -> &Engagement {
        &self.enga
    }
}

impl<'b, 'g> Env<'b, 'g> {
    pub fn push_rel(&mut self, d: RDecl) {
        self.rel_context.push(d);
    }
}
