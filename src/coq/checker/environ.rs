/* use coq::checker::univ::{
    Universes,
}; */
use coq::kernel::names::{
    CMapEnv,
    KnMap,
    MindMapEnv,
    // MpMap,
    MutInd,
};
use ocaml::values::{
    Cb,
    Constr,
    Cst,
    CstDef,
    // Engagement,
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
use take_mut;


/// Used to represent a computation that is only ever applied once.
///
/// This is useful because it lets us remember whether we've checked that a constant was already
/// evaluated in a way that Rust's type system understands, therefore letting us share the lazily
/// initialized version freely at lifetime 'a, without making us use separate maps or something
/// for the immutable and mutable versions, or requiring us to modify the structures used by OCaml.
/// The only negative is that it could be a bit wasteful of space (since this doesn't fit in a word
/// according to Rust, and we probably can't make it use pointer tagging without unsafe code).  We
/// can fix that later if we must, though.
///
/// (A way to potentially make this nicer would be to use Serde to allow us to put this enum
/// directly on the CstrDef, rather than making us freeze the entire Cb, which we don't need).
enum LazyRef<'a, T> where T: 'a {
    Owned(&'a mut T),
    Borrowed(&'a T),
}

/// Environments

#[derive(Default)]
pub struct Globals<'g> {
    /// Invariant: always LazyRef::Owned until constant_value is called for the first time.
    /// (never inserted as LazyRef::Borrowed)
    constants: CMapEnv<LazyRef<'g, Cb>>,
    inductives: MindMapEnv<'g, &'g IndPack>,
    inductives_eq: KnMap<Kn>,
    // modules: MpMap<Module>,
    // modtypes: MpMap<ModType>,
}

pub struct Stratification {
    // universes: Universes,
    // enga: Engagement,
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
    // stratification: Stratification,
    // imports: MpMap<VoDigest>,
}

#[derive(Debug,Copy,Clone)]
pub enum ConstEvaluationResult {
    NoBody,
    Opaque,
}

pub enum EnvError {
    Anomaly(String),
    NotEvaluableConst(ConstEvaluationResult),
}

pub type EnvResult<T> = Result<T, EnvError>;

impl<'a, T> AsRef<T> for LazyRef<'a, T> {
    fn as_ref(&self) -> &T {
        match *self {
            LazyRef::Owned(ref v) => &**v,
            LazyRef::Borrowed(ref v) => &**v,
        }
    }
}

impl<'g> Globals<'g> where {
    /// Constants

    /// Global constants
    pub fn lookup_constant(&self, c: &Cst) -> Option<&Cb> {
        self.constants.get(c).map( |c| c.as_ref() )
    }

    fn lookup_constant_mut(&mut self, c: &Cst) -> Option<&mut LazyRef<'g, Cb>> {
        self.constants.get_mut(c)
    }

    pub fn constant_value(&mut self, o: &PUniverses<Cst>) ->
        Option<Result<&'g Constr, ConstEvaluationResult>>
    {
        let PUniverses(ref kn, ref _u) = *o;
        self.lookup_constant_mut(kn)
            .and_then( |rf| {
                // NB: I think there's a way to solve this problem without using take_mut (or
                // RefCell, which we are trying to avoid altogether), but it would be worse in
                // most ways except that it doesn't abort on panic, which I don't care about
                // The method involves storing a dummy &'g Cb in the Env structure and would
                // probably result in a somewhat annoying interface (more importantly, it would
                // still probably result in incorrect results if a panic was caught while the
                // HashMap was still alive, though if people are actually paying attention to
                // UnwindSafe, this should not be a problem).
                // Gory details available on request.
                let mut b = None;
                take_mut::take(rf, |rf|
                    LazyRef::Borrowed(match rf {
                        LazyRef::Owned(cb) => {
                            if let CstDef::Def(ref mut l_body) = cb.body {
                                l_body.force_constr();
                                if cb.polymorphic {
                                    unimplemented!("Universe substitution not yet implemented")
                                    // u.subst(l_body.force());
                                }
                            };
                            // Shouldn't have to do this as two match statement, but do in order to
                            // satisfy the borrow checker.
                            b = Some(match cb.body {
                                CstDef::Def(ref l_body) => {
                                    Ok(&*l_body.value)
                                },
                                CstDef::OpaqueDef(_) =>
                                    Err(ConstEvaluationResult::NoBody),
                                CstDef::Undef(_) =>
                                    Err(ConstEvaluationResult::Opaque),
                            });
                            &*cb
                        },
                        LazyRef::Borrowed(cb) => {
                            b = Some(match cb.body {
                                CstDef::Def(ref l_body) => {
                                    // By our invariant, if we are Borrowed l_body was already
                                    // forced, so we know we can just take the value.
                                    Ok(&*l_body.value)
                                },
                                CstDef::OpaqueDef(_) =>
                                    Err(ConstEvaluationResult::NoBody),
                                CstDef::Undef(_) =>
                                    Err(ConstEvaluationResult::Opaque),
                            });
                            &*cb
                        }
                    })
                );
                b
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
        self.inductives_eq.get(kn).unwrap_or(kn)
    }

    pub fn mind_equiv(&self, ind1: &Ind, ind2: &Ind) -> bool {
        ind1.pos == ind2.pos &&
        self.scrape_mind(ind1.name.user()) == self.scrape_mind(ind2.name.user())
    }

    pub fn lookup_mind(&self, kn: &MutInd) -> Option<&'g IndPack>
    {
        self.inductives.get(kn).map( |&v| v )
    }
}
