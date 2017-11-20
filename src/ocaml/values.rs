use ocaml::de::{Array, ORef, Seed, Str};
use serde;
use std::collections::{HashMap};
use std::hash::Hash;

pub type Fail = !;

#[derive(Debug, Clone, DeserializeState, Hash, PartialEq, Eq)]
#[serde(deserialize_state = "Seed<'de>")]
#[serde(bound(deserialize = "T: serde::de::DeserializeState<'de, Seed<'de>> + 'static"))]
pub enum List<T> {
    Nil,
    Cons(#[serde(deserialize_state)] ORef<(T, List<T>)>),
}

#[derive(Debug, Clone, DeserializeState, Hash, PartialEq, Eq)]
#[serde(deserialize_state = "Seed<'de>")]
#[serde(bound(deserialize = "T: serde::de::DeserializeState<'de, Seed<'de>> + 'static"))]
/// A version of List that uses ownership rather than Rc.  It isn't totally clear that we actually
/// *don't* have sharing in the case we're using it, but hopefully we don't, since that gives us
/// mutable access to things in the list without runtime borrow checking (which will turn out to
/// be useful in some cases).
///
/// TODO: Probably make this just turn into a Vec instead of using the default derivation, as we
/// know there's no sharing.
pub enum OList<T> {
    Nil,
    Cons(#[serde(deserialize_state)] Box<(T, OList<T>)>),
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct OVec<T>(pub Vec<T>);

pub type Opt<T> = Option<T>;

/* Ocaml standard library */

pub type Bool = bool;

pub type Int = i64;

#[derive(Debug, Clone, DeserializeState)]
#[serde(de_parameters = "S")]
#[serde(deserialize_state = "S")]
#[serde(bound(deserialize = "T: serde::de::DeserializeState<'de, S>"))]
pub struct Ref<T>(#[serde(deserialize_state)] T);

#[derive(Debug, Clone, DeserializeState, Hash, PartialEq, Eq)]
#[serde(deserialize_state = "Seed<'de>")]
pub struct Any;

#[derive(Debug, Clone, DeserializeState)]
#[serde(deserialize_state = "Seed<'de>")]
pub struct Dyn;

#[derive(Debug, Clone, DeserializeState)]
#[serde(deserialize_state = "Seed<'de>")]
#[serde(bound(deserialize = "V: serde::de::DeserializeState<'de, Seed<'de>> + 'static"))]
pub enum Set<V> {
    Nil,
    Node(#[serde(deserialize_state)] ORef<(Set<V>, V, Set<V>, Int)>),
}

#[derive(DeserializeState,Debug,Clone)]
#[serde(deserialize_state = "Seed<'de>")]
#[serde(bound(deserialize = "K: serde::de::DeserializeState<'de, Seed<'de>> + 'static, V: serde::de::DeserializeState<'de, Seed<'de>> + 'static"))]
pub enum CMap<K, V> {
    Nil,
    Node(#[serde(deserialize_state)] ORef<(CMap<K, V>, K, V, CMap<K, V>, Int)>),
}

#[derive(Debug,Clone)]
pub struct Map<K, V>(pub HashMap<K, V>) where K: Hash + Eq;

pub type HSet<V> = CMap<Int, Set<V>>;

#[derive(Debug, Clone, DeserializeState, Eq, PartialEq)]
#[serde(deserialize_state = "Seed<'de>")]
#[serde(bound(deserialize = "T: serde::de::DeserializeState<'de, Seed<'de>> + 'static"))]
/// FIXME: Make equality check the hash first?  Rust might already do this.
pub enum HList<T> {
    Nil,
    Cons(#[serde(deserialize_state)] ORef<(T, Int, HList<T>)>),
}

pub type HMap<K, V> = CMap<Int, CMap<K, V>>;

/* lib/future */

#[allow(unreachable_code)] // Allowed because of Fail
#[allow(unreachable_patterns)] // Allowed because of Fail
#[derive(DeserializeState,Debug,Clone)]
#[serde(de_parameters = "S")]
#[serde(deserialize_state = "S")]
#[serde(bound(deserialize = "F: serde::de::DeserializeState<'de, S>, !: serde::de::DeserializeState<'de, S>"))]
pub enum FutureComput<F> {
    Done(#[serde(deserialize_state)] F),
    Ongoing(#[serde(deserialize_state)] Fail),
}

pub type Computation<F> = Ref<FutureComput<F>>;

/* kernel/names */

pub type Id = Str;

pub type Dp = List<Id>;

#[derive(Debug, Clone, DeserializeState)]
#[serde(de_parameters = "S")]
#[serde(deserialize_state = "S")]
#[serde(bound(deserialize = "Str: serde::de::DeserializeState<'de, S>"))]
pub enum Name {
    Anonymous, // anonymous identifier
    Name(#[serde(deserialize_state)] Id), // non-anonymous identifier
}

#[derive(Debug, Clone, DeserializeState, Hash, PartialEq, Eq)]
#[serde(deserialize_state = "Seed<'de>")]
pub struct UId(Int, #[serde(deserialize_state)] Str, #[serde(deserialize_state)] Dp);

#[derive(Debug, Clone, DeserializeState, Hash, PartialEq, Eq)]
#[serde(deserialize_state = "Seed<'de>")]
pub enum Mp {
    Dot(#[serde(deserialize_state)] ORef<Mp>, #[serde(deserialize_state)] Id),
    Bound(#[serde(deserialize_state)] UId),
    File(#[serde(deserialize_state)] Dp),
}

#[derive(Debug, Clone, DeserializeState)]
// FIXME: Use OCaml's nice refhash caching.
#[derive(Hash, PartialEq, Eq)]
#[serde(deserialize_state = "Seed<'de>")]
pub struct Kn {
    #[serde(deserialize_state)] canary: Any,
    #[serde(deserialize_state)] modpath: Mp,
    #[serde(deserialize_state)] dirpath: Dp,
    #[serde(deserialize_state)] knlabel: Id,
    refhash: Int,
}

#[derive(Debug, Clone, DeserializeState, Hash, Eq)]
#[serde(deserialize_state = "Seed<'de>")]
pub enum Cst {
    Dual(#[serde(deserialize_state)] ORef<(Kn, Kn)>), // user then canonical
    Same(#[serde(deserialize_state)] Kn), // user = canonical
}

#[derive(Debug, Clone, DeserializeState)]
#[serde(deserialize_state = "Seed<'de>")]
pub struct Ind {
    /// the name of the inductive type
    #[serde(deserialize_state)] pub name: Cst,
    /// The position of the inductive type within the block of mutually-recursive types.
    /// Beware: indexing starts from 0.
    pub pos: Int,
}

/// Designation of a (particular) constructor of a (particular) inductive type.
#[derive(Debug, Clone, DeserializeState)]
#[serde(deserialize_state = "Seed<'de>")]
pub struct Cons {
    /// designates the inductive type
    #[serde(deserialize_state)] pub ind: Ind,
    /// The index of the constructor.  Beware: indexing starts from 1.
    pub idx: Int,
}

/* kernel/univ */

#[derive(Debug, Clone, DeserializeState, Hash, Eq, PartialEq)]
#[serde(deserialize_state = "Seed<'de>")]
pub enum RawLevel {
    Prop,
    Set,
    Var(Int),
    Level(Int, #[serde(deserialize_state)] ORef<Dp>),
}

#[derive(Debug, Clone,DeserializeState, Hash, Eq, PartialEq)]
#[serde(deserialize_state = "Seed<'de>")]
pub struct Level {
    pub hash: Int,
    #[serde(deserialize_state)] pub data: RawLevel,
}

#[derive(Debug, Clone, DeserializeState, Eq, PartialEq)]
#[serde(deserialize_state = "Seed<'de>")]
pub struct Expr(#[serde(deserialize_state)] pub Level, pub Int);

pub type Univ = HList<Expr>;

#[derive(Debug, Clone, DeserializeState)]
#[serde(deserialize_state = "Seed<'de>")]
enum ConstraintType {
    Lt,
    Le,
    Eq,
}

#[derive(Debug, Clone, DeserializeState)]
#[serde(deserialize_state = "Seed<'de>")]
pub struct UnivConstraint(#[serde(deserialize_state)] Level, #[serde(deserialize_state)] ConstraintType, #[serde(deserialize_state)] Level);

pub type Cstrs = Set<UnivConstraint>;

pub type Instance = Array<Level>;

#[derive(Debug, Clone, DeserializeState)]
#[serde(deserialize_state = "Seed<'de>")]
pub struct Context(#[serde(deserialize_state)] Instance, #[serde(deserialize_state)] Cstrs);

pub type AbsContext = Context;

// static ABS_CUM_INFO : ValueS = TUPLE!("cumulativity_info", ABS_CONTEXT, CONTEXT);

pub type LevelSet = HSet<Level>;
#[derive(Debug, Clone,DeserializeState)]
#[serde(deserialize_state = "Seed<'de>")]
pub struct ContextSet(#[serde(deserialize_state)] LevelSet, #[serde(deserialize_state)] Cstrs);

/* kernel/term */
#[derive(Clone, Copy, Debug, DeserializeState, Eq, PartialEq)]
#[serde(deserialize_state = "Seed<'de>")]
pub enum SortContents {
    Pos,
    Null,
}

#[derive(Debug, Clone,DeserializeState)]
#[serde(deserialize_state = "Seed<'de>")]
pub enum Sort {
    Type(#[serde(deserialize_state)] ORef<Univ>),
    Prop(#[serde(deserialize_state)] SortContents),
}

#[derive(Debug, Clone,DeserializeState)]
#[serde(deserialize_state = "Seed<'de>")]
pub enum SortFam {
    InProp,
    InSet,
    InType,
}

#[derive(Debug, Clone,DeserializeState, Hash, Eq, PartialEq)]
#[serde(deserialize_state = "Seed<'de>")]
#[serde(bound(deserialize = "T: serde::de::DeserializeState<'de, Seed<'de>>"))]
pub struct PUniverses<T>(#[serde(deserialize_state)] pub T, #[serde(deserialize_state)] pub Instance);

pub type BoolList = List<Bool>;

#[derive(DeserializeState, Debug,Clone)]
#[serde(deserialize_state = "Seed<'de>")]
pub enum CStyle {
    Let,
    If,
    LetPattern,
    Match,
    Regular, // infer printing form from number of constructor
}

#[derive(DeserializeState, Debug,Clone)]
#[serde(deserialize_state = "Seed<'de>")]
pub struct CPrint {
    #[serde(deserialize_state)] ind_tags: BoolList,
    #[serde(deserialize_state)] cstr_tags: Array<BoolList>,
    #[serde(deserialize_state)] style: CStyle,
}

#[derive(DeserializeState, Debug,Clone)]
#[serde(deserialize_state = "Seed<'de>")]
pub struct CaseInfo {
    #[serde(deserialize_state)] pub ind: Ind,
    pub npar: Int,
    #[serde(deserialize_state)] cstr_ndecls: Array<Int>,
    #[serde(deserialize_state)] cstr_nargs: Array<Int>,
    #[serde(deserialize_state)] cstr_pp_info: CPrint, // not interpreted by the kernel
}

#[derive(DeserializeState,Debug,Clone,Copy)]
#[serde(deserialize_state = "Seed<'de>")]
pub enum Cast {
    VMCast,
    NATIVECast,
    DEFAULTCast,
    RevertCast, // FIXME: Figure out why this is apparently appearing in the file?
}

#[derive(DeserializeState,Debug,Clone)]
#[serde(deserialize_state = "Seed<'de>")]
pub struct Proj(#[serde(deserialize_state)] pub Cst, pub Bool);

#[allow(unreachable_code)] // Allowed because of Fail
#[allow(unreachable_patterns)] // Allowed because of Fail
#[derive(DeserializeState,Debug,Clone)]
#[serde(deserialize_state = "Seed<'de>")]
pub enum Constr {
    Proj(#[serde(deserialize_state)] ORef<(Proj, Constr)>),
    CoFix(#[serde(deserialize_state)] ORef<CoFix>),
    Fix(#[serde(deserialize_state)] ORef<Fix>),
    Case(#[serde(deserialize_state)] ORef<(CaseInfo, Constr, Constr, Array<Constr>)>),
    Construct(#[serde(deserialize_state)] ORef<PUniverses<Cons>>),
    Ind(#[serde(deserialize_state)] ORef<PUniverses<Ind>>),
    Const(#[serde(deserialize_state)] ORef<PUniverses<Cst>>),
    App(#[serde(deserialize_state)] ORef<(Constr, Array<Constr>)>),
    LetIn(#[serde(deserialize_state)] ORef<(Name, Constr, Constr, Constr)>),
    Lambda(#[serde(deserialize_state)] ORef<(Name, Constr, Constr)>),
    Prod(#[serde(deserialize_state)] ORef<(Name, Constr, Constr)>),
    Cast(#[serde(deserialize_state)] ORef<(Constr, Cast, Constr)>),
    Sort(#[serde(deserialize_state)] ORef<Sort>),
    Evar(#[serde(deserialize_state)] Fail),
    Meta(#[serde(deserialize_state)] Fail),
    Var(#[serde(deserialize_state)] Fail),
    Rel(Int),
}

#[derive(DeserializeState, Debug, Clone)]
#[serde(deserialize_state = "Seed<'de>")]
pub struct PRec(#[serde(deserialize_state)] pub Array<Name>, #[serde(deserialize_state)] pub Array<Constr>, #[serde(deserialize_state)] pub Array<Constr>);

#[derive(DeserializeState, Debug, Clone)]
#[serde(deserialize_state = "Seed<'de>")]
pub struct Fix2(#[serde(deserialize_state)] pub Array<Int>, pub Int);

#[derive(DeserializeState, Debug, Clone)]
#[serde(deserialize_state = "Seed<'de>")]
pub struct Fix(#[serde(deserialize_state)] pub Fix2, #[serde(deserialize_state)] pub PRec);

#[derive(DeserializeState,Debug, Clone)]
#[serde(deserialize_state = "Seed<'de>")]
pub struct CoFix(pub Int, #[serde(deserialize_state)] pub PRec);

#[derive(Debug, Clone, DeserializeState)]
#[serde(deserialize_state = "Seed<'de>")]
pub enum RDecl {
    LocalDef(#[serde(deserialize_state)] Name, #[serde(deserialize_state)] Constr, #[serde(deserialize_state)] ORef<Constr>),
    LocalAssum(#[serde(deserialize_state)] Name, #[serde(deserialize_state)] Constr),
}

pub type Rctxt = List<RDecl>;

#[derive(Debug, Clone, DeserializeState)]
#[serde(de_parameters = "S")]
#[serde(deserialize_state = "S")]
pub enum SectionCtxt {
    Nil,
}

/* kernel/mod_subst */

#[derive(Debug, Clone, DeserializeState)]
#[serde(deserialize_state = "Seed<'de>")]
pub enum DeltaHint {
    Equiv(#[serde(deserialize_state)] Kn),
    Inline(Int, #[serde(deserialize_state)] ORef<Opt<Constr>>),
}

#[derive(Debug, Clone, DeserializeState)]
#[serde(deserialize_state = "Seed<'de>")]
pub struct Resolver(#[serde(deserialize_state)] CMap<Mp, Mp>, #[serde(deserialize_state)] HMap<Kn, DeltaHint>);

#[derive(Debug, Clone, DeserializeState)]
#[serde(deserialize_state = "Seed<'de>")]
pub struct MpResolver(#[serde(deserialize_state)] Mp, #[serde(deserialize_state)] Resolver);

#[derive(Debug, Clone, DeserializeState)]
#[serde(deserialize_state = "Seed<'de>")]
pub struct Subst(#[serde(deserialize_state)] pub CMap<Mp, MpResolver>, #[serde(deserialize_state)] pub CMap<UId, MpResolver>);

/* kernel/lazyconstr */

#[derive(Debug, Clone, DeserializeState)]
#[serde(deserialize_state = "Seed<'de>")]
#[serde(bound(deserialize = "T: serde::de::DeserializeState<'de, Seed<'de>>"))]
pub struct Substituted<T> {
    /// NB: Value and subst are lazily initialized, and therefore may be modified mutably!  This
    /// turns out to be fine as long as we are careful about how we do it; for now, we assume that
    /// we'll always be able to access the substitution mutably when we want to modify it.
    #[serde(deserialize_state)] pub value: T,
    /// TODO: Verify there isn't significant sharing here.  Currently it seems like there usually
    /// shouldn't be; the majority of the time, there should probably not be any substitutions here
    /// at all.  If there are any, it seems like this may be a substitution generated during
    /// typechecking--one which usually needs to be mutated later anyway--so it's probably okay to
    /// copy it in that case.
    #[serde(deserialize_state)] pub subst: OVec<Subst>,
}

/// We add an ORef here because it seems likely that the Constrs themselves are potentially shared.
pub type CstrSubst = Substituted<ORef<Constr>>;

// NB: Second constructor [Direct] isn't supposed to appear in a .vo
#[derive(Debug, Clone, DeserializeState)]
#[serde(deserialize_state = "Seed<'de>")]
pub enum LazyConstr {
    // Direct(CstrSubst),
    Indirect(#[serde(deserialize_state)] List<Subst>, #[serde(deserialize_state)] Dp, Int),
}

/* kernel/declarations */

// static IMPREDICATIVE_SET : ValueS = ENUM!("impr-set", 2);
#[derive(Debug, Clone, DeserializeState)]
#[serde(deserialize_state = "Seed<'de>")]
pub enum Engagement {
    ImpredicativeSet,
    PredicativeSet,
}

#[derive(Debug, Clone, DeserializeState)]
#[serde(deserialize_state = "Seed<'de>")]
pub struct PolArity {
    #[serde(deserialize_state)] param_levels: List<Opt<Level>>,
    #[serde(deserialize_state)] level: Univ,
}

#[derive(Debug, Clone, DeserializeState)]
#[serde(deserialize_state = "Seed<'de>")]
pub enum CstType {
    TemplateArity(#[serde(deserialize_state)] ORef<(Rctxt, PolArity)>),
    RegularArity(#[serde(deserialize_state)] Constr),
}

#[derive(Debug, Clone, DeserializeState)]
#[serde(deserialize_state = "Seed<'de>")]
pub enum CstDef {
    OpaqueDef(#[serde(deserialize_state)] ORef<LazyConstr>),
    /// NB: From analyzing the OCaml, this isn't (shouldn't be?) actually shared by any operation
    /// Coq performs, at least not for anything in the .vo (specifically: anything that assigns
    /// a CstDef::Def to a Cb body always appears to create a unique CstrSubst).  So we hopefully
    /// don't lose anything by using direct ownership here (the reason we want this is because
    /// we'd like to mutate CstrSubst later, and it becomes inconvenient if it's inside an Rc
    /// since we seemingly would need runtime borrow checking to make it work).
    Def(#[serde(deserialize_state)] Box<CstrSubst>),
    Undef(Opt<Int>),
}

#[derive(Debug, Clone, DeserializeState)]
#[serde(deserialize_state = "Seed<'de>")]
pub struct ProjEta(#[serde(deserialize_state)] Constr, #[serde(deserialize_state)] Constr);

#[derive(Debug, Clone, DeserializeState)]
#[serde(deserialize_state = "Seed<'de>")]
pub struct ProjBody {
    #[serde(deserialize_state)] ind: Cst,
    pub npars: Int,
    pub arg: Int,
    #[serde(deserialize_state)] ty: Constr,
    #[serde(deserialize_state)] eta: ProjEta,
    #[serde(deserialize_state)] body: Constr,
}

#[derive(Debug, Clone, DeserializeState)]
#[serde(deserialize_state = "Seed<'de>")]
pub struct TypingFlags {
    check_guarded: Bool,
    check_universes: Bool,
}

// static CONST_UNIVS : ValueS = SUM!("constant_universes", 0, [CONTEXT], [ABS_CONTEXT]);

#[derive(Debug, Clone, DeserializeState)]
#[serde(deserialize_state = "Seed<'de>")]
pub struct Cb {
    #[serde(deserialize_state)] hyps: SectionCtxt,
    /// Note that there may be some sharing of CstDefs (didn't check for all cases, only Def), but
    /// we sacrifice it to obtain the possibility of interior mutability without RefCell.
    #[serde(deserialize_state)] pub body: CstDef,
    #[serde(deserialize_state)] ty: CstType,
    #[serde(deserialize_state)] body_code: Any,
    pub polymorphic: Bool,
    #[serde(deserialize_state)] universes: Context,
    #[serde(deserialize_state)] pub proj: Opt<ProjBody>,
    inline_code: Bool,
    #[serde(deserialize_state)] typing_flags: TypingFlags,
}

#[derive(Debug, Clone, DeserializeState)]
#[serde(deserialize_state = "Seed<'de>")]
pub enum RecArg {
    Norec,
    Imbr(#[serde(deserialize_state)] ORef<Ind>),
    Mrec(#[serde(deserialize_state)] ORef<Ind>),
}

#[derive(Debug, Clone, DeserializeState)]
#[serde(deserialize_state = "Seed<'de>")]
pub enum Wfp {
    Rec(Int, #[serde(deserialize_state)] Array<Wfp>),
    Node(#[serde(deserialize_state)] RecArg, #[serde(deserialize_state)] Array<Wfp>),
    Param(Int, Int),
}

#[derive(Debug, Clone, DeserializeState)]
#[serde(deserialize_state = "Seed<'de>")]
pub struct MonoIndArity {
    #[serde(deserialize_state)] user_arity: Constr,
    #[serde(deserialize_state)] sort: Sort,
}

#[derive(Debug, Clone, DeserializeState)]
#[serde(deserialize_state = "Seed<'de>")]
pub enum IndArity {
    TemplateArity(#[serde(deserialize_state)] PolArity),
    RegularArity(#[serde(deserialize_state)] MonoIndArity),
}

#[derive(Debug, Clone, DeserializeState)]
#[serde(deserialize_state = "Seed<'de>")]
pub struct OneInd {
    #[serde(deserialize_state)] typename: Id,
    #[serde(deserialize_state)] arity_ctxt: Rctxt,
    #[serde(deserialize_state)] arity: IndArity,
    #[serde(deserialize_state)] consnames: Array<Id>,
    #[serde(deserialize_state)] user_lc: Array<Constr>,
    nrealargs: Int,
    nrealdecls: Int,
    #[serde(deserialize_state)] kelim: List<SortFam>,
    #[serde(deserialize_state)] nf_lc: Array<Constr>,
    #[serde(deserialize_state)] consnrealargs: Array<Int>,
    #[serde(deserialize_state)] consnrealdecls: Array<Int>,
    #[serde(deserialize_state)] recargs: Wfp,
    nb_constant: Int,
    nb_args: Int,
    #[serde(deserialize_state)] reloc_tbl: Any,
}

#[derive(Debug, Clone, DeserializeState, PartialEq)]
#[serde(deserialize_state = "Seed<'de>")]
pub enum Finite {
    Finite,
    CoFinite,
    BiFinite,
}

#[derive(Debug, Clone, DeserializeState)]
#[serde(deserialize_state = "Seed<'de>")]
pub struct RecordBody(#[serde(deserialize_state)] pub Id, #[serde(deserialize_state)] pub Array<Cst>, #[serde(deserialize_state)] pub Array<ProjBody>);

pub type MindRecord = Opt<Opt<RecordBody>>;

/* static IND_PACK_UNIVS : ValueS = SUM!("abstract_inductive_universes", 0,
    [CONTEXT],
    [ABS_CONTEXT],
    [ABS_CUM_INFO]
); */

#[derive(Debug, Clone, DeserializeState)]
#[serde(deserialize_state = "Seed<'de>")]
pub struct IndPack {
    #[serde(deserialize_state)] packets: Array<OneInd>,
    #[serde(deserialize_state)] pub record: MindRecord,
    #[serde(deserialize_state)] pub finite: Finite,
    ntypes: Int,
    #[serde(deserialize_state)] hyps: SectionCtxt,
    pub nparams: Int,
    nparams_rec: Int,
    #[serde(deserialize_state)] params_ctxt: Rctxt,
    polymorphic: Bool,
    #[serde(deserialize_state)] universes: Context,
    private: Opt<Bool>,
    #[serde(deserialize_state)] typing_flags: TypingFlags,
}

#[derive(Debug, Clone, DeserializeState)]
#[serde(deserialize_state = "Seed<'de>")]
pub struct WithDef(#[serde(deserialize_state)] Constr, #[serde(deserialize_state)] Context);

#[derive(Debug, Clone, DeserializeState)]
#[serde(deserialize_state = "Seed<'de>")]
pub enum With {
    Def(#[serde(deserialize_state)] List<Id>, #[serde(deserialize_state)] WithDef),
    Mod(#[serde(deserialize_state)] List<Id>, #[serde(deserialize_state)] Mp),
}

#[derive(Debug, Clone, DeserializeState)]
#[serde(deserialize_state = "Seed<'de>")]
pub enum Mae {
    With(#[serde(deserialize_state)] ORef<Mae>, #[serde(deserialize_state)] With),
    Apply(#[serde(deserialize_state)] ORef<Mae>, #[serde(deserialize_state)] Mp),
    Ident(#[serde(deserialize_state)] Mp),
}

#[derive(Debug, Clone, DeserializeState)]
#[serde(deserialize_state = "Seed<'de>")]
pub enum Sfb {
    ModType(#[serde(deserialize_state)] ModType),
    Module(#[serde(deserialize_state)] Module),
    Mind(#[serde(deserialize_state)] IndPack),
    Const(#[serde(deserialize_state)] Cb),
}

#[derive(Debug, Clone, DeserializeState)]
#[serde(deserialize_state = "Seed<'de>")]
/// Note: not sure whether Sfb can be shared or not, but we need it mutable to be able to modify
/// Def in place.  TODO: Verify that there's not significant sharing here (there was an ORef
/// previously, but that may have been a [mistaken] attempt to reduce space usage of variants).
pub struct StructureBody(#[serde(deserialize_state)] Id, #[serde(deserialize_state)] Box<Sfb>);

/// TODO: Verify that there's not significant sharing of StructureBody, since we'd like to have
/// interior mutability here without runtime borrow checking, but we'd also like to not lose
/// too much sharing (if possible).
pub type Struc = OVec<StructureBody>;

#[derive(Debug, Clone, DeserializeState)]
#[serde(deserialize_state = "Seed<'de>")]
pub enum Sign {
    /// Note: not sure whether ModType or Sign can be shared or not, but we need them mutable to be
    /// able to modify Def in place.  TODO: Verify that there's not significant sharing here.
    MoreFunctor(#[serde(deserialize_state)] UId, #[serde(deserialize_state)] Box<ModType>, #[serde(deserialize_state)] Box<Sign>),
    NoFunctor(#[serde(deserialize_state)] Struc),
}

#[derive(Debug, Clone, DeserializeState)]
#[serde(deserialize_state = "Seed<'de>")]
pub enum MExpr {
    /// Note: not sure whether ModType or Sign can be shared or not, but we need them mutable to be
    /// able to modify Def in place.  TODO: Verify that there's not significant sharing here.
    MoreFunctor(#[serde(deserialize_state)] UId, #[serde(deserialize_state)] Box<ModType>, #[serde(deserialize_state)] Box<MExpr>),
    NoFunctor(#[serde(deserialize_state)] Mae),
}

#[derive(Debug, Clone, DeserializeState)]
#[serde(deserialize_state = "Seed<'de>")]
pub enum Impl {
    Abstract,
    FullStruct,
    Struct(#[serde(deserialize_state)] Sign),
    Algebraic(#[serde(deserialize_state)] MExpr),
}

#[derive(Debug, Clone, DeserializeState)]
#[serde(deserialize_state = "Seed<'de>")]
pub enum NoImpl {
    Abstract,
}

#[derive(Debug, Clone, DeserializeState)]
#[serde(deserialize_state = "Seed<'de>")]
pub struct Module {
    #[serde(deserialize_state)] mp: Mp,
    #[serde(deserialize_state)] expr: Impl,
    #[serde(deserialize_state)] ty: Sign,
    #[serde(deserialize_state)] type_alg: Opt<MExpr>,
    #[serde(deserialize_state)] constraints: ContextSet,
    #[serde(deserialize_state)] delta: Resolver,
    #[serde(deserialize_state)] retroknowledge: Any,
}

#[derive(Debug, Clone, DeserializeState)]
#[serde(deserialize_state = "Seed<'de>")]
pub struct ModType {
    #[serde(deserialize_state)] mp: Mp,
    #[serde(deserialize_state)] expr: NoImpl,
    #[serde(deserialize_state)] ty: Sign,
    #[serde(deserialize_state)] type_alg: Opt<MExpr>,
    #[serde(deserialize_state)] constraints: ContextSet,
    #[serde(deserialize_state)] delta: Resolver,
    #[serde(deserialize_state)] retroknowledge: Any,
}

/* kernel/safe_typing */

#[derive(Debug, Clone, DeserializeState)]
#[serde(deserialize_state = "Seed<'de>")]
pub enum VoDigest {
    Dviovo(#[serde(deserialize_state)] Str, #[serde(deserialize_state)] Str),
    Dvo(#[serde(deserialize_state)] Str),
}

#[derive(Debug, Clone, DeserializeState)]
#[serde(deserialize_state = "Seed<'de>")]
pub struct LibraryInfo(#[serde(deserialize_state)] Dp, #[serde(deserialize_state)] VoDigest);

pub type Deps = Array<LibraryInfo>;

#[derive(Debug, Clone, DeserializeState)]
#[serde(deserialize_state = "Seed<'de>")]
pub struct CompiledLib {
    #[serde(deserialize_state)] name: Dp,
    #[serde(deserialize_state)] module: Module,
    #[serde(deserialize_state)] deps: Deps,
    #[serde(deserialize_state)] enga: Engagement,
    #[serde(deserialize_state)] natsymbs: Any,
}

/* Library objects */

pub type Obj = Dyn;

#[derive(Debug, Clone, DeserializeState)]
#[serde(deserialize_state = "Seed<'de>")]
pub struct LibObj(#[serde(deserialize_state)] Id, #[serde(deserialize_state)] Obj);

pub type LibObjs = List<LibObj>;

#[derive(Debug, Clone, DeserializeState)]
#[serde(deserialize_state = "Seed<'de>")]
pub struct LibraryObjs {
    #[serde(deserialize_state)] compiled: LibObjs,
    #[serde(deserialize_state)] objects: LibObjs,
}

// STM objects

// static FROZEN : ValueS = TUPLE!("frozen", LIST!(PAIR!(INT, DYN)), OPT!(DYN));
//
// static STATES : ValueS = PAIR!(ANY, FROZEN);
//
// static STATE : ValueS = TUPLE!("state", STATES, ANY, BOOL);

/* static VCS : ValueS = {
    static DATA : ValueS = OPT!(ANY);
    static MP_MAP : ValueS = MAP!(MP_MAP, ANY, TUPLE!("state_info",
        ANY, ANY, OPT!(STATE), PAIR!(DATA, ANY))
    );
    //
    // module Make(OT : Map.OrderedType) = struct
    //
    // type id = OT.t
    //
    //
    //
    // Vcs.Make(Stateid.Self)
    //
    // module Branch : (module type of Vcs_.Branch with type t = Vcs_.Branch.t)
    // type id = Stateid.t
    // type 'branch_type branch_info = 'branch_type Vcs_.branch_info = {
    //   kind : [> `Master] as 'branch_type;
    //   root : id;
    //   pos  : id;
    // }
    //
    TUPLE!("vcs", ANY, ANY, TUPLE!("dag", ANY, ANY, MP_MAP)) // (branch_type, transaction, vcs_state_info, box) Vcs_.t
} */
/*

(** STM objects *)

let v_frozen = Tuple ("frozen", [|List (v_pair Int Dyn); Opt Dyn|])
let v_states = v_pair Any v_frozen
let v_state = Tuple ("state", [|v_states; Any; v_bool|])

let v_vcs =
  let data = Opt Any in
  let vcs =
    Tuple ("vcs",
      [|Any; Any;
        Tuple ("dag",
          [|Any; Any; v_map Any (Tuple ("state_info",
            [|Any; Any; Opt v_state; v_pair data Any|]))
          |])
      |])
  in
  let () = Obj.set_field (Obj.magic data) 0 (Obj.magic vcs) in
  vcs

let v_uuid = Any
let v_request id doc =
  Tuple ("request", [|Any; Any; doc; Any; id; String|])
let v_tasks = List (v_pair (v_request v_uuid v_vcs) v_bool)
let v_counters = Any
let v_stm_seg = v_pair v_tasks v_counters
*/

/* Toplevel structures in a vo (see Cic.mli) */

#[derive(Debug, Clone,DeserializeState)]
#[serde(deserialize_state = "Seed<'de>")]
pub struct LibSum {
    #[serde(deserialize_state)] name: Dp,
    #[serde(deserialize_state)] imports: Array<Dp>,
    #[serde(deserialize_state)] deps: Deps,
}

#[derive(Debug, Clone, DeserializeState)]
#[serde(deserialize_state = "Seed<'de>")]
pub struct Lib {
    #[serde(deserialize_state)] compiled: CompiledLib,
    #[serde(deserialize_state)] objects: LibraryObjs,
}

pub type Opaques = Array<Computation<Constr>>;

#[derive(Debug, Clone,DeserializeState)]
#[serde(deserialize_state = "Seed<'de>")]
pub struct UnivTable(#[serde(deserialize_state)] Array<Computation<ContextSet>>, #[serde(deserialize_state)] ContextSet, Bool);

pub type UnivOpaques = Opt<UnivTable>;

/*(** Registering dynamic values *)

module IntOrd =
struct
  type t = int
  let compare (x : t) (y : t) = compare x y
end

module IntMap = Map.Make(IntOrd)

let dyn_table : value IntMap.t ref = ref IntMap.empty

let register_dyn name t =
  dyn_table := IntMap.add name t !dyn_table

let find_dyn name =
  try IntMap.find name !dyn_table
  with Not_found -> Any*/

/// Some useful helper implementations

/// An iterator specialized to Lists.
pub struct ListIter<'a, T> where T: 'a {
    node: &'a List<T>
}

impl<'a, T> ListIter<'a, T> {
    fn new(node: &'a List<T>) -> Self {
        ListIter {
            node: node,
        }
    }
}

impl<'a, T> Iterator for ListIter<'a, T> {
    type Item = &'a T;

    // Note: if there were a cycle (which there shouldn't be) in the original List,
    // this could loop forever.  But if used as intended (from a DeserializeSeed), this is unlikely
    // to happen, since DeserializeSeed will already loop forever in that case...
    fn next(&mut self) -> Option<&'a T> {
        match *self.node {
            List::Cons(ref node) => {
                let (ref v, ref next) = **node;
                self.node = next;
                return Some(v);
            },
            List::Nil => None,
        }
    }
}

impl<T> List<T> {
    pub fn iter<'a>(&'a self) -> ListIter<'a, T> {
        ListIter::new(self)
    }
}

/// An iterator specialized to OLists.
pub struct OListIter<'a, T> where T: 'a {
    node: &'a OList<T>,
}

impl<'a, T> OListIter<'a, T> {
    fn new(node: &'a OList<T>) -> Self {
        OListIter {
            node: node,
        }
    }
}

impl<'a, T> Iterator for OListIter<'a, T> {
    type Item = &'a T;

    // Note: if there were a cycle (which there shouldn't be) in the original OList,
    // this could loop forever.  But if used as intended (from a DeserializeSeed), this is unlikely
    // to happen, since DeserializeSeed will already loop forever in that case...
    fn next(&mut self) -> Option<&'a T> {
        match *self.node {
            OList::Cons(ref node) => {
                let (ref v, ref next) = **node;
                self.node = next;
                return Some(v);
            },
            OList::Nil => None,
        }
    }
}

impl<T> OList<T> {
    pub fn iter<'a>(&'a self) -> OListIter<'a, T> {
        OListIter::new(self)
    }
}

/// An iterator specialized to HLists.
pub struct HListIter<'a, T> where T: 'a {
    node: &'a HList<T>
}

impl<'a, T> HListIter<'a, T> {
    fn new(node: &'a HList<T>) -> Self {
        HListIter {
            node: node,
        }
    }
}

impl<'a, T> Iterator for HListIter<'a, T> {
    type Item = &'a T;

    // Note: if there were a cycle (which there shouldn't be) in the original HList,
    // this could loop forever.  But if used as intended (from a DeserializeSeed), this is unlikely
    // to happen, since DeserializeSeed will already loop forever in that case...
    fn next(&mut self) -> Option<&'a T> {
        match *self.node {
            HList::Cons(ref node) => {
                let (ref v, _, ref next) = **node;
                self.node = next;
                return Some(v);
            },
            HList::Nil => None,
        }
    }
}

impl<T> HList<T> {
    pub fn iter<'a>(&'a self) -> HListIter<'a, T> {
        HListIter::new(self)
    }
}

/// Owned vectors.
impl<'de, T> serde::de::DeserializeState<'de, Seed<'de>> for OVec<T>
    where T: Clone + 'static,
          T: serde::de::DeserializeState<'de, Seed<'de>>,
{
    fn deserialize_state<'seed, D>(seed: &'seed mut Seed<'de>, deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::de::Deserializer<'de>,
    {
        // Lazy: we just deserialize the OList, then add everything to a Vec.
        let olist: OList<T> = OList::deserialize_state(seed, deserializer)?;
        Ok(OVec(olist.iter().map(T::clone).collect()))
    }
}

impl<T> ::std::ops::Deref for OVec<T> {
    type Target = Vec<T>;
    fn deref(&self) -> &Vec<T> {
        &self.0
    }
}

impl<T> ::std::ops::DerefMut for OVec<T> {
    fn deref_mut(&mut self) -> &mut Vec<T> {
        &mut self.0
    }
}
