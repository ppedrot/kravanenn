use ocaml::marshal::{RawString};

pub type Fail = u8;

#[derive(Debug, Deserialize)]
pub enum List<T> {
    Nil,
    Cons(T, Box<List<T>>),
}

pub type Opt<T> = Option<T>;

/* Ocaml standard library */

pub type Bool = bool;

pub type Int = i64;

#[derive(Debug, Deserialize)]
pub struct Ref<T>(T);

pub type Str = RawString;//Box<[u8]>;

#[derive(Debug, Deserialize)]
pub struct Any;

#[derive(Debug, Deserialize)]
pub struct Dyn;

#[derive(Deserialize,Debug)]
pub enum Set<V> {
    Nil,
    Node(Box<Set<V>>, V, Box<Set<V>>, Int),
}

#[derive(Deserialize,Debug)]
pub enum Map<K, V> {
    Nil,
    Node(Box<Map<K, V>>, K, V, Box<Map<K,V>>, Int),
}

pub type HSet<V> = Map<Int, Set<V>>;

#[derive(Debug,Deserialize)]
pub enum HList<T> {
    Nil,
    Cons(T, Int, Box<HList<T>>),
}

pub type HMap<K, V> = Map<Int, Map<K, V>>;

/* lib/future */

#[derive(Deserialize,Debug)]
pub enum FutureComput<F> {
    Done(F),
    Ongoing(Fail),
}

pub type Computation<F> = Ref<FutureComput<F>>;

/* kernel/names */

pub type Id = Str;

pub type Dp = List<Id>;

#[derive(Debug, Deserialize)]
pub enum Name {
    Anonymous, // anonymous identifier
    Name(Id), // non-anonymous identifier
}

#[derive(Debug, Deserialize)]
pub struct UId(Int, Str, Dp);

#[derive(Debug, Deserialize)]
pub enum Mp {
    Dot(Box<Mp>, Id),
    Bound(UId),
    File(Dp),
}

#[derive(Debug, Deserialize)]
pub struct Kn {
    canary: Any,
    modpath: Mp,
    dirpath: Dp,
    knlabel: Id,
    refhash: Int,
}

#[derive(Debug, Deserialize)]
pub enum Cst {
    Dual(Kn, Kn), // user then canonical
    Same(Kn), // user = canonical
}

#[derive(Debug, Deserialize)]
pub struct Ind {
    /// the name of the inductive type
    name: Cst,
    /// The position of the inductive type within the block of mutually-recursive types.
    /// Beware: indexing starts from 0.
    pos: Int,
}

/// Designation of a (particular) constructor of a (particular) inductive type.
#[derive(Debug, Deserialize)]
pub struct Cons {
    /// designates the inductive type
    ind: Ind,
    /// The index of the constructor.  Beware: indexing starts from 1.
    idx: Int,
}

/* kernel/univ */

#[derive(Debug, Deserialize)]
pub enum RawLevel {
    Prop,
    Set,
    Var(Int),
    Level(Int, Dp),
}

#[derive(Debug,Deserialize)]
pub struct Level {
    hash: Int,
    data: RawLevel,
}

#[derive(Debug, Deserialize)]
pub struct Expr(Level, Int);

pub type Univ = HList<Expr>;

#[derive(Debug, Deserialize)]
enum ConstraintType {
    Lt,
    Le,
    Eq,
}

#[derive(Debug, Deserialize)]
pub struct UnivConstraint(Level, ConstraintType, Level);

pub type Cstrs = Set<UnivConstraint>;

pub type Instance = Vec<Level>;

#[derive(Debug, Deserialize)]
pub struct Context(Instance, Cstrs);

pub type AbsContext = Context;

// static ABS_CUM_INFO : ValueS = TUPLE!("cumulativity_info", ABS_CONTEXT, CONTEXT);

pub type LevelSet = HSet<Level>;
#[derive(Debug,Deserialize)]
pub struct ContextSet(LevelSet, Cstrs);

/* kernel/term */
#[derive(Debug,Deserialize)]
pub enum SortContents {
    Pos,
    Null,
}

#[derive(Debug,Deserialize)]
pub enum Sort {
    Type(Univ),
    Prop(SortContents),
}

#[derive(Debug,Deserialize)]
pub enum SortFam {
    InProp,
    InSet,
    InType,
}

#[derive(Debug,Deserialize)]
pub struct PUniverses<T>(T, Instance);

pub type BoolList = List<Bool>;

#[derive(Deserialize, Debug)]
pub enum CStyle {
    Let,
    If,
    LetPattern,
    Match,
    Regular, // infer printing form from number of constructor
}

#[derive(Deserialize, Debug)]
pub struct CPrint {
    ind_tags: BoolList,
    cstr_tags: Vec<BoolList>,
    style: CStyle,
}

#[derive(Deserialize, Debug)]
pub struct CaseInfo {
    ind: Ind,
    npar: Int,
    cstr_ndecls: Vec<Int>,
    cstr_nargs: Vec<Int>,
    cstr_pp_info: CPrint, // not interpreted by the kernel
}

#[derive(Deserialize,Debug)]
pub enum Cast {
    VMCast,
    NATIVECast,
    DEFAULTCast,
    RevertCast, // FIXME: Figure out why this is apparently appearing in the file?
}

#[derive(Deserialize,Debug)]
pub struct Proj(Cst, Bool);

#[derive(Deserialize,Debug)]
pub enum Constr {
    Proj(Proj, Box<Constr>),
    CoFix(CoFix),
    Fix(Fix),
    Case(CaseInfo, Box<Constr>, Box<Constr>, Vec<Constr>),
    Construct(PUniverses<Cons>),
    Ind(PUniverses<Ind>),
    Const(PUniverses<Cst>),
    App(Box<Constr>, Vec<Constr>),
    LetIn(Name, Box<Constr>, Box<Constr>, Box<Constr>),
    Lambda(Name, Box<Constr>, Box<Constr>),
    Prod(Name, Box<Constr>, Box<Constr>),
    Cast(Box<Constr>, Cast, Box<Constr>),
    Sort(Sort),
    Evar(Fail),
    Meta(Fail),
    Var(Fail),
    Rel(Int),
}

#[derive(Deserialize, Debug)]
pub struct PRec(Vec<Name>, Vec<Constr>, Vec<Constr>);

#[derive(Deserialize, Debug)]
pub struct Fix2(Vec<Int>, Int);

#[derive(Deserialize, Debug)]
pub struct Fix(Fix2, PRec);

#[derive(Deserialize,Debug)]
pub struct CoFix(Int, PRec);

#[derive(Debug, Deserialize)]
pub enum RDecl {
    LocalDef(Name, Constr, Constr),
    LocalAssum(Name, Constr),
}

pub type Rctxt = List<RDecl>;

#[derive(Debug, Deserialize)]
pub enum SectionCtxt {
    Nil,
}

/* kernel/mod_subst */

#[derive(Debug, Deserialize)]
pub enum DeltaHint {
    Equiv(Kn),
    Inline(Int, Opt<Constr>),
}

#[derive(Debug, Deserialize)]
pub struct Resolver(Map<Mp, Mp>, HMap<Kn, DeltaHint>);

#[derive(Debug, Deserialize)]
pub struct MpResolver(Mp, Resolver);

#[derive(Debug, Deserialize)]
pub struct Subst(Map<Mp, MpResolver>, Map<UId, MpResolver>);

/* kernel/lazyconstr */

#[derive(Debug, Deserialize)]
pub struct Substituted<T> {
    value: T,
    subst: List<Subst>,
}

pub type CstrSubst = Substituted<Constr>;

// NB: Second constructor [Direct] isn't supposed to appear in a .vo
#[derive(Debug, Deserialize)]
pub enum LazyConstr {
    // Direct(CstrSubst),
    Indirect(List<Subst>, Dp, Int),
}

/* kernel/declarations */

// static IMPREDICATIVE_SET : ValueS = ENUM!("impr-set", 2);
#[derive(Debug, Deserialize)]
pub enum Engagement {
    ImpredicativeSet,
    PredicativeSet,
}

#[derive(Debug, Deserialize)]
pub struct PolArity {
    param_levels: List<Opt<Level>>,
    level: Univ,
}

#[derive(Debug, Deserialize)]
pub enum CstType {
    TemplateArity((Rctxt, PolArity)),
    RegularArity(Constr),
}

#[derive(Debug, Deserialize)]
pub enum CstDef {
    OpaqueDef(LazyConstr),
    Def(CstrSubst),
    Undef(Opt<Int>),
}

#[derive(Debug, Deserialize)]
pub struct ProjEta(Constr, Constr);

#[derive(Debug, Deserialize)]
pub struct ProjBody {
    ind: Cst,
    npars: Int,
    arg: Int,
    ty: Constr,
    eta: ProjEta,
    body: Constr,
}

#[derive(Debug, Deserialize)]
pub struct TypingFlags {
    check_guarded: Bool,
    check_universes: Bool,
}

// static CONST_UNIVS : ValueS = SUM!("constant_universes", 0, [CONTEXT], [ABS_CONTEXT]);

#[derive(Debug, Deserialize)]
pub struct Cb {
    hyps: SectionCtxt,
    body: CstDef,
    ty: CstType,
    body_code: Any,
    polymorphic: Bool,
    universes: Context,
    proj: Opt<ProjBody>,
    inline_code: Bool,
    typing_flags: TypingFlags,
}

#[derive(Debug, Deserialize)]
pub enum RecArg {
    Norec,
    Imbr(Ind),
    Mrec(Ind),
}

#[derive(Debug, Deserialize)]
pub enum Wfp {
    Rec(Int, Vec<Wfp>),
    Node(RecArg, Vec<Wfp>),
    Param(Int, Int),
}

#[derive(Debug, Deserialize)]
pub struct MonoIndArity {
    user_arity: Constr,
    sort: Sort
}

#[derive(Debug, Deserialize)]
pub enum IndArity {
    TemplateArity(PolArity),
    RegularArity(MonoIndArity),
}

#[derive(Debug, Deserialize)]
pub struct OneInd {
    typename: Id,
    arity_ctxt: Rctxt,
    arity: IndArity,
    consnames: Vec<Id>,
    user_lc: Vec<Constr>,
    nrealargs: Int,
    nrealdecls: Int,
    kelim: List<SortFam>,
    nf_lc: Vec<Constr>,
    consnrealargs: Vec<Int>,
    consnrealdecls: Vec<Int>,
    recargs: Wfp,
    nb_constant: Int,
    nb_args: Int,
    reloc_tbl: Any,
}

#[derive(Debug, Deserialize)]
pub enum Finite {
    Finite,
    CoFinite,
    BiFinite,
}

#[derive(Debug, Deserialize)]
pub struct RecordBody(Id, Vec<Cst>, Vec<ProjBody>);

pub type MindRecord = Opt<Opt<RecordBody>>;

/* static IND_PACK_UNIVS : ValueS = SUM!("abstract_inductive_universes", 0,
    [CONTEXT],
    [ABS_CONTEXT],
    [ABS_CUM_INFO]
); */

#[derive(Debug, Deserialize)]
pub struct IndPack {
    packets: Vec<OneInd>,
    record: MindRecord,
    finite: Finite,
    ntypes: Int,
    hyps: SectionCtxt,
    nparams: Int,
    nparams_rec: Int,
    params_ctxt: Rctxt,
    polymorphic: Bool,
    universes: Context,
    private: Opt<Bool>,
    typing_flags: TypingFlags,
}

#[derive(Debug, Deserialize)]
pub struct WithDef(Constr, Context);

#[derive(Debug, Deserialize)]
pub enum With {
    Def(List<Id>, WithDef),
    Mod(List<Id>, Mp),
}

#[derive(Debug, Deserialize)]
pub enum Mae {
    With(Box<Mae>, With),
    Apply(Box<Mae>, Mp),
    Ident(Mp),
}

#[derive(Debug, Deserialize)]
pub enum Sfb {
    ModType(ModType),
    Module(Module),
    Mind(IndPack),
    Const(Cb),
}

#[derive(Debug, Deserialize)]
pub struct StructureBody(Id, Box<Sfb>);

pub type Struc = List<StructureBody>;

#[derive(Debug, Deserialize)]
pub enum Sign {
    MoreFunctor(UId, Box<ModType>, Box<Sign>),
    NoFunctor(Struc),
}

#[derive(Debug, Deserialize)]
pub enum MExpr {
    MoreFunctor(UId, Box<ModType>, Box<MExpr>),
    NoFunctor(Mae),
}

#[derive(Debug, Deserialize)]
pub enum Impl {
    Abstract,
    FullStruct,
    Struct(Sign),
    Algebraic(MExpr),
}

#[derive(Debug, Deserialize)]
pub enum NoImpl {
    Abstract,
}

#[derive(Debug, Deserialize)]
pub struct Module {
    mp: Mp,
    expr: Impl,
    ty: Sign,
    type_alg: Opt<MExpr>,
    constraints: ContextSet,
    delta: Resolver,
    retroknowledge: Any,
}

#[derive(Debug, Deserialize)]
pub struct ModType {
    mp: Mp,
    expr: NoImpl,
    ty: Sign,
    type_alg: Opt<MExpr>,
    constraints: ContextSet,
    delta: Resolver,
    retroknowledge: Any,
}

/* kernel/safe_typing */

#[derive(Debug, Deserialize)]
pub enum VoDigest {
    Dviovo(Str, Str),
    Dvo(Str),
}

#[derive(Debug, Deserialize)]
pub struct LibraryInfo(Dp, VoDigest);

pub type Deps = Vec<LibraryInfo>;

#[derive(Debug, Deserialize)]
pub struct CompiledLib {
    name: Dp,
    module: Module,
    deps: Deps,
    enga: Engagement,
    natsymbs: Any,
}

/* Library objects */

pub type Obj = Dyn;

#[derive(Debug, Deserialize)]
pub struct LibObj(Id, Obj);

pub type LibObjs = List<LibObj>;

#[derive(Debug, Deserialize)]
pub struct LibraryObjs {
    compiled: LibObjs,
    objects: LibObjs,
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

#[derive(Debug,Deserialize)]
pub struct LibSum {
    name: Dp,
    imports: Vec<Dp>,
    deps: Deps,
}

#[derive(Debug, Deserialize)]
pub struct Lib {
    compiled: CompiledLib,
    objects: LibraryObjs,
}

pub type Opaques = Vec<Computation<Constr>>;

#[derive(Debug,Deserialize)]
pub struct UnivTable(Vec<Computation<ContextSet>>, ContextSet, Bool);

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
