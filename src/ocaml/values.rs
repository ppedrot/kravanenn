use ocaml::marshal::{Obj, RawString};

type CowS<'a, T> = &'a T;
type CowVec<'a, T> = CowS<'a, [T]>;
type CowVec2<'a, T> = CowVec<'a, CowVec<'a, T>>;

pub type ValueR<'a> = &'a ValueT<'a>;

type CowVecV<'a> = CowVec<'a, ValueR<'a>>;
type CowVecV2<'a> = CowVec2<'a, ValueR<'a>>;

#[derive(PartialEq, Eq, Ord, PartialOrd, Copy, Clone, Debug)]
pub enum ValueT<'a> {
  Any,
  Fail(&'a str),
  Tuple(&'a str, CowVecV<'a>),
  Sum(&'a str, usize, CowVecV2<'a>),
  Array(ValueR<'a>),
  List(ValueR<'a>),
  Opt(ValueR<'a>),
  Int,
  String,
  // Annot(String, Rc<ValueT<'a>>),
  Dyn,
}

type ValueS = ValueT<'static>;

macro_rules! B {
    ($e:expr) => {
        &$e
    }
}

macro_rules! CB {
    ($( $e:expr ),*) => {
        &[$( $e ),*]
    }
}

macro_rules! FAIL {
    ($e:expr) => {
        ValueT::Fail(B!($e))
    }
}
pub type Fail = u8;

macro_rules! TUPLE {
    ($s:expr, $( $e:expr ),* ) => {
        ValueT::Tuple($s, CB!($( B!($e) ),*))
    }
}

macro_rules! SUM {
    ($s:expr, $i:expr, $( [ $( $e:expr ),* ] ),* ) => {
        ValueT::Sum($s, $i, CB!($( CB!($( B!($e) ),*) ),*))
    }
}

macro_rules! LIST {
    ($e:expr) => {
        ValueT::List(B!($e))
    }
}
#[derive(Debug, Deserialize)]
pub enum List<T> {
    Nil,
    Cons(T, Box<List<T>>),
}

macro_rules! OPT {
    ($e:expr) => {
        ValueT::Opt(B!($e))
    }
}
/*#[derive(Deserialize, Debug)]
pub enum Opt<T> {
    None,
    Some(T)
} */
pub type Opt<T> = Option<T>;

macro_rules! ARRAY {
    ($e:expr) => {
        ValueT::Array(B!($e))
    }
}

macro_rules! ENUM {
    ($s:expr, $i:expr) => {
        SUM!($s, $i, [])
    }
}

/* Ocaml standard library */
macro_rules! PAIR {
    ($v1:expr, $v2:expr) => {
        TUPLE!("*", $v1, $v2)
    }
}

static BOOL : ValueS = ENUM!("bool", 2);
/* #[derive(Deserialize, Debug)]
pub enum Bool {
    False,
    True
} */
pub type Bool = bool;

static INT : ValueS = ValueT::Int;
pub type Int = i64;

macro_rules! REF {
    ($v:expr) => {
        TUPLE!("ref", $v)
    }
}
#[derive(Debug, Deserialize)]
pub struct Ref<T>(T);

static STRING : ValueS = ValueT::String;
pub type Str = RawString;//Box<[u8]>;

static ANY : ValueS = ValueT::Any;
#[derive(Debug, Deserialize)]
pub struct Any;

static DYN : ValueS = ValueT::Dyn;

macro_rules! SET {
    ($s:ident, $e:expr) => {
        SUM!("set", 1, [$s, $e, $s, INT])
   }
}
#[derive(Deserialize,Debug)]
pub enum Set<V> {
    Nil,
    Node(Box<Set<V>>, V, Box<Set<V>>, Int),
}

macro_rules! MAP {
    ($m:ident, $vk:expr, $vd:expr) => {
        SUM!("map", 1, [$m, $vk, $vd, $m, INT])
   }
}
#[derive(Deserialize,Debug)]
pub enum Map<K, V> {
    Nil,
    Node(Box<Map<K, V>>, K, V, Box<Map<K,V>>, Int),
}

macro_rules! HSET {
    ($s:ident, $v:expr) => {
        MAP!($s, INT, $v)
    }
}
pub type HSet<V> = Map<Int, Set<V>>;

#[derive(Debug,Deserialize)]
pub enum HList<T> {
    Nil,
    Cons(T, Int, Box<HList<T>>),
}

macro_rules! HMAP {
    ($m:ident, $vk:expr, $vd:expr) => {
        {
            static M : ValueS = MAP!(M, $vk, $vd);
            MAP!($m, INT, M)
        }
   }
}
pub type HMap<K, V> = Map<Int, Map<K, V>>;

/* lib/future */
macro_rules! COMPUTATION {
    ($f:expr) => {
        REF!(SUM!("Future.comput", 0, [FAIL!("Future.ongoing")], [$f]))
    }
}
#[derive(Deserialize,Debug)]
pub enum FutureComput<F> {
    Done(F),
    Ongoing(Fail),
}

pub type Computation<F> = Ref<FutureComput<F>>;

/* kernel/names */

static ID : ValueS = ValueT::String;
pub type Id = Str;

static DP : ValueS = LIST!(ID);
pub type Dp = List<Id>;

static NAME : ValueS = SUM!("name", 1, [ID]);
#[derive(Debug, Deserialize)]
pub enum Name {
    Anonymous, // anonymous identifier
    Name(Id), // non-anonymous identifier
}

static UID : ValueS = TUPLE!("uniq_ident", INT, STRING, DP);
#[derive(Debug, Deserialize)]
pub struct UId(Int, Str, Dp);

static MP : ValueS = SUM!("module_path", 0, [DP], [UID], [MP, ID]);
#[derive(Debug, Deserialize)]
pub enum Mp {
    Dot(Box<Mp>, Id),
    Bound(UId),
    File(Dp),
}

static KN : ValueS = TUPLE!("kernel_name", ANY, MP, DP, ID, INT);
#[derive(Debug, Deserialize)]
pub struct Kn {
    canary: Any,
    modpath: Mp,
    dirpath: Dp,
    knlabel: Id,
    refhash: Int,
}

static CST : ValueS = SUM!("cst|mind", 0, [KN], [KN, KN]);
#[derive(Debug, Deserialize)]
pub enum Cst {
    Dual(Kn, Kn), // user then canonical
    Same(Kn), // user = canonical
}

static IND : ValueS = TUPLE!("inductive", CST, INT);
#[derive(Debug, Deserialize)]
pub struct Ind {
    /// the name of the inductive type
    name: Cst,
    /// The position of the inductive type within the block of mutually-recursive types.
    /// Beware: indexing starts from 0.
    pos: Int,
}

static CONS : ValueS = TUPLE!("constructor", IND, INT);
/// Designation of a (particular) constructor of a (particular) inductive type.
#[derive(Debug, Deserialize)]
pub struct Cons {
    /// designates the inductive type
    ind: Ind,
    /// The index of the constructor.  Beware: indexing starts from 1.
    idx: Int,
}

/* kernel/univ */

static RAW_LEVEL : ValueS = SUM!("raw_level", 2 /* Prop, Set */, /*Level*/[INT, DP], /*Var*/[INT]);
#[derive(Debug, Deserialize)]
pub enum RawLevel {
    Prop,
    Set,
    Var(Int),
    Level(Int, Dp),
}

static LEVEL : ValueS = TUPLE!("level", INT, RAW_LEVEL);
#[derive(Debug,Deserialize)]
pub struct Level {
    hash: Int,
    data: RawLevel,
}

static EXPR : ValueS = TUPLE!("levelexpr", LEVEL, INT);
#[derive(Debug, Deserialize)]
pub struct Expr(Level, Int);

static UNIV : ValueS = SUM!("universe", 1, [EXPR, INT, UNIV]);
pub type Univ = HList<Expr>;

static CSTRS : ValueS = SET!(CSTRS, TUPLE!("univ_constraint", LEVEL, ENUM!("order_request", 3), LEVEL));
#[derive(Debug, Deserialize)]
enum ConstraintType {
    Lt,
    Le,
    Eq,
}
#[derive(Debug, Deserialize)]
pub struct UnivConstraint(Level, ConstraintType, Level);
pub type Cstrs = Set<UnivConstraint>;

static INSTANCE : ValueS = ARRAY!(LEVEL);
pub type Instance = Vec<Level>;

static CONTEXT : ValueS = TUPLE!("universe_context", INSTANCE, CSTRS);

// static ABS_CONTEXT : ValueS = CONTEXT; // Only for clarity
static ABS_CONTEXT : ValueS = TUPLE!("universe_context", INSTANCE, CSTRS); // Only for clarity

// static ABS_CUM_INFO : ValueS = TUPLE!("cumulativity_info", ABS_CONTEXT, CONTEXT);

static CONTEXT_SET : ValueS = {
    static LEVEL_SET : ValueS = HSET!(LEVEL_SET, LEVEL);
    TUPLE!("universe_context_set", LEVEL_SET, CSTRS)
 };
pub type LevelSet = HSet<Level>;
#[derive(Debug,Deserialize)]
pub struct ContextSet(LevelSet, Cstrs);

/* kernel/term */
static SORT : ValueS = SUM!("sort", 0, [ENUM!("cnt", 2)], [UNIV]);
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

static SORTFAM : ValueS = ENUM!("sorts_family", 3);
#[derive(Debug,Deserialize)]
pub enum SortFam {
    InProp,
    InSet,
    InType,
}

macro_rules! PUNIVERSES {
    ($v:expr) => {
        TUPLE!("punivs", $v, INSTANCE)
    }
}
#[derive(Debug,Deserialize)]
pub struct PUniverses<T>(T, Instance);

static BOOLLIST : ValueS = LIST!(BOOL);
pub type BoolList = List<Bool>;

static CASEINFO : ValueS = {
    static CSTYLE : ValueS = ENUM!("case_style", 5);
    static CPRINT : ValueS = TUPLE!("case_printing", BOOLLIST, ARRAY!(BOOLLIST), CSTYLE);
    TUPLE!("case_info", IND, INT, ARRAY!(INT), ARRAY!(INT), CPRINT)
};

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

static CAST : ValueS = ENUM!("cast_kind", 4);
#[derive(Deserialize,Debug)]
pub enum Cast {
    VMCast,
    NATIVECast,
    DEFAULTCast,
    RevertCast, // FIXME: Figure out why this is apparently appearing in the file?
}

static PROJ : ValueS = TUPLE!("projection", CST, BOOL);
#[derive(Deserialize,Debug)]
pub struct Proj(Cst, Bool);

pub static CONSTR : ValueS = SUM!("constr", 0,
    [INT], // Rel
    [FAIL!("Var")], // Var
    [FAIL!("Meta")], // Meta
    [FAIL!("Evar")], // Evar
    [SORT], // Sort
    [CONSTR, CAST, CONSTR], // Cast
    [NAME, CONSTR, CONSTR], // Prod
    [NAME, CONSTR, CONSTR], // Lambda
    [NAME, CONSTR, CONSTR, CONSTR], // LetIn
    [CONSTR, ARRAY!(CONSTR)], // App
    [PUNIVERSES!(CST)], // Const
    [PUNIVERSES!(IND)], // Ind
    [PUNIVERSES!(CONS)], // Construct
    [CASEINFO, CONSTR, CONSTR, ARRAY!(CONSTR)], // Case
    [FIX], // Fix
    [COFIX], // CoFix
    [PROJ, CONSTR] // Proj
);
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

static PREC : ValueS = TUPLE!("prec_declaration", ARRAY!(NAME), ARRAY!(CONSTR), ARRAY!(CONSTR));
#[derive(Deserialize, Debug)]
pub struct PRec(Vec<Name>, Vec<Constr>, Vec<Constr>);

static FIX : ValueS = TUPLE!("pfixpoint", TUPLE!("fix2", ARRAY!(INT), INT), PREC);
#[derive(Deserialize, Debug)]
pub struct Fix2(Vec<Int>, Int);
#[derive(Deserialize, Debug)]
pub struct Fix(Fix2, PRec);

static COFIX : ValueS = TUPLE!("pcofixpoint", INT, PREC);
#[derive(Deserialize,Debug)]
pub struct CoFix(Int, PRec);

static RDECL : ValueS = SUM!("rel_declaration", 0,
    [NAME, CONSTR], // LocalAssum
    [NAME, CONSTR, CONSTR] // LocalDef
);

static RCTXT : ValueS = LIST!(RDECL);

static SECTION_CTXT : ValueS = ENUM!("emptylist", 1);


/* kernel/mod_subst */

static DELTA_HINT : ValueS = SUM!("delta_hint", 0, [INT, OPT!(CONSTR)], [KN]);

static RESOLVER : ValueS = {
    static MP_MAP : ValueS = MAP!(MP_MAP, MP, MP);
    static KN_MAP : ValueS = HMAP!(KN_MAP, KN, DELTA_HINT);
    TUPLE!("delta_resolver", MP_MAP, KN_MAP)
};

static MP_RESOLVER : ValueS = TUPLE!("", MP, RESOLVER);

static SUBST : ValueS = {
    static MP_MAP : ValueS = MAP!(MP_MAP, MP, MP_RESOLVER);
    static UID_MAP : ValueS = MAP!(UID_MAP, UID, MP_RESOLVER);
    TUPLE!("substitution", MP_MAP, UID_MAP)
};

/* kernel/lazyconstr */


macro_rules! SUBSTITUTED {
    ($a:expr) => {
        TUPLE!("substituted", $a, LIST!(SUBST))
    }
}

static CSTR_SUBST : ValueS = SUBSTITUTED!(CONSTR);

// NB: Second constructor [Direct] isn't supposed to appear in a .vo
static LAZY_CONSTR : ValueS = SUM!("lazy_constr", 0, [LIST!(SUBST), DP, INT]);

/* kernel/declarations */

// static IMPREDICATIVE_SET : ValueS = ENUM!("impr-set", 2);
static ENGAGEMENT : ValueS = ENUM!("impr-set", 2); // IMPREDICATIVE_SET;

static POL_ARITY : ValueS = TUPLE!("polymorphic_arity", LIST!(OPT!(LEVEL)), UNIV);

static CST_TYPE : ValueS = SUM!("constant_type", 0, [CONSTR], [PAIR!(RCTXT, POL_ARITY)]);

static CST_DEF : ValueS = SUM!("constant_def", 0, [OPT!(INT)], [CSTR_SUBST], [LAZY_CONSTR]);

static PROJBODY : ValueS = TUPLE!("projection_body", CST, INT, INT, CONSTR, TUPLE!("proj_eta", CONSTR, CONSTR), CONSTR);

static TYPING_FLAGS : ValueS = TUPLE!("typing_flags", BOOL, BOOL);

// static CONST_UNIVS : ValueS = SUM!("constant_universes", 0, [CONTEXT], [ABS_CONTEXT]);

static CB : ValueS = TUPLE!("constant_body", SECTION_CTXT, CST_DEF, CST_TYPE, ANY, BOOL, CONTEXT, /*CONST_UNIVS,*/ OPT!(PROJBODY), BOOL, TYPING_FLAGS);

static RECARG : ValueS = SUM!("recarg",
    1, // Norec
    [IND], // Mrec
    [IND] // Imbr
);

static WFP : ValueS = SUM!("wf_paths", 0,
    [INT, INT], // Rtree.Param
    [RECARG, ARRAY!(WFP)], // Rtree.Node
    [INT, ARRAY!(WFP)] // Rtree.Rec
);

static MONO_IND_ARITY : ValueS = TUPLE!("monomorphic_inductive_arity", CONSTR, SORT);

static IND_ARITY : ValueS = SUM!("inductive_arity", 0, [MONO_IND_ARITY], [POL_ARITY]);

static ONE_IND : ValueS = TUPLE!("one_inductive_body",
    ID,
    RCTXT,
    IND_ARITY,
    ARRAY!(ID),
    ARRAY!(CONSTR),
    INT,
    INT,
    LIST!(SORTFAM),
    ARRAY!(CONSTR),
    ARRAY!(INT),
    ARRAY!(INT),
    WFP,
    INT,
    INT,
    ANY
);

static FINITE : ValueS = ENUM!("recursivity_kind", 3);

static MIND_RECORD : ValueS = OPT!(OPT!(TUPLE!("record", ID, ARRAY!(CST), ARRAY!(PROJBODY))));

/* static IND_PACK_UNIVS : ValueS = SUM!("abstract_inductive_universes", 0,
    [CONTEXT],
    [ABS_CONTEXT],
    [ABS_CUM_INFO]
); */

static IND_PACK : ValueS = TUPLE!("mutual_inductive_body",
    ARRAY!(ONE_IND),
    MIND_RECORD,
    FINITE,
    INT,
    SECTION_CTXT,
    INT,
    INT,
    RCTXT,
    BOOL, BOOL, TUPLE!("universes", CONTEXT, CONTEXT), // IND_PACK_UNIVS, // universes
    OPT!(BOOL),
    TYPING_FLAGS
);

static WITH : ValueS = SUM!("with_declaration_body", 0,
    [LIST!(ID), MP],
    [LIST!(ID), TUPLE!("with_def", CONSTR, CONTEXT)]
);

static MAE : ValueS = SUM!("module_alg_expr", 0,
    [MP], // SEBident
    [MAE, MP], // SEBapply
    [MAE, WITH] // SEBwith
);

static SFB : ValueS = SUM!("struct_field_body", 0,
    [CB], // SFBconst
    [IND_PACK], // SFBmind
    [MODULE], // SFBmodule
    [MODTYPE] // SFBmodtype
);

static STRUC : ValueS = LIST!(TUPLE!("label*sfb", ID, SFB));

static SIGN : ValueS = SUM!("module_sign", 0,
    [STRUC], // NoFunctor
    [UID, MODTYPE, SIGN] // MoreFunctor
);

static MEXPR : ValueS = SUM!("module_expr", 0,
    [MAE], // NoFunctor
    [UID, MODTYPE, MEXPR] // MoreFunctor
);

static IMPL : ValueS = SUM!("module_impl", 2, // Abstract, FullStruct
    [MEXPR], // Algebraic
    [SIGN] // Struct
);

static NOIMPL : ValueS = ENUM!("no_impl", 1); // Astract is mandatory for mtb

static MODULE : ValueS = TUPLE!("module_body", MP, IMPL, SIGN, OPT!(MEXPR), CONTEXT_SET, RESOLVER, ANY);

static MODTYPE : ValueS = TUPLE!("module_type_body", MP, NOIMPL, SIGN, OPT!(MEXPR), CONTEXT_SET, RESOLVER, ANY);

/* kernel/safe_typing */

static VODIGEST : ValueS = SUM!("module_impl", 0, [STRING], [STRING, STRING]);
#[derive(Debug, Deserialize)]
pub enum VoDigest {
    Dviovo(Str, Str),
    Dvo(Str),
}

static DEPS : ValueS = ARRAY!(TUPLE!("dep", DP, VODIGEST));
#[derive(Debug, Deserialize)]
pub struct LibraryInfo(Dp, VoDigest);
pub type Deps = Vec<LibraryInfo>;

static COMPILED_LIB : ValueS = TUPLE!("compiled", DP, MODULE, DEPS, ENGAGEMENT, ANY);

/* Library objects */

static OBJ : ValueS = ValueT::Dyn;

static LIBOBJ : ValueS = TUPLE!("libobj", ID, OBJ);

static LIBOBJS : ValueS = LIST!(LIBOBJ);

static LIBRARYOBJS : ValueS = TUPLE!("library_objects", LIBOBJS, LIBOBJS);

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

pub static LIBSUM : ValueS = TUPLE!("summary", DP, ARRAY!(DP), DEPS);
#[derive(Debug,Deserialize)]
pub struct LibSum {
    name: Dp,
    imports: Vec<Dp>,
    deps: Deps,
}

pub static LIB : ValueS = TUPLE!("library", COMPILED_LIB, LIBRARYOBJS);

static OPAQUES : ValueS = ARRAY!(COMPUTATION!(CONSTR));
pub type Opaques = Vec<Computation<Constr>>;

static UNIVOPAQUES : ValueS = OPT!(TUPLE!("univopaques", ARRAY!(COMPUTATION!(CONTEXT_SET)), CONTEXT_SET, BOOL));

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

/*

let v_set v =
  let rec s = Sum ("Set.t",1,
    [|[|s; Annot("elem",v); s; Annot("bal",Int)|]|])
  in s

let v_map vk vd =
  let rec m = Sum ("Map.t",1,
    [|[|m; Annot("key",vk); Annot("data",vd); m; Annot("bal",Int)|]|])
  in m

let v_hset v = v_map Int (v_set v)
let v_hmap vk vd = v_map Int (v_map vk vd)

(* lib/future *)
let v_computation f =
  Annot ("Future.computation",
  v_ref
    (v_sum "Future.comput" 0
      [| [| Fail "Future.ongoing" |]; [| f |] |]))

(** kernel/names *)

let v_id = String
let v_dp = Annot ("dirpath", List v_id)
let v_name = v_sum "name" 1 [|[|v_id|]|]
let v_uid = v_tuple "uniq_ident" [|Int;String;v_dp|]
let rec v_mp = Sum("module_path",0,
  [|[|v_dp|];
    [|v_uid|];
    [|v_mp;v_id|]|])
let v_kn = v_tuple "kernel_name" [|Any;v_mp;v_dp;v_id;Int|]
let v_cst = v_sum "cst|mind" 0 [|[|v_kn|];[|v_kn;v_kn|]|]
let v_ind = v_tuple "inductive" [|v_cst;Int|]
let v_cons = v_tuple "constructor" [|v_ind;Int|]


(** kernel/univ *)

let v_raw_level = v_sum "raw_level" 2 (* Prop, Set *)
  [|(*Level*)[|Int;v_dp|]; (*Var*)[|Int|]|]
let v_level = v_tuple "level" [|Int;v_raw_level|]
let v_expr = v_tuple "levelexpr" [|v_level;Int|]
let rec v_univ = Sum ("universe", 1, [| [|v_expr; Int; v_univ|] |])

let v_cstrs =
  Annot
    ("Univ.constraints",
     v_set
       (v_tuple "univ_constraint"
          [|v_level;v_enum "order_request" 3;v_level|]))

let v_instance = Annot ("instance", Array v_level)
let v_context = v_tuple "universe_context" [|v_instance;v_cstrs|]
let v_context_set = v_tuple "universe_context_set" [|v_hset v_level;v_cstrs|]

(** kernel/term *)

let v_sort = v_sum "sort" 0 [|[|v_enum "cnt" 2|];[|v_univ|]|]
let v_sortfam = v_enum "sorts_family" 3

let v_puniverses v = v_tuple "punivs" [|v;v_instance|]

let v_boollist = List v_bool

let v_caseinfo =
  let v_cstyle = v_enum "case_style" 5 in
  let v_cprint = v_tuple "case_printing" [|v_boollist;Array v_boollist;v_cstyle|] in
  v_tuple "case_info" [|v_ind;Int;Array Int;Array Int;v_cprint|]

let v_cast = v_enum "cast_kind" 4

let rec v_constr =
  Sum ("constr",0,[|
    [|Int|]; (* Rel *)
    [|Fail "Var"|]; (* Var *)
    [|Fail "Meta"|]; (* Meta *)
    [|Fail "Evar"|]; (* Evar *)
    [|v_sort|]; (* Sort *)
    [|v_constr;v_cast;v_constr|]; (* Cast *)
    [|v_name;v_constr;v_constr|]; (* Prod *)
    [|v_name;v_constr;v_constr|]; (* Lambda *)
    [|v_name;v_constr;v_constr;v_constr|]; (* LetIn *)
    [|v_constr;Array v_constr|]; (* App *)
    [|v_puniverses v_cst|]; (* Const *)
    [|v_puniverses v_ind|]; (* Ind *)
    [|v_puniverses v_cons|]; (* Construct *)
    [|v_caseinfo;v_constr;v_constr;Array v_constr|]; (* Case *)
    [|v_fix|]; (* Fix *)
    [|v_cofix|]; (* CoFix *)
    [|v_cst;v_constr|] (* Proj *)
  |])

and v_prec = Tuple ("prec_declaration",
                    [|Array v_name; Array v_constr; Array v_constr|])
and v_fix = Tuple ("pfixpoint", [|Tuple ("fix2",[|Array Int;Int|]);v_prec|])
and v_cofix = Tuple ("pcofixpoint",[|Int;v_prec|])


let v_rdecl = v_tuple "rel_declaration" [|v_name;Opt v_constr;v_constr|]
let v_rctxt = List v_rdecl

let v_section_ctxt = v_enum "emptylist" 1


(** kernel/mod_subst *)

let v_delta_hint =
  v_sum "delta_hint" 0 [|[|Int; Opt v_constr|];[|v_kn|]|]

let v_resolver =
  v_tuple "delta_resolver"
    [|v_map v_mp v_mp;
      v_hmap v_kn v_delta_hint|]

let v_mp_resolver = v_tuple "" [|v_mp;v_resolver|]

let v_subst =
  v_tuple "substitution"
    [|v_map v_mp v_mp_resolver;
      v_map v_uid v_mp_resolver|]


(** kernel/lazyconstr *)

let v_substituted v_a =
  v_tuple "substituted" [|v_a; List v_subst|]

let v_cstr_subst = v_substituted v_constr

(** NB: Second constructor [Direct] isn't supposed to appear in a .vo *)
let v_lazy_constr =
  v_sum "lazy_constr" 0 [|[|List v_subst;v_dp;Int|]|]


(** kernel/declarations *)

let v_engagement = v_enum "eng" 1

let v_pol_arity =
  v_tuple "polymorphic_arity" [|List(Opt v_level);v_univ|]

let v_cst_type =
  v_sum "constant_type" 0 [|[|v_constr|]; [|v_pair v_rctxt v_pol_arity|]|]

let v_cst_def =
  v_sum "constant_def" 0
    [|[|Opt Int|]; [|v_cstr_subst|]; [|v_lazy_constr|]|]

let v_projbody =
  v_tuple "projection_body" [|v_cst;Int;Int;v_constr;v_tuple "proj_eta" [|v_constr;v_constr|];
                              v_constr|]

let v_cb = v_tuple "constant_body"
  [|v_section_ctxt;
    v_cst_def;
    v_cst_type;
    Any;
    v_bool;
    v_context;
    Opt v_projbody;
    v_bool|]

let v_recarg = v_sum "recarg" 1 (* Norec *)
  [|[|v_ind|] (* Mrec *);[|v_ind|] (* Imbr *)|]

let rec v_wfp = Sum ("wf_paths",0,
    [|[|Int;Int|]; (* Rtree.Param *)
      [|v_recarg;Array v_wfp|]; (* Rtree.Node *)
      [|Int;Array v_wfp|] (* Rtree.Rec *)
    |])

let v_mono_ind_arity =
  v_tuple "monomorphic_inductive_arity" [|v_constr;v_sort|]

let v_ind_arity = v_sum "inductive_arity" 0
  [|[|v_mono_ind_arity|];[|v_pol_arity|]|]

let v_one_ind = v_tuple "one_inductive_body"
  [|v_id;
    v_rctxt;
    v_ind_arity;
    Array v_id;
    Array v_constr;
    Int;
    Int;
    List v_sortfam;
    Array v_constr;
    Array Int;
    Array Int;
    v_wfp;
    Int;
    Int;
    Any|]

let v_finite = v_enum "recursivity_kind" 3
let v_mind_record = Annot ("mind_record",
                           Opt (Opt (v_tuple "record" [| v_id; Array v_cst; Array v_projbody |])))

let v_ind_pack = v_tuple "mutual_inductive_body"
  [|Array v_one_ind;
    v_mind_record;
    v_finite;
    Int;
    v_section_ctxt;
    Int;
    Int;
    v_rctxt;
    v_bool;
    v_context;
    Opt v_bool|]

let v_with =
  Sum ("with_declaration_body",0,
       [|[|List v_id;v_mp|];
         [|List v_id;v_tuple "with_def" [|v_constr;v_context|]|]|])

let rec v_mae =
  Sum ("module_alg_expr",0,
  [|[|v_mp|];         (* SEBident *)
    [|v_mae;v_mp|];   (* SEBapply *)
    [|v_mae;v_with|]  (* SEBwith *)
  |])

let rec v_sfb =
  Sum ("struct_field_body",0,
  [|[|v_cb|];       (* SFBconst *)
    [|v_ind_pack|]; (* SFBmind *)
    [|v_module|];   (* SFBmodule *)
    [|v_modtype|]   (* SFBmodtype *)
  |])
and v_struc = List (Tuple ("label*sfb",[|v_id;v_sfb|]))
and v_sign =
  Sum ("module_sign",0,
  [|[|v_struc|];                   (* NoFunctor *)
    [|v_uid;v_modtype;v_sign|]|])  (* MoreFunctor *)
and v_mexpr =
  Sum ("module_expr",0,
  [|[|v_mae|];                     (* NoFunctor *)
    [|v_uid;v_modtype;v_mexpr|]|]) (* MoreFunctor *)
and v_impl =
  Sum ("module_impl",2, (* Abstract, FullStruct *)
  [|[|v_mexpr|];  (* Algebraic *)
    [|v_sign|]|])  (* Struct *)
and v_noimpl = v_enum "no_impl" 1 (* Abstract is mandatory for mtb *)
and v_module =
  Tuple ("module_body",
         [|v_mp;v_impl;v_sign;Opt v_mexpr;v_cstrs;v_resolver;Any|])
and v_modtype =
  Tuple ("module_type_body",
         [|v_mp;v_noimpl;v_sign;Opt v_mexpr;v_cstrs;v_resolver;Any|])

(** kernel/safe_typing *)

let v_vodigest = Sum ("module_impl",0, [| [|String|]; [|String;String|] |])
let v_deps = Array (v_tuple "dep" [|v_dp;v_vodigest|])
let v_compiled_lib =
  v_tuple "compiled" [|v_dp;v_module;v_deps;Opt v_engagement;Any|]

(** Library objects *)

let v_obj = Dyn
let v_libobj = Tuple ("libobj", [|v_id;v_obj|])
let v_libobjs = List v_libobj
let v_libraryobjs = Tuple ("library_objects",[|v_libobjs;v_libobjs|])

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

(** Toplevel structures in a vo (see Cic.mli) *)

let v_lib =
  Tuple ("library",[|v_dp;v_compiled_lib;v_libraryobjs;v_deps;Array v_dp|])

let v_opaques = Array (v_computation v_constr)
let v_univopaques =
  Opt (Tuple ("univopaques",[|Array (v_computation v_context_set);v_context_set;v_bool|]))

(** Registering dynamic values *)

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
  with Not_found -> Any

*/
