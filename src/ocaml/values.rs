use std::rc::Rc;

pub enum Value<'a> {
  Any,
//   Fail(&'static str),
  Tuple(&'static str, &'a [&'a Value<'a>]),
  Sum(&'static str, usize, &'a [&'a [Value<'a>]]),
//   Array(Rc<Value>),
//   List(Rc<Value>),
//   Opt(Rc<Value>),
  Int,
  String,
//   Annot(String, Rc<Value>),
//   Dyn,
//   Fix(Box<Fn (Value) -> Value>),
}

static UNIT : Value<'static> = Value::Tuple ("unit", &[]);
static BOOL : Value<'static> = Value::Sum ("bool", 2, &[]);

impl <'a> Value<'a> {

// fn tuple(name : &'static str, v : &'a[&'a Value<'a>]) -> Value<'a> {
//   Value::Tuple(name, v)
// }

// fn sum(name : &'static str, constr : usize, v : Vec<Vec<Rc<Value>>>) -> Value {
//   Value::Sum(name, constr, v)
// }

// fn enum_(name : &'static str, constr : usize) -> Value {
//   Value::Sum(name, constr, Vec::new())
// }

// fn pair(v1 : Value, v2 : Value) -> Value {
//   Value::tuple("*", vec!(Rc::new(v1), Rc::new(v2)))
// }

// fn ref_ (v : Rc<Value>) -> Value {
//   Value::tuple("ref", vec!(v))
// }

// fn set (e : Rc<Value>) -> Value {
//   let f = |v : Value| {
//     let v1 = Rc::new(v);
//     let v2 = v1.clone();
//     Value::Sum ("set", 1, vec!(vec!(v1, v2)))
//   };
//   Value::Fix(Box::new(f))
// }

}

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
