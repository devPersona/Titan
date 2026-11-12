open Ast
open Prim
open Span
open Error

type symbol_id = int
type s_id = symbol_id
type v_id = symbol_id

and symbol = {
  id:      int;
  name: string;
}

type disamb_ctx = {
  sigs: (t_id, t_sig) Hashtbl.t;
  mutable env:       disamb_env;
  mutable curr:         module_;
  mutable errors: err_kind list;
} 
and disamb_env = { mutable vars: disamb_var list; parent: disamb_env option }
and disamb_var = { name: string; typ: t; is_comptime: bool; value: value  }


let push_err kind span ctx = ctx.errors <- (make_err_in_module kind span ctx.curr :: ctx.errors)
let push_env ctx = 
  let old = ctx.env in
  ctx.env <- { vars = []; parent = Some old };
  fun () -> ctx.env <- old
let push_var name typ is_comptime value ctx = ctx.env.vars <- { name; typ; is_comptime; value } :: ctx.env.vars
let get_var name ctx = 
  let rec loop env =
    match List.find_opt (fun v -> v.name = name) env.vars with
    | Some v -> v
    | None   -> loop (Option.get env.parent) (* safe *)
  in loop ctx.env

let map func l ctx = List.map (fun i -> func i ctx) l




(* type type_check_ctx = {
  defs:   (t_id,      t_def) Hashtbl.t;
  vars:   (v_id,   var_info) Hashtbl.t;
  scopes: (s_id, scope_info) Hashtbl.t;

  mutable hint:                      t;
  mutable env:              scope_info;
  mutable error:         err_kind list;
}
and var_info = {
  symbol:      symbol;
  t:                t;
  mods: modifier list;
  scope:         s_id;
  is_const:      bool;
  is_comptime:   bool;
  reassigned:    bool;
  kind:      var_kind;
}
and var_kind =
| VKVar
| VKField   of t_id
| VKMethod  of t_id
| VKStatic  of var_kind
(* TODO: add "enum" field *)
and scope_info = {
  id:                     s_id;
  parent:    scope_info option;
  mutable vars:  var_info list;
  (* TODO: add an "access" field *)
}
and t_def = {
  symbol:                           symbol;
  t_sig:                             t_sig;
  fields:  (string,  field_info) Hashtbl.t;
  methods: (v_id,   method_info) Hashtbl.t;
  ops:     ((op * t), t_op_kind) Hashtbl.t;
  from_t:  (t,             v_id) Hashtbl.t;
  to_t:    (t,             v_id) Hashtbl.t;
}
and field_info  = {
  symbol:      symbol;
  t:                t;
  belongs:       t_id;
  is_static:     bool;
  is_private:    bool;
  is_extern:     bool;
  prop:     prop_kind;
}
and prop_kind = 
| PKCustom of { get: prop_info; set: prop_info }
| PKPlain
and prop_info = 
| PFunc of v_id
| PDefault
| PNull
| PNever
and method_info = {
  symbol:          symbol;
  t:                    t;
  params: param_info list;
  belongs:           t_id;
  is_static:         bool;
  is_private:        bool;
  is_extern:         bool;
  is_inline:         bool;
}
and t_op_kind =
| TOKPrim     of t
| TOKOverload of v_id

and texpr      = { texpr: texpr_def; info: texpr_info; mods: modifier list; span: span }
and texpr_info = {
  t:                t;
  v_kind:  value_kind;
}
and value_kind =
| RValue
| LValue
and texpr_def  =
| TEEmpty
| TELit     of basic
| TEVar     of v_id
| TEThis
| TEBinOp   of texpr * op   * texpr
| TELUnOp   of op   * texpr
| TERUnOp   of texpr * op
| TEArray   of texpr list
| TETuple   of texpr list
| TEIf      of texpr * texpr * texpr
| TECall    of texpr * texpr
| TEField   of texpr * texpr
| TEIndex   of texpr * texpr
| TEGeneric of texpr * generic_arg list
| TEAddress of texpr
| TENew     of texpr
| TEDecl    of placed_name * t * texpr
| TELambda  of param_info list * t * texpr
| TEReturn  of texpr
| TEPoly    of texpr * generic_param list
| TEType    of t
| TEBlock   of stmt list
| TETrace   of texpr


let to_list tbl = Hashtbl.to_seq tbl |> List.of_seq

let pack_texpr texpr t v_kind mods span = { texpr; info = { t; v_kind }; mods; span }
let pack_texpr_from (e:expr) te t vk = pack_texpr te t vk e.mods e.span
let pack_error_expr e = pack_texpr_from e TEEmpty TUnknown RValue


let get_t_id t =
  match get_t t with
  | TID id -> id
  | _      -> assert false
let get_def  id ctx = Hashtbl.find ctx.defs id
let get_t_def t = get_def (get_t_id t)
let get_var_by_id id ctx = Hashtbl.find ctx.vars id
let get_var     name ctx = List.find (fun v -> v.symbol.name = name) ctx.env.vars  *)


let rec get_t t =
  match t with
  | TDefault (t, _) -> t
  | TNamed   (_, t) -> t
  | _               -> t

let is_mutable op = 
  match op with
  | Asg | AAdd | ASub | ADiv | AMul | LInc | LDec | RInc | RDec | New -> true
  | _ -> false


let rec is_comptime e ctx =
  match e.expr with
  | ELit  (Float  _)
  | ELit  (String _)   -> false
  | ELit   _           -> true
  | EVar   name        -> (get_var name  ctx).is_comptime
  | EBinOp (e1, _, e2) -> is_comptime e1 ctx && is_comptime e2 ctx
  | ELUnOp (_,      e) -> is_comptime e  ctx
  | ERUnOp (e,      _) -> is_comptime e  ctx
  | EArray exprs       -> List.for_all (fun e -> is_comptime e ctx) exprs
  | ETuple exprs       -> List.for_all (fun e -> is_comptime e ctx) exprs
  | EIf    (c,  t,  e) -> is_comptime c ctx && is_comptime t ctx && is_comptime e ctx
  | EIndex (t,  i    ) -> is_comptime t ctx && is_comptime i ctx
  (* TODO: add tuple/static class fields *)
  | _                  -> false

let rec is_t_comptime t =
  match get_t t with
  | TID id when List.mem id comptime_allowed  -> None
  | TApplied (id, _) when id = fixedArrID     -> None
  | TUnknown                                  -> None
  | TTuple types                              -> List.find_map is_t_comptime types
  | _                                         -> Some t


let int_of_v v =
  match v with
  | VBool b -> if b then 1 else 0
  | VChar c -> Char.code c
  | VInt  i -> i
  | _       -> assert false
let bool_of_v v = int_of_v v <> 0

let rec is_unknown t = match t with | TUnknown | TUnit -> true | TApplied (_, [GAType t; _]) when is_unknown t -> true | _ -> false

let rec normalize_t expected got ctx =
  let is_plain id = id = intID || id = boolID || id = charID in
  match get_t expected, get_t got with
  | t1, t2 when is_unknown t1 && is_unknown t2 -> TUnknown (* fancy error later *)
  | t1, t2 when t1 = t2 -> expected
  | t1, t2 when is_unknown t1 -> t2
  | TID i1, TID i2 when is_plain i1 && is_plain i2 -> expected
  | TTuple ts1, TTuple ts2 when List.length ts1 = List.length ts2 -> 
    let rec bind ts1 ts2 acc = 
      match ts1, ts2 with
      | [], []             -> TTuple (List.rev acc)
      | t1 :: r1, t2 :: r2 -> let t = normalize_t t1 t2 ctx in if t = TUnknown then TUnknown else bind r1 r2 (t :: acc)
      | _                  -> assert false (* impossible *)
    in bind ts1 ts2 []
  | TApplied (id, [GAType t1; GAVal v1]), TApplied (_, [GAType t2; GAVal v2]) ->
    let len = int_of_v v1 in
    if  len <> int_of_v v2 then TUnknown (* fancy error later *)
    else let t = normalize_t t1 t2 ctx in if t = TUnknown then TUnknown else TApplied (id, [GAType t; GAVal (VInt len)])
  | _ -> TUnknown (* fancy error later *)


let rec type_of_v v ctx =
  let t = 
    match v with
    | VInt   _  -> TID  intID
    | VBool  _  -> TID boolID
    | VChar  _  -> TID charID
    | VTuple vs -> let ts = (List.map (fun v -> type_of_v v ctx) vs) in if List.mem TUnknown ts then TUnknown else TTuple ts 
    | VArray vs ->
      let rec loop t vs =
        match vs with
        | []           -> t
        | head :: tail -> normalize_t t (type_of_v head ctx) ctx
      in let t = loop TUnknown vs in if t = TUnknown then TUnknown else TApplied (fixedArrID, [GAType t; GAVal (VInt (List.length vs))])
    | VNone     -> TUnknown
  in if is_unknown t then TUnknown else t





let rec eval_binop e1 op e2 s ctx =
  match e1, e2 with
  | VTuple es1, VTuple es2 -> eval_binop_tuple es1 op es2 s ctx
  | VTuple es,  _          -> VTuple (List.map (fun e -> eval_binop e op e2 s ctx) es)
  | _,          VTuple es  -> VTuple (List.map (fun e -> eval_binop e1 op e s ctx) es)
  | VArray _,_|_, VArray _ -> VNone (* fancy error later *)
  | v1,         v2         -> let res = eval_binop_int (int_of_v v1) op (int_of_v v2) s ctx in if res = VNone then VNone else res

and eval_binop_tuple es1 op es2 s ctx =
  let rec loop es1 es2 acc =
    match es1, es2 with
    | [],       []       -> VTuple (List.rev acc)
    | e1 :: r1, e2 :: r2 -> let res = eval_binop e1 op e2 s ctx in if res = VNone then VNone else loop r1 r2 (res :: acc)
    | e  :: r,  []       -> loop r [] (e :: acc)
    | [],       e  :: r  -> loop [] r (e :: acc)
  in loop es1 es2 []

and eval_binop_int i1 op i2 s ctx =
  let b x = VBool x in
  let i x = VInt  x in
  match op with
  | Add -> i (i1 + i2)
  | Sub -> i (i1 - i2)
  | Mul -> i (i1 * i2)
  | Div -> if i2 = 0 then (VNone (* fancy error later *)) else i (i1 /   i2)
  | Mod -> if i2 = 0 then (VNone (* fancy error later *)) else i (i1 mod i2)
  | Eq  -> b (i1 =  i2)
  | Neq -> b (i1 <> i2)
  | Gt  -> b (i1 >  i2)
  | Ge  -> b (i1 >= i2)
  | Lt  -> b (i1 <  i2)
  | Le  -> b (i1 <= i2)
  | And -> b (i1 <> 0 && i2 <> 0)
  | Or  -> b (i1 <> 0 || i2 <> 0)
  | Xor -> i (i1 lxor i2)
  | Amp -> i (i1 land i2)
  | Pip -> i (i1 lor  i2)
  | _   -> assert false (* impossible *)

let rec eval_lunop op e s ctx = 
  match e with
  | VTuple es -> VTuple (List.map (fun e -> eval_lunop op e s ctx) es)
  | VArray _  -> VNone (* fancy error later *)
  | v         -> let i = int_of_v v in
    match op with
    | Sub -> VInt (-i)
    | Not -> VBool (i = 0)
    | _   -> assert false (* impossible *)

let eval_index t i ctx =
  match t with
  | VArray vs -> begin
    match i with
    | VArray _ | VTuple _ -> VNone (* fancy error later *)
    | v                   ->
      let i = int_of_v v in if i < 0 then VNone (* fancy error later *) else 
      match List.nth_opt vs i with
      | Some v -> v
      | None   -> VNone (* fancy error later *)
  end
  | _         -> VNone (* fancy error later *)

let rec eval_expr e ctx = 
  match e.expr with
  | ELit (Int  i) -> VInt  i
  | ELit (Bool b) -> VBool b
  | ETuple exprs  -> VTuple (map eval_expr exprs ctx)
  | EArray exprs  ->
    let vs = map eval_expr exprs ctx in
    if List.mem VNone vs then VNone else
    let check = type_of_v (VArray vs) ctx in
    if  check = TUnknown then VNone else VArray vs
  | EVar   name   -> (get_var name ctx).value
  | EBinOp (e1, op, e2) ->
    if is_mutable op then VNone (* fancy error later *) else 
    let v1 = eval_expr e1 ctx in begin
    match op, v1 with
    | _, (VTuple _ | VArray _)       -> eval_binop v1 op (eval_expr e2 ctx) e.span ctx
    | And, _ when bool_of_v v1       -> VBool false
    | Or,  _ when not (bool_of_v v1) -> VBool true
    | _, _                           -> eval_binop v1 op (eval_expr e2 ctx) e.span ctx
  end
  | ELUnOp (op, e1) -> 
    if is_mutable op then VNone (* fancy error later *) else 
    let v = eval_expr e1 ctx in
    eval_lunop op v e.span ctx
  | ERUnOp _ -> VNone (* only mutable exists, fancy error later *)
  | EIndex (t, i) ->
    let t = eval_expr t ctx in
    let i = eval_expr i ctx in
    if  t = VNone || i = VNone then VNone else eval_index t i ctx
  | _ -> assert false



let rec disamb_type t ctx =
  match t with
  | TDefault (t, e) ->
    let t = disamb_type t ctx in if t = TUnknown then TUnknown else
    TDefault (t, disamb_expr e ctx)
  | TNamed   (n, t) ->
    let t = disamb_type t ctx in if t = TUnknown then TUnknown else
    TNamed (n, t)
  | TTuple ts       ->
    let ts = map disamb_type ts ctx in if List.mem TUnknown ts then TUnknown else
    TTuple ts
  | TFunc    (a, r) -> 
    let a = disamb_type a ctx in 
    let r = disamb_type r ctx in
    if a = TUnknown || r = TUnknown then TUnknown else
    TFunc (a, r)
  | TGeneric (TAmb ids, a) ->
    let a = map disamb_generic_type_args a ctx in
    disamb_generic_type ids a ctx
  | _                     -> assert false

and disamb_generic_type_args a ctx =
  match a.arg with
  | GAType t -> Some { a with arg = GAType (disamb_type t ctx) }
  | GAExpr e ->
    if not (is_comptime e ctx) then None (* fancy error later *)
    else Some { a with arg = (GAVal (eval_expr e ctx)) }
  | _ -> assert false 

and disamb_generic_type ids a ctx =
  let params = ids |> List.map (fun id -> (Hashtbl.find ctx.sigs id).params) |> List.combine ids in
  match params, a with
  | [], [] -> 
  | 
  | _      -> assert false



and disamb_expr e ctx =
  let expr = 
  match e.expr with
    | EBinOp (e1, op, e2) -> if is_comptime e1 ctx && is_mutable op then assert false (* error message later *) else
      let e1 = disamb_expr e1 ctx in
      let e2 = disamb_expr e2 ctx in
      EBinOp (e1, op, e2)
    | ELUnOp (op, e)    -> if is_comptime e ctx && is_mutable op then assert false (* error message later *) else ELUnOp (op, e)
    | ERUnOp (e, op)    -> if is_comptime e ctx && is_mutable op then assert false (* error message later *) else ERUnOp (e, op)
    | EArray  exprs     -> EArray (map disamb_expr exprs ctx)
    | ETuple  exprs     -> ETuple (map disamb_expr exprs ctx)
    | EIf  (c, t, e)    ->
      let res_c = push_env ctx in
      let c     = disamb_expr c ctx in
      let res_t = push_env ctx in
      let t     = disamb_expr t ctx in
      res_t();
      let e     = disamb_expr e ctx in
      res_c();
      EIf (c, t, e)
    | ECall    (t, a)   -> ECall  (disamb_expr t ctx, disamb_expr a ctx)
    | EField   (t, f)   -> EField (disamb_expr t ctx, disamb_expr f ctx)
    | EIndex   (t, f)   -> EIndex (disamb_expr t ctx, disamb_expr f ctx)
    | EGeneric (t, a)   -> disamb_egeneric t a ctx
    | EAddress e        -> EAddress (disamb_expr       e ctx)
    | ENew     e        -> ENew     (disamb_expr       e ctx)
    | EDecl   (n, t, v) -> disamb_decl e n t v ctx
    | ELambda (p, t, b) -> disamb_lambda p t b ctx
    | EReturn e         -> EReturn  (disamb_expr       e ctx)
    | EPoly   (t, p)    -> disamb_epoly    t a ctx
    | EType   t         -> disamb_type       t ctx
    | EBlock  stmt      -> EBlock (map disamb_stmt stmt ctx)
    | ETrace  e         -> ETrace (disamb_expr     e    ctx)
    | e                 -> e
  in { e with expr }

and disamb_egeneric t a ctx =
  let t = disamb_expr t ctx in
  let rec loop (a:generic_arg list) acc =
    match a with
    | []           -> List.rev acc
    | head :: tail -> 
      match head.arg with
      | GAType t     -> loop tail ({ head with arg = GAType (disamb_type t ctx   ) } :: acc)
      | GAAmb (t, e) -> loop tail ({ head with arg = GAAmb  (disamb_type t ctx, e) } :: acc)
      | _            -> loop tail (head :: acc)
  in
  let a = loop a [] in
  EGeneric (t, a)

and disamb_decl e n t v ctx =
  let is_comptime =
    let rec loop m =
      match m with
      | [] -> false
      | head :: tail -> 
        match head.modifier with
        | MMeta ("comptime", []) -> true
        | MMeta ("comptime",  _) -> assert false (* fancy error later *)
        | _                      -> loop tail
    in loop e.mods
  in
  if not is_comptime then (push_var n.name TUnknown false VNone ctx; EDecl (n, disamb_type t ctx, disamb_expr v ctx))
  else if is_t_comptime t <> None then assert false (* fancy error later *)
  else let t = disamb_type t ctx in
  let v = disamb_expr v ctx in
  eval_comptime n t v ctx;
  EDecl (n, t, v)

and eval_comptime n t v ctx =
  match v.expr with
  | EEmpty -> EEmpty (* fancy error later *)
  | _      ->
    if not (is_comptime v ctx) then EEmpty (* fancy error later *)
    else let value = eval_expr v ctx in