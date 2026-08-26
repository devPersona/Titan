open Ast
open Span
open Error
open Debug

let (int_sig:t_sig)   = { name = "Int";    kind = TSKPrimal; mods = []; generics = [] }
let (float_sig:t_sig) = { name = "Float";  kind = TSKPrimal; mods = []; generics = [] }
let (bool_sig:t_sig)  = { name = "Bool";   kind = TSKPrimal; mods = []; generics = [] }
let (str_sig:t_sig)   = { name = "String"; kind = TSKPrimal; mods = []; generics = [] }
let (arr_sig:t_sig)   = { name = "Array";  kind = TSKPrimal; mods = []; generics = [{ param = GPTypename "T"; metadata = []; span = file_start_span }] }
let (ptr_sig:t_sig)   = { name = "Ptr";    kind = TSKPrimal; mods = []; generics = [{ param = GPTypename "T"; metadata = []; span = file_start_span }] }

type resolve_env = {
  mutable vars: string list;
  parent: resolve_env option
}
type resolve_ctx = {
  modules: (path, module_   ) Hashtbl.t;
  types:   (path, t_sig list) Hashtbl.t;
  mutable curr:                 module_;
  mutable local:             t_sig list;
  mutable env:              resolve_env;
  mutable errors:         err_kind list;
}
let push_err kind span ctx = 
  ctx.errors <- make_err_in_module kind span ctx.curr :: ctx.errors
let map func l ctx =
  List.map (fun i -> func i ctx) l
let rec find_var_opt n env = 
  match List.find_opt ((=) n) env.vars with
  | Some v -> Some v
  | None   -> 
    match env.parent with
    | Some p -> find_var_opt n p
    | None   -> None
let push_var v ctx =
  ctx.env.vars <- v :: ctx.env.vars
let push_env ctx =
  let old = ctx.env in
  ctx.env <- { vars = []; parent = Some (ctx.env) };
  fun () -> ctx.env <- old









let sig_to_type s = 
  match s.kind with
  | TSKClass    -> TClass s.name
  | TSKPrimal   -> TClass s.name
  | TSKTypename -> TTypename s.name

let rec type_to_expr t s ctx =
  let empty = { expr = EEmpty; mods = []; span = s } in
  match t with
  | TName (n, _)    -> { expr = EVar n; mods = []; span = s; } 
  | TTuple types    -> let exprs = List.map (fun t -> type_to_expr t s ctx) types in if List.exists (fun e -> e.expr = EEmpty) exprs then empty else { expr = ETuple exprs; mods = []; span = s; }
  | TArray t        -> let e = type_to_expr t s ctx in if e.expr = EEmpty then empty else { expr = EArray [e]; mods = []; span = s; }
  | TGeneric (t, a) -> let e = type_to_expr t s ctx in if e.expr = EEmpty then empty else { expr = EGeneric (e, a); mods = []; span = s; }
  | TUnit           -> { expr = ETuple []; mods = []; span = s; }
  |  _              -> push_err (Expected "expression") s ctx; empty

let rec expr_to_type e ctx =
  match e.expr with
  | EVar   n        -> TName (n, e.span)
  | EThis           -> TName ("this", e.span)
  | EArray exprs when List.length exprs = 1 -> let t = expr_to_type (List.hd exprs) ctx in if t = TUnknown then TUnknown else TArray t 
  | ETuple exprs    -> let types = map expr_to_type exprs ctx in if List.exists ((=) TUnknown) types then TUnknown else TTuple (types)
  | EGeneric (t, a) -> let t = expr_to_type t ctx in if t = TUnknown then TUnknown else TGeneric (t, a)
  | EType t         -> t 
  | _               -> push_err (Expected "type") e.span ctx; TUnknown
 


let gather_types modules =
  let types = Hashtbl.create 8 in
  let err = ref [] in
  let to_sig (i:item) (t:t_decl_info) = 
    match t.kind with
    | TDKClass info -> { name = t.name.name; kind = TSKClass; generics = info.generics; mods = i.mods }
  in
  let gather _ m = 
    let fold acc i =
      match i.item with
      | IType t -> if List.exists (fun s -> s.name = t.name.name) acc then (err := make_err_in_module (Redef_type (t.name.name)) t.name.span m :: !err; acc) else to_sig i t :: acc
      | _       -> acc
    in
    Hashtbl.add types m.name (List.fold_left fold [] m.items |> List.rev)
  in
  Hashtbl.iter gather modules;
  types, List.rev !err

let gather_local path ctx =
  let add_local t = 
    if not (List.exists (fun s -> s.name = t.name) ctx.local) then ctx.local <- t :: ctx.local
  in
  ctx.local <- Hashtbl.find ctx.types path;
  List.iter (fun i -> List.iter add_local (Hashtbl.find ctx.types i.path)) (Hashtbl.find ctx.modules path).imports





let rec resolve_type t ctx =
  match t with
  | TName    (n, s) -> resolve_type_name n s ctx
  | TPath (p, t, _) -> resolve_type_path p t ctx
  | TNamed   (n, t) -> TNamed   (n, resolve_type t ctx)
  | TDefault (t, e) -> TDefault (resolve_type t ctx, resolve_expr e ctx)
  | TTuple types    -> TTuple   (map resolve_type types ctx)
  | TArray t        -> TArray   (resolve_type t ctx)
  | TPtr   t        -> TPtr     (resolve_type t ctx)
  | TGeneric (t, a) -> resolve_generic_type t a ctx
  | TPoly    (t, p) -> resolve_poly_type    t p ctx
  | TFunc    (a, r) -> TFunc    (resolve_type a ctx, resolve_type r ctx)
  | _               -> t

and resolve_type_name n s ctx =
  match List.find_opt (fun s -> s.name = n) ctx.local with
  | Some s -> sig_to_type s
  | None   -> push_err (Undefined_type n) s ctx; TUnknown

and resolve_type_path p t ctx =
  let types = Hashtbl.find ctx.types p in
  let n, s = 
    match t with
    | TName (n, s) -> n, s
    | _            -> assert false
  in
  match List.find_opt (fun s -> s.name = n) types with
  | Some s -> sig_to_type s
  | None   -> push_err (Undefined_type n) s ctx; TUnknown

and resolve_generic_type t a ctx =
  let rec check t =
    match t with
    | TName (n,    s) -> resolve_type_name n s ctx, n
    | TPath (p, t, s) -> resolve_type_path p t ctx, (match t with TName (n, _) -> n | _ -> assert false)
    | TNamed   (_, t) -> check t
    | TDefault (t, _) -> check t
    | TTuple   _      -> push_err (Msg "Tuples cannot take type parameters")             (List.hd a).span ctx; TUnknown, ""
    | TArray   _      -> push_err (Msg "Arrays cannot take type parameters")             (List.hd a).span ctx; TUnknown, ""
    | TPtr     _      -> push_err (Msg "Pointers cannot take type parameters")           (List.hd a).span ctx; TUnknown, ""
    | TGeneric _      -> push_err (Msg "Double generic type parameters are not allowed") (List.hd a).span ctx; TUnknown, ""
    | TFunc    _      -> push_err (Msg "Function types cannot take type parameters")     (List.hd a).span ctx; TUnknown, ""
    | TUnit           -> push_err (Msg "Unit type cannot take type parameters")          (List.hd a).span ctx; TUnknown, ""
    | _               -> assert false (* impossible to reach *)
  in 
  let t, n = check t in
  match t with
  | TUnknown -> TUnknown
  | _        ->
    let s = List.find (fun s -> s.name = n) ctx.local in  (* TODO: match for path types *)
    let rec loop (params:generic_param list) (args:generic_arg list) acc =
      match params, args with
      | [], []     -> List.rev acc
      | [], a :: _ -> push_err (Msg ("Too many type parameters for type \"" ^ n ^ "\"")) a.span ctx; List.rev acc
      | _ :: _, [] -> push_err (Msg ("Not enough type parameters for type \"" ^ n ^ "\"")) (a |> List.rev |> List.hd).span ctx; List.rev acc
      | p :: pr, a :: ar -> 
        match p.param, a.arg with
        | GPConst    _, GAExpr _ 
        | GPTypename _, GAType _ -> loop pr ar (a :: acc)
        | GPConst    _, GAType t -> 
          let e = type_to_expr t a.span ctx in
          if e.expr = EEmpty then loop pr ar acc else loop pr ar ({ a with arg = GAExpr e } :: acc)
        | GPTypename _, GAExpr e ->
          let t = expr_to_type e ctx in
          if t = TUnknown then loop pr ar acc else loop pr ar ({ a with arg = GAType t } :: acc)
    in
    let args = loop s.generics a [] in
    TGeneric (t, map resolve_generic_arg args ctx)

and resolve_generic_arg a ctx = 
  let arg = 
    match a.arg with
    | GAExpr e -> GAExpr (resolve_expr e ctx)
    | GAType t -> GAType (resolve_type t ctx)
  in { a with arg }

and resolve_poly_type t p ctx =
  let old = ctx.local in
  let p = resolve_generic_params p ctx in
  let t = resolve_type t ctx in
  ctx.local <- old;
  TPoly (t, p)

and resolve_generic_params p ctx =
  let get_name p =
    match p.param with
    | GPConst (n, _) -> n.name
    | GPTypename n   -> n
  in
  let rec loop p acc =
    match p with
    | []           -> List.rev acc
    | head :: tail ->
      match head.param with
      | GPTypename n -> 
        if List.exists (fun p -> n = get_name p) acc then push_err (Msg ("Duplicated type parameter \"" ^ n ^ "\"")) head.span ctx
        else ctx.local <- { name = n; kind = TSKTypename; generics = []; mods = head.metadata } :: ctx.local;
        loop tail (head :: acc)
      | GPConst (n, t) -> 
        if List.exists (fun p -> n.name = get_name p) acc
        then push_err (Msg ("Duplicated type parameter \"" ^ n.name ^ "\"")) n.span ctx;
        loop tail ({ head with param = GPConst (n, resolve_type t ctx) } :: acc)
  in loop p []
   
and resolve_type_generic_params ctx = 
  let resolve_m _ (m:module_) =
    ctx.curr <- m;
    gather_local m.name ctx;
    let resolve_params s =
      let local = ctx.local in
      let generics = resolve_generic_params s.generics ctx in
      ctx.local <- local;
      { s with generics }
    in
    let resolved = List.map resolve_params (Hashtbl.find ctx.types m.name) in
    Hashtbl.replace ctx.types m.name resolved
  in Hashtbl.iter resolve_m ctx.modules


and resolve_expr e ctx =
  let expr = 
    match e.expr with
    | EVar n              -> resolve_var n e.span ctx
    | EBinOp (e1, op, e2) -> EBinOp   (resolve_expr e1 ctx, op, resolve_expr e2 ctx)
    | ELUnOp (op, e)      -> ELUnOp   (                     op, resolve_expr e  ctx)
    | ERUnOp (e, op)      -> ERUnOp   (resolve_expr e  ctx, op                     )
    | EArray exprs        -> EArray   (map resolve_expr exprs ctx)
    | ETuple exprs        -> ETuple   (map resolve_expr exprs ctx)
    | EIf (c, t, e)       -> resolve_if c t e ctx
    | ECall (t, a)        -> ECall    (resolve_expr t ctx, resolve_expr a ctx)
    | EAddress e          -> EAddress (resolve_expr e ctx)
    | EField (t, f)       -> EField   (resolve_expr t ctx, resolve_expr f ctx)
    | EIndex (t, i)       -> EIndex   (resolve_expr t ctx, resolve_expr i ctx)
    | EGeneric (t, a)     -> EGeneric (resolve_expr t ctx, map resolve_generic_arg a ctx)
    | ENew e              -> ENew     (resolve_expr e ctx)
    | EDecl (n, t, v)     -> resolve_decl   n t v e.mods ctx 
    | ELambda (p, t, b)   -> resolve_lambda p t b        ctx 
    | EReturn e           -> EReturn  (resolve_expr e ctx)
    | EPoly (t, p)        -> resolve_poly t p ctx
    | EType t             -> EType    (resolve_type t ctx)
    | EBlock stmts        -> resolve_block stmts ctx
    | ETrace e            -> ETrace   (resolve_expr e ctx)
    | _                   -> e.expr
  in { e with expr }

and resolve_var n s ctx =
  match find_var_opt n ctx.env with
  | Some _ -> EVar n
  | None   -> 
    match List.find_opt (fun s -> s.name = n) ctx.local with
    | Some s -> EType (sig_to_type s)
    | None   -> push_err (Undefined n) s ctx; EEmpty

and resolve_if c t e ctx =
  let res_c = push_env       ctx in
  let     c = resolve_expr c ctx in
  let res_t = push_env       ctx in
  let     t = resolve_expr t ctx in
  res_t();
  let     e = resolve_expr e ctx in
  res_c();
  EIf (c, t, e)

and resolve_decl n t v meta ctx =
  let is_lambda = match v.expr with ELambda _ -> true | _ -> false in
  if is_lambda then push_var n.name ctx;
  let t = resolve_type t ctx in
  let v = resolve_expr v ctx in
  if not is_lambda then push_var n.name ctx;
  EDecl (n, t, v)

and resolve_lambda p t b ctx =
  let res = push_env ctx in
  let p = resolve_params p ctx in
  let t = resolve_type t ctx in
  let b = resolve_expr b ctx in
  res();
  ELambda (p, t, b)
  
and resolve_params p ctx =
  let fold acc (p:param_info) =
    if List.exists (fun (param:param_info) -> param.name.name = p.name.name) acc then push_err (Redef_param p.name.name) p.name.span ctx;
    push_var p.name.name ctx; ({ p with typ = resolve_type p.typ ctx } :: acc)
  in List.fold_left fold [] p |> List.rev

and resolve_poly t p ctx =
  let old = ctx.local in
  let p = resolve_generic_params p ctx in
  let t = resolve_expr t ctx in
  ctx.local <- old;
  EPoly (t, p)

and resolve_block s ctx =
  let res = push_env ctx in
  let stmts = map resolve_stmt s ctx in
  res();
  EBlock stmts
  
and resolve_stmt s ctx =
  let stmt = 
    match s.stmt with
    | SExpr e -> SExpr (resolve_expr e ctx)
  in { s with stmt }
  




let resolve_item i ctx =
  let item = 
    match i.item with
    | IType t -> IType t
    | IStmt s -> IStmt (resolve_stmt s ctx)
  in { i with item }

let resolve_module m ctx =
  ctx.curr <- m;
  ctx.env <- { vars = []; parent = None };
  gather_local m.name ctx;
  let items = map resolve_item m.items ctx in
  { m with items }



let resolve main modules = 
  let types, errors = gather_types modules in
  let ctx = { modules; types; curr = (Hashtbl.find modules [main]); local = []; env = { vars = []; parent = None }; errors } in
  resolve_type_generic_params ctx;
  let resolved = Hashtbl.create 8 in
  Hashtbl.iter (fun p m -> Hashtbl.add resolved p (resolve_module m ctx)) modules;
  ctx, resolved