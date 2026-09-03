open Ast
open Span
open Error
open Debug

let (int_sig:t_sig)   = { name = "Int";     kind = TSKPrimal; mods = []; generics = [] }
let (float_sig:t_sig) = { name = "Float";   kind = TSKPrimal; mods = []; generics = [] }
let (bool_sig:t_sig)  = { name = "Bool";    kind = TSKPrimal; mods = []; generics = [] }
let (str_sig:t_sig)   = { name = "String";  kind = TSKPrimal; mods = []; generics = [] }
let (arr_sig:t_sig)   = { name = "Array";   kind = TSKPrimal; mods = []; generics = [{ param = GPTypename "T"; metadata = []; span = file_start_span }] }
let (ptr_sig:t_sig)   = { name = "Ptr";     kind = TSKPrimal; mods = []; generics = [{ param = GPTypename "T"; metadata = []; span = file_start_span }] }
let (heap_sig:t_sig)  = { name = "HeapPtr"; kind = TSKPrimal; mods = []; generics = [{ param = GPTypename "T"; metadata = []; span = file_start_span }] }
let (ref_sig:t_sig)   = { name = "Ref";     kind = TSKPrimal; mods = []; generics = [{ param = GPTypename "T"; metadata = []; span = file_start_span }] }

type resolve_env = {
  mutable vars: string list;
  parent: resolve_env option
}
type resolve_ctx = {
  modules: (path, module_   ) Hashtbl.t;
  types:   (path, t_sig list) Hashtbl.t;
  mutable curr:                 module_;
  mutable local:             t_sig list;
  mutable curr_sig:        t_sig option;
  mutable env:              resolve_env;
  mutable field_access:            bool;
  mutable errors:         err_kind list;
}
let push_err kind span ctx = 
  let err = make_err_in_module kind span ctx.curr in
  (* if not (List.mem err ctx.errors) then *) ctx.errors <- err :: ctx.errors
let map func l ctx =
  List.map (fun i -> func i ctx) l
let rec find_var_opt n env = 
  match List.find_opt ((=) n) env.vars with
  | Some v -> Some v
  | None   -> 
    match env.parent with
    | Some p -> find_var_opt n p
    | None   -> None
let push_var n ctx =
  ctx.env.vars <- n :: ctx.env.vars
let push_env ctx =
  let old = ctx.env in
  ctx.env <- { vars = []; parent = Some (ctx.env) };
  fun () -> ctx.env <- old
let ss_ctx ctx =
  let local = ctx.local    in
  let res   = push_env ctx in
  fun () -> ctx.local <- local; res()
  









let sig_to_type s = 
  match s.kind with
  | TSKClass    -> TClass    s.name
  | TSKPrimal   -> TClass    s.name
  | TSKTypename -> TTypename s.name

 
let bind_generic_args params (args:generic_arg list) name span ctx =
  let rec loop p (a:generic_arg list) (acc:generic_arg list) =
  match p, a with
  | [], []     -> List.rev acc
  | [], a :: _ -> push_err (Msg ("Too many generic arguments for "   ^ name)) a.span ctx; List.rev acc
  | _ :: _, [] -> push_err (Msg ("Not enough generic arguments for " ^ name)) (if acc = [] then span else (acc |> List.hd).span) ctx; List.rev acc
  | p :: pr, a :: ar -> 
    match p.param, a.arg with 
    | GPTypename _, GAAmb (t, _) -> loop pr ar ({ a with arg = GAType t } :: acc)
    | GPConst    _, GAAmb (_, e) -> loop pr ar ({ a with arg = GAExpr e } :: acc)
    | GPTypename _, GAType _     -> loop pr ar (a :: acc)
    | GPConst    _, GAExpr _     -> loop pr ar (a :: acc)
    | GPConst    _, GAType _     -> push_err (Expected "expression") a.span ctx; loop pr ar acc
    | GPTypename _, GAExpr _     -> push_err (Expected "type"      ) a.span ctx; loop pr ar acc
  in loop params args []

let get_generic_param_name p =
  match p.param with
  | GPConst (n, _) -> n
  | GPTypename n   -> { name = n; span = p.span }

let check_param_name (n:placed_name) names ctx =
  if List.mem n.name names then (push_err (Redef_param n.name) n.span ctx; false) else true



let gather_types modules =
  let types = Hashtbl.create 8 in
  let err   = ref []           in
  let to_sig (i:item) t = 
    match t.decl with
    | DClass info -> { name = t.name.name; kind = TSKClass; generics = info.generics; mods = i.mods }
  in
  let gather _ m = 
    let fold acc i =
      match i.item with
      | IDecl t -> if List.exists (fun s -> s.name = t.name.name) acc then (err := make_err_in_module (Redef_type (t.name.name)) t.name.span m :: !err; acc) else to_sig i t :: acc
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
  | TName    (n, s) -> resolve_type_name n s true ctx
  | TPath (p, t, _) -> resolve_type_path p t ctx (* TODO: implement the same fix on TName for generics *)
  | TNamed   (n, t) -> TNamed   (n, resolve_type t ctx)
  | TDefault (t, e) -> TDefault (resolve_type t ctx, resolve_expr e ctx)
  | TTuple types    -> resolve_tuple types ctx
  | TArray t        -> TArray   (resolve_type t ctx) (* TODO: produce a normal type *)
  | TPtr   t        -> TPtr     (resolve_type t ctx) (* TODO: produce a normal type *)
  | TGeneric (t, a) -> resolve_generic_type t a ctx
  | TPoly    (t, p) -> resolve_poly_type    t p ctx
  | TFunc    (a, r) -> TFunc    (resolve_type a ctx, resolve_type r ctx)
  | _               -> t

and resolve_type_name n span check_generics ctx =
  match n with
  | "This" -> resolve_this span ctx
  | _ ->
    match List.find_opt (fun s -> s.name = n) ctx.local with
    | Some s -> if check_generics && s.generics <> [] then (push_err (Msg ("Not enough type parameters for type \"" ^ s.name ^ "\"")) span ctx; TUnknown) else sig_to_type s
    | None   -> push_err (Undefined_type n) span ctx; TUnknown

and resolve_this span ctx =
  match ctx.curr_sig with
  | Some s -> 
    let typ = sig_to_type s in begin
    match s.generics with
    | [] -> typ
    | _  ->
      let rec get_generic_args params acc = 
        match params with 
        | []           -> List.rev acc
        | head :: tail -> 
          match head.param with
          | GPConst (n, _) -> get_generic_args tail ({ arg = GAExpr { expr = EVar n.name; mods = []; span }; metadata = []; span } :: acc)
          | GPTypename n   -> get_generic_args tail ({ arg = GAType (TTypename n);                           metadata = []; span } :: acc)
      in TGeneric (typ, get_generic_args s.generics [])
    end
  | None   -> push_err (Msg "Cannot use type \"This\" outside of a class") span ctx; TUnknown

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

and resolve_tuple types ctx =
  let rec loop t names acc =
    match t with
    | [] -> List.rev acc
    | head :: tail ->
      match head with
      | TNamed (n, t) ->
        if check_param_name n names ctx then loop tail (n.name :: names) (resolve_type head ctx :: acc)
        else loop tail names (resolve_type t    ctx :: acc)
      | _ -> loop tail names (resolve_type head ctx :: acc)
  in TTuple (loop types [] [])

and resolve_generic_type t a ctx =
  let rec check t =
    match t with
    | TName (n,    s) -> resolve_type_name n s false ctx, n, Some s
    | TPath (p, t, s) -> let t = resolve_type_path p t ctx in let n, s = (match t with TName (n, s) -> n, s | _ -> assert false) in t, n, Some s
    | TNamed   (_, t) -> check t
    | TDefault (t, _) -> check t
    | TTuple   _      -> push_err (Msg "Tuples cannot take type parameters")             (List.hd a).span ctx; TUnknown, "", None
    | TArray   _      -> push_err (Msg "Arrays cannot take type parameters")             (List.hd a).span ctx; TUnknown, "", None
    | TPtr     _      -> push_err (Msg "Pointers cannot take type parameters")           (List.hd a).span ctx; TUnknown, "", None
    | TGeneric _      -> push_err (Msg "Double generic type parameters are not allowed") (List.hd a).span ctx; TUnknown, "", None
    | TFunc    _      -> push_err (Msg "Function types cannot take type parameters")     (List.hd a).span ctx; TUnknown, "", None
    | TUnit           -> push_err (Msg "Unit type cannot take type parameters")          (List.hd a).span ctx; TUnknown, "", None
    | _               -> assert false (* impossible to reach *)
  in 
  let t, n, span = check t in
  match t with
  | TUnknown -> TUnknown
  | _        ->
    let s    = List.find (fun s -> s.name = n) ctx.local in  (* TODO: match for path types *)
    let args = bind_generic_args s.generics a ("type \"" ^ n ^ "\"") (Option.get span) ctx in
    TGeneric (t, map resolve_generic_arg args ctx)

and resolve_generic_arg a ctx = 
  let old = ctx.field_access in
  ctx.field_access <- false;
  let arg = 
    match a.arg with
    | GAExpr e ->
      let e = resolve_expr e ctx in
      (match e.expr with
      | EType _ -> push_err (Expected "expression") e.span ctx;
      | _       -> ());
      GAExpr e
    | GAType t -> GAType (resolve_type t ctx)
    | GAAmb  _ -> a.arg
  in
  ctx.field_access <- old;
  { a with arg }

and resolve_poly_type t p ctx =
  let res = ss_ctx ctx in
  let p = resolve_generic_params p ctx in
  let t = resolve_type t ctx in
  res();
  TPoly (t, p)

and resolve_generic_params p ctx =
  let rec check p acc names =
    match p with
    | []           -> acc (* gets reversed in loop *)
    | head :: tail -> 
      let n = get_generic_param_name head in
      if List.mem n.name names then (push_err (Msg ("Duplicated type parameter \"" ^ n.name ^ "\"")) n.span ctx; check tail acc names)
      else check tail (head :: acc) (n.name :: names)
  in
  let rec loop p acc =
    match p with
    | []           -> acc 
    | head :: tail ->
      match head.param with
      | GPTypename n -> (* input already reversed *)
        ctx.local <- { name = n; kind = TSKTypename; generics = []; mods = head.metadata } :: ctx.local; loop tail (head :: acc)
      | GPConst (n, t) -> 
        push_var n.name ctx; loop tail ({ head with param = GPConst (n, resolve_type t ctx) } :: acc)
  in loop (check p [] []) []
   
and resolve_type_generic_params ctx = 
  let resolve_m _ (m:module_) =
    ctx.curr <- m;
    gather_local m.name ctx;
    let resolve_params s =
      let rec check p acc =
        match p with
        | []           -> List.rev acc
        | head :: tail ->
          let n = get_generic_param_name head in
          if s.name = n.name then (push_err (Msg "Cannot use the same name as the type for a generic parameter") n.span ctx; check tail acc)
          else check tail (head :: acc)
        in
      let res = ss_ctx ctx in
      let generics = check (resolve_generic_params s.generics ctx) [] in
      res();
      { s with generics }
    in
    let resolved = List.map resolve_params (Hashtbl.find ctx.types m.name) in
    Hashtbl.replace ctx.types m.name resolved
  in
  Hashtbl.iter resolve_m ctx.modules


and resolve_expr e ctx =
  let expr = 
    match e.expr with
    | EVar n              -> resolve_var n e.span ctx
    | EBinOp (e1, op, e2) ->
      let e1 = resolve_expr e1 ctx in (* manual assignment needed because of OCaml's undefined evaluation order *)
      let e2 = resolve_expr e2 ctx in
      EBinOp   (e1, op, e2)
    | ELUnOp (op, e)      -> ELUnOp (op, resolve_expr e ctx) (* constructors with only a single argument that needs resolving are safe to inline *)
    | ERUnOp (e, op)      -> ERUnOp (resolve_expr e ctx, op)
    | EArray exprs        -> EArray (map resolve_expr exprs ctx)
    | ETuple exprs        -> ETuple (map resolve_expr exprs ctx)
    | EIf (c, t, e)       -> resolve_if c t e ctx
    | ECall (t, a)        -> 
      let t = resolve_expr t ctx in
      let a = resolve_expr_with false a ctx in 
      ECall (t, a)
    | EAddress e          -> EAddress (resolve_expr e ctx)
    | EField (t, f)       ->
      let t = resolve_expr t ctx in 
      let f = resolve_expr_with true f ctx in
      EField (t, f)
    | EIndex (t, i)       ->
      let t = resolve_expr t ctx in
      let i = resolve_expr_with false i ctx in
      EIndex (t, i)
    | EGeneric (t, a)     -> 
      let t = resolve_expr            t ctx in
      let a = map resolve_generic_arg a ctx in
      EGeneric (t, a)
    | ENew e              -> ENew (resolve_expr e ctx)
    | EDecl (n, t, v)     -> resolve_decl n t v ctx 
    | ELambda (p, t, b)   -> resolve_lambda p t b [] ctx 
    | EReturn e           -> EReturn (resolve_expr e ctx)
    | EPoly (t, p)        -> resolve_poly t p ctx
    | EType t             -> EType   (resolve_type t ctx)
    | EBlock stmts        -> resolve_block stmts ctx
    | ETrace e            -> ETrace  (resolve_expr e ctx)
    | _                   -> e.expr
  in { e with expr }

and resolve_expr_with field_access e ctx =
  let old = ctx.field_access in
  ctx.field_access <- field_access;
  let expr = resolve_expr e ctx in
  ctx.field_access <- old;
  expr

and resolve_var n s ctx =
  if ctx.field_access then EVar n else
  match find_var_opt n ctx.env with
  | Some _ -> EVar n
  | None   -> 
    match List.find_opt (fun s -> s.name = n) ctx.local with
    | Some s -> EType (sig_to_type s)
    | None   -> push_err (Undefined n) s ctx; EEmpty

and resolve_if c t e ctx =
  let res_c = push_env                  ctx in
  let     c = resolve_expr_with false c ctx in
  let res_t = push_env                  ctx in
  let     t = resolve_expr t            ctx in
  res_t();            
  let     e = resolve_expr e            ctx in
  res_c();
  EIf (c, t, e)


and resolve_decl n t v ctx =
  let is_lambda = match v.expr with ELambda _ -> true | _ -> false in
  if is_lambda then push_var n.name ctx;
  let t = resolve_type t ctx in
  let v = resolve_expr v ctx in
  if not is_lambda then push_var n.name ctx;
  EDecl (n, t, v)

and resolve_lambda p t b g ctx =
  let res = push_env           ctx in
  let p   = resolve_params p g ctx in
  let t   = resolve_type   t   ctx in
  let b   = resolve_expr   b   ctx in
  res();
  ELambda (p, t, b)
  
and resolve_params p g ctx =
  let g = 
    let rec get_consts params acc =
      match params with
      | []                                    -> List.rev acc
      | { param = GPConst (n, _); _ } :: rest -> get_consts rest (n.name :: acc)
      | _                             :: rest -> get_consts rest acc
    in get_consts g []
  in
  let fold acc (p:param_info) =
    if List.exists (fun (param:param_info) -> param.name.name = p.name.name) acc || List.exists ((=) p.name.name) g then push_err (Redef_param p.name.name) p.name.span ctx;
    push_var p.name.name ctx; ({ p with typ = resolve_type p.typ ctx } :: acc)
  in List.fold_left fold [] p |> List.rev

and resolve_poly t p ctx =
  let res = ss_ctx ctx in
  let p = resolve_generic_params p ctx in
  let rec check p acc name =
    match p with
    | []           -> List.rev acc
    | head :: tail ->
      let n = get_generic_param_name head in
      if  n.name = name then push_err (Msg "Cannot use the same name as the type for a generic parameter") n.span ctx;
      check tail acc name
    in
  let t, p = 
    match t.expr with
    | EDecl   (n,   typ, v) -> { t with expr = resolve_decl n     typ   v ctx}, check p [] n.name
    | ELambda (par, typ, b) -> { t with expr = resolve_lambda par typ b p ctx }, p
    | _                     -> resolve_expr t ctx, p
  in
  res();
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
  
let resolve_class_field (info:class_field_info) member ctx =
  let old = ctx.local in
  let generics = resolve_generic_params info.generics ctx in
  let typ      = resolve_type           info.typ      ctx in
  let default     = resolve_expr        info.default  ctx in
  ctx.local <- old;
  CMField { info with generics; typ; default }

let resolve_class_constructor (info:class_method_info) (member:class_member) ctx =
  if info.generics <> []       then push_err (Msg "Generic constructors are not allowed") (info.generics |> List.hd).span ctx;
  if info.typ      <> TUnknown then push_err (Msg "Explicit return type on constructors is not allowed") member.span ctx;
  let env = ctx.env in
  let params   = resolve_params info.params [] ctx in
  let body     = resolve_expr   info.body      ctx in
  ctx.env <- env;
  CMNew { body; params }

let resolve_class_method (info:class_method_info) member ctx =
  match info.name.name with
  | s when s = (Option.get ctx.curr_sig).name -> resolve_class_constructor info member ctx
  | _ ->
    let res = ss_ctx ctx in
    let generics = resolve_generic_params info.generics        ctx in
    let typ      = resolve_type           info.typ             ctx in
    let params   = resolve_params         info.params generics ctx in
    let body     = resolve_expr           info.body            ctx in
    res();
    CMMethod { info with generics; typ; params; body }

let resolve_class_member m ctx =
  let member = 
    match m.member with
    | CMField  info -> resolve_class_field  info m ctx
    | CMMethod info -> resolve_class_method info m ctx
    | _             -> assert false (* constructors are not yet in the stream *)
  in { m with member }

let gather_class_env name (members:class_member list) ctx =
  ctx.curr_sig <- Some (List.find (fun s -> s.name = name) ctx.local);
  let fold acc m = 
    match m.member with
    | CMField  info ->
      if List.exists ((=) info.name.name) acc then (push_err (Redef ("field " ^ info.name.name)) info.name.span ctx; acc)
      else info.name.name :: acc
    | CMMethod info -> if List.exists ((=) info.name.name) acc then (push_err (Redef ("method " ^ info.name.name)) info.name.span ctx; acc)
      else info.name.name :: acc
    | CMNew    _    -> acc
  in ctx.env <- { parent = None; vars = List.fold_left fold [] members |> List.rev }

let resolve_class info (t:decl_info) ctx =
  gather_class_env t.name.name info.members ctx;
  let old      = ctx.local in
  let generics = resolve_generic_params   info.generics ctx in
  let members  = map resolve_class_member info.members  ctx in
  ctx.local <- old;
  DClass { members; generics }

let resolve_type_decl t i ctx =
  let decl = 
    match t.decl with
    | DClass info -> (resolve_class info t ctx)
  in IDecl { t with decl }


let resolve_item i ctx =
  let item = 
    match i.item with
    | IDecl t -> resolve_type_decl t i ctx
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
  let ctx = { modules; types; curr = (Hashtbl.find modules [main]); local = []; curr_sig = None; env = { vars = []; parent = None }; field_access = false; errors } in
  resolve_type_generic_params ctx;
  let resolved = Hashtbl.create 8 in
  Hashtbl.iter (fun p m -> Hashtbl.add resolved p (resolve_module m ctx)) modules;
  ctx, resolved