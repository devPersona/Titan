open Ast
open Span
open Error
open Debug

type resolve_ctx = {
  modules: (path, module_) Hashtbl.t;
  types:   (path, t list ) Hashtbl.t;
  mutable curr: module_;
  mutable local: t list;
  mutable errors: err_kind list;
}

let rec name_of_type t =
  match t with
  | TPoly (t, _) -> name_of_type t
  | TPath (_, t, _) -> name_of_type t
  | TClass name  -> name
  | _            -> assert false
let rec type_exists_name name types = 
    match types with
    | []           -> false
    | head :: tail -> name_of_type head = name || type_exists_name name tail
let type_exists t types =
  type_exists_name (name_of_type t) types
let get_type_name name types = 
  List.find (fun t -> name_of_type t = name) types
let get_type t types = 
  get_type_name (name_of_type t) types







let gather_types modules =
  let types = Hashtbl.create 8 in
  let err = ref [] in
  let gather _ (m:module_) =
    let rec loop i acc =
      match i with
      | []                              -> Hashtbl.add types m.name (List.rev acc)
      | {item = IClass info; _} :: rest ->
        if type_exists_name info.name.name acc then (err := (make_err_in_module (Redef_type info.name.name) info.name.span m) :: !err; loop rest acc)
        else loop rest (TClass info.name.name :: acc)
      | _                       :: rest -> loop rest acc
    in loop m.items []
  in
  Hashtbl.iter gather modules;
  types, !err

let push_locals path ctx =
  let rec loop t acc =
    match t with
    | []           -> List.rev acc
    | head :: tail -> let t = if not (type_exists head ctx.local) then (head :: acc) else acc in loop tail t
  in ctx.local <- ctx.local @ loop (Hashtbl.find ctx.types path) []

let gather_local path ctx =
  ctx.local <- Hashtbl.find ctx.types path;
  let rec loop i =
    match i with
    | []           -> ()
    | head :: tail -> push_locals head.path ctx; loop tail
  in loop (Hashtbl.find ctx.modules path).imports

let push_err kind span ctx =
  ctx.errors <- (make_err_in_module kind span ctx.curr) :: ctx.errors





let map f l ctx = List.map (fun i -> f i ctx) l
 
(* and expr_def =
| EVar     of string
| EPoly    of expr * generic_param list *)

let rec resolve_type t ctx =
  match t with
  | TName    (n, s) -> resolve_type_name n   s ctx
  | TPath (p, t, s) -> resolve_path_type p t s ctx
  | TNamed   (n, t) -> TNamed   (n, resolve_type t ctx)
  | TDefault (t, e) -> TDefault (resolve_type t ctx, resolve_expr e ctx)
  | TTuple   types  -> TTuple   (map resolve_type types ctx)
  | TArray   t      -> TArray   (resolve_type t ctx)
  | TPtr     t      -> TPtr     (resolve_type t ctx)
  | TGeneric (t, g) -> TGeneric (resolve_type t ctx, map resolve_generic_arg g ctx)
  | TFunc    (a, r) -> TFunc    (resolve_type a ctx, resolve_type r ctx)
  | _               -> t

and resolve_type_name n s ctx = 
  if not (type_exists_name n ctx.local) then (push_err (Msg ("Undefined type: \"" ^ n ^ "\"")) s ctx; TUnknown) else get_type_name n ctx.local

and resolve_path_type path t s ctx =
  let types = Hashtbl.find ctx.types path in
  if not (type_exists t types) then (push_err (Msg ("Undefined type \"" ^ name_of_type t ^ "\" in module " ^ String.concat "::" ctx.curr.name)) s ctx; TUnknown)
  else TPath (path, get_type t types, s)

and resolve_expr e ctx =
  let expr = 
    match e.expr with
    | EBinOp (e1, op, e2) -> EBinOp   (resolve_expr e1 ctx, op,                 resolve_expr e2 ctx)
    | ELUnOp (    op, e ) -> ELUnOp   (                     op,                 resolve_expr e  ctx)
    | ERUnOp (e,  op    ) -> ERUnOp   (resolve_expr e  ctx, op                                     )
    | EArray exprs        -> EArray   (map resolve_expr exprs ctx                                  )
    | ETuple exprs        -> ETuple   (map resolve_expr exprs ctx                                  )
    | EIf    (c,  t,  e ) -> EIf      (resolve_expr c  ctx, resolve_expr t ctx, resolve_expr e  ctx)
    | ECall  (t,  a     ) -> ECall    (resolve_expr t  ctx, resolve_expr a ctx                     )
    | EAddress e          -> EAddress (resolve_expr e  ctx                                         )
    | EField (t,  a     ) -> EField   (resolve_expr t  ctx, resolve_expr a ctx                     )
    | EIndex (t,  i     ) -> EField   (resolve_expr t  ctx, resolve_expr i ctx                     )
    | EGeneric   (t,   a) -> EGeneric (resolve_expr t  ctx, map resolve_generic_arg a ctx          )
    | ENew    e           -> ENew     (resolve_expr e  ctx                                         )
    | EDecl  (n,  t,  v ) -> EDecl    (n, resolve_type t ctx, resolve_expr v ctx                   )
    | ELambda (p, t,  v ) -> ELambda  (map resolve_param p ctx, resolve_type t ctx, resolve_expr v ctx)
    | EReturn e           -> EReturn  (resolve_expr e  ctx                                         )
    | EType   t           -> EType    (resolve_type t ctx                                          )
    | EBlock  stmts       -> EBlock   (map resolve_stmt stmts ctx                                  )
    | ETrace  e           -> ETrace   (resolve_expr e  ctx                                         )
    | _                   -> e.expr
  in { e with expr }

and resolve_generic_arg a ctx =
  let arg = 
    match a.arg with 
    | GAExpr e -> GAExpr (resolve_expr e ctx)
    | GAType t -> GAType (resolve_type t ctx)
  in { a with arg }

and resolve_param p ctx =
  let (n, t) = p.param in
  { p with param = (n, resolve_type t ctx) }

and resolve_stmt s ctx =
  let stmt = 
    match s.stmt with
    | SExpr e -> SExpr (resolve_expr e ctx)
  in { s with stmt }

let resolve_item i ctx =
  let item = 
    match i.item with
    | IStmt stmt -> IStmt (resolve_stmt stmt ctx)
    | _          -> failwith "Later"
  in { i with item }

let resolve_module m ctx =
  ctx.curr <- m;
  let items = map resolve_item m.items ctx in
  { m with items }


let resolve main modules = 
  let types, errors = gather_types modules in
  let ctx = { modules; types; local = []; curr = (Hashtbl.find modules main); errors } in 
  let rec loop t =
    match t with
    | [] -> () 
    | head :: tail -> debug_type head |> print_endline; loop tail
  in loop ctx.local;
  if ctx.errors <> [] then err_list ctx.errors