open Ast
open Error
open Prim

let score_nttp      = 2
let score_typename  = 1
let score_bonus     = 1
let score_generic   = score_bonus
let score_tuple     = score_bonus
let score_func      = score_bonus


let map func i ctx = List.map (fun i -> func i ctx) i

let push_type id (name:placed_name) params kind ctx = 
  Hashtbl.add ctx.types id { id; name = name.name; m_path = ctx.curr.name; decl_span = name.span; params; kind }
let push_local id ctx = 
  ctx.local <- Hashtbl.find ctx.types id :: ctx.local
let push_locals l ctx = 
  ctx.local <- l @ ctx.local
let get_env_depth ctx =
  let rec loop env depth =
    match env.parent with
    | Some p -> loop p (depth + 1)
    | None   -> depth
  in loop ctx.env 0
let push_env_raw ctx = 
  ctx.env <- { vars = []; parent = Some ctx.env }
let push_env ctx =
  push_env_raw ctx;
  fun () -> ctx.env <- (ctx.env.parent) |> Option.get
let push_var n ctx =
  ctx.env.vars <- n :: ctx.env.vars
let push_err kind span ctx =
  ctx.errors <- (make_err_in_module kind span ctx.curr) :: ctx.errors


let replace_sig s ctx =
  Hashtbl.replace ctx.types s.id s;
  Hashtbl.replace ctx.decls s.m_path (List.map (fun i -> if i.id = s.id then s else i) (Hashtbl.find ctx.decls s.m_path)) 

let snapshot_ctx ctx = 
  let local  = ctx.local in
  let env = push_env ctx in
  fun () -> ctx.local <- local; env()

let push_type_params params ctx =
  let rec loop p =
    match p with
    | [] -> ()
    | head :: tail ->
      let rec push_param p =
        match p.param with
        | GPTypename id    -> if not (List.exists (fun s -> s.id = id) ctx.local) then push_local id ctx
        | GPConst   (n, _) -> push_var n.name ctx
        | GPGeneric (p, a) -> push_param p; loop a
        | GPTuple    ps    -> loop ps
        | GPFunc    (a, r) -> push_param a; push_param r
        | _                -> assert false
      in push_param head; loop tail
  in let res = snapshot_ctx ctx in loop params; res

let type_exists name ctx = List.exists (fun s -> s.name = name) ctx.local
let var_exists  name ctx =
  let rec find env = 
    match List.find_opt ((=) name) env.vars with
    | Some _ -> true
    | None   ->
      match env.parent with
      | Some p -> find p
      | None   -> false
  in find ctx.env



let view_params params = 
  let rec loop p acc =
    match p with
    | []           -> List.rev acc
    | head :: tail -> 
      match head.param with
      | GPConst _ -> loop tail (PVConst :: acc)
      | _         -> loop tail (PVType  :: acc)
  in loop params []




let rec is_type t ctx = 
  match t with
  | TName    (n, _) -> type_exists n ctx
  | TDefault (t, _) -> is_type t ctx
  | TGeneric (t, _) -> is_type t ctx
  | TTuple types    -> List.for_all (fun t -> is_type t ctx) types
  | _               -> assert false (* unreachable for current use *)
let rec is_expr e ctx =
  match e.expr with
  | EVar      n     -> var_exists n ctx
  | EGeneric (e, _) -> is_expr e ctx
  | ETuple    exprs -> List.for_all (fun e -> is_expr e ctx) exprs
  | _               -> assert false (* unreachable for current use *)
let disambiguate a ctx =
  let rec loop (a:generic_arg list) acc =
    match a with
    | [] -> List.rev acc
    | head :: tail ->
      match head.arg with
      | GAAmb (t, e) ->
        let is_type = is_type t ctx in
        let is_expr = is_expr e ctx in
        if is_type = is_expr then loop tail (head :: acc) (* let error be handled later *)
        else if is_type      then loop tail ({ head with arg = GAType t } :: acc)
        else                      loop tail ({ head with arg = GAExpr e } :: acc)
      | _ -> loop tail (head :: acc)
  in loop a []

let rec get_score p a =
  match p.param, a with
  | GPConst          _, (GAExpr _                   | GAAmb _)                      -> score_nttp
  | GPTypename       _, (GAType _                   | GAAmb _)                      -> score_typename
  | GPFunc    (pa, pr), (GAType (TFunc (ta, tr))    | GAAmb (TFunc (ta, tr),    _)) -> 
         let s1 = get_score pa (GAType ta) in if s1 = 0 then 0
    else let s2 = get_score pr (GAType tr) in if s2 = 0 then 0
    else s1 + s2 + score_func
  | GPTuple         ps, (GAType (TTuple ts)         | GAAmb (TTuple ts,         _)) -> (* impossible for tuple to be empty *)
    let s = get_inner ps (List.map (fun t -> GAType t) ts) 0 in if s = 0 then 0
    else s + score_tuple
  | GPGeneric (pt, pa), (GAType (TGeneric (tt, ta)) | GAAmb (TGeneric (tt, ta), _)) -> (* impossible to have no args *)
         let s1 = get_score pt (GAType tt) in if s1 = 0 then 0
    else let s2 = get_inner pa (List.map (fun (a:generic_arg) -> a.arg) ta) 0 in if s2 = 0 then 0
    else s1 + s2 + score_generic
  | _ -> 0
and get_inner params args score =
  match params, args with
  | [],      []      -> score
  | p :: pr, a :: ar -> let s = get_score p a in if s = 0 then 0 else get_inner pr ar (s + score)
  | _                -> 0

let rec bind_score params args acc =
  match params, (args:generic_arg list) with
  | [], []           -> List.rev acc
  | p :: pr, a :: ar -> bind_score pr ar (get_score p a.arg :: acc)
  | _                -> assert false
let sum_scores scores = List.fold_left (fun acc s -> acc + s) 0 scores
let rec get_max_score pairs max =
  match pairs with
  | [] -> max
  | (_, scores) :: tail -> let sum = sum_scores scores in get_max_score tail (if sum > max then sum else max)

let rec same_type_base t1 t2 allow_nttp = (* TODO: normalize alias types *)
  match t1, t2 with
  | TUnknown, _       | _, TUnknown      -> true (* errored type *)
  | TNamed   (_,  t1), _                 -> same_type_base t1 t2 allow_nttp
  | TDefault (t1,  _), _                 -> same_type_base t1 t2 allow_nttp
  | _,                 TNamed   (_,  t2) -> same_type_base t1 t2 allow_nttp
  | _,                 TDefault (t2,  _) -> same_type_base t1 t2 allow_nttp
  | TTuple ts1,        TTuple    ts2     -> List.length ts1 = List.length ts2 && List.for_all2 (fun t1 t2 -> same_type_base t1 t2 allow_nttp) ts1 ts2
  | TFunc    (a1, r1), TFunc    (a2, r2) -> same_type_base a1 a2 allow_nttp && same_type_base r1 r2 allow_nttp
  | TGeneric (t1, a1), TGeneric (t2, a2) -> same_type_base t1 t2 allow_nttp && List.length a1 = List.length a2 && List.for_all2 (fun t1 t2 -> same_generic_arg t1 t2 allow_nttp) a1 a2
  | _                                    -> t1 = t2
and same_generic_arg a1 (a2:generic_arg) allow_nttp =
  match a1.arg, a2.arg with
  | GAExpr _,  GAExpr _  -> allow_nttp (* typechecker decides *)
  | GAType t1, GAType t2 -> same_type_base t1 t2 allow_nttp
  | _                    -> allow_nttp

let same_type        t1 t2 = same_type_base t1 t2 true
let same_type_strict t1 t2 = same_type_base t1 t2 false

let get_typenames params = List.filter    (fun p                   -> match p.param with GPConst _               -> false    | _ -> true) params
let get_types     args   = List.fold_left (fun acc (a:generic_arg) -> match a.arg   with GAType t | GAAmb (t, _) -> t :: acc | _ -> acc) [] args |> List.rev

let rec same_layout params =
  match params with
  | [] | [_] -> true
  | head :: (mid :: _ as tail) ->
    let rec check p1 p2 =
      match p1.param, p2.param with
      | GPConst    _,       GPConst _          -> same_layout tail
      | GPConst    _,    _ | _, GPConst    _   -> false
      | GPTypename _,    _ | _, GPTypename _   -> same_layout tail
      | GPGeneric (_, ps1), GPGeneric (_, ps2) -> List.length ps1 = List.length ps2 && List.for_all2 check ps1 ps2 && same_layout tail
      | GPTuple   ps1,      GPTuple   ps2      -> List.length ps1 = List.length ps2 && List.for_all2 check ps1 ps2 && same_layout tail
      | GPFunc    (a1, r1), GPFunc    (a2, r2) -> check a1 a2 && check r1 r2 && same_layout tail
      | _                                      -> assert false
    in check head mid

let rec transpose map lists =
  let rec loop lists = 
    match lists with
    | [] | [] :: _ -> []
    | _            -> (List.map List.hd lists) :: loop (List.map List.tl lists)
  in loop (List.map map lists)

let rec nttp_mismatch p =
  match p with
  | []           -> false
  | head :: tail ->
    let rec check ps =
      match List.hd ps with
      | GPTypename _ -> nttp_mismatch tail
      | GPConst    _ -> 
        let rec loop p = 
          match p with
          | [] | [_]                                          -> false
          | GPConst (_, t1) :: (GPConst (_, t2) :: _ as tail) -> not (same_type_strict t1 t2) || loop tail
          | _                                                 -> assert false (* impossible *)
        in loop ps || nttp_mismatch tail
      | GPTuple _ ->
        let params = transpose (fun p -> match p with GPTuple ps -> ps | _ -> assert false) ps in
        nttp_mismatch params || nttp_mismatch tail
      | GPFunc _ ->
        let args = transpose (fun p -> match p with GPFunc (a, r) -> [a; r] | _ -> assert false) ps in
        nttp_mismatch args || nttp_mismatch tail
      | GPGeneric _ ->
        let args = transpose (fun p -> match p with GPGeneric (_, a) -> a | _ -> assert false) ps in
        nttp_mismatch args || nttp_mismatch tail
      | _ -> assert false (* unreachable *)
    in check (List.map (fun p -> p.param) head)







let gather_types modules =
  let types = Hashtbl.create 8 in
  let decls = Hashtbl.create 8 in
  let gather _ (m:module_) =
    let std = m.name = std_name in
    let rec loop i acc =
      match i with 
      | [] -> List.rev acc
      | head :: tail ->
        match head.item with
        | IStmt _ -> loop tail acc
        | IDecl t -> 
          let name = t.name.name in
          let id = if std then get_std_id name else new_id() in
          let kind, params = 
            match t.decl with
            | DClass info -> TSKClass,             info.generics
            | DAlias info -> TSKAlias info.target, info.generics
          in let s = { id; name; m_path = m.name; decl_span = t.name.span; params; kind; } in
          Hashtbl.add types id s;
          loop tail (s :: acc)
    in let sigs = loop m.items [] in
    Hashtbl.add decls m.name sigs
  in Hashtbl.iter gather modules;
  types, decls

let gather_local m ctx =
  ctx.curr  <- m;
  ctx.local <- Hashtbl.find ctx.decls std_name;
  if m.name <> std_name then ctx.local <- Hashtbl.find ctx.decls m.name @ ctx.local;
  List.iter (fun (i:import) -> push_locals (Hashtbl.find ctx.decls i.path) ctx) m.imports



let rec resolve_type t ctx =
  match t with
  | TName    (n, s) -> resolve_type_name n s ctx
  | TNamed   (n, t) -> TNamed (n, resolve_type t ctx)
  | TDefault (t, e) -> TDefault (resolve_type t ctx, resolve_expr e ctx)
  | TTuple   types  -> TTuple (map resolve_type types ctx)
  | TGeneric (t, a) -> resolve_generic_type_args t a ctx
  | TFunc    (a, r) -> TFunc (resolve_type a ctx, resolve_type r ctx)
  | _               -> t (* already resolved *)

and resolve_type_name n s ctx = (* TODO: correctly resolve "Self" type within classes *)
  let matching = List.find_all (fun s -> s.name = n) ctx.local in
  if  matching = [] then (push_err (Undefined_type n) s ctx; TUnknown) else
  match List.filter (fun s -> s.params = []) matching with
  | [{ id; kind = TSKParam (PSKTypename) }] -> TID id
  | [s]                                     -> TID s.id
  | []                                      -> push_err (Msg ("Too few arguments for type " ^ wrap n)) s ctx; TUnknown
  | _                                       -> push_err (Msg ("Ambiguous type " ^ wrap n)) s ctx; TUnknown


and resolve_generic_type_args t a ctx =
  let a    = disambiguate a ctx in
  let seen = Hashtbl.create 4   in
  let rec bind params (args:generic_arg list) acc scores =
    let rec check p t =
      match p.param, t with
      | _, TUnknown -> 0 (* errorred type *)
      | GPTypename id, _ -> begin
        match Hashtbl.find_opt seen id with
        | Some typ -> if not (same_type t typ) then 0 else 2
        | None     -> Hashtbl.add seen id t; 1
      end
      | GPGeneric (pt, pp), TGeneric (tt, ta) ->
        let s = check pt tt in if s = 0 then 0
        else let scores = List.map2 check (get_typenames pp) (get_types ta) in if List.mem 0 scores then 0 else
        sum_scores scores
      | GPTuple ps,      TTuple ts      -> let scores = List.map2 check ps ts in if List.mem 0 scores then 0 else 1
      | GPFunc (pa, pr), TFunc (ta, tr) ->
             let s1 = check pa ta in if s1 = 0 then 0
        else let s2 = check pr tr in if s2 = 0 then 0
        else s1 + s2
      | _ -> assert false (* unreachable for now *)
    in
    match params, args with
    | [],      []      -> List.rev acc, sum_scores scores
    | p :: pr, a :: ar -> begin
      match p.param, a.arg with
      | GPConst     _, (GAExpr e | GAAmb (_, e)) -> bind pr ar ({ a with arg = GAExpr (resolve_expr e ctx) } :: acc) (1 :: scores)
      | _,             (GAType t | GAAmb (t, _)) ->
        let t = resolve_type t ctx in
        let s = check p t in if s = 0 then [], 0
        else bind pr ar ({ a with arg = GAType t } :: acc) (s :: scores)
      | _ -> assert false (* not implemented yet *)
    end
    | _ -> assert false (* impossible *)
  in
  let matching, name, span = 
    match t with
    | TName (n, s) -> begin
      match List.find_all (fun s -> s.name = n) ctx.local with
      | []   -> (push_err (Undefined_type n) s ctx; [], n, s)
      | sigs -> sigs, n, s
    end
    | _ -> assert false (* impossible *)
  in
  if matching = [] then TUnknown else
  if List.length matching = 1 && (List.hd matching).params = [] then (push_err (Msg ("Too many arguments for type " ^ name)) span ctx; TUnknown) else
  let same_len = List.filter (fun s -> List.length s.params = List.length a) matching in
  let scores   = same_len |> List.map (fun s -> bind_score s.params a []) |> List.combine same_len |> List.filter (fun (_, s) -> not (List.mem 0 s)) in
  let max      = get_max_score scores 0 in
  match scores |> List.filter (fun (_, s) -> sum_scores s = max) with
  | [(s, _)] ->
    let args, _ = bind s.params a [] [] in
    if args = [] then (push_err (Msg ("No matching overload for generic arguments for type " ^ name)) span ctx; TUnknown) else
    if List.exists (fun (a:generic_arg) -> match a.arg with GAType TUnknown | GAExpr { expr = EEmpty } -> true | _ -> false) args then TUnknown
    else TGeneric (TID s.id, args)
  | []   -> push_err (Msg ("No matching overload for generic arguments for type " ^ name)) span ctx; TUnknown
  | sigs ->
    let sigs = List.map (fun (s, _) -> s) sigs in
    let args_scores = sigs |> List.map (fun s -> let results = bind s.params a [] [] in Hashtbl.reset seen; results) |> List.combine sigs |> List.map (fun (a, (b, c)) -> ((a, b), c)) in
    match args_scores |> List.filter (fun (_, s) -> s <> 0) with
    | [] -> push_err (Msg ("No matching overload for generic arguments for type " ^ name)) span ctx; TUnknown
    | sigs -> 
      let max = let rec get_max s max = match s with [] -> max | (_, s) :: tail -> get_max tail (if s > max then s else max) in get_max sigs 0 in
      match sigs |> List.filter (fun (_, s) -> s = max) with
      | [(s, a), _] -> TGeneric (TID s.id, a)
      | sigs        ->
        let sigs = List.map (fun ((a, b), _) -> (a, b)) sigs   in
        if not (List.for_all same_layout (transpose (fun (s, _) -> s.params) sigs)) then (push_err (Msg ("No matching overload for generic arguments for type " ^ name)) span ctx; TUnknown)
        else
        if nttp_mismatch (transpose (fun (s, _) -> s.params) sigs) then let ids = List.map (fun (s, _) -> s.id) sigs in TGeneric (TAmb ids, (sigs |> List.hd |> snd))
        else (push_err (Msg ("Ambiguous overload for generic arguments for type " ^ name)) span ctx; TUnknown)





and resolve_generic_params resolve_nttp params ctx =
  let find n = List.find_opt (fun s -> s.name = n && match s.kind with TSKParam _ -> true | _ -> false) ctx.local in
  let rec fold acc p =
    match p.param with
    | GPName n -> if List.exists ((=) n.name) ctx.env.vars then (push_err (Msg ("Typename " ^ wrap n.name ^ " already declared as a constant parameter")) n.span ctx; acc) (* env contains only nttps *)
    else begin
      match find n.name with
      | None ->
        let id = new_id() in push_type id n [] (TSKParam PSKTypename) ctx; push_local id ctx;
        { p with param = GPTypename id } :: acc
      | Some { id; kind = TSKParam (PSKTypename);  _ } -> { p with param = GPTypename id } :: acc
      | Some {     kind = TSKParam (PSKGeneric _); _ } -> push_err (Msg ("Not enough generic parameters for typename " ^ wrap n.name)) n.span ctx; acc
      | Some _                                         -> assert false (* impossible accoring to "find" *)
    end
    | GPTypename id    -> push_local id ctx; p :: acc (* already resolved *)
    | GPConst   (n, t) -> begin
      match find n.name with
      | None ->
        let t = if resolve_nttp then resolve_type t ctx else t in
        let rec check left =
          match left with
          | []           -> push_var n.name ctx; { p with param = GPConst (n, t) } :: acc
          | head :: tail -> 
            match head.param with
            | GPConst (name, _  ) when name.name = n.name -> push_err (Msg ("Constant parameter " ^ wrap n.name ^ " already declared")) n.span ctx; acc
            | _                                           -> check tail
        in check acc
      | Some _ -> push_err (Msg ("Constant parameter " ^ wrap n.name ^ " already declared as a typename")) n.span ctx; acc
    end
    | GPGeneric (t, ps) ->
      let view = view_params ps in begin
        match t.param with
        | GPName n -> if List.exists ((=) n.name) ctx.env.vars then (push_err (Msg ("Typename " ^ wrap n.name ^ " already declared as a constant parameter")) n.span ctx; acc) else begin 
          match find n.name with
          | None ->
            let id    = new_id() in push_type id n [] (TSKParam (PSKGeneric view)) ctx; push_local id ctx;
            let inner = List.fold_left fold acc ps in
            if inner == acc then acc else
            { p with param = GPGeneric ({t with param = GPTypename id}, inner |> List.take (List.length inner - List.length acc) |> List.rev) } :: acc
          | Some { id; kind = TSKParam (PSKGeneric v) } when v = view ->
            let inner = List.fold_left fold acc ps in
            if inner == acc then acc else
            { p with param = GPGeneric ({t with param = GPTypename id}, inner |> List.take (List.length inner - List.length acc) |> List.rev) } :: acc
          | Some {     kind = TSKParam (PSKGeneric _) }               -> push_err (Msg ("Generic parameter mismatch of typename "   ^ wrap n.name)) n.span ctx; acc
          | Some {     kind = TSKParam (PSKTypename ) }               -> push_err (Msg ("Too many generic parameters for typename " ^ wrap n.name)) n.span ctx; acc
          | Some _                                                    -> assert false (* shouldnt be able to find a non-param in local *)
        end
        | GPTypename id -> push_local id ctx; p :: acc (* already resolved *)
        | _             -> assert false (* parser wont allow it *) 
      end
    | GPTuple params -> 
      let new_acc = List.fold_left fold acc params in
      if new_acc == acc then acc else
      { p with param = GPTuple (new_acc |> List.take (List.length new_acc - List.length acc) |> List.rev) } :: acc
    | GPFunc  (a, r) -> begin
      let a_acc = fold acc a in
      if a_acc == acc then acc else
      let r_acc = fold a_acc r in
      if r_acc == a_acc then acc else
      { p with param = GPFunc (List.hd a_acc, List.hd r_acc) } :: acc
    end
    | _ -> assert false (* TODO: add @:usingTypes support, and potentially @:requires *)
  in params |> List.fold_left fold [] |> List.rev


and resolve_type_params ctx =
  let resolve_params resolve_nttps = 
    let iter_m _ m =
      gather_local m ctx;
      let iter s   = 
        let res    = snapshot_ctx ctx in
        let params = resolve_generic_params resolve_nttps s.params ctx in
        res();
        replace_sig { s with params } ctx;
      in List.iter iter (Hashtbl.find ctx.decls m.name)
    in Hashtbl.iter iter_m ctx.modules
  in
  resolve_params false; (* resolves type parameters but nttps *)
  resolve_params true   (* resolves nttps types *)

and resolve_alias_types ctx = (* TODO: fix circular and self dependency issues *)
  let rec loop decls =
    match decls with
    | [] -> ()
    | (path, sigs) :: tail ->
      gather_local (Hashtbl.find ctx.modules path) ctx;
      let rec inner sigs =
        match sigs with
        | []       -> loop tail
        | sh :: st ->
          match sh.kind with
          | TSKAlias t -> 
            let res = snapshot_ctx ctx in
            ignore (resolve_generic_params true sh.params ctx);
            sh.kind <- TSKAlias (resolve_type t ctx);
            res();
            inner st
          | _          -> inner st
      in inner sigs
  in loop (Hashtbl.to_seq ctx.decls |> List.of_seq)


and resolve_expr e ctx = (* TODO: resolve constructors as EInit *)
  let expr =  
    match e.expr with
    | EVar   n            -> resolve_var n e.span ctx
    | EBinOp (e1, op, e2) ->
      let e1 = resolve_expr e1 ctx in (* explicit ordered definitions because OCaml constructors have unspecified evaluation order for multi-element constructors *)
      let e2 = resolve_expr e2 ctx in
      EBinOp (e1, op, e2)
    | ELUnOp (    op, e ) ->
      let e  = resolve_expr e  ctx in
      ELUnOp (op, e)
    | ERUnOp (e,  op    ) ->
      let e  = resolve_expr e  ctx in
      ERUnOp (e, op)
    | EArray exprs ->
      let exprs = map resolve_expr exprs ctx in
      EArray exprs
    | ETuple exprs ->
      let exprs = map resolve_expr exprs ctx in
      ETuple exprs
    | EIf   (c, t, e) -> resolve_if   c t e ctx
    | ECall (t, a   ) -> 
      let t   = resolve_expr t ctx in
      let old = ctx.field_access   in
      ctx.field_access <- false;
      let a   = resolve_expr a ctx in
      ctx.field_access <- old;
      ECall  (t, a)
    | EField (t, f) ->
      let t   = resolve_expr t ctx in
      let old = ctx.field_access   in
      ctx.field_access <- true;
      let f   = resolve_expr f ctx in
      ctx.field_access <- old;
      EField (t, f)
    | EIndex (t, i) ->
      let t   = resolve_expr t ctx in
      let old = ctx.field_access   in
      ctx.field_access <- false;
      let i   = resolve_expr i ctx in
      ctx.field_access <- old;
      EIndex   (t, i)
    | EGeneric (t, a)   -> resolve_generic_expr t a ctx
    | EAddress e        -> EAddress (resolve_expr e ctx) 
    | ENew     e        -> ENew     (resolve_expr e ctx)
    | EDecl   (n, t, v) -> resolve_decl   n t v ctx
    | ELambda (p, t, b) -> resolve_lambda p t b ctx
    | EReturn  e        -> EReturn  (resolve_expr e ctx)
    | EPoly   (t, p)    -> resolve_poly_expr t p ctx
    | EType    t        -> EType    (resolve_type t ctx)
    | EBlock   stmts    -> resolve_block stmts ctx
    | ETrace   e        -> ETrace   (resolve_expr e ctx)
    | e                 -> e
  in { e with expr }


and resolve_var n s ctx =
  if ctx.field_access || var_exists  n ctx then EVar n
  else if type_exists n ctx then let t = resolve_type_name n s ctx in if t = TUnknown then EEmpty else EType t
  else (push_err (Undefined n) s ctx; EEmpty)

and resolve_if c t e ctx =
  let con_res = push_env       ctx in
  let c       = resolve_expr c ctx in
  let tru_res = push_env       ctx in
  let t       = resolve_expr t ctx in
  tru_res();
  let e       = resolve_expr e ctx in
  con_res();
  EIf (c, t, e)

and resolve_generic_expr t a ctx =
  let resolve_args a =
    let rec loop (a:generic_arg list) acc =
      match a with
      | []           -> List.rev acc
      | head :: tail ->
        let arg = 
          match head.arg with
          | GAAmb (t, e) -> begin
            match is_expr e ctx, is_type t ctx with
            | true,  true  -> GAAmb  (resolve_type t ctx, resolve_expr e ctx)
            | true,  false -> GAExpr (resolve_expr e ctx)
            | false, true  -> GAType (resolve_type t ctx)
            | false, false -> GAType (resolve_type t ctx) (* let it handle error here *)
          end
          | GAType t -> GAType (resolve_type t ctx)
          | GAExpr e -> GAExpr (resolve_expr e ctx)
          | _        -> assert false (* impossible *)
        in loop tail ({ head with arg } :: acc)
    in loop a []
  in
  let t = resolve_expr t ctx in
  let a = resolve_args a     in
  EGeneric (t, a)


and resolve_decl n t v ctx =
  let t = resolve_type t ctx in
  push_var n.name ctx;
  let v = resolve_expr v ctx in
  EDecl (n, t, v)

and resolve_lambda p t b ctx =
  let res = push_env ctx in
  let p   = List.map (fun (p:param_info) -> push_var p.name.name ctx; { p with typ = resolve_type p.typ ctx }) p in
  let t   = resolve_type t ctx in
  let b   = resolve_expr b ctx in
  res();
  ELambda (p, t, b)

and resolve_poly_expr t p ctx =
  let wrong_kind p =
    match p.param with
    | GPConst _ | GPName _ -> false
    | _                    -> push_err (Msg "This kind of generic parameter is not allowed in expression space") p.span ctx; true
  in
  let rec name_overload p acc =
    match p with
    | []           -> acc, false
    | head :: tail ->
      match head.param with
      | GPConst (n, _) | GPName n ->
        if List.mem n.name acc then (push_err (Msg ("Generic parameter '" ^ n.name ^ "' is already declared")) head.span ctx; acc, true)
        else name_overload tail (n.name :: acc)
      | _ -> assert false
  in
  if List.exists wrong_kind p then EEmpty else
  let names, overlap = name_overload p [] in
  if overlap then EEmpty else
  let global = ctx.env   in
  let local  = ctx.local in
  push_env_raw ctx;
  let p = resolve_generic_params true p ctx in
  push_env_raw ctx;
  let t = resolve_expr t ctx in
  ctx.env   <- { global with vars = ctx.env.vars @ global.vars };
  ctx.local <- local;
  EPoly (t, p)



and resolve_block stmts ctx =
  let res   = push_env ctx in
  let stmts = map resolve_stmt stmts ctx in
  res();
  EBlock stmts


and resolve_stmt s ctx =
  let stmt =
    match s.stmt with
    | SExpr e -> SExpr (resolve_expr e ctx)
  in { s with stmt }







let gather_class_members members ctx =
  let rec loop m f_names m_names =
    match m with
    | []           -> ctx.env.vars <- f_names @ m_names @ ctx.env.vars
    | head :: tail ->
      match head.member with 
      | CMField { name = n } ->
        let f_names = 
               if List.mem n.name f_names      then (push_err (Msg ("Field '" ^ n.name ^ "' already declared"                        )) n.span ctx; f_names)
          else if List.mem n.name m_names      then (push_err (Msg ("Field '" ^ n.name ^ "' already declared as a method"            )) n.span ctx; f_names)
          else if List.mem n.name ctx.env.vars then (push_err (Msg ("Field '" ^ n.name ^ "' already declared as a constant parameter")) n.span ctx; f_names)
          else n.name :: f_names
        in
        loop tail f_names m_names
      | CMMethod { name = n } ->
        let m_names = 
          (* overloading allowed *)
               if List.mem n.name f_names      then (push_err (Msg ("Method '" ^ n.name ^ "' already declared as a field"))              n.span ctx; m_names)
          else if List.mem n.name ctx.env.vars then (push_err (Msg ("Method '" ^ n.name ^ "' already declared as a constant parameter")) n.span ctx; f_names)
          else n.name :: m_names
        in
        loop tail f_names m_names
      | _ -> assert false (* constructors do not exist yet *)
  in loop members [] []

let resolve_class_field (info:class_field_info) ctx =
  let res      = snapshot_ctx ctx in
  let generics = resolve_generic_params true info.generics ctx in
  let typ      = resolve_type info.typ     ctx in
  let default  = resolve_expr info.default ctx in
  res();
  CMField { info with typ; default; generics }

let resolve_class_method (info:class_method_info) ctx =
  let res    = snapshot_ctx ctx in
  let generics = resolve_generic_params true info.generics ctx in
  let typ    = resolve_type info.typ ctx in
  let params = List.map (fun (p:param_info) -> push_var p.name.name ctx; { p with typ = resolve_type p.typ ctx }) info.params in
  let body   = resolve_expr info.body ctx in
  res();
  CMMethod { info with typ; generics; params; body; }

let resolve_class_constructor (info:class_method_info) ctx =
  let params = List.map (fun (p:param_info) -> push_var p.name.name ctx; { p with typ = resolve_type p.typ ctx }) info.params in
  let body   = resolve_expr info.body ctx in
  CMNew { body; params }

let resolve_class_member m name ctx =
  let res = push_env ctx in
  let member = 
    match m.member with
    | CMField  info -> resolve_class_field info ctx
    | CMMethod info -> 
      if info.name.name = name then resolve_class_constructor info ctx
      else resolve_class_method info ctx
    | _ -> assert false (* constructors do not exist yet *)
  in
  res();
  { m with member }

let resolve_class info (name:placed_name) ctx =
  let generics = (List.find (fun s -> s.decl_span = name.span) (Hashtbl.find ctx.decls ctx.curr.name)).params in
  let res      = push_type_params generics ctx in
  gather_class_members info.members ctx;
  let members  = List.map (fun m -> resolve_class_member m name.name ctx) info.members in
  res();
  { generics; members }


let resolve_alias info (name:placed_name) ctx =
  let generics = (List.find (fun s -> s.decl_span = name.span) (Hashtbl.find ctx.decls ctx.curr.name)).params in
  let res      = push_type_params generics ctx in
  let target   = resolve_type info.target ctx in
  res();
  { generics; target }
  

let resolve_type_decl t ctx =
  let decl = 
    match t.decl with
    | DClass info -> DClass (resolve_class info t.name ctx)
    | DAlias info -> DAlias (resolve_alias info t.name ctx)
  in { t with decl }

let resolve_item i ctx =
  let item =
    match i.item with
    | IDecl t -> IDecl (resolve_type_decl t ctx)
    | IStmt s -> IStmt (resolve_stmt s ctx)
  in { i with item }

let resolve_module m ctx =
  gather_local m ctx;
  Hashtbl.replace ctx.modules m.name { m with items = List.map (fun i -> resolve_item i ctx) m.items }

let resolve main modules =
  let m            = Hashtbl.find modules [main] in
  let types, decls = gather_types modules in 
  let ctx          = { modules; types; decls; local = []; curr = m; env = { vars = []; parent = None }; field_access = false; errors = [] } in 
  resolve_type_params ctx;
  resolve_alias_types ctx; 
  resolve_module m ctx;
  ctx