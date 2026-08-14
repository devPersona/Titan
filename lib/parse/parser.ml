open Ast
open Span
open Lexer
open Error
open Debug



let empty_ctx tbl dir curr newlines = 
{
  tbl;
  dir;
  curr;
  newlines;
  pos_s = file_start_span.s_pos;
  pos_e = file_start_span.s_pos;
  allow_gt = true;
  errors = []
}

let curr_token tokens = List.hd tokens
let curr_span  tokens = snd (curr_token tokens)

let err_at_span  kind span   ctx = err (Syntax_err (make_err_in_file kind span ctx.newlines ctx.curr))
let err_at_token kind tokens ctx = err_at_span kind (curr_span tokens) ctx
let add_err      kind span   ctx = ctx.errors <- (Syntax_err (make_err_in_file kind span ctx.newlines ctx.curr)) :: ctx.errors



let path_of_name path ctx = ctx.dir ^ "/" ^ String.concat "/" path ^ ".ttn"
let file_exists  path ctx =
  path_of_name path ctx |> Sys.file_exists



let ss_pos p ctx =
  let old = ctx.pos_s in
  ctx.pos_s <- p;
  fun() -> ctx.pos_s <- old


let pack_item  item span                      = { item;       span }
let pack_mod   m    span                      = { m;          span }
let pack_name  name span                      = { name;       span }
let pack_expr  expr span                      = { expr; mods = []; span }
let pack_param param metadata span:param_info = { param; metadata; span }
let pack_binop e1 op e2                       = pack_expr (EBinOp (e1, op, e2)) (span_join e1.span e2.span)
let pack_lunop op e s                         = pack_expr (ELUnOp (op, e     )) (span_join s e.span       )
let pack_runop e op s                         = pack_expr (ERUnOp (e, op     )) (span_join e.span s       )

let pack_tuple (exprs:expr list) s =
  match exprs with
  | [x] -> { x with span = s }
  | _   -> pack_expr (ETuple exprs) s

let pack_type_tuple types =
  match types with
  | []  -> TUnit
  | [t] -> t
  | _   -> TTuple types

let type_of_params params = 
  let rec loop (p:param_info list) acc =
    match p with
    | []            -> pack_type_tuple (List.rev acc)
    | param :: rest -> loop rest (snd (param.param) :: acc)
  in loop params []

let wrap_expr s func tokens ctx =
  let restore = ss_pos s.s_pos ctx in
  let expr, rest = func tokens ctx in
  restore();
  expr, rest







let consume_semicols tokens =
  let rec loop t =
    match t with
    | (Punc SemiCol, _) :: tail -> loop tail
    | _                         -> t
  in loop tokens
let semicol_next tokens =
  match tokens with
  | (Punc SemiCol, _) :: tail -> true
  | _                         -> false
let rec needs_semicol expr =
  match expr.expr with
  | EBlock _          -> false
  | EIf (_, tru, els) -> if els.expr = EEmpty then needs_semicol tru else needs_semicol els
  | EDecl (_, _,   v) -> needs_semicol v
  | ELambda (_, _, b) -> needs_semicol b
  | EReturn e         -> needs_semicol e
  | EPoly (d, _)      -> needs_semicol d
  | _                 -> true
let check_semicol expr tokens ctx =
  if needs_semicol expr && not (semicol_next tokens) then add_err (Missing "';'") (span_of_pos expr.span.e_pos) ctx;
  consume_semicols tokens





















let rec parse_type tokens ctx = parse_type_arrow tokens ctx

and parse_type_arrow tokens ctx =
  let t1, rest = parse_type_ptr tokens ctx in
  match rest with
  | (Punc RArrow, _) :: tail -> let t2, rest = parse_type_ptr tail ctx in TFunc (t1, t2), rest
  | _                        -> t1, rest

and parse_type_ptr tokens ctx =
  let t, rest = parse_type_generic tokens ctx in
  match rest with
  | (Op Mul, s) :: tail -> ctx.pos_e <- s.e_pos; TPtr t, tail
  | _                   -> t, rest

and parse_type_generic tokens ctx =
  let t, rest = parse_type_raw tokens ctx in
  match rest with
  | (Op Lt, _) :: tail -> let args, remaining = parse_generic_args tail ctx in TGeneric (t, args), remaining
  | _                  -> t, rest

and parse_type_raw tokens ctx =
  match tokens with
  | (Ident dir,      s) :: (Punc CC, _) :: tail -> ctx.pos_e <- s.s_pos; parse_type_path dir tokens ctx
  | (Ident typ,      s)                 :: tail -> ctx.pos_e <- s.e_pos; TName (typ, s), tail
  | (Punc  LParen,   _)                 :: tail -> parse_type_tuple tail ctx
  | (Punc  LBracket, _)                 :: tail -> parse_type_array tail ctx
  | _                                           -> err_at_token (Expected "type") tokens ctx

and parse_type_path dir tokens ctx =
  let rec loop t acc =
    match t with
    | (Ident dir, _) :: (Punc CC, _) :: tail -> loop tail (dir :: acc)
    | _                                      -> List.rev acc, parse_type t ctx
  in 
  let s_pos             = ctx.pos_e                 in
  let path, (typ, rest) = loop tokens [dir]         in
  let span              = span_make s_pos ctx.pos_e in
  let rec wrap typ path = 
    match typ with
    | TName     _     -> TPath    (path, span, typ)
    | TArray    t     -> TArray   (wrap t path )
    | TPtr      t     -> TPtr     (wrap t path )
    | TGeneric (t, a) -> TGeneric (wrap t path, a)
    | TTuple   types  -> TTuple   (List.map (fun t -> wrap t path) types)
    | TDefault (t, e) -> TDefault (wrap t path, e)
    | TNamed  (n, t)  -> TNamed   (n, wrap t path)
    | TFunc (t1, t2)  -> TFunc    (wrap t1 path, wrap t2 path)
    | TPath (_, s, _) -> add_err (Msg "Nested paths are not allowed")           s    ctx; TUnknown
    | TUnit           -> add_err (Msg "Unit type '()' is not allowed in paths") span ctx; TUnknown
    | _               -> typ
  in
  if file_exists path ctx then wrap typ path, rest else 
    match typ with
    | TName (name, _) -> let p = path @ [name] in if file_exists p ctx then wrap typ p, rest else err_at_span (File_not_found (path_of_name path ctx)) span ctx
    | _               -> err_at_span (File_not_found (path_of_name path ctx)) span ctx

and parse_type_array tokens ctx =
  let typ, rest = parse_type tokens ctx in
  match rest with
  | (Punc RBracket, s) :: tail -> ctx.pos_e <- s.e_pos; TArray typ, tail
  | _                          -> err_at_token (Expected "]") rest ctx

and parse_type_tuple tokens ctx =
  match tokens with
  | (Punc RParen, s) :: tail -> ctx.pos_e <- s.e_pos; TUnit, tail
  | _                        ->
    let first, rest = parse_type_leaf tokens ctx in
    let rec loop t acc = 
      match t with
      | (Punc Comma,  _) :: tail -> let typ, rest = parse_type_leaf tail ctx in loop rest (typ :: acc)
      | (Punc RParen, s) :: tail -> ctx.pos_e <- s.e_pos; pack_type_tuple (List.rev acc), tail
      | _                        -> err_at_token (Expected ", or )") t ctx
    in loop rest [first]

and parse_type_leaf tokens ctx =
  let t, rest = 
    match tokens with
    | (Ident name,     s) :: (Punc Col, _) :: tail -> let typ, rest = parse_type tail ctx in TNamed (pack_name name s, typ), rest
    | _                                            -> parse_type tokens ctx
  in 
  match rest with
  | (Op Asg, _) :: tail -> let expr, rest = parse_expr tail ctx in TDefault (t, expr), rest
  | _                   -> t, rest












and parse_generic_arg_opt tokens ctx =
  let metadata, rest = get_mods tokens ctx in
  let old = ctx.allow_gt in
  ctx.allow_gt <- false;
  let pos_e = ctx.pos_e in
  let e = try Some (parse_expr rest ctx) with Err _ -> None in
  ctx.pos_e <- pos_e;
  let t = try Some (parse_type rest ctx) with Err _ -> None in
  ctx.allow_gt <- old;
  match e, t with
  | None,                                 None          -> None, tokens
  | Some ({ expr = EType t; span }, e_r), None          -> Some { arg = GAType t; metadata; span                                 }, e_r
  | Some (e,                        e_r), None          -> Some { arg = GAExpr e; metadata; span = e.span                        }, e_r
  | None,                                 Some (t, t_r) -> Some { arg = GAType t; metadata; span = span_make ctx.pos_s ctx.pos_e }, t_r
  | Some ({ expr = EType t; span }, e_r), Some _        -> Some { arg = GAType t; metadata; span                                 }, e_r
  | Some (e,                        e_r), Some (t, t_r) -> 
    match t_r with
    | (Op Gt, _) :: _ | (Punc Comma, _) :: _ -> Some { arg = GAType t; metadata; span = span_make ctx.pos_s ctx.pos_e }, t_r
    | _                                      -> 
      match e_r with
      | (Op Gt, _) :: _ | (Punc Comma, _) :: _ -> Some { arg = GAExpr e; metadata; span = e.span }, e_r
      | _                                      -> None, tokens

and parse_generic_arg tokens ctx =
  match parse_generic_arg_opt tokens ctx with
  | Some a, rest -> a, rest
  | None,   _    -> err_at_token (Expected "generic argument") tokens ctx
  
and parse_generic_args_opt tokens ctx =
  let rec loop t acc =
    match t with
    | (Punc Comma, _) :: tail -> let arg, rest = parse_generic_arg tail ctx in loop rest (arg :: acc)
    | (Op   Gt,    s) :: tail -> ctx.pos_e <- s.e_pos; Some (List.rev acc), tail
    | _                       -> err_at_token (Expected ", or >") t ctx
  in 
  let first, rest = parse_generic_arg_opt tokens ctx in
  match first with
  | None   -> None, tokens
  | Some a -> 
    match rest with
    | (Op Gt,      _) :: tail -> Some [a], tail
    | (Punc Comma, _) :: tail -> loop rest [a]
    | _                       -> None, tokens

and parse_generic_args tokens ctx =
  match parse_generic_args_opt tokens ctx with
  | Some args, rest -> args, rest
  | None,      _    -> err_at_token (Expected "generic argument") tokens ctx

and parse_generic_param tokens ctx =
  match tokens with
  | (Ident name, s) :: (Punc Col, _) :: tail -> let typ, rest = parse_type tail ctx in { param = GPConst ({ name; span = s }, typ); metadata = []; span = span_join s (span_of_pos ctx.pos_e) }, rest
  | (Ident typ,  s)                  :: tail -> { param = GPTypename typ; metadata = []; span = s }, tail
  | _                                        -> err_at_token (Invalid "generic parameter") tokens ctx

and parse_generic_params tokens ctx =
  let first, rest = parse_generic_param tokens ctx in
  let rec loop t acc =
    match t with
    | (Op   Gt,    s) :: tail -> ctx.pos_e <- s.e_pos; List.rev acc, tail
    | (Punc Comma, _) :: tail -> let param, rest = parse_generic_param tail ctx in loop rest (param :: acc)
    | _                       -> err_at_token (Expected ", or >") t ctx
  in loop rest [first]







and parse_meta_arg tokens ctx =
  try
    let expr, rest = parse_expr tokens ctx in MAExpr expr, rest
  with Err _ -> 
    match tokens with
    | (Op op, _) :: rest -> MAOp op, rest
    | _                  -> err_at_token (Invalid "metadata argument") tokens ctx
and parse_meta_args tokens ctx =
  let rec loop t acc =
    match t with
    | (Punc RParen, s) :: tail -> ctx.pos_e <- s.e_pos; List.rev acc, tail
    | (Punc Comma,  _) :: tail -> let arg, rest = parse_meta_arg tail ctx in loop rest (arg :: acc)
    | _                        -> err_at_token (Expected ", or )") t ctx
  in
  match tokens with
  | (Punc RParen, s) :: tail -> ctx.pos_e <- s.e_pos; [], tail
  | _                        -> let first, rest = parse_meta_arg tokens ctx in loop rest [first]
and parse_meta tokens ctx = 
  match tokens with
  | (Ident name, _) :: (Punc LParen, _) :: tail -> let args, rest = parse_meta_args tail ctx in pack_mod (MMeta (name, args)) (span_make ctx.pos_s ctx.pos_e), tail
  | (Ident name, s)                     :: tail -> pack_mod (MMeta (name, [])) (span_make ctx.pos_s s.e_pos), tail
  | _                                           -> err_at_token (Expected "metadata name") tokens ctx














and get_type tokens ctx =
  match tokens with
  | (Punc Col, _) :: rest -> parse_type rest ctx
  | _                     -> TUnknown, tokens
and get_generic_args tokens ctx =
  match tokens with
  | (Op Lt, _) :: rest -> parse_generic_args rest ctx
  | _                  -> [], tokens
and get_generic_params tokens ctx =
  match tokens with
  | (Op Lt, s) :: tail -> let params, rest = parse_generic_params tail ctx in params, rest
  | _                  -> [], tokens
and get_mods tokens ctx =
  let rec loop t acc =
    match t with
    | (Kw KwPublic,  s) :: tail -> loop tail (pack_mod MPublic  s :: acc)
    | (Kw KwPrivate, s) :: tail -> loop tail (pack_mod MPrivate s :: acc)
    | (Kw KwStatic,  s) :: tail -> loop tail (pack_mod MStatic  s :: acc)
    | (Kw KwInline,  s) :: tail -> loop tail (pack_mod MInline  s :: acc)
    | (Kw KwExtern,  s) :: tail -> loop tail (pack_mod MExtern  s :: acc)
    | (Punc AtCol,   s) :: tail -> let res = ss_pos s.s_pos ctx in let meta, rest = parse_meta tail ctx in res(); loop rest (meta :: acc)
    | _                         -> List.rev acc, t
  in loop tokens []










and parse_expr tokens ctx =
  let mods, rest      = get_mods  tokens ctx in
  let expr, remaining = parse_asg rest   ctx in
  { expr with mods }, remaining

and parse_asg tokens ctx =
  let left, rest = parse_or tokens ctx in
  let rec loop e1 t =
    match t with
    | (Op Asg, _) :: rest -> let e2, remaining = parse_asg rest ctx in loop (pack_binop e1 Asg e2) remaining
    | (Op AA,  _) :: rest -> let e2, remaining = parse_asg rest ctx in loop (pack_binop e1 AA  e2) remaining
    | (Op SA,  _) :: rest -> let e2, remaining = parse_asg rest ctx in loop (pack_binop e1 SA  e2) remaining
    | (Op MA,  _) :: rest -> let e2, remaining = parse_asg rest ctx in loop (pack_binop e1 MA  e2) remaining
    | (Op DA,  _) :: rest -> let e2, remaining = parse_asg rest ctx in loop (pack_binop e1 DA  e2) remaining
    | _                   -> e1, t
  in loop left rest
and parse_or tokens ctx =
  let left, rest = parse_and tokens ctx in
  let rec loop e1 t =
    match t with
    | (Op Or,  _) :: rest -> let e2, remaining = parse_and rest ctx in loop (pack_binop e1 Or  e2) remaining
    | _                   -> e1, t
  in loop left rest
and parse_and tokens ctx =
  let left, rest = parse_pip tokens ctx in
  let rec loop e1 t =
    match t with
    | (Op And, _) :: rest -> let e2, remaining = parse_pip rest ctx in loop (pack_binop e1 And e2) remaining
    | _                   -> e1, t
  in loop left rest
and parse_pip tokens ctx =
  let left, rest = parse_xor tokens ctx in
  let rec loop e1 t =
    match t with
    | (Op Pip, _) :: rest -> let e2, remaining = parse_xor rest ctx in loop (pack_binop e1 Pip e2) remaining
    | _                   -> e1, t
  in loop left rest
and parse_xor tokens ctx =
  let left, rest = parse_amp tokens ctx in
  let rec loop e1 t =
    match t with
    | (Op Xor, _) :: rest -> let e2, remaining = parse_amp rest ctx in loop (pack_binop e1 Xor e2) remaining
    | _                   -> e1, t
  in loop left rest
and parse_amp tokens ctx =
  let left, rest = parse_eq tokens ctx in
  let rec loop e1 t =
    match t with
    | (Op Amp, _) :: rest -> let e2, remaining = parse_eq  rest ctx in loop (pack_binop e1 Amp e2) remaining
    | _                   -> e1, t
  in loop left rest
and parse_eq tokens ctx =
  let left, rest = parse_rel tokens ctx in
  let rec loop e1 t =
    match t with
    | (Op Eq,  _) :: rest -> let e2, remaining = parse_rel rest ctx in loop (pack_binop e1 Eq  e2) remaining
    | (Op Neq, _) :: rest -> let e2, remaining = parse_rel rest ctx in loop (pack_binop e1 Neq e2) remaining
    | _                   -> e1, t
  in loop left rest
and parse_rel tokens ctx =
  let left, rest = parse_add tokens ctx in
  let rec loop e1 t =
    match t with
    | (Op Gt,  _) :: rest
      when ctx.allow_gt   -> let e2, remaining = parse_add rest ctx in loop (pack_binop e1 Gt  e2) remaining
    | (Op Ge,  _) :: rest -> let e2, remaining = parse_add rest ctx in loop (pack_binop e1 Ge  e2) remaining
    | (Op Lt,  _) :: rest -> let e2, remaining = parse_add rest ctx in loop (pack_binop e1 Lt  e2) remaining
    | (Op Le,  _) :: rest -> let e2, remaining = parse_add rest ctx in loop (pack_binop e1 Le  e2) remaining
    | _                   -> e1, t
  in loop left rest 
and parse_add tokens ctx =
  let left, rest = parse_mul tokens ctx in
  let rec loop e1 t =
    match t with
    | (Op Add, _) :: rest -> let e2, remaining = parse_mul rest ctx in loop (pack_binop e1 Add e2) remaining
    | (Op Sub, _) :: rest -> let e2, remaining = parse_mul rest ctx in loop (pack_binop e1 Sub e2) remaining
    | _                   -> e1, t
  in loop left rest 
and parse_mul tokens ctx =
  let left, rest = parse_lunop tokens ctx in
  let rec loop e1 t =
    match t with
    | (Op Mul, _) :: rest -> let e2, remaining = parse_lunop rest ctx in loop (pack_binop e1 Mul e2) remaining
    | (Op Div, _) :: rest -> let e2, remaining = parse_lunop rest ctx in loop (pack_binop e1 Div e2) remaining
    | (Op Mod, _) :: rest -> let e2, remaining = parse_lunop rest ctx in loop (pack_binop e1 Mod e2) remaining
    | _                   -> e1, t
  in loop left rest 
and parse_lunop tokens ctx =
  match tokens with
  | (Op Not, s) :: rest -> let e,  remaining = parse_lunop rest ctx in (pack_lunop Not e s), remaining
  | (Op Sub, s) :: rest -> let e,  remaining = parse_lunop rest ctx in (pack_lunop Sub e s), remaining
  | (Op Inc, s) :: rest -> let e,  remaining = parse_lunop rest ctx in (pack_lunop Inc e s), remaining
  | (Op Dec, s) :: rest -> let e,  remaining = parse_lunop rest ctx in (pack_lunop Dec e s), remaining
  | (Op Amp, s) :: rest -> let e,  remaining = parse_lunop rest ctx in pack_expr (EAddress e) (span_join s e.span), remaining
  | (Op New, s) :: rest -> let e,  remaining = parse_lunop rest ctx in pack_expr (ENew     e) (span_join s e.span), remaining
  | _                     -> parse_runop tokens ctx 
and parse_runop tokens ctx =
  let left, rest = parse_primary tokens ctx in
  let rec loop e t =
    match t with
    | (Op   Inc,      s) :: rest -> loop (pack_runop e Inc s) rest
    | (Op   Dec,      s) :: rest -> loop (pack_runop e Dec s) rest
    | (Op   Lt,       _) :: rest -> let generics, remaining = parse_generic_args_opt rest ctx in if generics = None then e, t else loop (pack_expr (EGeneric (e, Option.get generics)) (span_make e.span.s_pos ctx.pos_e)) remaining
    | (Punc LParen,   _) :: rest -> let args,     remaining = parse_tuple            rest ctx in loop (pack_expr (ECall  (e,  args)) (span_join e.span  args.span)) remaining
    | (Punc LBracket, _) :: rest -> let index,    remaining = parse_array            rest ctx in loop (pack_expr (EIndex (e, index)) (span_join e.span index.span)) remaining
    | (Punc Dot,      _) :: rest -> let field,    remaining = parse_primary          rest ctx in loop (pack_expr (EField (e, field)) (span_join e.span field.span)) remaining
    | (Punc QMark,    _) :: rest -> let ternary,  remaining = parse_ternay         e rest ctx in loop ternary                                                       remaining
    | (Punc CC,       _) :: rest -> let t,        remaining = parse_type_path_expr e rest ctx in loop t                                                             remaining
    | _                          -> e, t
  in loop left rest
and parse_primary tokens ctx =
  match tokens with
  | (Basic b,       s) :: rest -> pack_expr (ELit    b) s, rest
  | (Ident "this",  s) :: rest -> pack_expr (EThis    ) s, rest
  | (Ident name,    s) :: rest -> pack_expr (EVar name) s, rest

  | (Kw KwVar,      s) :: rest -> wrap_expr s parse_decl  rest ctx
  | (Kw KwIf,       s) :: rest -> wrap_expr s parse_if    rest ctx
  | (Kw KwFunc,     s) :: rest -> wrap_expr s parse_func  rest ctx
  | (Kw KwRet,      s) :: rest -> wrap_expr s parse_ret   rest ctx
  | (Kw KwTrace,    s) :: rest -> wrap_expr s parse_trace rest ctx

  | (Punc LBracket, s) :: rest -> wrap_expr s parse_array rest ctx
  | (Punc LParen,   s) :: rest -> wrap_expr s parse_tuple rest ctx
  | (Punc LBrace,   s) :: rest -> wrap_expr s parse_block rest ctx

  | _                          -> err_at_token (Expected "expression") tokens ctx

and parse_ternay con tokens ctx =
  let tru, rest      = parse_expr tokens ctx in
  let els, remaining =
    match rest with
    | (Punc Col, _) :: rest -> parse_expr rest ctx
    | _                     -> err_at_token (Expected "':'") rest ctx
  in pack_expr (EIf (con, tru, els)) (span_join con.span els.span), remaining

and parse_type_path_expr expr tokens ctx =
  match expr.expr with
  | EVar dir -> ctx.pos_e <- expr.span.s_pos; let t, rest = parse_type_path dir tokens ctx in pack_expr (EType t) (span_make expr.span.s_pos ctx.pos_e), rest
  | _        -> err_at_token (Invalid "type path") tokens ctx

and parse_decl tokens ctx =
  let name, rest =
    match tokens with
    | (Ident name, s) :: rest -> pack_name name s, rest
    | _                       -> err_at_token (Expected "variable name") tokens ctx
  in
  let generics, remaining = get_generic_params rest ctx in
  let typ, final          = get_type remaining ctx in
  let value, tail         =
    match final with
    | (Op Asg, _) :: rest -> parse_expr rest ctx
    | _                   -> pack_expr EEmpty name.span, final
  in
  let e_pos = if value.expr <> EEmpty then value.span.e_pos else if typ <> TUnknown || generics <> [] then ctx.pos_e else name.span.e_pos in
  let expr  = pack_expr (EDecl (name, typ, value)) (span_make ctx.pos_s e_pos) in
  if generics = [] then expr, tail else pack_expr (EPoly (expr, generics)) expr.span, tail

and parse_if tokens ctx =
  let con, rest = 
    match tokens with
    | (Punc LParen, _) :: rest -> parse_tuple rest ctx
    | _                        -> err_at_token (Expected "')'") tokens ctx
  in
  let tru, remaining = parse_expr rest ctx in
  let els, final     = 
    match consume_semicols remaining with
    | (Kw KwElse, _) :: rest -> parse_expr rest ctx
    | _                      -> pack_expr EEmpty tru.span, remaining
  in pack_expr (EIf (con, tru, els)) (span_make ctx.pos_s con.span.e_pos), final

and parse_func tokens ctx =
  match tokens with
  | (Ident name,   s) :: rest -> parse_func_decl (pack_name name s) rest   ctx
  | _                         -> parse_lambda                       tokens ctx

and parse_lambda tokens ctx =
  let generics, rest = get_generic_params tokens ctx in
  match rest with
  | (Punc LParen, _) :: tail -> 
    let params, remaining = parse_params  tail ctx in
    let ret, final        = get_type remaining ctx in
    let body, final'      = if semicol_next final then pack_expr EEmpty (span_of_pos ctx.pos_e), final else parse_expr final ctx in
    if generics = [] then
      pack_expr (ELambda (params, TFunc (type_of_params params, ret), body)) (span_make ctx.pos_s body.span.e_pos), final'
    else let expr = pack_expr (ELambda (params, TPoly (TFunc (type_of_params params, ret), generics), body)) (span_make ctx.pos_s body.span.e_pos) in
      pack_expr (EPoly (expr, generics)) expr.span, final'
  | _ -> err_at_token (Expected "parameter list") tokens ctx

and parse_func_decl name tokens ctx =
  match tokens with
  | (Punc  LParen, _) :: _ ->
    let lambda, rest = parse_lambda tokens ctx in
    let typ = 
      match lambda.expr with
      | ELambda (_, t, _) -> t
      | _                 -> assert false
    in
    pack_expr (EDecl (name, typ, lambda)) lambda.span, rest
  | _                         -> err_at_token (Expected "parameter list") tokens ctx

and parse_params tokens ctx =
  match tokens with
  | (Punc RParen, s) :: rest -> ctx.pos_e <- s.e_pos; [], rest
  | _                        ->
    let param, rest = parse_param tokens ctx in
    let rec loop t acc =
      match t with
      | (Punc RParen, s) :: rest -> ctx.pos_e <- s.e_pos; List.rev acc, rest
      | (Punc Comma,  _) :: rest -> let param, remaining = parse_param rest ctx in loop remaining (param :: acc)
      | _                        -> err_at_token (Expected ", or )") t ctx
    in loop rest [param]
  
and parse_param tokens ctx =
  let mods, rest = get_mods tokens ctx in
  let name, remaining = 
    match tokens with
    | (Ident name, s) :: rest -> pack_name name s, rest
    | _                       -> err_at_token (Expected "parameter name") tokens ctx
  in
  let typ, final = 
    match remaining with
    | (Punc Col, _) :: rest -> parse_type rest ctx
    | _                     -> err_at_token (Msg "Implicit parameter types are not allowed") rest ctx
  in pack_param (name, typ) mods (span_make name.span.e_pos ctx.pos_e), final


and parse_ret tokens ctx =
  let expr, rest = parse_expr tokens ctx in
  pack_expr (EReturn expr) (span_make ctx.pos_s expr.span.e_pos), rest

and parse_trace tokens ctx =
  match tokens with
  | (Punc LParen, _) :: rest -> let expr, remaining = parse_tuple rest ctx in pack_expr (ETrace expr) (span_make ctx.pos_s expr.span.e_pos), remaining
  | _                        -> err_at_token (Expected "'('") tokens ctx

and parse_array tokens ctx = 
  let old = ctx.allow_gt in
  ctx.allow_gt <- true;
  match tokens with 
  | (Punc RBracket, s) :: rest -> pack_expr (EArray []) (span_make ctx.pos_s s.e_pos), rest
  | _                          -> 
    let expr, rest = parse_expr tokens ctx in
    let rec loop t acc =
      match t with
      | (Punc RBracket, s) :: rest -> pack_expr (EArray (List.rev acc)) (span_make ctx.pos_s s.e_pos), rest
      | (Punc Comma,    _) :: rest -> let expr, remaining = parse_expr rest ctx in loop remaining (expr :: acc)
      | _                          -> err_at_token (Expected ", or ]") t ctx
    in ctx.allow_gt <- old; loop rest [expr] 

and parse_tuple tokens ctx =
  let old = ctx.allow_gt in
  ctx.allow_gt <- true;
  match tokens with 
  | (Punc RParen, s) :: rest -> pack_expr (ETuple []) (span_make ctx.pos_s s.e_pos), rest
  | _                        -> 
    let expr, rest = parse_expr tokens ctx in
    let rec loop t acc =
      match t with
      | (Punc RParen, s) :: rest -> pack_tuple (List.rev acc) (span_make ctx.pos_s s.e_pos), rest
      | (Punc Comma,  _) :: rest -> let expr, remaining = parse_expr rest ctx in loop remaining (expr :: acc)
      | _                        -> err_at_token (Expected ", or )") t ctx
    in ctx.allow_gt <- old; loop rest [expr] 

and parse_block tokens ctx =
  let rec loop t acc =
    match t with
    | (Punc RBrace, s) :: rest -> pack_expr (EBlock (List.rev acc)) (span_make ctx.pos_s s.e_pos), rest
    | [(EOF,         s)]       -> err_at_span (Missing "'}'") s ctx
    | _                        -> let stmt, rest = parse_stmt [] t ctx in loop rest (stmt :: acc)
  in loop tokens []







and parse_stmt mods tokens ctx =
  let expr, rest = parse_expr (consume_semicols tokens) ctx in
  { stmt = SExpr { expr with mods = expr.mods @ mods }; span = expr.span }, check_semicol expr tokens ctx







and parse_class_field tokens mods ctx = 
  let decl, rest = parse_decl tokens ctx in
  let member = 
    match decl.expr with
    |                 EDecl (name, typ, default)                 -> CMField { name; generics = []; typ; default }
    | EPoly ({ expr = EDecl (name, typ, default); _ }, generics) -> CMField { name; generics;      typ; default }
    | _                                                          -> assert false (* errors should be caught in parse_decl *)
  in { member; mods; span = decl.span }, check_semicol decl rest ctx

and parse_class_method tokens mods ctx =
  let name, tail = 
    match tokens with
    | (Ident name, s) :: tail -> pack_name name s, tail
    | _                       -> err_at_token (Expected "method name") tokens ctx
  in
  let decl, rest = parse_func_decl name tail ctx in
  let member = 
    match decl.expr with
    |                 EDecl (name, typ, { expr = ELambda (params, _, body); _ })                 -> CMMethod { name; generics = []; typ; params; body }
    | EPoly ({ expr = EDecl (name, typ, { expr = ELambda (params, _, body); _ }); _ }, generics) -> CMMethod { name; generics;      typ; params; body }
    | _                                                                                          -> assert false (* errors should be caught in parse_func_decl *)
  in { member; mods; span = decl.span }, check_semicol decl rest ctx


and parse_class_body tokens ctx =
  let decl_span s (mods:modifier list) = ss_pos (match mods with [] -> s | _  -> (List.hd mods).span).s_pos ctx in
  let rec loop t block_mods saved_mods acc =
    let inline_mods, after = get_mods t ctx           in
    let active_mods        = inline_mods @ block_mods in
    match after with
    | (Kw   KwVar,  s) :: tail -> let res = decl_span s inline_mods in let f, rest = parse_class_field  tail active_mods ctx in res(); loop rest block_mods saved_mods (f :: acc)
    | (Kw   KwFunc, s) :: tail -> let res = decl_span s inline_mods in let m, rest = parse_class_method tail active_mods ctx in res(); loop rest block_mods saved_mods (m :: acc)
    | (Punc LBrace, _) :: tail -> loop tail active_mods (block_mods :: saved_mods) acc 
    | (Punc RBrace, s) :: tail -> begin 
      match saved_mods with
      | []             -> List.rev acc, s.e_pos, tail
      | block :: saved -> loop tail block saved acc end
    | _                -> err_at_token (Missing "'}'") tokens ctx
  in loop tokens [] [] [] 

and parse_class tokens mods ctx =
  let name, rest = 
    match tokens with
    | (Ident name, s) :: tail -> { name; span = s }, tail
    | _                       -> err_at_token (Expected "class name") tokens ctx
  in
  let generics, remaining = get_generic_params rest ctx in
  match remaining with
  | (Punc SemiCol, _) :: tail -> let e_pos = if generics = [] then name.span.e_pos else ctx.pos_e in pack_item (IClass { name; mods; generics; members = [] }) (span_make ctx.pos_s e_pos), tail
  | (Punc LBrace,  _) :: tail -> let members, e_pos, rest = parse_class_body tail ctx in pack_item (IClass { name; mods; generics; members }) (span_make ctx.pos_s e_pos), rest
  | _                         -> err_at_token (Expected "'}'") rest ctx 




let parse_item tokens ctx =
  let mods, rest = get_mods tokens ctx in
  match rest with
  | (Kw KwClass, s) :: tail -> ctx.pos_s <- s.s_pos; parse_class tail mods ctx
  | _                       -> let stmt, remaining = parse_stmt mods rest ctx in pack_item (IStmt stmt) stmt.span, remaining










let rec load_import import ctx =
  if Hashtbl.mem ctx.tbl import.path then () else
  let path = path_of_name import.path ctx in
  if not (Sys.file_exists path) then add_err (File_not_found path) import.span ctx else
  let tokens, lex_ctx = tokenize path in
  let m = parse_module tokens (empty_ctx ctx.tbl ctx.dir lex_ctx.filename lex_ctx.newlines) in
  Hashtbl.add ctx.tbl import.path m;
  List.iter (fun i -> load_import i ctx) m.imports
  

and parse_import tokens ctx =
  let rec loop t acc = 
    match t with
    | (Ident dir, _) :: (Punc CC, _) :: tail -> loop tail (dir :: acc)
    | (Ident m,   s)                 :: tail -> { path = List.rev (m :: acc); span = span_make ctx.pos_s s.e_pos }, tail
    | _                                      -> err_at_token (Invalid "import") t ctx
  in loop tokens []

and parse_imports tokens ctx =
  let rec loop t acc =
    match t with
    | (Kw KwImport, s) :: tail -> ctx.pos_s <- s.s_pos; let i, rest = parse_import tail ctx in loop rest (i :: acc)
    | _                        -> List.rev acc, t
  in loop tokens []

and remove_comments tokens =
  let rec loop t acc =
    match t with
    | (Comment _, _) :: rest -> loop rest acc
    | head           :: tail -> loop tail (head :: acc)
    | []                     -> List.rev acc
  in loop tokens []

and parse_module tokens ctx =
  print_endline ("Parsing \"" ^ ctx.curr ^ "\"...");
  let clean = remove_comments tokens in
  let imports, rest = parse_imports clean ctx in
  let rec loop t acc =
    match t with
    | (EOF, _) :: _ -> List.rev acc
    | _             -> let item, rest = parse_item t ctx in loop rest (item :: acc)
  in
  let items = loop rest [] in
  { name = String.split_on_char '/' (ctx.dir ^ (Filename.chop_extension ctx.curr)); imports; items }






and parse main = 
  let tokens, lexer_ctx = tokenize main in
  let abs  = Unix.realpath    main in
  let dir  = Filename.dirname  abs in
  let curr = Filename.basename abs in
  let tbl  = Hashtbl.create 8      in
  let ctx  = empty_ctx tbl dir curr lexer_ctx.newlines in
  let m    = parse_module tokens ctx in
  Hashtbl.add tbl [curr] m;
  List.iter (fun i -> load_import i ctx) m.imports;
  ctx