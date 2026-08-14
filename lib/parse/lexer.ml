open Ast
open Span
open Error


module CharMap   = Map.Make(Char)
module StringMap = Map.Make(String)


let str_of_char c     = 
  String.make 1 c
let str_of_list chars = 
  chars |> List.to_seq |> String.of_seq

let op_list = [
  ('+', Add);
  ('-', Sub);
  ('*', Mul);
  ('/', Div);
  ('=', Asg);
  ('>', Gt );
  ('<', Lt );
  ('!', Not);
  ('^', Xor);
  ('&', Amp);
  ('|', Pip);
  ('%', Mod);
]
let op_map   = op_list |> List.to_seq |> CharMap.of_seq
let get_op c = CharMap.find c op_map
let is_op  c = CharMap.mem  c op_map

let punc_list = [
  ('.', Dot     );
  (',', Comma   );
  (':', Col     );
  (';', SemiCol );
  ('?', QMark   );
  ('(', LParen  );
  (')', RParen  );
  ('{', LBrace  );
  ('}', RBrace  );
  ('[', LBracket);
  (']', RBracket)
]
let punc_map   = punc_list |> List.to_seq |> CharMap.of_seq
let get_punc p = CharMap.find p punc_map
let is_punc  p = CharMap.mem  p punc_map

let kw_list = [
  ("var",      KwVar    );
  ("function", KwFunc   );
  ("return",   KwRet    );
  ("if",       KwIf     );
  ("else",     KwElse   );
  ("class",    KwClass  );
  ("public",   KwPublic );
  ("private",  KwPrivate);
  ("static",   KwStatic );
  ("inline",   KwInline );
  ("extern",   KwExtern );
  ("import",   KwImport )
]
let kw_map   = kw_list |> List.to_seq |> StringMap.of_seq

let is_num   c = match c with '0' .. '9'                    -> true | _ -> false
let is_alpha c = match c with 'a' .. 'z' | 'A' .. 'Z' | '_' -> true | _ -> false
let is_alnum c = is_alpha c || is_num c

let is_ws    c = match c with ' ' | '\n' | '\t' | '\r'      -> true | _ -> false
let is_sep   c = is_ws c || is_op c || is_punc c


let inc_ctx_by n ctx =
  ctx.index <- ctx.index + n
let inc_ctx ctx = 
  inc_ctx_by 1 ctx
let inc_and_get ctx =
  let span = span_make ctx.index (ctx.index + 1) in
  inc_ctx ctx; span



let consume_comment chars ctx =
  let buf = Buffer.create 16 in 
  let rec loop c =
    match c with
    | '\n' :: tail -> tail
    | head :: tail -> inc_ctx ctx; Buffer.add_char buf head; loop tail
    | []           -> [] (* let tokenize_raw handle it *)
  in 
  let s_pos   = ctx.index  in
  inc_ctx_by 2 ctx; (* for the inital '//' *)
  let rest    = loop chars in
  let span    = span_make s_pos ctx.index in
  inc_ctx ctx; (* for the new line *)
  (Comment (Buffer.contents buf), span), rest

let consume_comment_block chars ctx =
  let buf = Buffer.create 16 in
  let rec loop c =
    match c with
    | '*' :: '/' :: tail -> inc_ctx_by 2 ctx; tail (* terminator *)
    | head       :: tail -> inc_ctx      ctx; Buffer.add_char buf head; loop tail
    | []                 -> err_in_file (Missing "'*/'") (span_of_pos ctx.index) ctx.newlines ctx.filename
  in
  let s_pos = ctx.index in
  inc_ctx_by 2 ctx; (* for the inital '/*' *)
  let rest  = loop chars in
  (Comment (Buffer.contents buf), span_make s_pos ctx.index), rest



let consume_str chars ctx =
  let buf = Buffer.create 16 in
  let rec loop c =
    match c with
    | '"'          :: tail -> inc_ctx ctx; tail (* terminator *)
    | '\\' :: '"'  :: tail -> add '"'  2 tail
    | '\\' :: '\\' :: tail -> add '\\' 2 tail
    | '\\' :: 'n'  :: tail -> add '\n' 2 tail
    | '\\' :: 't'  :: tail -> add '\t' 2 tail
    | head         :: tail -> add head 1 tail
    | []                   -> err_in_file (Missing "'\"'") (span_of_pos ctx.index) ctx.newlines ctx.filename
  and add c inc rest = inc_ctx_by inc ctx; Buffer.add_char buf c; loop rest
  in 
  let s_pos = ctx.index  in 
  inc_ctx ctx; (* for the inital '"' *)
  let rest  = loop chars in
  (Basic (String (Buffer.contents buf)), span_make s_pos ctx.index), rest


let consume_num chars ctx =
  let rec loop c dot acc =
    match c with
    | '.' :: tail when not dot    -> inc_ctx ctx; loop tail true ('.' :: acc)
    | num :: tail when is_num num -> inc_ctx ctx; loop tail dot  (num :: acc)
    | _                           -> (str_of_list (List.rev acc)), dot, c
  in 
  let s_pos          = ctx.index in
  let str, dot, rest = loop chars false [] in
  let num            = if dot then 
    let f = 
      match float_of_string_opt str with
      | Some f -> f
      | None   -> err_in_file (Msg "Float literal is too large") (span_of_pos ctx.index) ctx.newlines ctx.filename
    in Float f
  else 
    let i = 
      match int_of_string_opt str with
      | Some i -> i
      | None   -> err_in_file (Msg "Integer literal is too large") (span_of_pos ctx.index) ctx.newlines ctx.filename
    in Int i
  in
  (Basic num, span_make s_pos ctx.index), rest

let consume_ident chars ctx =
  let rec loop c acc =
    match c with
    | head  :: tail when is_alnum head -> inc_ctx ctx; loop tail (head :: acc)
    | _                                -> (str_of_list (List.rev acc)), c
  in 
  let s_pos       = ctx.index     in
  let ident, rest = loop chars [] in
  let token       = if ident = "new" then Op New else
    match StringMap.find_opt ident kw_map with
    | Some kw -> Kw    kw
    | None    -> Ident ident
  in (token, span_make s_pos ctx.index), rest


let tokenize_raw chars ctx =
  let rec loop c acc =
    match c with
    | []                                     -> List.rev ((EOF, span_of_pos ctx.index) :: acc)
    | ws         :: tail when is_ws     ws   -> inc_ctx  ctx; loop tail acc
    | '"'        :: tail                     -> let str,     rest = consume_str           tail ctx in loop rest (str     :: acc)
    | '/' :: '/' :: tail                     -> let comment, rest = consume_comment       tail ctx in loop rest (comment :: acc)
    | '/' :: '*' :: tail                     -> let comment, rest = consume_comment_block tail ctx in loop rest (comment :: acc)
    | '@' :: ':' :: tail                     -> inc_ctx_by 2 ctx; loop tail ((Punc AtCol, inc_and_get ctx) :: acc)
    | op         :: tail when is_op     op   -> loop tail ((Op    (get_op   op  ), inc_and_get ctx) :: acc)
    | punc       :: tail when is_punc   punc -> loop tail ((Punc  (get_punc punc), inc_and_get ctx) :: acc)
    | num        :: _    when is_num    num  -> let num,     rest = consume_num           c    ctx in loop rest (num     :: acc)
    | alpha      :: _    when is_alpha alpha -> let ident,   rest = consume_ident         c    ctx in loop rest (ident   :: acc)
    | head       :: _                        -> err_in_file (Msg ("Unknown token: '" ^ str_of_char head ^ "'" )) (span_make ctx.index (ctx.index + 1)) ctx.newlines ctx.filename
  in loop chars []




let merge_tokens tokens =
  let rec loop t acc =
    match t with
    | []                                                             -> List.rev acc
    | (Op   Add, s1) :: (Op   Asg, s2) :: tail when span_touch s1 s2 -> loop tail ((Op       AA, span_join s1 s2) :: acc)
    | (Op   Sub, s1) :: (Op   Asg, s2) :: tail when span_touch s1 s2 -> loop tail ((Op       SA, span_join s1 s2) :: acc)
    | (Op   Mul, s1) :: (Op   Asg, s2) :: tail when span_touch s1 s2 -> loop tail ((Op       MA, span_join s1 s2) :: acc)
    | (Op   Div, s1) :: (Op   Asg, s2) :: tail when span_touch s1 s2 -> loop tail ((Op       DA, span_join s1 s2) :: acc)
    | (Op   Asg, s1) :: (Op   Asg, s2) :: tail when span_touch s1 s2 -> loop tail ((Op       Eq, span_join s1 s2) :: acc)
    | (Op    Gt, s1) :: (Op   Asg, s2) :: tail when span_touch s1 s2 -> loop tail ((Op       Ge, span_join s1 s2) :: acc)
    | (Op    Lt, s1) :: (Op   Asg, s2) :: tail when span_touch s1 s2 -> loop tail ((Op       Le, span_join s1 s2) :: acc)
    | (Op   Add, s1) :: (Op   Add, s2) :: tail when span_touch s1 s2 -> loop tail ((Op      Inc, span_join s1 s2) :: acc)
    | (Op   Sub, s1) :: (Op   Sub, s2) :: tail when span_touch s1 s2 -> loop tail ((Op      Dec, span_join s1 s2) :: acc)
    | (Op   Not, s1) :: (Op   Asg, s2) :: tail when span_touch s1 s2 -> loop tail ((Op      Neq, span_join s1 s2) :: acc)
    | (Op   Amp, s1) :: (Op   Amp, s2) :: tail when span_touch s1 s2 -> loop tail ((Op      And, span_join s1 s2) :: acc)
    | (Op   Pip, s1) :: (Op   Pip, s2) :: tail when span_touch s1 s2 -> loop tail ((Op       Or, span_join s1 s2) :: acc)
    | (Op   Sub, s1) :: (Op    Gt, s2) :: tail when span_touch s1 s2 -> loop tail ((Punc RArrow, span_join s1 s2) :: acc)
    | (Punc Col, s1) :: (Punc Col, s2) :: tail when span_touch s1 s2 -> loop tail ((Punc     CC, span_join s1 s2) :: acc)
    | head                             :: tail                       -> loop tail (head                           :: acc)
  in loop tokens []




let read filename = 
  if not (Sys.file_exists filename) then err (File_not_found filename) else
  In_channel.with_open_text filename In_channel.input_all

let tokenize filename =
  let source = read filename in
  let ctx    = { filename; source; index = 0; newlines = get_nl_list source } in
  let chars  = List.init (String.length source) (String.get source) in
  tokenize_raw chars ctx |> merge_tokens, ctx