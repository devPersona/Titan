open Ast
open Error

type lexer_ctx = {
  filename:   string;
  source:     string;
  mutable index: pos;
  mutable newlines: pos list 
}

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
  ("var",     KwVar    );
  ("func",    KwFunc   );
  ("return",  KwRet    );
  ("if",      KwIf     );
  ("else",    KwElse   );
  ("class",   KwClass  );
  ("public",  KwPublic );
  ("private", KwPrivate);
  ("static",  KwStatic );
  ("inline",  KwInline );
  ("extern",  KwExtern );
  ("import",  KwImport )
]
let kw_map   = kw_list |> List.to_seq |> StringMap.of_seq

let is_num   c = match c with '0' .. '9'                    -> true | _ -> false
let is_alpha c = match c with 'a' .. 'z' | 'A' .. 'Z' | '_' -> true | _ -> false
let is_alnum c = is_alpha c || is_num c

let is_ws    c = match c with ' ' | '\n' | '\t' | '\r'      -> true | _ -> false
let is_sep   c = is_ws c || is_op c || is_punc c

let span_make s_pos e_pos = 
  { s_pos; e_pos }
let span_of_pos pos = 
  span_make pos pos

let inc_ctx_by n ctx =
  ctx.index <- ctx.index + n
let inc_ctx ctx = 
  inc_ctx_by 1 ctx
let add_nl ctx =
  ctx.newlines <- ctx.index :: ctx.newlines
let inc_line ctx =
  add_nl ctx; inc_ctx ctx
let inc_and_get ctx =
  let span = span_make ctx.index (ctx.index + 1) in
  inc_ctx ctx; span



let consume_comment chars ctx =
  let buf = Buffer.create 16 in 
  let rec loop c =
    match c with
    | '\n' :: tail -> inc_line ctx; tail
    | head :: tail -> inc_ctx  ctx; Buffer.add_char buf head; loop tail
    | []           -> [] (* let tokenize_raw handle it *)
  in 
  let s_pos   = ctx.index  in
  inc_ctx_by 2 ctx; (* for the inital '//' *)
  let rest    = loop chars in
  (Comment (Buffer.contents buf), span_make s_pos ctx.index), rest

let consume_comment_block chars ctx =
  let buf = Buffer.create 16 in
  let rec loop c =
    match c with
    | '*' :: '/' :: tail -> inc_ctx_by 2 ctx; tail (* terminator *)
    | '\n'       :: tail -> inc_line     ctx; Buffer.add_char buf '\n'; loop tail
    | head       :: tail -> inc_ctx      ctx; Buffer.add_char buf head; loop tail
    | []                  -> err_at (Missing "*/") (span_of_pos ctx.index)  
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
    | '\n'         :: tail -> add_nl  ctx; add '\n' 1 tail
    | '\\' :: '"'  :: tail -> add '"'  2 tail
    | '\\' :: '\\' :: tail -> add '\\' 2 tail
    | '\\' :: 'n'  :: tail -> add '\n' 2 tail
    | '\\' :: 't'  :: tail -> add '\t' 2 tail
    | head         :: tail -> add head 1 tail
    | []                   -> err_at (Missing "\"") (span_of_pos ctx.index)  
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
  let num            = if dot then Float (float_of_string str) else Int (int_of_string str) in
  (Basic num, span_make s_pos ctx.index), rest

let consume_ident chars ctx =
  let rec loop c acc =
    match c with
    | head  :: tail when is_alnum head -> inc_ctx ctx; loop tail (head :: acc)
    | _                                -> (str_of_list (List.rev acc)), c
  in 
  let s_pos       = ctx.index     in
  let ident, rest = loop chars [] in
  let token       = 
    match StringMap.find_opt ident kw_map with
    | Some kw -> Kw    kw
    | None    -> Ident ident
  in (token, span_make s_pos ctx.index), rest


let tokenize_raw chars ctx =
  let rec loop c acc =
    match c with
    | []                                     -> List.rev ((EOF, span_of_pos ctx.index) :: acc)
    | '\n'       :: tail                     -> inc_line ctx; loop tail acc
    | ws         :: tail when is_ws     ws   -> inc_ctx  ctx; loop tail acc
    | '"'        :: tail                     -> let str,     rest = consume_str           tail ctx in loop rest (str     :: acc)
    | '/' :: '/' :: tail                     -> let comment, rest = consume_comment       tail ctx in loop rest (comment :: acc)
    | '/' :: '*' :: tail                     -> let comment, rest = consume_comment_block tail ctx in loop rest (comment :: acc)
    | op         :: tail when is_op     op   -> loop tail ((Op    (get_op   op  ), inc_and_get ctx) :: acc)
    | punc       :: tail when is_punc   punc -> loop tail ((Punc  (get_punc punc), inc_and_get ctx) :: acc)
    | num        :: _    when is_num    num  -> let num,     rest = consume_num           c    ctx in loop rest (num     :: acc)
    | alpha      :: _    when is_alpha alpha -> let ident,   rest = consume_ident         c    ctx in loop rest (ident   :: acc)
    | head       :: _                        -> err (Msg ("Unknown token: '" ^ str_of_char head ^ "'" ))
  in loop chars []

  


let read filename = 
  if not (Sys.file_exists filename) then err (Msg ("File not found: " ^ filename)) else
  In_channel.with_open_text filename In_channel.input_all

let tokenize filename =
  let source = read filename in
  let ctx    = { filename; source; index = 0; newlines = [] } in
  let chars  = List.init (String.length source) (String.get source) in
  tokenize_raw chars ctx 