open Ast
open Span

let print_list list func = List.iter (fun i -> func i |> print_endline) list

let debug_span s nl_list =
  let (ls, cs), (le, ce) = line_col_of_span s nl_list in
  let line = if ls = le then string_of_int ls else string_of_int ls ^ "-" ^ string_of_int le in
  let col  = if cs = ce then string_of_int cs else string_of_int cs ^ "-" ^ string_of_int ce in
  "line " ^ line ^ ", col " ^ col



let debug_basic b =
  match b with
  | Int    i -> "Int "   ^ string_of_int i
  | Float  f -> "Float " ^ string_of_float f
  | Bool   b -> "Bool "  ^ string_of_bool b
  | String s -> "String \"" ^ s ^ "\""
  
let debug_op op =
  match op with
  | Add -> "+"
  | Sub -> "-"
  | Mul -> "*"
  | Div -> "/"
  | Asg -> "="
  | AA  -> "+="
  | SA  -> "-="
  | MA  -> "*="
  | DA  -> "/="
  | Eq  -> "=="
  | Neq -> "!="
  | Gt  -> ">"
  | Ge  -> ">="
  | Lt  -> "<"
  | Le  -> "<="
  | Inc -> "++"
  | Dec -> "--"
  | Not -> "!"
  | And -> "&&"
  | Or  -> "||"
  | Xor -> "^"
  | Amp -> "&"
  | Pip -> "|"
  | Mod -> "%"

let debug_kw kw =
  match kw with
  | KwVar     -> "Var"
  | KwFunc    -> "Func"
  | KwRet     -> "Return"
  | KwIf      -> "If"
  | KwElse    -> "Else"
  | KwClass   -> "Class"
  | KwPublic  -> "Public"
  | KwPrivate -> "Private"
  | KwStatic  -> "Static"
  | KwInline  -> "Inline"
  | KwExtern  -> "Extern"
  | KwImport  -> "Import"

let debug_punc p =
  match p with
  | Dot      -> "."
  | DD       -> ".."
  | Col      -> ":"
  | SemiCol  -> ";"
  | QMark    -> "?"
  | LParen   -> "("
  | RParen   -> ")"
  | LBrace   -> "{"
  | RBrace   -> "}"
  | LBracket -> "["
  | RBracket -> "]"
  | RArrow   -> "->"
  | AtCol    -> "@:"

let debug_token (t, _) =
  let token =
    match t with 
    | Basic   b -> debug_basic b
    | Op      o -> "Op "    ^ (debug_op   o)
    | Punc    p -> "Punc "  ^ (debug_punc p)
    | Kw      k -> "Kw "    ^ (debug_kw   k)
    | Ident   i -> "Ident " ^ i
    | Comment c -> "Comment /* " ^ c ^ " */"
    | EOF       -> "EOF"
  in "Token: " ^ token

