open Ast
open Span

let print_list list func = List.iter (fun i -> func i |> print_endline) list

let debug_span s nl_list =
  let (ls, cs), (le, ce) = line_col_of_span s nl_list in
  let line = if ls = le then string_of_int ls else string_of_int ls ^ "-" ^ string_of_int le in
  let col  = if cs = ce then string_of_int cs else string_of_int cs ^ "-" ^ string_of_int ce in
  "line " ^ line ^ ", col " ^ col
let concat sep strs = (String.concat sep strs) ^ sep
let concat_list sep func items = String.concat sep (List.map func items)

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
  | New -> "New"

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
  | KwTrace   -> "Trace"

let debug_punc p =
  match p with
  | Dot      -> "."
  | CC       -> ".."
  | Col      -> ":"
  | Comma    -> ","
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




let rec get_ret t =
  match t with
  | TFunc (_, r) -> r
  | TPoly (t, _) -> get_ret t
  | _            -> assert false

let rec debug_type t = 
  match t with
  | TName (n, _) -> "TName \"" ^ n ^ "\""
  | TClass    n  -> "TClass \"" ^ n ^ "\""
  | TTypename n  -> "TTypename \"" ^ n ^ "\""
  | TPath (p, _, t) -> concat ".." p ^ debug_type t
  | TNamed (n, t) -> n.name ^ ":" ^ debug_type t
  | TDefault (t, d) -> debug_type t ^ " = " ^ debug_expr d
  | TTuple types -> "TTuple(" ^ concat_list ", " debug_type types ^ ")"
  | TArray t     -> "TArray<" ^ debug_type t ^ ">"
  | TPtr   t     -> "TPtr<"   ^ debug_type t ^ ">"
  | TGeneric (t, g) -> debug_type t ^ "<" ^ concat_list ", " debug_generic_arg g ^ ">"
  | TPoly    (t, g) -> "Poly<" ^ concat_list ", " debug_generic_param g ^ ">(" ^ debug_type t ^ ")"
  | TFunc (p, r) -> "TFunc(" ^ debug_type p ^ ")->(" ^ debug_type r ^ ")"
  | TVoid        -> "Void"
  | TUnit        -> "()"
  | TUnknown     -> "TUnknown"

and debug_expr e =
  let expr = 
    match e.expr with
    | EEmpty              -> "Empty"
    | ELit    b           -> debug_basic b
    | EVar    n           -> "EVar \"" ^ n ^ "\""
    | EThis               -> "This"
    | EBinOp (e1, op, e2) -> "BinOp(" ^ debug_expr e1 ^ " " ^ debug_op op ^ " " ^ debug_expr e2 ^ ")"
    | ELUnOp (    op, e ) -> "LUnOp(" ^                       debug_op op ^       debug_expr e  ^ ")"
    | ERUnOp (e,  op    ) -> "RUnOp(" ^ debug_expr e  ^       debug_op op ^                       ")"
    | EArray exprs        -> "[" ^ concat_list ", " debug_expr exprs ^                       "]"
    | ETuple exprs        -> "(" ^ concat_list ", " debug_expr exprs ^                       ")"
    | EIf    (c,  t,  e ) -> "If (" ^ debug_expr c ^ ") then " ^ debug_expr t ^ if e.expr = EEmpty then "" else " else " ^ debug_expr e
    | ECall  (t,  a     ) -> "Call " ^ debug_expr t ^ " with args (" ^ debug_expr a ^ ")"
    | EAddress    e       -> "Address of (" ^ debug_expr e ^ ")"
    | EField (t,  f     ) -> "Field Access (" ^ debug_expr t ^ "." ^ debug_expr f ^ ")"
    | EIndex (t,  i     ) -> "Array Access (" ^ debug_expr t ^ ")" ^ debug_expr i
    | EGeneric   (t,  g ) -> "Generic " ^ debug_expr t ^ "<" ^ concat_list ", " debug_generic_arg g ^ ">"
    | ENew    e           -> "New " ^ debug_expr e
    | EDecl   (n, t,  v ) -> "Decl " ^ n.name ^ " of " ^ debug_type t ^ if v.expr = EEmpty then "" else " as " ^ debug_expr v
    | ELambda (p, t,  b ) -> "Lambda(" ^ concat_list ", " debug_param p ^ ") returning " ^ debug_type (get_ret t) ^ ": " ^ debug_expr b
    | EReturn e           -> "Return " ^ debug_expr e
    | EPoly   (e, g     ) -> "Poly<" ^ concat_list ", " debug_generic_param g ^ ">(" ^ debug_expr e ^ ")"
    | EType    t          -> "EType " ^ debug_type t 
    | EBlock   stmts      -> "Block { " ^ concat_list " ;\t" debug_stmt stmts ^ " }"
    | ETrace   e          -> "Trace " ^ debug_expr e 
  in expr

and debug_param p =
  concat " " (List.map debug_metadata p.metadata) ^ (fst p.param).name ^ " of " ^ debug_type (snd p.param)

and debug_generic_param g =
  let p = 
    match g.param with
    | GPConst    e -> "Const: " ^ debug_param {param = e; metadata = g.metadata; span = g.span}
    | GPTypename n -> "Typename: " ^ n
  in
  concat " " (List.map debug_metadata g.metadata) ^ p

and debug_stmt s =
  match s.stmt with
  | SExpr e -> debug_expr e

and debug_generic_arg g =
  match g.arg with
  | GAExpr e -> "Expr " ^ debug_expr e
  | GAType t -> "Type " ^ debug_type t


and debug_metadata_arg arg =
  match arg with
  | MAOp  op -> debug_op  op
  | MAExpr e -> debug_expr e

and debug_metadata m =
  match m.m with
  | MMeta (n, args) -> "@" ^ n ^ if args <> [] then "(" ^ (String.concat ", " (List.map debug_metadata_arg args)) ^ ")" else ""
  | _               -> assert false

and debug_modifier m = 
  match m.m with
  | MPublic  -> "Public"
  | MPrivate -> "Private"
  | MStatic  -> "Static"
  | MExtern  -> "Extern"
  | MInline  -> "Inline"
  | _        -> debug_metadata m

let debug_class_member_def member =
  match member with
  | CMField  info -> "Field " ^ info.name.name ^ ":" ^ debug_type info.typ ^ (if info.default.expr = EEmpty then "" else " = " ^ debug_expr info.default)
  | CMMethod info -> "Method " ^ info.name.name ^ "(" ^ concat_list ", " debug_param info.params ^ "):" ^ debug_type info.typ ^ " " ^ debug_expr info.body
  | CMNew    info -> "Constructor(" ^ concat_list ", " debug_param info.params ^ ") " ^ debug_expr info.body

let debug_class_member (member:class_member) =
  "\t" ^ concat " " (List.map debug_modifier member.mods) ^ debug_class_member_def member.member 

let debug_class (info:class_info) = 
  "Class " ^ info.name.name ^ " {\n\t" ^ String.concat "\n\t" (List.map debug_class_member info.members) ^ "\n}"

let debug_item i = 
  match i.item with
  | IClass info -> debug_class info
  | IStmt  stmt -> debug_stmt  stmt

let debug_import i = 
  "Import " ^ String.concat ".." i.path

let debug_module m =
  concat "\n" (List.map debug_import m.imports) ^ "\n" ^ String.concat "\n" (List.map debug_item m.items)


let debug_with_span func item span file nl = func item ^ " in file \"" ^ file ^ "\", " ^ debug_span span nl |> print_endline