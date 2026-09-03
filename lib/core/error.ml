open Ast
open Span
open Debug


let err           kind                   = raise  (Err kind)
let err_at        kind span nl_list      = err    (Err_at (kind, span, nl_list))
let err_in_file   kind span nl_list file = err_at (Err_in_file (kind, file)) span nl_list
let err_in_module kind span (m:module_)  = err_in_file kind span m.newlines (String.concat "/" m.name ^ ".ttn")
let err_list      errs                   = err    (Err_list errs)

let make_err                kind                   = Err kind
let make_err_at             kind span nl_list      = Err_at (kind, span, nl_list)
let make_err_in_file        kind span nl_list file = make_err_at (Err_in_file (kind, file)) span nl_list
let make_err_in_module      kind span (m:module_)  = make_err_in_file kind span m.newlines (String.concat "/" m.name ^ ".ttn")

let rec string_of_err k =
  match k with
  | Err_in_file (k, f)    -> string_of_err k ^ "\nIn file \"" ^ f ^ "\""
  | Err_at      (k, s, n) -> string_of_err k ^ ", " ^ debug_span s n
  | Msg      m            -> m
  | File_not_found f      -> "File not found: " ^ f
  | Missing        m      -> "Missing "  ^ m
  | Expected       m      -> "Expected " ^ m
  | Invalid        m      -> "Invalid "  ^ m
  | Redef          n      -> "Redefinition of " ^ n
  | Redef_param    n      -> "Redefinition of parameter \"" ^ n ^ "\""
  | Redef_type     n      -> "Redefinition of type \"" ^ n ^ "\""
  | Undefined      n      -> "Undefined identifier \"" ^ n ^ "\""
  | Undefined_type n      -> "Undefined type \"" ^ n ^ "\""
  | _                     -> assert false

let rec handle_err kind =
  match kind with
  | Err_list   k -> (List.fold_left (fun acc k -> if List.mem k acc then acc else (k :: acc)) [] k) |> List.rev |> List.iter handle_err 
  | Syntax_err k -> "Syntax error: " ^ (string_of_err k)    |> print_endline
  | _            -> "Fatal error: "  ^ (string_of_err kind) |> print_endline
