open Ast
open Span
open Debug

let err         kind                   = raise  (Err kind)
let err_at      kind span nl_list      = err    (Err_at (kind, span, nl_list))
let err_in_file kind span nl_list file = err_at (Err_in_file (kind, file)) span nl_list


let rec string_of_err k =
  match k with
  | Err_in_file (k, f)    -> string_of_err k ^ "\nIn file \"" ^ f ^ "\""
  | Err_at      (k, s, n) -> string_of_err k ^ ", " ^ debug_span s n
  | Msg     m             -> m
  | Missing m             -> "Missing '" ^ m ^ "'"
  
let handle_err kind =
  "Fatal error: " ^ (string_of_err kind) |> print_endline
