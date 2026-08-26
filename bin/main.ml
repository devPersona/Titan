open Ast
open Debug
open Error
open Parse.Lexer
open Parse.Parser
open Semantics.Resolve


let run main =
  try 
    let parse_ctx = parse main in 
    if parse_ctx.errors <> [] then err (Err_list (List.rev parse_ctx.errors));
    let resolve_ctx, resolved = resolve (Filename.chop_extension main) parse_ctx.tbl in
    if resolve_ctx.errors <> [] then err (Err_list (List.rev resolve_ctx.errors)); ()
  with Err kind -> handle_err kind

let () = run "input.ttn"