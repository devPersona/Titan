open Ast
open Debug
open Error
open Parse.Lexer
open Parse.Parser



let run main =
  try 
    let parse_ctx = parse main in 
    if parse_ctx.errors <> [] then err (Err_list (List.rev parse_ctx.errors))
  with Err kind -> handle_err kind 

let () = run "input.ttn"