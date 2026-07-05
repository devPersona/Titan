open Ast
open Debug
open Error
open Parse.Lexer



let run main =
  try 
    let tokens, ctx = tokenize main in print_list tokens (fun ((t, s) as token)  -> (debug_token token) ^ "\nIn file " ^ main ^ ", " ^ debug_span s ctx.newlines)
  with Err kind -> handle_err kind 

let () = run "input.ttn"