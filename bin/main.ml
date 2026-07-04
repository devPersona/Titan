open Ast
open Parse.Lexer

let run main =
  try 
    let _tokens = tokenize main in ()
  with Err _ -> ()

let () = run "input.ttn"