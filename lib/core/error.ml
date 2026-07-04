open Ast

let err         kind           = raise (Err kind)
let err_at      kind span      = err (Err_at (kind, span))
let err_in_file kind span file = err (Err_in_file (Err_at (kind, span), file))