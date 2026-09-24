open Ast

let std_name = ["std"]
let std_path = "std.ttn"

let id_counter = ref 256
let new_id() =
  let id = !id_counter in
  id_counter := !id_counter + 1;
  id

let voidID     = 0
let intID      = 1
let floatID    = 2
let boolID     = 3
let charID     = 4
let stringID   = 5
let ptrID      = 6
let arrayID    = 7
let fixedArrID = 8

let get_std_id name = 
  match name with
  | "Void"       -> voidID
  | "Int"        -> intID
  | "Float"      -> floatID
  | "Bool"       -> boolID
  | "Char"       -> charID
  | "String"     -> stringID
  | "Ptr"        -> ptrID
  | "Array"      -> arrayID
  | "FixedArray" -> fixedArrID
  | _            -> new_id()