type pos  = int (* byte offset *)
type span = { s_pos: pos; e_pos: pos } 

type basic =
| Int    of int
| Float  of float
| Bool   of bool
| String of string

type op =
| Add   (* +   *)
| Sub   (* -   *)
| Mul   (* *   *)
| Div   (* /   *)
| Asg   (* =   *)
| AA    (* +=  *)
| SA    (* -=  *)
| MA    (* *=  *)
| DA    (* /=  *)
| Eq    (* ==  *)
| Neq   (* !=  *)
| Gt    (* >   *)
| Ge    (* >=  *)
| Lt    (* <   *)
| Le    (* <=  *)
| Inc   (* ++  *)
| Dec   (* --  *)
| Not   (* !   *)
| And   (* &&  *)
| Or    (* ||  *)
| Xor   (* ^   *)
| Amp   (* &   *)
| Pip   (* |   *)
| Mod   (* %   *)
| New   (* new *)


type punc =
| Dot      (* .  *)
| CC       (* .. *)
| Col      (* :  *)
| Comma    (* ,  *)
| SemiCol  (* ;  *)
| QMark    (* ?  *)
| LParen   (* (  *)
| RParen   (* )  *)
| LBrace   (* {  *)
| RBrace   (* }  *)
| LBracket (* [  *)
| RBracket (* ]  *)
| RArrow   (* -> *)
| AtCol    (* @: *)

type kw = 
| KwVar    
| KwFunc   
| KwRet    
| KwIf     
| KwElse   
| KwClass  
| KwPublic 
| KwPrivate
| KwStatic 
| KwInline 
| KwExtern 
| KwImport 
| KwTrace  

type token_def =
| Basic   of basic
| Op      of op
| Punc    of punc
| Kw      of kw
| Ident   of string
| Comment of string
| EOF

type token = token_def * span


type lexer_ctx = {
  filename:   string;
  source:     string;
  newlines: pos list;
  mutable index: pos;
}



type path = string list
type placed_name = { name: string; span: span }

type module_ = {
  name:           path;
  imports: import list;
  items:   item   list;
}

and import = {
  path: path;
  span: span
}

and item = { item: item_def; span: span }
and item_def = 
| IClass of class_info
| IStmt  of stmt

and class_info = {
  name:            placed_name;
  mods:          modifier list;
  generics: generic_param list;
  members:   class_member list;
}

and class_member = { member: class_member_def; mods: modifier list; span: span; }

and class_member_def = 
| CMField  of class_field_info
| CMMethod of class_method_info
| CMNew    of class_constructor_info
and class_field_info       = { name: placed_name; generics: generic_param list;                          typ: t; default: expr }
and class_method_info      = { name: placed_name; generics: generic_param list; params: param_info list; typ: t; body:    expr }
and class_constructor_info = {                                                  params: param_info list; typ: t; body:    expr }




and t = 
| TName     of string * span          (* unresolved                  *)
| TClass    of string                 (* resolved, class name        *)
| TTypename of string                 (* resolved, generic type name *)
| TPath     of path * span * t        (* path..to..Module..Type      *)
| TNamed    of placed_name * t        (* a:T                         *)
| TDefault  of t * expr               (* T = expr                    *)
| TTuple    of t list                 (* (A, B)                      *)
| TArray    of t                      (* [T] or Array<T>             *)
| TPtr      of t                      (* T*  or Ptr<T>               *)
| TGeneric  of t * generic_arg   list (* A<B>                        *)
| TPoly     of t * generic_param list (* generic type declaration    *)
| TFunc     of t * t                  (* A->B                        *)
| TVoid  
| TUnit                               (* for empty tuples '()'       *)
| TUnknown                            (* uninferred type             *)





and stmt = { stmt: stmt_def; span: span }
and stmt_def =
| SExpr of expr

and expr = { expr: expr_def; mods: modifier list; span: span }
and expr_def =
| EEmpty 
| ELit     of basic
| EVar     of string
| EThis
| EBinOp   of expr * op   * expr
| ELUnOp   of op   * expr
| ERUnOp   of expr * op 
| EArray   of expr list
| ETuple   of expr list
| EIf      of expr * expr * expr
| ECall    of expr * expr
| EAddress of expr
| EField   of expr * expr
| EIndex   of expr * expr
| EGeneric of expr * generic_arg list
| ENew     of expr
| EDecl    of placed_name * t * expr
| ELambda  of param_info list * t * expr
| EReturn  of expr
| EPoly    of expr * generic_param list
| EType    of t 
| EBlock   of stmt list
| ETrace   of expr

and param_info = { param: param_def; metadata: modifier list; span: span }
and param_def  = placed_name * t

and generic_param = { param: generic_param_def; metadata: modifier list; span: span }
and generic_param_def = 
| GPTypename of string
| GPConst    of param_def
and generic_arg = { arg: generic_arg_def; metadata: modifier list; span: span }
and generic_arg_def = 
| GAType of t
| GAExpr of expr

and modifier = { m: modifier_def; span: span }
and modifier_def =
| MPublic
| MPrivate
| MStatic
| MInline
| MExtern
(* metadata *)
| MMeta   of string *  meta_arg list
| MSet    of string    meta_arg_span                           (* setter referencing a field,            on class methods            *)
| MGet    of string    meta_arg_span                           (* getter referencing a field,            on class methods            *)
| MProp   of meta_prop meta_arg_span * meta_prop meta_arg_span (* (get, set) field property,             on class fields             *)
| MOp     of meta_op   meta_arg_span                           (* operation overload,                    on class methods            *)
| MConst                                                       (* marks a variable as constant,          on declarations             *)
| MHide                                                        (* hides variable from IDE auto-complete, on declarations and classes *)
| MCopy
and meta_arg = (* general unchecked metadata argument *)
| MAExpr of expr
| MAOp   of op
and meta_prop =
| MPDefault (* default                   *)
| MPGet     (* getter                    *)
| MPSet     (* setter                    *)
| MPNull    (* only set/get inside class *)
| MPNever   (* never set/get             *)
and meta_op =
| MOExpr of expr
| MOOp   of op
and 'v meta_arg_span = { arg: 'v; span: span }



type parser_ctx = {
  tbl: (path, module_) Hashtbl.t;
  dir:            string;
  curr:           string;
  newlines:     pos list;
  mutable pos_s:     pos; (* start of position *)
  mutable pos_e:     pos; (* end   of position *)
  mutable allow_gt: bool; (* allow '>' to be treated as a binary operator, used for generic args *)
  mutable errors: err_kind list;
}


and err_kind = 
| Err_list       of err_kind list
| Syntax_err     of err_kind
| Err_in_file    of err_kind * string
| Err_at         of err_kind * span * pos list
| Msg            of string
| File_not_found of string
| Missing        of string
| Expected       of string
| Invalid        of string


exception Err of err_kind