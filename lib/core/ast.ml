type pos  = int (* byte offset *)
type span = { s_pos: pos; e_pos: pos } 

type basic =
| Int    of int
| Float  of float
| Bool   of bool
| String of string

type op =
| Add   (* +  *)
| Sub   (* -  *)
| Mul   (* *  *)
| Div   (* /  *)
| Asg   (* =  *)
| AA    (* += *)
| SA    (* -= *)
| MA    (* *= *)
| DA    (* /= *)
| Eq    (* == *)
| Neq   (* != *)
| Gt    (* >  *)
| Ge    (* >= *)
| Lt    (* <  *)
| Le    (* <= *)
| Inc   (* ++ *)
| Dec   (* -- *)
| Not   (* !  *)
| And   (* && *)
| Or    (* || *)
| Xor   (* ^  *)
| Amp   (* &  *)
| Pip   (* |  *)
| Mod   (* %  *)


type punc =
| Dot      (* .  *)
| DD       (* .. *)
| Col      (* :  *)
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

type token_def =
| Basic   of basic
| Op      of op
| Punc    of punc
| Kw      of kw
| Ident   of string
| Comment of string
| EOF

type token = token_def * span










type err_kind = 
| Err_in_file of err_kind * string
| Err_at      of err_kind * span
| Msg         of string
| Missing     of string


exception Err of err_kind