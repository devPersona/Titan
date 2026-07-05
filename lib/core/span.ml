open Ast


let file_start_line = 1
let file_start_col  = 1


let span_make s_pos e_pos = 
  { s_pos; e_pos }
let span_of_pos pos = 
  span_make pos pos
let span_touch s1 s2 = 
  s1.e_pos = s2.s_pos
let span_join s1 s2 = 
  { s_pos = s1.s_pos; e_pos = s2.e_pos }



let get_nl_list source =
  let len = String.length source in
  let rec loop i acc =
    if i >= len then List.rev acc 
    else
      if String.get source i = '\n' then loop (i + 1) ((i + 1) :: acc)
      else loop (i + 1) acc
  in
  loop 0 []


let line_col_of_pos pos nl_list =
  let rec loop curr i l =
    match l with
    | line :: tail when line <= pos -> loop line (i + 1) tail
    | _                             -> i, curr
  in 
  let line_count, line_index = loop 0 0 nl_list in
  let line = line_count + file_start_line in  (* subtract the sentinel's extra count, then apply the real offset *)
  let col  = (pos - line_index) + file_start_col in
  line, col

let line_col_of_span span nl_list =
  let line_s, col_s = line_col_of_pos span.s_pos nl_list in
  let line_e, col_e = line_col_of_pos span.e_pos nl_list in
  (line_s, col_s), (line_e, col_e)