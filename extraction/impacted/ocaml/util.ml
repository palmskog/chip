let rec string_of_list f sep fin = function
  | [] -> ""
  | e :: [] -> f e ^ fin
  | e :: l -> f e ^ sep ^ string_of_list f sep fin l

let string_of_int_list =
  string_of_list string_of_int " " ""

let print_int_list l =
  print_string (string_of_int_list l)

let char_list_of_string s =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) []

let bytes_of_char_list l =
  let res = Bytes.create (List.length l) in
  let rec imp i = function
    | [] -> res
    | c :: l -> Bytes.set res i c; imp (i + 1) l in
  imp 0 l

let string_of_char_list l =
  Bytes.to_string (bytes_of_char_list l)
