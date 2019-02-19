open Yojson.Basic.Util
open Util
open ExtLib

let vertex_entry json =
  to_int (member "id" json)

let () =
  let json = Yojson.Basic.from_file Sys.argv.(1) in
  let list = to_list json in
  let ids = List.map (fun json -> to_int (member "id" json)) list in
  print_string (string_of_list (fun s -> string_of_int s) "\n" "\n" ids)
