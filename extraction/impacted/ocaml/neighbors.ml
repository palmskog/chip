open Yojson.Basic.Util
open Util
open ExtLib

let () =
  let json = Yojson.Basic.from_file Sys.argv.(1) in
  let list = to_list json in
  let nm = List.map (fun json -> to_list (member "neighbors" json)) list in
  let nm = List.map (fun json -> List.map to_int json) nm in
  let nm = List.flatten nm in
  List.iter (fun i -> print_string ((string_of_int i)^"\n")) nm

