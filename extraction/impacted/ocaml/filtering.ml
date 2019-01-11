open Yojson.Basic.Util
open Util
open ExtLib

let new_vertex_entry json =
  let id = to_int (member "id" json) in
  let uri = to_string (member "uri" json) in
  let checkable = to_bool (member "checkable" json) in
  let checksum = to_string (member "checksum" json) in
  (id, uri, checkable, checksum)

let old_vertex_entry json =
  let id = to_int (member "id" json) in
  let uri = to_string (member "uri" json) in
  let adjacent = List.map to_int (to_list (member "neighbors" json)) in
  let checkable = to_bool (member "checkable" json) in
  let checksum = to_string (member "checksum" json) in
  (id, uri, adjacent, checkable, checksum)

let build_id_idx_tbl el =
  let tbl = Hashtbl.create (List.length el) in
  let idx = ref 0 in
  List.iter
    (fun (id, _, _, _, _) ->
      Hashtbl.add tbl id !idx;
      idx := !idx + 1)
    el;
  tbl

let extend_id_idx_tbl tbl el =
  let idx = ref (Hashtbl.length tbl) in
  List.iter
    (fun (id, _, _, _) ->
      if not (Hashtbl.mem tbl id) then
        (Hashtbl.add tbl id !idx;
         idx := !idx + 1))
    el;
  tbl

let build_old_idx_arr old_id_idx_tbl el =
  let arr = Array.make (List.length el) (0, [], false, "") in
  List.iter
    (fun (id, uri, adjacent, checkable, checksum) ->
      let idx = Hashtbl.find old_id_idx_tbl id in
      let al = List.map (Hashtbl.find old_id_idx_tbl) adjacent in
      let elt = (id, al, checkable, checksum) in      
      arr.(idx) <- elt)    
    el;
  arr

let build_new_idx_arr new_id_idx_tbl el =
  let arr = Array.make (List.length el) (0, "", false, "") in
  List.iter
    (fun (id, uri, checkable, checksum) ->
      let idx = Hashtbl.find new_id_idx_tbl id in
      arr.(idx) <- (id, uri, checkable, checksum))
    el;
  arr

let build_succs_arr old_idx_arr =
  let arr = Array.make (Array.length old_idx_arr) [] in
  Array.iteri
    (fun idx (_, adjacent, _, _) ->
      List.iter (fun idx' -> arr.(idx') <- idx :: arr.(idx')) adjacent)
    old_idx_arr;
  arr

let () =
  let json_new = Yojson.Basic.from_file Sys.argv.(1) in
  let json_old = Yojson.Basic.from_file Sys.argv.(2) in

  let new_list = to_list json_new in
  let new_entries = List.map new_vertex_entry new_list in

  let old_list = to_list json_old in
  let old_entries = List.map old_vertex_entry old_list in

  let old_id_idx_tbl = build_id_idx_tbl old_entries in
  let old_idx_arr = build_old_idx_arr old_id_idx_tbl old_entries in

  let new_id_idx_tbl = extend_id_idx_tbl old_id_idx_tbl new_entries in
  let new_idx_arr = build_new_idx_arr new_id_idx_tbl new_entries in

  let succs_arr = build_succs_arr old_idx_arr in

  let num_new = Array.length new_idx_arr in
  let num_old = Array.length old_idx_arr in

  let successors k = succs_arr.(k) in
  let f_new k = let (_,_,_,checksum) = new_idx_arr.(k) in checksum in
  let f_old k = let (_,_,_,checksum) = old_idx_arr.(k) in checksum in
  let rnb k = let (_,_,checkable,_) = new_idx_arr.(k) in checkable in

  let rnb_imp_fr =
    Change_impact.checkable_impacted_fresh
      num_new num_old
      successors
      f_new f_old
      rnb
  in

  let res =
    List.map
      (fun k -> let (_,uri,_,_) = new_idx_arr.(k) in uri)
      rnb_imp_fr
  in

  print_string (string_of_list (fun s -> s) "\n" "\n" res)
