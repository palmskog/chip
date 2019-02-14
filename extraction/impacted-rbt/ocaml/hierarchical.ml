open Yojson.Basic.Util
open Util
open ExtLib

let new_vertex_entry json =
  let id = to_int (member "id" json) in
  let uri = to_string (member "uri" json) in
  let checkable = to_bool (member "checkable" json) in
  let checksum = to_string (member "checksum" json) in
  (id, uri, checkable, checksum)

let old_top_vertex_entry json =
  let id = to_int (member "id" json) in
  let uri = to_string (member "uri" json) in
  let checkable = to_bool (member "checkable" json) in
  let neighbors = List.map to_int (to_list (member "neighbors" json)) in
  let contents = List.map to_int (to_list (member "contents" json)) in
  let checksum = to_string (member "checksum" json) in
  (id, uri, checkable, neighbors, contents, checksum)

let old_bot_vertex_entry json =
  let id = to_int (member "id" json) in
  let uri = to_string (member "uri" json) in
  let checkable = to_bool (member "checkable" json) in
  let neighbors = List.map to_int (to_list (member "neighbors" json)) in
  let checksum = to_string (member "checksum" json) in
  (id, uri, checkable, neighbors, checksum)

let build_old_top_id_idx_tbl el =
  let tbl = Hashtbl.create (List.length el) in
  let idx = ref 0 in
  List.iter
    (fun (id, _, _, _, _,_) ->
      Hashtbl.add tbl id !idx;
      idx := !idx + 1)
    el;
  tbl

let build_old_top_id_idx_tbl el =
  let tbl = Hashtbl.create (List.length el) in
  let idx = ref 0 in
  List.iter
    (fun (id, _, _, _, _,_) ->
      Hashtbl.add tbl id !idx;
      idx := !idx + 1)
    el;
  tbl

let build_old_bot_id_idx_tbl el =
  let tbl = Hashtbl.create (List.length el) in
  let idx = ref 0 in
  List.iter
    (fun (id, _, _, _, _) ->
      Hashtbl.add tbl id !idx;
      idx := !idx + 1)
    el;
  tbl

let build_old_bot_idx_arr old_id_idx_tbl el =
  let arr = Array.make (List.length el) (0, [], false, "") in
  List.iter
    (fun (id, uri, checkable, neighbors, checksum) ->
      let idx = Hashtbl.find old_id_idx_tbl id in
      let al = List.map (Hashtbl.find old_id_idx_tbl) neighbors in
      let elt = (id, al, checkable, checksum) in
      arr.(idx) <- elt)
    el;
  arr

let build_old_top_idx_arr old_top_id_idx_tbl old_bot_id_idx_tbl el =
  let arr = Array.make (List.length el) (0, [], [], false, "") in
  List.iter
    (fun (id, uri, checkable, neighbors, contents, checksum) ->
      let idx = Hashtbl.find old_top_id_idx_tbl id in
      let al = List.map (Hashtbl.find old_top_id_idx_tbl) neighbors in
      let cl = List.map (Hashtbl.find old_bot_id_idx_tbl) contents in
      let elt = (id, al, cl, checkable, checksum) in
      arr.(idx) <- elt)
    el;
  arr

let extend_id_idx_tbl tbl el =
  let idx = ref (Hashtbl.length tbl) in
  List.iter
    (fun (id, _, _, _) ->
      if not (Hashtbl.mem tbl id) then
        (Hashtbl.add tbl id !idx;
         idx := !idx + 1))
    el;
  tbl    

let build_new_idx_arr new_id_idx_tbl el =
  let arr = Array.make (List.length el) (0, "", false, "") in
  List.iter
    (fun (id, uri, checkable, checksum) ->
      let idx = Hashtbl.find new_id_idx_tbl id in
      arr.(idx) <- (id, uri, checkable, checksum))
    el;
  arr

(* invert bot graph *)
let build_bot_succs_arr old_bot_idx_arr =
  let arr = Array.make (Array.length old_bot_idx_arr) [] in
  Array.iteri
    (fun idx (_, neighbors, _, _) ->
      List.iter (fun idx' -> arr.(idx') <- idx :: arr.(idx')) neighbors)
    old_bot_idx_arr;
  arr        

(* invert top graph *)
let build_top_succs_arr old_top_idx_arr =
  let arr = Array.make (Array.length old_top_idx_arr) [] in
  Array.iteri
    (fun idx (_, neighbors, _, _, _) ->
      List.iter (fun idx' -> arr.(idx') <- idx :: arr.(idx')) neighbors)
    old_top_idx_arr;
  arr

let () =
  let json_new = Yojson.Basic.from_file Sys.argv.(1) in
  let json_old = Yojson.Basic.from_file Sys.argv.(2) in

  let bot_new = to_list (member "bot" json_new) in
  let top_new = to_list (member "top" json_new) in

  let bot_old = to_list (member "bot" json_old) in
  let top_old = to_list (member "top" json_old) in

  let new_bot_entries = List.map new_vertex_entry bot_new in
  let new_top_entries = List.map new_vertex_entry top_new in

  let old_bot_entries = List.map old_bot_vertex_entry bot_old in
  let old_top_entries = List.map old_top_vertex_entry top_old in

  let old_bot_id_idx_tbl = build_old_bot_id_idx_tbl old_bot_entries in
  let old_bot_idx_arr = build_old_bot_idx_arr old_bot_id_idx_tbl old_bot_entries in

  let old_top_id_idx_tbl = build_old_top_id_idx_tbl old_top_entries in
  let old_top_idx_arr = build_old_top_idx_arr old_top_id_idx_tbl old_bot_id_idx_tbl old_top_entries in

  let new_bot_id_idx_tbl = extend_id_idx_tbl old_bot_id_idx_tbl new_bot_entries in
  let new_bot_idx_arr = build_new_idx_arr new_bot_id_idx_tbl new_bot_entries in

  let new_top_id_idx_tbl = extend_id_idx_tbl old_top_id_idx_tbl new_top_entries in
  let new_top_idx_arr = build_new_idx_arr new_top_id_idx_tbl new_top_entries in 

  let bot_succs_arr = build_bot_succs_arr old_bot_idx_arr in
  let top_succs_arr = build_top_succs_arr old_top_idx_arr in

  let num_top_new = Array.length new_top_idx_arr in
  let num_top_old = Array.length old_top_idx_arr in

  let num_bot_new = Array.length new_bot_idx_arr in
  let num_bot_old = Array.length old_bot_idx_arr in

  let top_successors k = top_succs_arr.(k) in
  let bot_successors k = bot_succs_arr.(k) in

  let top_f_new k = let (_,_,_,checksum) = new_top_idx_arr.(k) in checksum in
  let top_f_old k = let (_,_,_,_,checksum) = old_top_idx_arr.(k) in checksum in

  let bot_f_new k = let (_,_,_,checksum) = new_bot_idx_arr.(k) in checksum in
  let bot_f_old k = let (_,_,_,checksum) = old_bot_idx_arr.(k) in checksum in

  let bot_chk k = let (_,_,checkable,_) = new_bot_idx_arr.(k) in checkable in

  let partition k = let (_,_,contents,_,_) = old_top_idx_arr.(k) in contents in

  let bot_chk_imp_fr =
    Change_impact.hierarchical_checkable_impacted_fresh
      num_top_new num_top_old
      top_successors
      top_f_new top_f_old
      num_bot_new num_bot_old
      bot_successors
      bot_f_new bot_f_old
      bot_chk
      partition
  in

  let res =
    List.map
      (fun k -> let (_,uri,_,_) = new_bot_idx_arr.(k) in uri)
      bot_chk_imp_fr
  in

  print_string (string_of_list (fun s -> s) "\n" "\n" res)
