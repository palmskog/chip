open Impacted_rbt
open Util

let impacted_fresh num_new num_old successors f_new f_old =
  let module Ords =
      struct
        let n = num_new
        let m' = num_old - 1
      end
  in
  let module OCI = OrdinalsCheckableImpacted (Ords) in
  Obj.magic
    (OCI.succs_impacted_fresh
       (Obj.magic successors)
       (Obj.magic (fun x -> char_list_of_string (f_new x)))
       (Obj.magic (fun x -> char_list_of_string (f_old x))))

let checkable_impacted_fresh num_new num_old successors f_new f_old chk =
  let module Ords =
      struct
        let n = num_new
        let m' = num_old - 1
      end
  in
  let module OCI = OrdinalsCheckableImpacted (Ords) in
  Obj.magic
    (OCI.succs_checkable_impacted_fresh
       (Obj.magic successors)
       (Obj.magic (fun x -> char_list_of_string (f_new x)))
       (Obj.magic (fun x -> char_list_of_string (f_old x)))
       chk)

let topsort num_new num_old successors f_new f_old chk successors' =
  let module Ords =
      struct
        let n = num_new
        let m' = num_old - 1
      end
  in
  let module OCI = OrdinalsCheckableImpacted (Ords) in
  Obj.magic
    (OCI.succs_ts
       (Obj.magic successors)
       (Obj.magic (fun x -> char_list_of_string (f_new x)))
       (Obj.magic (fun x -> char_list_of_string (f_old x)))
       chk
       (Obj.magic successors'))

let hierarchical_checkable_impacted_fresh
    top_num_new top_num_old top_successors top_f_new top_f_old
    bot_num_new bot_num_old bot_successors bot_f_new bot_f_old bot_chk p =
  let module OrdsTop =
      struct
        let n = top_num_new
        let m' = top_num_old - 1
      end
  in
  let module OrdsBot =
      struct
        let n = bot_num_new
        let m' = bot_num_old - 1
      end
  in
  let module OHCI = OrdinalsHierarchicalCheckableImpacted (OrdsTop) (OrdsBot) in
  Obj.magic
    (OHCI.succs_checkable_impacted_fresh
       (Obj.magic top_successors)
       (Obj.magic bot_successors)
       (Obj.magic (fun x -> char_list_of_string (top_f_new x)))
       (Obj.magic (fun x -> char_list_of_string (top_f_old x)))
       (Obj.magic (fun x -> char_list_of_string (bot_f_new x)))
       (Obj.magic (fun x -> char_list_of_string (bot_f_old x)))
       bot_chk
       (Obj.magic p))
