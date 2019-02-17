open Impacted
open Util

let modified num_new num_old f_new f_old =
  Obj.magic
    (succs_modified
       num_new (num_old-1)
       (Obj.magic (fun x -> char_list_of_string (f_new x)))
       (Obj.magic (fun x -> char_list_of_string (f_old x))))

let checkable_impacted num successors f_new f_old chk =
  Obj.magic
    (succs_checkable_impacted
       num (num-1)
       (Obj.magic successors)
       (Obj.magic (fun x -> char_list_of_string (f_new x)))
       (Obj.magic (fun x -> char_list_of_string (f_old x)))
       chk)

let impacted_fresh num_new num_old successors f_new f_old =
  Obj.magic
    (succs_impacted_fresh
       num_new (num_old-1)
       (Obj.magic successors)
       (Obj.magic (fun x -> char_list_of_string (f_new x)))
       (Obj.magic (fun x -> char_list_of_string (f_old x))))

let checkable_impacted_fresh num_new num_old successors f_new f_old chk =
  Obj.magic
    (succs_checkable_impacted_fresh  
       num_new (num_old-1)
       (Obj.magic successors)
       (Obj.magic (fun x -> char_list_of_string (f_new x)))
       (Obj.magic (fun x -> char_list_of_string (f_old x)))
       chk)

let topsort num_new num_old successors f_new f_old chk successors' =
  Obj.magic
    (succs_ts
       num_new (num_old-1)
       (Obj.magic successors)
       (Obj.magic (fun x -> char_list_of_string (f_new x)))
       (Obj.magic (fun x -> char_list_of_string (f_old x)))
       chk
       (Obj.magic successors'))

let hierarchical_checkable_impacted_fresh
    top_num_new top_num_old top_successors top_f_new top_f_old
    bot_num_new bot_num_old bot_successors bot_f_new bot_f_old bot_chk
    partition =
  Obj.magic
    (succs_hierarchical_checkable_impacted_fresh
       top_num_new (top_num_old-1)
       (Obj.magic top_successors)
       (Obj.magic (fun x -> char_list_of_string (top_f_new x)))
       (Obj.magic (fun x -> char_list_of_string (top_f_old x)))
       bot_num_new (bot_num_old-1)
       (Obj.magic bot_successors)
       (Obj.magic (fun x -> char_list_of_string (bot_f_new x)))
       (Obj.magic (fun x -> char_list_of_string (bot_f_old x)))
       bot_chk
       (Obj.magic partition))
