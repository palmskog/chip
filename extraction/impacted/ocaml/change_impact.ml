open Impacted
open Util

let runnable_impacted num successors f_new f_old rnb =
  Obj.magic
    (succs_runnable_impacted
       num (num-1)
       (Obj.magic successors)
       (Obj.magic (fun x -> char_list_of_string (f_new x)))
       (Obj.magic (fun x -> char_list_of_string (f_old x)))
       rnb)

let impacted_fresh num_new num_old successors f_new f_old =
  Obj.magic
    (succs_impacted_fresh
       num_new (num_old-1)
       (Obj.magic successors)
       (Obj.magic (fun x -> char_list_of_string (f_new x)))
       (Obj.magic (fun x -> char_list_of_string (f_old x))))

let runnable_impacted_fresh num_new num_old successors f_new f_old rnb =
  Obj.magic
    (succs_runnable_impacted_fresh  
       num_new (num_old-1)
       (Obj.magic successors)
       (Obj.magic (fun x -> char_list_of_string (f_new x)))
       (Obj.magic (fun x -> char_list_of_string (f_old x)))
       rnb)

let topsort num_new num_old successors f_new f_old rnb successors' =
  Obj.magic
    (succs_ts
       num_new (num_old-1)
       (Obj.magic successors)
       (Obj.magic (fun x -> char_list_of_string (f_new x)))
       (Obj.magic (fun x -> char_list_of_string (f_old x)))
       rnb
       (Obj.magic successors'))
