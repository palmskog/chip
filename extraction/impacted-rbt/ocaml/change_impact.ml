open Impacted_rbt
open Util

let impacted_fresh num_new num_old successors f_new f_old =
  let module Ords =
      struct
        let n = num_new
        let m' = num_old - 1
      end
  in
  let module OCI = OrdinalsRunnableImpacted(Ords) in
  Obj.magic
    (OCI.succs_impacted_fresh
       (Obj.magic successors)
       (Obj.magic (fun x -> char_list_of_string (f_new x)))
       (Obj.magic (fun x -> char_list_of_string (f_old x))))

let runnable_impacted_fresh num_new num_old successors f_new f_old rnb =
  let module Ords =
      struct
        let n = num_new
        let m' = num_old - 1
      end
  in
  let module OCI = OrdinalsRunnableImpacted(Ords) in
  Obj.magic
    (OCI.succs_runnable_impacted_fresh
       (Obj.magic successors)
       (Obj.magic (fun x -> char_list_of_string (f_new x)))
       (Obj.magic (fun x -> char_list_of_string (f_old x)))
       rnb)

let topsort num_new num_old successors f_new f_old rnb successors' =
    let module Ords =
      struct
        let n = num_new
        let m' = num_old - 1
      end
  in
  let module OCI = OrdinalsRunnableImpacted(Ords) in
  Obj.magic
    (OCI.succs_ts
       (Obj.magic successors)
       (Obj.magic (fun x -> char_list_of_string (f_new x)))
       (Obj.magic (fun x -> char_list_of_string (f_old x)))
       rnb
       (Obj.magic successors'))
