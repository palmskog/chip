val modified : int -> int ->
  (int -> string) ->
  (int -> string) ->
  int list

val checkable_impacted : int ->
  (int -> int list) ->
  (int -> string) ->
  (int -> string) ->
  (int -> bool) ->
  int list

val impacted_fresh : int -> int ->
  (int -> int list) ->
  (int -> string) ->
  (int -> string) ->
  int list

val checkable_impacted_fresh : int -> int ->
  (int -> int list) ->
  (int -> string) ->
  (int -> string) ->
  (int -> bool) ->
  int list

val topsort : int -> int ->
  (int -> int list) ->
  (int -> string) ->
  (int -> string) ->
  (int -> bool) ->
  (int -> int list) ->
  int list

val hierarchical_impacted_fresh :
  int -> int -> (* top *)
  (int -> int list) ->
  (int -> string) ->
  (int -> string) ->
  int -> int -> (* bot *)
  (int -> int list) ->
  (int -> string) ->
  (int -> string) ->
  (int -> int list) -> (* partition *)
  int list    

val hierarchical_checkable_impacted_fresh :
  int -> int -> (* top *)
  (int -> int list) ->
  (int -> string) ->
  (int -> string) ->
  int -> int -> (* bot *)
  (int -> int list) ->
  (int -> string) ->
  (int -> string) ->
  (int -> bool) ->
  (int -> int list) -> (* partition *)
  int list
