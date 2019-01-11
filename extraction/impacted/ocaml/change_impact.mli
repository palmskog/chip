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
