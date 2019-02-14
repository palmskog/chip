From mathcomp
Require Import all_ssreflect.
From chip
Require Import string dfs_set finn_set.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlString.

Extract Inlined Constant negb => "not".
Extract Inlined Constant app => "ExtLib.List.append".
Extract Inlined Constant fst => "fst".
Extract Inlined Constant snd => "snd".
Extract Inlined Constant List.rev_append => "ExtLib.List.rev_append".

Extract Inlined Constant eqn => "(=)".
Extract Inlined Constant leq => "(<=)".
Extract Inlined Constant filter => "ExtLib.List.filter".
Extract Inlined Constant cat => "ExtLib.List.append".
Extract Inlined Constant map => "ExtLib.List.map".
Extract Inlined Constant foldl => "ExtLib.List.fold_left".
Extract Inlined Constant foldr => "(fun a b c -> ExtLib.List.fold_right a c b)".
Extract Inlined Constant size => "ExtLib.List.length".
Extract Inlined Constant nth => "(fun e l n -> match ExtLib.List.nth_opt l n with None -> e | Some e' -> e')".

Extract Inlined Constant eq_string => "(=)".
Extract Inlined Constant subltn => "(fun _ _ -> (<))".

Extract Constant SetDef.pred_of_set => "fun t a -> Obj.magic (FunFinfun.fun_of_fin t ((set_subType t).val0 (Obj.magic a)))".

Extract Constant fintype.Finite.base2 => "fun c -> { Countable.base = c.base; Countable.mixin = (Obj.magic mixin_base __ c.mixin) }".

Extraction "extraction/impacted-rbt/ocaml/impacted_rbt.ml" set_subType OrdinalsCheckableImpacted OrdinalsHierarchicalCheckableImpacted.
