From mathcomp Require Import all_ssreflect.
From chip Require Import close_dfs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Closure.

Variable V : finType.
Variable g : rel V.
Variable modified : {set V}.

Definition impacted := \bigcup_( x | x \in modified) [set y | connect g x y].

Lemma impactedP x :
  reflect
    (exists2 v, v \in modified & connect g v x)
    (x \in impacted).
Proof.
apply: (iffP idP).
- move/bigcupP => [v H_v H_i].
  exists v; first by [].
  by rewrite inE in H_i.
- move => [v H_m H_c].
  apply/bigcupP.
  exists v; first by [].
  by rewrite inE.
Qed.

Lemma rclosed_impacted :
  forall x y, connect g x y -> x \in impacted -> y \in impacted.
Proof.
move => x y Hc.
move/bigcupP => [v Hv] Hcx.
apply/bigcupP.
exists v => //.
rewrite inE.
rewrite inE in Hcx.
exact: connect_trans Hcx Hc.
Qed.

End Closure.
