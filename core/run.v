From mathcomp
Require Import all_ssreflect.

From chip
Require Import extra connect close_dfs closure.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section InvRel.

Variable T : finType.

Definition rinv (r : rel T) := [rel x y | r y x].

End InvRel.

Notation "r ^-1" := (rinv r).

Section Checked.

(* artifact *)
Variable A : eqType.

(* paths *)
Variable V' : finType.

Variable f' : V' -> A.

(* old graph *)
Variable P : pred V'.

Local Notation V := (sig_finType P).

Variable f : V -> A.

Variable g : rel V.

Variable runnable : pred V'.

Variable R : eqType.

Variable run : V' -> R.

Definition freshV' : {set V'} := [set v | ~~ P v].

Lemma sub_freshV' v' :
  (~~ @insub _ _ [subType of V] v') = (v' \in freshV').
Proof.
case Hs: (~~ _); case Hf: (_ \in _) => //.
- move/negP: Hf; case.
  have H_sp := (insubP [subType of V] v').
  destruct H_sp => //.
  by rewrite in_set.
- move/negP/negP: Hs => Hs.
  move: Hf.
  rewrite in_set.
  move/negP.
  case.
  have H_sp := (insubP [subType of V] v').  
  by destruct H_sp.
Qed.

Lemma freshV'P v' :
  reflect (forall v : V, val v != v') (v' \in freshV').
Proof.
apply: (iffP idP).
- rewrite in_set.
  move/negP => HP v.
  apply/negP.
  move/eqP => Hv.
  case: HP.
  rewrite -Hv.
  exact: valP.
- move => Hv.
  rewrite in_set.
  apply/negP => HP.
  have H_sp := (insubP [subType of V] v').
  destruct H_sp; last by move/negP: i; case.
  have Hvu := Hv u.
  move/negP/negP: Hvu.
  rewrite e.
  by move/eqP.
Qed.

Definition modifiedV := [set v | f v != f' (val v)].

Lemma not_modifiedP v :
  reflect (f v == f' (val v)) (v \notin modifiedV).
Proof.
apply: (iffP idP).
- move/negPf.
  rewrite in_set.
  by move/negP/negP.
- move => Hf.
  apply/negPf.
  rewrite in_set.
  by apply/negP/negP.
Qed.

Definition runnable_impactedV modified :=
  [set v in impacted g^-1 modified | runnable (val v)].

Definition runnable_impacted :=
  [seq (val v) | v <- enum (runnable_impactedV modifiedV)].

Lemma impactedVP (modified : {set V}) x :
  reflect
    (exists2 v, v \in modified & connect g^-1 v x)
    (x \in impacted g^-1 modified).
Proof. exact: impactedP. Qed.

Lemma impacted_closure : forall (modified : {set V}),
  [set x in closure g modified] = impacted g^-1 modified.
Proof.
move => modified.
apply/eqP.
rewrite eqEsubset.
apply/andP.
split.
- apply/subsetP.
  move => x.
  rewrite inE /=.
  move/closureP => [v Hv] Hc.
  apply/impactedVP.
  exists v => //.
  by apply/connect_rev.
apply/subsetP.
move => x.
move/impactedVP => [v Hv] Hc.
rewrite inE /=.
apply/closureP.
exists v => //.
by move/connect_rev: Hc.
Qed.

Lemma not_impactedP (modified : {set V}) x :
  reflect
  (forall v, connect g x v -> v \notin modified)
  (x \notin impacted g^-1 modified).
Proof.
apply: (iffP idP).
- move/impactedVP => Hex.
  move => v Hc.
  apply/negP => Hv.
  apply connect_rev in Hc.
  case: Hex.
  by exists v.
- move => Hc.
  apply/negP.
  move => Hx.
  move/impactedVP: Hx.
  move => [v Hv].
  move/connect_rev => /=.
  have ->: rel_of_simpl_rel [rel x' y' | g^-1 y' x'] = g by [].
  by move/Hc/negP.
Qed.

Definition impactedVV' modified := [set (val v) | v in impacted g^-1 modified].

Lemma impactedVV'_freshV' modified x :
  x \in impactedVV' modified -> x \notin freshV'.
Proof.
move => Hx.
rewrite in_set.
apply/negP.
move => HP.
move/negP: HP.
case.
move: Hx.
move/imsetP => [v [Hv Hx]].
rewrite Hx.
exact: valP.
Qed.

Definition impactedV' : {set V'} := impactedVV' modifiedV :|: freshV'.

Definition impacted_fresh : seq V' := enum impactedV'.

Lemma impactedV'P x :
  reflect ((x \in impactedVV' modifiedV /\ x \notin freshV') \/ (x \in freshV' /\ x \notin impactedVV' modifiedV))
          (x \in impactedV').
Proof.
apply: (iffP idP).
- rewrite in_set.
  move/orP.
  case => Hx.
  * left; split => //.
    move: Hx.
    exact: impactedVV'_freshV'.
  * right; split => //.
    apply/negP.
    by move/impactedVV'_freshV'/negP.
- case.
  * move => [Hx Hf].
    rewrite in_set.
    apply/orP.
    by left.
  * move => [Hx Hf].
    rewrite in_set.
    apply/orP.
    by right.
Qed.

Definition runnable_impactedV' :=
 [set v in impactedV' | runnable v].

Definition runnable_impacted_fresh : seq V' :=
 enum runnable_impactedV'.

Definition run_impactedV'_cert :=
  [seq (v, run v) | v <- runnable_impacted_fresh].

Lemma run_impactedV'_cert_run v r :
  (v,r) \in run_impactedV'_cert -> 
  runnable v /\ run v == r /\ v \in impactedV'.
Proof.
move/mapP => [v' Hv] Hc.
move: Hc Hv.
case =>->->.
rewrite mem_enum in_set.
move/andP => [Hc Hv].
by split.
Qed.

Lemma cert_run_impactedV'_run v r :
  runnable v ->
  run v == r ->
  v \in impactedV' ->
  (v,r) \in run_impactedV'_cert.
Proof.
move => Hc Hv Hi.
apply/mapP.
exists v; last by move/eqP: Hv=><-.
rewrite mem_enum in_set.
apply/andP.
by split.
Qed.

Lemma run_impactedV'_certP v r :
  reflect
    (runnable v /\ run v == r /\ v \in impactedV')
    ((v,r) \in run_impactedV'_cert).
Proof.
apply: (iffP idP).
- exact: run_impactedV'_cert_run.
- move => [Hc [Hv Hi]].
  exact: cert_run_impactedV'_run.
Qed.

Lemma run_impactedV'_cert_uniq :
  uniq [seq vr.1 | vr <- run_impactedV'_cert].
Proof.
rewrite map_inj_in_uniq.
- rewrite map_inj_uniq; first by rewrite enum_uniq.
  by move => x y; case.
- case => v1 r1.
  case => v2 r2.
  move => H1 H2 /= Heq.
  move: Heq H1 H2 =>-<-.
  move/mapP => [v1' Hv1' Hc1].
  rewrite mem_enum in Hv1'.
  case: Hc1 =><- Hr1.
  move/mapP => [v2' Hv2' Hc2].
  rewrite mem_enum in Hv2'.
  case: Hc2 =><- Hr2.
  by rewrite Hr1 Hr2.
Qed.

End Checked.

Section Other.

Variable A : eqType.
Variable V' : finType.
Variable f' : V' -> A.
Variable P : pred V'.
Local Notation V := (sig_finType P).
Variable f : V -> A.
Variables (g1 : rel V) (g2 : rel V).
Variable runnable : pred V'.
Variable R : eqType.
Variable run : V' -> R.

Hypothesis g1_g2_connect : connect g1 =2 connect g2.

Lemma connect_impactedV_eq modified :
  impacted g1^-1 modified = impacted g2^-1 modified.
Proof.
apply/eqP.
rewrite eqEsubset.
apply/andP.
split.
- apply/subsetP.
  move => x Hx.
  apply: rclosed_impacted; eauto.
  apply/impactedP.
  move/impactedP: Hx => [v Hv] Hc.
  exists v => //.
  apply connect_rev.
  rewrite -g1_g2_connect.
  by apply connect_rev.
- apply/subsetP.
  move => x Hx.
  apply: rclosed_impacted; eauto.
  apply/impactedP.
  move/impactedP: Hx => [v Hv] Hc.
  exists v => //.
  apply connect_rev.
  rewrite g1_g2_connect.
  by apply connect_rev.
Qed.

Lemma connect_impactedV'_eq :
  impactedV' f' f g1 = impactedV' f' f g2.
Proof.
apply/eqP.
rewrite eqEsubset.
apply/andP.
split.
- apply setSU.
  apply/subsetP.
  move => x.
  move/imsetP => [v Hi] Hv.
  apply/imsetP.
  exists v; last by [].
  by rewrite -connect_impactedV_eq.
- apply setSU.
  apply/subsetP.
  move => x.
  move/imsetP => [v Hi] Hv.
  apply/imsetP.
  exists v; last by [].
  by rewrite connect_impactedV_eq.
Qed.

Lemma connect_runnable_impactedV' :
  runnable_impactedV' f' f g1 runnable = runnable_impactedV' f' f g2 runnable.
Proof.
apply/eqP.
rewrite eqEsubset.
apply/andP.
split.
- apply/subsetP.
  move => x.
  rewrite in_set.
  move/andP => [Hi Hc].
  rewrite in_set.
  apply/andP.
  split => //.
  by rewrite -connect_impactedV'_eq.
- apply/subsetP.
  move => x.
  rewrite in_set.
  move/andP => [Hi Hc].
  rewrite in_set.
  apply/andP.
  split => //.
  by rewrite connect_impactedV'_eq.
Qed.

End Other.
