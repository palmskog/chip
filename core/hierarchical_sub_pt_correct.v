From mathcomp.ssreflect Require Import all_ssreflect.
From mathcomp.tarjan Require Import extra acyclic.
From chip Require Import closure check change hierarchical_sub.
From chip Require Import hierarchical_sub_correct hierarchical_sub_pt.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section ChangedHierarchicalSubPt.

Variables (A_top : eqType) (A_bot : eqType).

Variables (U' : finType) (V' : finType).

Variables (f'_top : U' -> A_top) (f'_bot : V' -> A_bot).

Variables (P_top : pred U') (P_bot : pred V').

Local Notation U := (sig_finType P_top).

Local Notation V := (sig_finType P_bot).

Variable (g'_top : rel U') (g'_bot : rel V').

Local Notation g'_top_rev := [rel x y | g'_top y x].

Local Notation g'_bot_rev := [rel x y | g'_bot y x].

Variables (f_top : U -> A_top) (f_bot : V -> A_bot).

Variables (g_top : rel U) (g_bot : rel V).

Local Notation g_top_rev := [rel x y | g_top y x].

Local Notation g_bot_rev := [rel x y | g_bot y x].

Variables (checkable' : pred V') (checkable : pred V).

Variable R : eqType.

Variables (check : V -> R) (check' : V' -> R).

Variables (p : U -> {set V}) (p' : U' -> {set V'}).

Hypothesis p_neq : forall (u u' : U), u <> u' -> p u <> p u'.

Hypothesis p'_neq : forall (u u' : U'), u <> u' -> p' u <> p' u'.

Hypothesis p_partition : partition (\bigcup_( u | u \in U ) [set p u]) [set: V].

Hypothesis p'_partition : partition (\bigcup_( u | u \in U' ) [set p' u]) [set: V'].

Hypothesis g_bot_top : forall (v v' : V) (u u' : U),
 u <> u' -> g_bot v v' -> v \in p u -> v' \in p u' -> g_top u u'.

Hypothesis f_top_bot : forall (u : U),
 f_top u = f'_top (val u) -> forall (v : V), v \in p u -> f_bot v = f'_bot (val v).

Hypothesis f_top_partition : forall (u : U),
 f_top u = f'_top (val u) -> [set val v | v in p u] = p' (val u).

Local Notation insub_g_top x y := (insub_g g_top x y).

Local Notation g_top_U' := [rel x y : U' | insub_g_top x y].

Local Notation g_top_U'_rev := [rel x y | g_top_U' y x].

Local Notation insub_g_bot x y := (insub_g g_bot x y).

Local Notation g_bot_V' := [rel x y : V' | insub_g_bot x y].

Local Notation g_bot_V'_rev := [rel x y | g_bot_V' y x].

Hypothesis f_top_equal_g_top :
  forall u, f_top u = f'_top (val u) -> forall u', g_top_U' (val u) u' = g'_top (val u) u'.

Hypothesis f_bot_equal_g_bot :
  forall v, f_bot v = f'_bot (val v) -> forall v', g_bot_V' (val v) v' = g'_bot (val v) v'.

Hypothesis checkable_bot :
  forall v, f_bot v = f'_bot (val v) -> checkable v = checkable' (val v).

Hypothesis check_bot :
  forall v, checkable v -> checkable' (val v) ->
  (forall v', connect g_bot_V' (val v) v' = connect g'_bot (val v) v') ->
  (forall v', connect g_bot_V' (val v) (val v') -> f_bot v' = f'_bot (val v')) ->
  check v = check' (val v).

Variable V_result_cert : seq (V * R).

Hypothesis V_result_certP :
  forall v r, reflect (checkable v /\ check v = r) ((v,r) \in V_result_cert).

Hypothesis V_result_cert_uniq : uniq [seq vr.1 | vr <- V_result_cert].

Local Notation V_sub := (sig_finType (P_V_sub f'_top g_top f_top p)).

Local Notation g_bot_sub := [rel x y : V_sub | g_bot (val x) (val y)].

Definition V'_result_filter_cert_sub_pt :=
  [seq (val vr.1, vr.2) | vr <- V_result_cert & val vr.1 \notin impactedVV' g_bot (modifiedV f'_bot f_bot)].

Definition check_all_cert_sub_pt :=
  check_impactedV'_sub_pt_cert f'_top f'_bot g_top g_bot f_top f_bot checkable' check' p p' ++ V'_result_filter_cert_sub_pt.

Definition check_all_cert_V'_sub_pt :=
 [seq vr.1 | vr <- check_all_cert_sub_pt].

Lemma check_all_cert_complete_sub_pt :
  forall (v : V'), checkable' v -> v \in check_all_cert_V'_sub_pt.
Proof.
rewrite /check_all_cert_V'_sub_pt /check_all_cert_sub_pt.
rewrite /check_impactedV'_sub_pt_cert.
rewrite /checkable_impacted_fresh_sub_pt.
rewrite /checkable_impactedV'_sub_pt.
rewrite impactedV'_sub_pt_eq.
apply: check_all_cert_complete; eauto.
- exact: p_neq.
- exact: p_partition.
- exact: p'_partition.
- exact: g_bot_top.  
- exact: f_top_bot.
- exact: f_top_partition.
Qed.

Lemma check_all_cert_sound_sub_pt :
  forall (v : V') (r : R), (v,r) \in check_all_cert_sub_pt ->
  checkable' v /\ check' v = r.
Proof.
move => v r.
rewrite /check_all_cert_sub_pt.
rewrite /check_impactedV'_sub_pt_cert.
rewrite /checkable_impacted_fresh_sub_pt.
rewrite /checkable_impactedV'_sub_pt.
rewrite impactedV'_sub_pt_eq.
apply: check_all_cert_sound; eauto.
- exact: p_neq.
- exact: p_partition.
- exact: p'_partition.  
- exact: g_bot_top.
- exact: f_top_bot.
- exact: f_top_partition.  
Qed.

Lemma check_all_cert_V'_sub_pt_uniq : uniq check_all_cert_V'_sub_pt.
Proof.
rewrite /check_all_cert_V'_sub_pt.
rewrite /check_all_cert_sub_pt.
rewrite /check_impactedV'_sub_pt_cert.
rewrite /checkable_impacted_fresh_sub_pt.
rewrite /checkable_impactedV'_sub_pt.
rewrite impactedV'_sub_pt_eq.
apply: check_all_cert_V'_uniq; eauto.
- exact: p_neq.
- exact: p_partition.
- exact: p'_partition.
- exact: g_bot_top.
- exact: f_top_bot.
- exact: f_top_partition.  
Qed.

End ChangedHierarchicalSubPt.
