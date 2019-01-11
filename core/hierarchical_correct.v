From mathcomp
Require Import all_ssreflect.

From chip
Require Import extra connect acyclic closure check change hierarchical.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section ChangedHierarchical.

Variables (A_top : eqType) (A_bot : eqType).

Variables (U' : finType) (V' : finType).

Variables (f'_top : U' -> A_top) (f'_bot : V' -> A_bot).

Variables (P_top : pred U') (P_bot : pred V').

Local Notation U := (sig_finType P_top).

Local Notation V := (sig_finType P_bot).

Variables (g'_top : rel U') (g'_bot : rel V').

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

Hypothesis f_top_partition : forall (u : U),
 f_top u = f'_top (val u) -> [set val v | v in p u] = p' (val u).

Hypothesis f_top_bot : forall (u : U),
 f_top u = f'_top (val u) -> forall (v : V), v \in p u -> f_bot v = f'_bot (val v).

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

Definition V'_result_filter_cert_p :=
  [seq (val vr.1, vr.2) | vr <- V_result_cert & val vr.1 \notin pimpacted_V' f'_top g_top f_top p'].

Definition check_all_cert_p :=
 check_pimpacted_V'_cert f'_top g_top f_top checkable' check' p' ++ V'_result_filter_cert_p.

Definition check_all_cert_V'_p :=
 [seq vr.1 | vr <- check_all_cert_p].

Lemma check_all_cert_complete_p :
  forall (v : V'), checkable' v -> v \in check_all_cert_V'_p.
Proof.
move => v Hc.
have H_sp := (insubP [subType of V] v).
destruct H_sp.
- have Hv: v \notin freshV' P_bot.
    apply/negP.
    move => Hv.
    move/freshV'P: Hv => Hv.
    move/negP: (Hv u) => Hv'.
    case: Hv'.
    by apply/eqP.
  apply/mapP.
  case Hv': (v \in pimpacted_V' f'_top g_top f_top p').
  * move/idP: Hv'.
    exists (v, check' v); last by [].
    rewrite mem_cat.
    apply/orP.
    left.
    by apply/check_pimpacted_V'_certP.
  * move/negP/negP: Hv'.
    exists (v, check u); last by [].
    rewrite mem_cat.
    apply/orP.
    right.
    apply/mapP.
    exists (u, check u); last by rewrite /= e.
    rewrite mem_filter.
    apply/andP; split; first by rewrite e.
    apply/V_result_certP.
    split => //.
    suff H_suff: f_bot u = f'_bot (val u) by rewrite checkable_bot //= e.
      apply/eqP.
      apply/not_modifiedP.
      apply/negP.
      move => Hu.
      move/negPn: Hv'.
      case.
      apply: pimpacted_V'_impactedV'; eauto.
      apply/impactedV'P.
      left.
      split => //.
      apply/imsetP.
      exists u; last by [].
      apply/impactedVP.
      by exists u.
- have Hv: v \in freshV' P_bot.
    rewrite -sub_freshV'.
    move/negP: i => Hp.
    apply/negP => Hs.
    case: Hp.
    have H_sp := (insubP [subType of V] v).
    move: Hs.
    by destruct H_sp.
  apply/mapP.
  exists (v, check' v) => //.
  rewrite mem_cat.
  apply/orP.
  left.
  apply/check_pimpacted_V'_certP.
  split => //; split => //.
  move: Hv.
  by apply: pimpacted_V'_fresh; eauto.
Qed.

Lemma check_all_cert_sound_p :
  forall (v : V') (r : R), (v,r) \in check_all_cert_p ->
  checkable' v /\ check' v = r.
Proof.
move => v r.
rewrite mem_cat.
move/orP; case.
- move/mapP => [v' Hc].
  case =>->->.
  split => //.
  move: Hc.
  rewrite mem_enum in_set.
  by move/andP => [Hp Hc].
- move/mapP.
  case; case => v' r' Hvr Hvr'.
  move: Hvr' Hvr.
  case =>->->.
  rewrite mem_filter.
  move/andP => /= [Hp Hv].
  have Hv': val v' \notin impactedV' f'_bot f_bot g_bot.
    apply/negP => Hv'.
    move/negP: Hp.
    case.
    by apply: pimpacted_V'_impactedV'; eauto.
  have Hf: val v' \notin freshV' P_bot.
    apply/negP => Hf.
    move/negP: Hp.
    case.
    by apply: pimpacted_V'_fresh; eauto.
  apply: check_all_cert_sound; eauto.
  rewrite mem_cat.
  apply/orP.
  right.
  apply/mapP.
  exists (v', r'); last by [].
  rewrite mem_filter.
  apply/andP; split => //.
  rewrite /=.
  apply/negP => Hi.
  move/impactedV'P: Hv'.
  case.
  by left.
Qed.

Lemma check_all_cert_V'_uniq_p : uniq check_all_cert_V'_p.
Proof.
rewrite map_inj_in_uniq.
- rewrite cat_uniq.
  apply/andP.
  split; last (apply/andP; split).
  * have Hu := check_pimpacted_V'_cert_uniq f'_top g_top f_top checkable' check' p'.
    move: Hu.
    exact: map_uniq.
  * apply/negP.
    case.
    move/hasP => [vr Hvr].
    move/mapP: Hvr => [vr' Hvr'].
    case: vr' Hvr' => v' r'.
    rewrite mem_filter.
    case: vr => /= v r.
    move/andP => [Hv Hvr].
    case => Hv'; move =>-> {r}.
    move/mapP => [v0 Hv0].
    case => Hvv0 Hr'.
    rewrite mem_enum -Hvv0 in Hv0.
    move/negP: Hv.
    case.
    rewrite -Hv'.
    move: Hv0.
    rewrite in_set.
    by move/andP => [Hp Hv0].
  * have Hm := map_uniq V_result_cert_uniq.
    rewrite map_inj_in_uniq; first by rewrite filter_uniq.
    case => v1 r1.
    case => v2 r2.
    rewrite /= => Hv1 Hv2.
    case.
    by move/val_inj =><-<-.
- case => v1 r1.
  case => v2 r2.
  rewrite /= 2!mem_cat.
  move/orP.
  case => Hv1; move/orP.
  * case => Hv2 Hv.
    + move: Hv Hv1 Hv2 =><-.
      move/mapP => [v1' Hv1' Hc1].
      rewrite mem_enum in Hv1'.
      case: Hc1 =><- Hr1.
      move/mapP => [v2' Hv2' Hc2].
      rewrite mem_enum in Hv2'.
      case: Hc2 =><- Hr2.
      by rewrite Hr1 Hr2.
    + move: Hv Hv1 Hv2 =><-.
      move/mapP => [v1' Hv1' Hc1].
      case: Hc1 Hv1' =><-.
      rewrite mem_enum => Hc.
      rewrite in_set.
      move/andP => [Hi H'c].
      move/mapP => [v' Hv' Heq].
      case: v' Hv' Heq => v2' r2'.
      rewrite mem_filter.
      move/andP => [Hv2' HV].
      case => Hv1 Hr2.
      rewrite /= in Hv2'.
      move/negP: Hv2'.
      case.
      by rewrite -Hv1.
  * case => Hv2 Hv.
    + move: Hv Hv1 Hv2.
      move =><-.
      move/mapP => [v1' Hv1' Hc1].
      case: v1' Hc1 Hv1' => v1' r1'.
      case =>->->.
      rewrite mem_filter.
      move/andP => [Hi H'c].
      move/mapP => [v' Hv' Heq].
      case: Heq Hv'.
      rewrite mem_enum.
      move =><-->.
      move => Hc.
      move/negP: Hi.
      case.
      rewrite in_set in Hc.
      by move/andP: Hc => [Hi Hc].
    + move: Hv1 Hv2.
      move/mapP.
      case; case => v1' r1'.
      rewrite mem_filter.
      move/andP => [Hi Hv'].
      case.
      move => H_eq_v H_eq_r.
      move/mapP.
      case; case => v2' r2'.
      rewrite mem_filter.
      move/andP => [Hi' Hv''].
      case => H_eq_v' H_eq_r'.
      rewrite Hv in H_eq_v, H_eq_v'.
      rewrite H_eq_v in H_eq_v'.
      apply val_inj in H_eq_v'.
      rewrite -H_eq_v' in Hv''.
      rewrite Hv H_eq_r H_eq_r'.
      have Hu := uniq_prod_eq V_result_cert_uniq Hv' Hv''.
      by rewrite -Hu.
Qed.

End ChangedHierarchical.
