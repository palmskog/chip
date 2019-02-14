From mathcomp
Require Import all_ssreflect.

From chip
Require Import extra connect acyclic closure check change hierarchical.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section HierarchicalSub.

Variable (A_top : eqType) (A_bot : eqType).

Variable (U' : finType) (V' : finType).

Variable (f'_top : U' -> A_top) (f'_bot : V' -> A_bot).

Variable (P_top : pred U') (P_bot : pred V').

Local Notation U := (sig_finType P_top).

Local Notation V := (sig_finType P_bot).

Variable (g_top : rel U) (g_bot : rel V).

Local Notation g_top_rev := [rel x y | g_top y x].

Local Notation g_bot_rev := [rel x y | g_bot y x].

Variable (f_top : U -> A_top) (f_bot : V -> A_bot).

Variable (checkable : pred V').

Variable (R : eqType).

Variable (check : V' -> R).

Variables (p : U -> {set V}).

Hypothesis p_neq : forall (u u' : U), u <> u' -> p u <> p u'.

Hypothesis p_partition : partition (\bigcup_( u | u \in U ) [set p u]) [set: V].

Hypothesis g_bot_top : forall (v v' : V) (u u' : U),
 u <> u' -> g_bot v v' -> v \in p u -> v' \in p u' -> g_top u u'.

Hypothesis f_top_bot : forall (u : U),
 f_top u = f'_top (val u) -> forall (v : V), v \in p u -> f_bot v = f'_bot (val v).

Definition pimpacted_sub_V := pimpacted_V f'_top g_top f_top p.

Definition P_V_sub v := v \in pimpacted_sub_V.

Local Notation V_sub := (sig_finType P_V_sub).

Local Notation g_bot_sub := [rel x y : V_sub | g_bot (val x) (val y)].

Definition modifiedV_sub := [set v : V_sub | val v \in modifiedV f'_bot f_bot].

Definition impactedV_sub := impacted g_bot_sub^-1 modifiedV_sub.

Definition impactedVV'_sub := [set val (val v) | v in impactedV_sub].

Definition impactedV'_sub := impactedVV'_sub :|: freshV' P_bot.

Definition impacted_fresh_sub : seq V' := enum impactedV'_sub.

Lemma impactedV_sub_impactedV_eq : forall v,
  v \in impactedV_sub ->
  val v \in impacted g_bot^-1 (modifiedV f'_bot f_bot).
Proof.
move => v.
rewrite /impactedV_sub.
move/impactedP.
move => [v0 [Hm Hc]].
move: Hc.
move/connect_rev.
rewrite /= => Hc.
apply/impactedP.
exists (val v0); first by move: Hm; rewrite in_set.
apply connect_rev.
rewrite in_set in Hm.
exact: gsub_connect.
Qed.

Lemma impactedV_impactedV_sub_eq : forall (v : V_sub),
  val v \in impacted g_bot^-1 (modifiedV f'_bot f_bot) ->
  v \in impactedV_sub.
Proof.
move => v.
move/impactedVP => [v0 Hv0] Hc.
have H_neq := Hv0.
move: H_neq.
rewrite in_set.
move/negP/negP/eqP => Hneq.
have H_sp := (insubP [subType of V_sub] v0).
destruct H_sp; last by move/negP: i; case; apply/(neq_connect_in_pimpacted_V p_neq p_partition g_bot_top f_top_bot Hneq).
move: Hc.
move/connect_rev.
rewrite /= => Hc.
apply/impactedVP.
exists u; first by rewrite in_set; rewrite e.
apply/connect_rev.
rewrite /=.
move: Hc.
have ->: rel_of_simpl_rel [rel x y | g_bot x y] = g_bot by [].
rewrite -e.
rewrite -e in Hneq.
move/connectP => [vs Hp] Hl.
have Hcp: forall v', v' \in vs -> connect g_bot_rev (val u) v'.
  elim: vs v Hp Hl => //.
  move => v' vs IH v Hp Hl.
  move/andP: Hp => [Hg Hp].
  rewrite -/(path _ _) in Hp.
  rewrite /= in Hl.
  have Hcp : connect g_bot_rev (val u) v'.
    apply/connect_rev.
    apply/connectP.
    by exists vs.
  have Hpi := neq_connect_in_pimpacted_V p_neq p_partition g_bot_top f_top_bot Hneq Hcp.
  have H_sp := (insubP [subType of V_sub] v').
  destruct H_sp; last by move/negP: i0; case.
  rewrite -e0 in Hp,Hl.
  have IH' := IH _ Hp Hl.
  move => v1.
  rewrite in_cons.
  move/orP; case; last by apply: IH'.
  by move/eqP=>->.
have H_p: forall v', v' \in vs -> v' \in pimpacted_V f'_top g_top f_top p.
  move => v' Hv'.
  apply/(neq_connect_in_pimpacted_V p_neq p_partition g_bot_top f_top_bot Hneq).
  exact: Hcp.
apply/connectP.
exists (pmap insub vs).
- clear Hneq Hv0 i e Hcp Hl u v0.
  move: v Hp H_p.
  elim: vs => //.
  move => v vs IH v0.
  move/andP => [Hg Hp].
  rewrite -/(path _ _) in Hp.
  move => Hp'.
  rewrite /= /oapp.
  have Hpp': forall v' : V, v' \in vs -> v' \in pimpacted_V f'_top g_top f_top p.
    move => v' Hv'.
    apply: Hp'.
    rewrite in_cons.
    apply/orP.
    by right.
  have Hpi : v \in pimpacted_V f'_top g_top f_top p.
    apply: Hp'.
    rewrite in_cons.
    by apply/orP; left.
  have H_sp := (insubP [subType of V_sub] v).
  move: H_sp.
  case; last by move/negP; case.
  move => u HPu Hu.
  rewrite /=.
  apply/andP.
  rewrite Hu.
  split => //.
  apply: IH => //.
  by rewrite Hu.
- clear Hp Hcp Hneq.
  move: v Hl H_p.
  elim: vs; first by move => /= v; move/val_inj.
  move => v vs IH v1 Hl Hp.
  rewrite /= in Hl.
  have Hpv : v \in pimpacted_V f'_top g_top f_top p.
    apply: Hp.
    rewrite in_cons.
    apply/orP.
    by left.    
  rewrite /= /oapp.
  have Hp': forall v' : V, v' \in vs -> v' \in pimpacted_V f'_top g_top f_top p.
    move => v' Hv'.
    apply: Hp.
    rewrite in_cons.
    apply/orP.
    by right.
  have H_sp := (insubP [subType of V_sub] v).
  move: H_sp.
  case; last by move/negP; case.
  move => u0 HPu0 Hu0.
  rewrite last_cons.
  apply: IH => //.
  by rewrite Hu0.
Qed.

Lemma impactedVV'_sub_eq :
  impactedVV'_sub = impactedVV' g_bot (modifiedV f'_bot f_bot).
Proof.
apply/eqP; rewrite eqEsubset; apply/andP; split.
- apply/subsetP => x.
  move/imsetP => [x1 Hx] Hx1.    
  apply/imsetP.
  exists (val x1); last by [].
  exact: impactedV_sub_impactedV_eq.
- apply/subsetP => x.
  move/imsetP => [x1 Hx] Hx1.
  rewrite Hx1.
  have Hi := Hx.
  move: Hx.
  move/(impactedV_in_pimpacted_V p_neq p_partition g_bot_top f_top_bot) => Hp.
  have H_sp := (insubP [subType of V_sub] x1).
  destruct H_sp; last by move/negP: i.
  apply/imsetP.
  exists u; last by rewrite e.
  rewrite -e in Hi.
  exact: impactedV_impactedV_sub_eq.
Qed.

Lemma impactedV'_sub_eq :
  impactedV'_sub = impactedV' f'_bot f_bot g_bot.
Proof. by rewrite /impactedV'_sub impactedVV'_sub_eq. Qed.

Definition checkable_impactedV'_sub :=
 [set v in impactedV'_sub | checkable v].

Definition checkable_impacted_fresh_sub : seq V' :=
 enum checkable_impactedV'_sub.

Definition check_impactedV'_sub_cert :=
 [seq (v, check v) | v <- checkable_impacted_fresh_sub].

End HierarchicalSub.
