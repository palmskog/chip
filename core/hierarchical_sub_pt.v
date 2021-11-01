From mathcomp.ssreflect Require Import all_ssreflect.
From mathcomp.tarjan Require Import extra acyclic.
From chip Require Import closure check change hierarchical hierarchical_sub.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section HierarchicalSubPt.

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

Variables (p : U -> {set V}) (p' : U' -> {set V'}).

Hypothesis p_neq : forall (u u' : U), u <> u' -> p u <> p u'.

Hypothesis p_partition : partition (\bigcup_( u | u \in U ) [set p u]) [set: V].

Hypothesis p'_partition : partition (\bigcup_( u | u \in U' ) [set p' u]) [set: V'].

Hypothesis g_bot_top : forall (v v' : V) (u u' : U),
 u <> u' -> g_bot v v' -> v \in p u -> v' \in p u' -> g_top u u'.

Hypothesis f_top_bot : forall (u : U),
 f_top u = f'_top (val u) -> forall (v : V), v \in p u -> f_bot v = f'_bot (val v).

Hypothesis f_top_partition : forall (u : U),
 f_top u = f'_top (val u) -> [set val v | v in p u] = p' (val u).

Local Notation V_sub := ((sig_finType P_V_sub) : finType).

Local Notation g_bot_sub := ([rel x y : V_sub | g_bot (val x) (val y)] : rel V_sub).

Definition pfreshV' := \bigcup_(u | u \in freshV' P_top) (p' u) :|: \bigcup_(u | u \in modifiedV f'_top f_top) (p' (val u)).

Definition freshV'_sub : {set V'} := [set v in pfreshV' | ~~ P_bot v].

Definition impactedV'_sub_pt := impactedVV'_sub f'_top f'_bot g_top g_bot f_top f_bot p :|: freshV'_sub.

Lemma pfreshV'_in_freshV' : forall v,
  v \in freshV' P_bot ->
  v \in pfreshV'.
Proof.
move => v; rewrite in_set => Hv.
apply/setUP.
have Hp := p'_partition.
move/andP: Hp => [Hc Hp].
move/andP: Hp => [Htr H0].
move: Hc.
rewrite /cover.
move/eqP => Hc.
have Hvv: v \in \bigcup_(B in \bigcup_(u in U') [set p' u]) B by rewrite Hc.
move/bigcupP: Hvv => [vs Hvv] Hvs.
move/bigcupP: Hvv => [u Hu] Huvs.
move: Huvs Hvs.
rewrite inE.
move/eqP =>-> Hv'.
have H_sp := (insubP [subType of U] u).
destruct H_sp; last by left; apply/bigcupP; exists u => //; rewrite inE.
right; apply/bigcupP; exists u0; last by rewrite e.
rewrite inE.
apply/negP.
move/eqP/f_top_partition => Hf.
move: Hf Hv'.
rewrite e =><-.
move/imsetP => [x Hx] Hpx.
move: Hv.
rewrite Hpx => Hv.
case/negP: Hv.
exact: valP.
Qed.

Lemma freshV'_sub_eq :
  freshV'_sub = freshV' P_bot.
Proof.
apply/setP => x.
apply/idP/idP.
- rewrite inE.
  move/andP => [Hp Hpb].
  by rewrite inE.
- rewrite inE => Hf.
  rewrite inE.
  apply/andP; split => //.
  apply/pfreshV'_in_freshV'.
  by rewrite inE.
Qed.
    
Lemma impactedV'_sub_pt_eq :
  impactedV'_sub_pt = impactedV' f'_bot f_bot g_bot.
Proof.
rewrite /impactedV'_sub_pt.
rewrite impactedVV'_sub_eq //.
by rewrite freshV'_sub_eq.
Qed.

Definition checkable_impactedV'_sub_pt :=
 [set v in impactedV'_sub_pt | checkable v].

Definition checkable_impacted_fresh_sub_pt : seq V' :=
 enum checkable_impactedV'_sub_pt.

Definition check_impactedV'_sub_pt_cert :=
 [seq (v, check v) | v <- checkable_impacted_fresh_sub_pt].

End HierarchicalSubPt.
