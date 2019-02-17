From mathcomp
Require Import all_ssreflect.

From chip
Require Import extra connect closure check check_seq change hierarchical hierarchical_sub hierarchical_sub_correct.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section CheckedSeqHierarchical.

Variable (A_top : eqType) (A_bot : eqType).  

Variable (U' : finType) (V' : finType).

Variable (f'_top : U' -> A_top) (f'_bot : V' -> A_bot).

Variable (P_top : pred U') (P_bot : pred V').

Local Notation U := (sig_finType P_top).

Local Notation V := (sig_finType P_bot).

Variable (f_top : U -> A_top) (f_bot : V -> A_bot).

Variable g_top_rev : U -> seq U.

Variable g_bot_rev : V -> seq V.

Variable p : U -> seq V.

Variable (checkable'_bot : pred V').

Variable clos_top : (U -> seq U) -> seq U -> seq U.

Hypothesis clos_topP : forall successors (s : seq U) (x : U),
  reflect
    (exists2 v, v \in s & connect (grel successors) v x)
    (x \in clos_top successors s).

Variable clos_bot : (V -> seq V) -> seq V -> seq V.

Hypothesis clos_botP : forall successors (s : seq V) (x : V),
  reflect
    (exists2 v, v \in s & connect (grel successors) v x)
    (x \in clos_bot successors s).

(* defs *)

Definition seq_modifiedU := [seq u <- enum U | f_top u != f'_top (val u)].
Definition seq_impactedU := clos_top g_top_rev seq_modifiedU.

Definition seq_pmodified_V := flatten [seq (p v) | v <- seq_modifiedU].
Definition seq_pimpacted_V := flatten [seq (p v) | v <- seq_impactedU].

Definition P_V_seq_sub v := v \in seq_pimpacted_V.
Definition g_bot_rev_sub (v : V) := [seq v <- g_bot_rev v | P_V_seq_sub v].

Definition seq_modifiedV_sub := [seq v <- seq_pmodified_V | f_bot v != f'_bot (val v)].
Definition seq_impactedV_sub := clos_bot g_bot_rev_sub seq_modifiedV_sub.
Definition seq_impactedVV'_sub := [seq val v | v <- seq_impactedV_sub].

Definition seq_freshV' := [seq v <- enum V' | ~~ P_bot v].

Definition seq_impacted_fresh_sub := seq_impactedVV'_sub ++ seq_freshV'.

Definition seq_checkable_impacted_fresh_sub :=
  [seq v <- seq_impacted_fresh_sub | checkable'_bot v].

(* proofs *)

Variable g_top : rel U.

Hypothesis g_top_grev : [rel x y | g_top y x] =2 grel g_top_rev.

Lemma seq_modifiedU_eq :
  modifiedV f'_top f_top =i seq_modifiedU.
Proof.
by move => x; rewrite inE mem_filter mem_enum andb_idr.
Qed.

Lemma seq_impactedU_eq :
  impacted g_top^-1 (modifiedV f'_top f_top) =i seq_impactedU.
Proof.
move => x.
apply/impactedVP.
case: ifP.
- move/clos_topP => [v Hv] Hc.
  move: Hv.
  rewrite -seq_modifiedU_eq => Hv.
  exists v => //.
  move/connectP: Hc => [p0 Hp] Hl.
  apply/connectP.
  exists p0 => //.
  elim: p0 v Hp {Hv Hl} => //.
  move => v p0 IH v0.
  rewrite /=.
  move/andP => [Hv Hp].
  apply/andP.
  split; last by apply: IH.
  move: Hv.
  have Hb := (g_top_grev v0 v).
  rewrite /= in Hb.
  by rewrite Hb.
- move/negP => Hs.
  move => [y Hy] Hc.
  case: Hs.
  apply/clos_topP.
  move: Hy.
  rewrite seq_modifiedU_eq => Hy.  
  exists y => //.
  move/connectP: Hc => [p0 Hp0] Hl.
  apply/connectP.
  exists p0 => //.
  elim: p0 y Hp0 {Hl Hy} => //.
  move => v p0 IH v0.
  rewrite /=.
  move/andP => [Hv Hp].
  apply/andP.
  split; last by apply: IH.
  move: Hv.
  have Hb := (g_top_grev v0 v).
  rewrite /= in Hb.
  by rewrite Hb.
Qed.

Variables (ps : U -> {set V}).

Hypothesis p_ps_eq : forall u : U, p u =i ps u.

Lemma seq_pimpacted_V_eq :
  pimpacted_sub_V f'_top g_top f_top ps =i seq_pimpacted_V.
Proof.
move => x.  
apply/bigcupP.
case: ifP => Hm.
- move/flattenP: Hm => [us Hus] Hx.
  move/mapP: Hus => [y Hy] Hyu.
  exists y; last by rewrite -p_ps_eq -Hyu.
  by rewrite seq_impactedU_eq.
- move/negP: Hm => Hm [u Hu] Hx.
  case: Hm.
  apply/flattenP.
  exists (p u); last by rewrite p_ps_eq.
  apply/mapP.
  exists u => //.
  by rewrite -seq_impactedU_eq.
Qed.

Lemma P_V_sub_V_seq_sub_eq : 
  P_V_sub f'_top g_top f_top ps =i P_V_seq_sub.
Proof.
move => x.
apply/idP/idP.
- by rewrite seq_pimpacted_V_eq.
- by rewrite seq_pimpacted_V_eq.
Qed.

(*
Lemma seq_modifiedV_bot_eq : modifiedV f'_bot f_bot =i seq_modifiedV_bot.
Proof.
by move => x; rewrite inE mem_filter mem_enum andb_idr.
Qed.
*)

(*
Lemma seq_modifiedV_sub_eq :
  forall x,  \in 
  modifiedV_sub f'_top f'_bot g_top f_top f_bot ps =i seq_modifiedV_sub.


Lemma V_sub_V_seq_sub_eq :
  forall v : V,  Sub v \in (sig_finType (P_V_sub f'_top g_top f_top ps)).
       v \in V_seq_sub.

  (sig_finType (P_V_sub f'_top g_top f_top ps)) =i V_seq_sub.
*)

Variable g_bot : rel V.

Hypothesis g_bot_grev : [rel x y | g_bot y x] =2 grel g_bot_rev.

(*
Lemma seq_impactedV_sub :
  impactedV_sub f'_top f'_bot g_top g_bot f_top f_bot ps =i seq_impactedV_sub.
 *)

(*Lemma seq_impacted_fresh_sub_uniq : *)

End CheckedSeqHierarchical.
