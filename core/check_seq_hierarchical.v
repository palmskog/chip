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

Hypothesis ps_partition : partition (\bigcup_( u | u \in U ) [set ps u]) [set: V].

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

Variable g_bot : rel V.

Hypothesis g_bot_grev : [rel x y | g_bot y x] =2 grel g_bot_rev.

Hypothesis f_top_bot_ps : forall (u : U),
 f_top u = f'_top (val u) -> forall (v : V), v \in ps u -> f_bot v = f'_bot (val v).

Lemma seq_modifiedV_sub_eq : forall z,
 (val z \in seq_modifiedV_sub) =
 (z \in modifiedV_sub f'_top f'_bot g_top f_top f_bot ps).
Proof.
move => z.
apply/idP/idP.
- rewrite mem_filter.
  move/andP => [Hz Ha].
  rewrite inE.
  move/flattenP: Ha => [x Hx] Hzx.
  apply/andP; split => //.
  apply/bigcupP.
  move/mapP: Hx => [u Hu] Hxu.
  exists u; last by rewrite -p_ps_eq -Hxu.
  by rewrite seq_modifiedU_eq.
- move => Hz.
  rewrite mem_filter.
  apply/andP.  
  move: Hz.
  rewrite inE.
  move/andP => [Hz Hf].
  split => //.
  move/bigcupP: Hz => [u Hu] Huz.
  apply/flattenP.  
  exists (p u); last by rewrite p_ps_eq.
  apply/mapP.
  exists u => //.
  by rewrite -seq_modifiedU_eq.
Qed.

Lemma seq_impactedVV'_sub_eq :
  impactedVV'_sub f'_top f'_bot g_top g_bot f_top f_bot ps =i seq_impactedVV'_sub.
Proof.
move => x.
apply/idP/idP.
- move/imsetP => [y Hy] Hyx.
  apply/mapP.
  exists (val y) => //.
  move/impactedP: Hy => [z Hz] Hyz.
  apply/clos_botP.
  exists (val z); first by rewrite seq_modifiedV_sub_eq.
  move: Hyz.
  move/connect_rev => /=.
  (*move/connectP => [s Hs] Hzs.
  apply/connectP.
  exists (map val s). *)
  by admit.
- move/mapP => [y Hy] Hyx.
  move/clos_botP: Hy => [v Hv] Hc.
  apply/imsetP.   
  have H_sp := (insubP (sig_subFinType (P_V_sub f'_top g_top f_top ps)) v).
  destruct H_sp; last first.
    case/negP: i.
    rewrite /P_V_sub.
    move: Hv.
    rewrite mem_filter.
    move/andP => [Hf Hs].
    have Hv: v \in modifiedV f'_bot f_bot by rewrite inE.
    suff Hsuff: v \in pmodified_sub_V f'_top f_top ps.
      move/bigcupP: Hsuff => [u Hu] Huv.
      apply/bigcupP.
      exists u => //.
      apply/impactedP.
      by exists u.
    move: Hv.
    by apply modifiedV_pmodified_sub_V.
  rewrite -e in Hv.  
  have H_sp := (insubP (sig_subFinType (P_V_sub f'_top g_top f_top ps)) y).
  destruct H_sp; last first.
    case/negP: i0.
    rewrite /P_V_sub.
    rewrite seq_modifiedV_sub_eq in Hv.
    suff Hsuff: y \in impacted g_bot^-1 (modifiedV f'_bot f_bot).    
      apply/bigcupP.
      
    (*
    suff Hsuff: y \in impactedV_sub f'_top f'_bot g_top g_bot f_top f_bot ps.
    
    apply/bigcupP.
    
    move: Hv.
    rewrite mem_filter.
    move/andP => [Hf Hs].
    suff Hsuff: y \in seq_pimpacted_V by rewrite seq_pimpacted_V_eq.
    
    
    apply/bigcupP.

    
  rewrite -e in Hv.
  rewrite seq_modifiedV_sub_eq in Hv.
  exists u; last first.
  rewrite e.*)
Admitted.

Lemma seq_impactedV'_sub_eq :
  impactedV'_sub f'_top f'_bot g_top g_bot f_top f_bot ps =i seq_impacted_fresh_sub.
Proof.
move => x.
apply/idP/idP.
- rewrite mem_cat.
  case/setUP => Hx.
  * apply/orP; left.
    by rewrite -seq_impactedVV'_sub_eq.
  * apply/orP; right.
    by rewrite -seq_freshV'_eq.
- rewrite mem_cat.
  move/orP; case => Hx.
  * apply/setUP.
    left.
    by rewrite seq_impactedVV'_sub_eq.
  * apply/setUP.
    right.
    by rewrite seq_freshV'_eq.
Qed.

Hypothesis g_bot_top_ps : forall (v v' : V) (u u' : U),
 u <> u' -> g_bot v v' -> v \in ps u -> v' \in ps u' -> g_top u u'.

Hypothesis ps_neq : forall (u u' : U), u <> u' -> ps u <> ps u'.

Lemma seq_impactedV'_sub_correct :
  seq_impacted_fresh_sub =i impactedV' f'_bot f_bot g_bot.
Proof.
move => x.
apply/idP/idP.
- rewrite -seq_impactedV'_sub_eq.
  by rewrite impactedV'_sub_eq //.
- rewrite -seq_impactedV'_sub_eq.
  by rewrite impactedV'_sub_eq //.
Qed.

End CheckedSeqHierarchical.
