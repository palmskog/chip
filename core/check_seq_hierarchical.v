From mathcomp
Require Import all_ssreflect.

From chip
Require Import extra connect closure check check_seq change hierarchical hierarchical_sub hierarchical_sub_correct tarjan_acyclic.

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

Lemma g_bot_rev_sub_eqq : forall x y : sig_finType (P_V_sub f'_top g_top f_top ps),
  ((grel g_bot_rev_sub) (val x) (val y)) = (g_bot (val y) (val x)).
Proof.
move => x y.
rewrite /=.
apply/idP/idP.
- rewrite mem_filter.
  move/andP.
  move => [Hp Hv].
  have Hb := g_bot_grev (val x) (val y).
  rewrite /= in Hb.
  by rewrite -Hb in Hv.
- have Hb := g_bot_grev (val x) (val y).
  rewrite /= in Hb.
  rewrite Hb /=.
  move => Hs.
  rewrite mem_filter.
  rewrite Hs.
  apply/andP; split => //.
  rewrite /P_V_seq_sub.
  rewrite -P_V_sub_V_seq_sub_eq.
  have H_sp := (insubP (sig_subFinType (P_V_sub f'_top g_top f_top ps)) (val y)).
  by destruct H_sp; last by case/negP: i; apply valP.
Qed.

Lemma connect_rel_sub : forall (y z : sig_finType (P_V_sub f'_top g_top f_top ps)),
  connect [rel x0 y0 | g_bot (val x0) (val y0)] y z ->
  connect (grel g_bot_rev_sub) (val z) (val y).
Proof.
move => y z.
move/connectP => [pt Hpt] Hz.
apply connect_rev.
apply/connectP.
exists (map val pt); last by rewrite last_map Hz.
clear Hz.
elim: pt y Hpt => //.
move => a pt IH y.
rewrite /=.
move/andP => [Hg Hp].
apply/andP.
split; last by apply: IH.
by rewrite -g_bot_rev_sub_eqq in Hg.
Qed.

Lemma connect_g_bot_rev_sub_g_bot_rev : forall v y,
  connect (grel g_bot_rev_sub) v y ->
  connect g_bot^-1 v y.
Proof.
move => v y.
move/connectP => [pt Hpt] Hl.
apply/connectP.
exists pt => //.
elim: pt v Hpt {Hl} => //.
move => z pt IH v.
rewrite /=.
move/andP => [Hz Hp].
apply/andP.
rewrite mem_filter in Hz.
move/andP: Hz => [Hzp Hgb].
have Hg := g_bot_grev v z.
rewrite /= in Hg.
rewrite -Hg in Hgb.
split => //.
by apply: IH.
Qed.

Hypothesis g_bot_top_ps : forall (v v' : V) (u u' : U),
 u <> u' -> g_bot v v' -> v \in ps u -> v' \in ps u' -> g_top u u'.

(* ps is injective *)
Hypothesis ps_neq : forall (u u' : U), u <> u' -> ps u <> ps u'.

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
  by apply connect_rel_sub.
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
  rewrite seq_modifiedV_sub_eq in Hv.
  apply connect_g_bot_rev_sub_g_bot_rev in Hc.
  rewrite inE in Hv.
  move/andP: Hv => [Hvp Hfb].
  rewrite e in Hfb.
  have Hyi: y \in impacted g_bot^-1 (modifiedV f'_bot f_bot).
    apply/impactedP.
    exists v => //.
    by rewrite inE.
  have H_sp := (insubP (sig_subFinType (P_V_sub f'_top g_top f_top ps)) y).
  destruct H_sp.
    rewrite -e0 in Hyi.
    apply impactedV_impactedV_sub_eq in Hyi => //.
    by exists u0; last by rewrite e0.  
  case/negP: i0.
  rewrite /P_V_sub.
  rewrite /pimpacted_sub_V /pimpacted_V.
  apply/bigcupP.
  have Hp := ps_partition.
  move/andP: Hp => [Hcc Hp].
  move/andP: Hp => [Htr H0].
  move: Hcc.
  rewrite /cover.
  move/eqP => Hcc.
  have Hyy: y \in \bigcup_(B in \bigcup_(u in U) [set ps u]) B by rewrite Hcc inE.
  move/bigcupP: Hyy => [ys Hyy] Hys.
  move/bigcupP: Hyy => [u0 Hu0] Huys.
  exists u0; last by move: Huys; rewrite inE; move/eqP =><-.
  rewrite inE in Huys.
  move/eqP: Huys => Huys.
  rewrite Huys in Hys.
  apply/impactedP.
  have Hvv: v \in \bigcup_(B in \bigcup_(u in U) [set ps u]) B by rewrite Hcc inE.
  move/bigcupP: Hvv => [vs Hvv] Hvs.
  move/bigcupP: Hvv => [u1 Hu1] Huvs.
  rewrite inE in Huvs.
  move/eqP: Huvs => Huvs.
  rewrite Huvs in Hvs.
  exists u1.
  - rewrite inE.
    apply/eqP => Hf.
    case/negP: Hfb.
    apply/eqP.    
    by have f_topb := f_top_bot_ps Hf Hvs.
  - move: Hys Hvs Hc.
    by apply connect_rev_v_u.
Qed.

Lemma seq_impacted_fresh_sub_eq :
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

Lemma seq_impacted_fresh_sub_correct :
  seq_impacted_fresh_sub =i impactedV' f'_bot f_bot g_bot.
Proof.
move => x.
apply/idP/idP.
- rewrite -seq_impacted_fresh_sub_eq.
  by rewrite impactedV'_sub_eq //.
- rewrite -seq_impacted_fresh_sub_eq.
  by rewrite impactedV'_sub_eq //.
Qed.

Lemma seq_checkable_impacted_fresh_sub_correct :
  seq_checkable_impacted_fresh_sub =i
  checkable_impactedV' f'_bot f_bot g_bot checkable'_bot.
Proof.
move => x.
rewrite mem_filter.
apply/idP/idP.
- move/andP => [Hc Hx].
  rewrite inE.
  apply/andP; split => //.
  by rewrite -seq_impacted_fresh_sub_correct.
- rewrite inE.
  move/andP => [Hc Hi].
  apply/andP.
  split => //.
  by rewrite seq_impacted_fresh_sub_correct.
Qed.

Hypothesis clos_top_uniq : forall successors (s : seq U),
  uniq s -> uniq (clos_top successors s).

Hypothesis clos_bot_uniq : forall successors (s : seq V),
  uniq s -> uniq (clos_bot successors s).

Hypothesis p_uniq : forall u, uniq (p u).

Lemma seq_modifiedU_uniq : uniq seq_modifiedU.
Proof.
exact: seq_modifiedV_uniq.
Qed.

Lemma seq_impactedU_uniq : uniq seq_impactedU.
Proof.
by apply/clos_top_uniq/seq_modifiedU_uniq.
Qed.

Lemma seq_pmodified_V_uniq : uniq seq_pmodified_V.
Proof.
apply uniq_flatten.
- elim => //.
  move => v l IH.
  move/mapP => [u Hu] Hp.
  rewrite Hp.
  exact: p_uniq.
- rewrite map_inj_in_uniq; first by apply seq_modifiedU_uniq.
  move => x y Hx Hy Hp.
  case Hxy: (x == y); first by move/eqP: Hxy.
  move/eqP: Hxy => Hxy.
  apply ps_neq in Hxy.
  case: Hxy.
  apply/setP.
  move => v.
  by rewrite -2!p_ps_eq Hp.
- move => l l'.
  move/mapP => [u Hu] Hlu.
  move/mapP => [u' Hu'] Hlu' Hneq.
  rewrite Hlu Hlu'.
  case Heq: (u == u').
    move/eqP: Heq Hlu =>->.
    move => Hlu.
    case/eqP: Hneq.
    by rewrite Hlu' Hlu.
  move/eqP: Heq => Heq.
  have Hp := ps_partition.
  move/andP: Hp => [Hcc Hp].
  move/andP: Hp => [Htr H0].
  move/trivIsetP: Htr => Htr.
  have Hpu: ps u \in \bigcup_(u in U) [set ps u].
    apply/bigcupP.
    exists u => //=.
    by rewrite in_set1.
  have Hpu': ps u' \in \bigcup_(u in U) [set ps u].
    apply/bigcupP.
    exists u' => //=.
    by rewrite in_set1.
  have Hneq': ps u != ps u'.
    apply/negP/negP/eqP => Hpp.
    contradict Hpp.
    exact: ps_neq.
  have Hpp := Htr _ _ Hpu Hpu' Hneq'.
  rewrite disjoint_subset.
  apply/subsetP.
  move => x.
  rewrite p_ps_eq => Hx.
  rewrite inE.
  apply/negP.
  case => Hp.
  have Hy: x \in p u' by [].
  move: Hy.
  rewrite p_ps_eq => Hy.
  move: Hpp.
  rewrite disjoint_subset.
  move/subsetP => Hs.
  move/Hs: Hx.
  rewrite inE.
  move/negP.
  by case.
Qed.

Lemma seq_pimpacted_V_uniq : uniq seq_pimpacted_V.
Proof.
apply uniq_flatten.
- elim => //.
  move => v l IH.
  move/mapP => [u Hu] Hp.
  rewrite Hp.
  exact: p_uniq.
- rewrite map_inj_in_uniq; first by apply seq_impactedU_uniq.
  move => x y Hx Hy Hp.
  case Hxy: (x == y); first by move/eqP: Hxy.
  move/eqP: Hxy => Hxy.
  apply ps_neq in Hxy.
  case: Hxy.
  apply/setP.
  move => v.
  by rewrite -2!p_ps_eq Hp.
- move => l l'.
  move/mapP => [u Hu] Hlu.
  move/mapP => [u' Hu'] Hlu' Hneq.
  rewrite Hlu Hlu'.
  case Heq: (u == u').
    move/eqP: Heq Hlu =>->.
    move => Hlu.
    case/eqP: Hneq.
    by rewrite Hlu' Hlu.
  move/eqP: Heq => Heq.
  have Hp := ps_partition.
  move/andP: Hp => [Hcc Hp].
  move/andP: Hp => [Htr H0].
  move/trivIsetP: Htr => Htr.
  have Hpu: ps u \in \bigcup_(u in U) [set ps u].
    apply/bigcupP.
    exists u => //=.
    by rewrite in_set1.
  have Hpu': ps u' \in \bigcup_(u in U) [set ps u].
    apply/bigcupP.
    exists u' => //=.
    by rewrite in_set1.
  have Hneq': ps u != ps u'.
    apply/negP/negP/eqP => Hpp.
    contradict Hpp.
    exact: ps_neq.
  have Hpp := Htr _ _ Hpu Hpu' Hneq'.
  rewrite disjoint_subset.
  apply/subsetP.
  move => x.
  rewrite p_ps_eq => Hx.
  rewrite inE.
  apply/negP.
  case => Hp.
  have Hy: x \in p u' by [].
  move: Hy.
  rewrite p_ps_eq => Hy.
  move: Hpp.
  rewrite disjoint_subset.
  move/subsetP => Hs.
  move/Hs: Hx.
  rewrite inE.
  move/negP.
  by case.
Qed.

Lemma seq_modifiedV_sub_uniq : uniq seq_modifiedV_sub.
Proof.
rewrite filter_uniq //.
exact: seq_pmodified_V_uniq.
Qed.

Lemma seq_impactedV_sub_uniq : uniq seq_impactedV_sub.
Proof.
apply/clos_bot_uniq.
exact: seq_modifiedV_sub_uniq.
Qed.

Lemma seq_impactedVV'_sub_uniq : uniq seq_impactedVV'_sub.
Proof.
rewrite map_inj_in_uniq; first by apply seq_impactedV_sub_uniq.
move => x y Hx Hy.
by move/val_inj.
Qed.

Lemma seq_freshV'_uniq : uniq seq_freshV'.
Proof.
rewrite filter_uniq //.
exact: enum_uniq.
Qed.

Lemma seq_impacted_fresh_sub_uniq : uniq seq_impacted_fresh_sub.
Proof.
rewrite cat_uniq.
apply/andP; split.
- rewrite map_inj_uniq; last by apply val_inj.
  apply clos_bot_uniq.
  by apply seq_modifiedV_sub_uniq.
- apply/andP; split; last by rewrite filter_uniq // enum_uniq.
  apply/negP.
  case.
  move/hasP.
  move => /= [x Hx] Hm.
  move: Hx Hm.
  rewrite -seq_freshV'_eq.
  rewrite -seq_impactedVV'_sub_eq impactedVV'_sub_eq // => Hx Hm.
  move/negP: Hx; case; apply/negP.
  move: Hm.
  by apply impactedVV'_freshV'.
Qed.

Lemma seq_checkable_impacted_fresh_sub_uniq : uniq seq_checkable_impacted_fresh_sub.
Proof.
rewrite filter_uniq //.
exact: seq_impacted_fresh_sub_uniq.
Qed.

End CheckedSeqHierarchical.
