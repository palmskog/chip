Require Import OrderedType.
Require Import MSetInterface.
Require Import MSetFacts.
Require Import MSetRBT.
Require Import String.

From mathcomp
Require Import all_ssreflect.

From chip
Require Import ordtype connect closure dfs_set string acyclic kosaraju topos check change check_seq hierarchical_sub check_seq_hierarchical.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition subltn (n : nat) (P : pred 'I_n) (v v' : sig_finType P) :=
  ltn (val v) (val v').

Module Type OrdinalsType.
Parameter n : nat.
Parameter m' : nat.
Notation m := m'.+1.
Parameter H_mn : m <= n.
End OrdinalsType.

Module OrdinalsCheckableImpacted (Import OT : OrdinalsType).
Local Notation A := [eqType of string].
Local Notation V' := 'I_n.
Definition lt_m_pred : pred V' := fun v => val v < m.
Local Notation V := (sig_finType lt_m_pred).

Module VFinType <: FinType.
Definition T : finType := V.
End VFinType.

Module VFinOrdType <: FinOrdType VFinType.
Definition ordT : rel V := fun x y => subltn x y.
Definition irr_ordT : irreflexive ordT := fun x => irr_ltn_nat (val x).
Definition trans_ordT : transitive ordT :=
 fun x y z => @trans_ltn_nat (val x) (val y) (val z).
Definition total_ordT : forall x y, [|| ordT x y, x == y | ordT y x] :=
 fun x y => total_ltn_nat (val x) (val y).
End VFinOrdType.

Module VFinOrdUsualOrderedType <: FinUsualOrderedType VFinType :=
 FinOrdUsualOrderedType VFinType VFinOrdType.
Module VRBSet <: MSetInterface.S :=
 MSetRBT.Make VFinOrdUsualOrderedType.
Module VDFS := DFS VFinType VFinOrdUsualOrderedType VRBSet.

Section Finn.

Variable successors : V -> seq V.
Variable f' : V' -> A.
Variable f : V -> A.
Variable checkable' : pred V'.

(* defs *)

Definition succs_closure := VDFS.elts_srclosure'.
Definition succs_closureP := VDFS.elts_srclosure'Pg.
Definition succs_closure_uniq := VDFS.elts_srclosure'_uniq.

Definition succs_checkable_impacted :=
 seq_checkable_impacted f' f successors checkable' succs_closure.
Definition succs_impacted_fresh :=
 seq_impacted_fresh f' f successors succs_closure.
Definition succs_checkable_impacted_fresh :=
 seq_checkable_impacted_fresh f' f successors checkable' succs_closure.

Variable successors' : V' -> seq V'.

Definition succs_ts :=
 ts_g'rev_imf_checkable_val f' f successors checkable' succs_closure tseq successors'.

(* proofs *)

Variable g : rel V.

Hypothesis g_grev : [rel x y | g y x] =2 grel successors.

Variable (g' : rel V').

Hypothesis g'_g'rev : [rel x y | g' y x] =2 grel successors'.

Lemma succs_impacted_fresh_eq :
  impactedV' f' f g =i succs_impacted_fresh.
Proof.
apply: seq_impacted_fresh_eq; eauto.
exact: succs_closureP.
Qed.

Lemma succs_checkable_impacted_fresh_eq :
 checkable_impactedV' f' f g checkable' =i succs_checkable_impacted_fresh.
Proof.
apply: seq_checkable_impacted_fresh_eq; eauto.
exact: succs_closureP.
Qed.

Lemma succs_impacted_fresh_uniq : uniq succs_impacted_fresh.
Proof.
apply: seq_impacted_fresh_uniq => //.
- exact: succs_closureP.
- move => gs s Hs.
  exact: succs_closure_uniq.
Qed.

Lemma succs_checkable_impacted_fresh_uniq :
  uniq succs_checkable_impacted_fresh.
Proof.
apply: seq_checkable_impacted_fresh_uniq => //.
- exact: succs_closureP.
- move => gs s Hs.
  exact: succs_closure_uniq.
Qed.

Lemma succs_ts_uniq :
  uniq succs_ts.
Proof.
apply: ts_g'rev_imf_checkable_val_uniq.
exact: tseq_uniq.
Qed.

Lemma in_succs_ts :
  forall x, x \in succs_ts ->
  checkable' x /\ x \in impactedV' f' f g.
Proof.
apply: in_ts_g'rev_imf_checkable_val; eauto.
exact: succs_closureP.
Qed.

Lemma succs_ts_in :
  forall x, checkable' x -> x \in impactedV' f' f g ->
  x \in succs_ts.
Proof.
apply: ts_g'rev_imf_checkable_val_in; eauto.
- exact: succs_closureP.
- exact: tseq_all.
Qed.

Hypothesis g'_acyclic : acyclic g'.

Local Notation gV' := [rel x y : V' | insub_g g x y].

Hypothesis f_equal_g :
  forall v, f v = f' (val v) -> forall v', gV' (val v) v' = g' (val v) v'.

Lemma succs_tseq_before : forall x y,
  x \in impactedV' f' f g -> checkable' x ->
  y \in impactedV' f' f g -> checkable' y ->
  connect g' x y ->
  before succs_ts y x.
Proof.
apply: ts_g'rev_imf_checkable_val_before; eauto.
- exact: succs_closureP.
- exact: tseq_sorted.
- exact: tseq_all.
Qed.

End Finn.

End OrdinalsCheckableImpacted.

Module OrdinalsHierarchicalCheckableImpacted (OT_top : OrdinalsType) (OT_bot : OrdinalsType).

Notation A_top := [eqType of string].
Notation A_bot := [eqType of string].
Notation n_top := OT_top.n.
Notation m_top := OT_top.m.
Notation n_bot := OT_bot.n.
Notation m_bot := OT_bot.m.
Notation U' := 'I_n_top.
Notation V' := 'I_n_bot.
Notation P_top := ((fun v => val v < m_top) : pred U').
Notation U := (sig_finType P_top).
Notation P_bot := ((fun v => val v < m_bot) : pred V').
Notation V := (sig_finType P_bot).

Module UFinType <: FinType.
Definition T : finType := U.
End UFinType.

Module UFinOrdType <: FinOrdType UFinType.
Definition ordT : rel U := fun x y => subltn x y.
Definition irr_ordT : irreflexive ordT := fun x => irr_ltn_nat (val x).
Definition trans_ordT : transitive ordT :=
 fun x y z => @trans_ltn_nat (val x) (val y) (val z).
Definition total_ordT : forall x y, [|| ordT x y, x == y | ordT y x] :=
 fun x y => total_ltn_nat (val x) (val y).
End UFinOrdType.

Module UFinOrdUsualOrderedType <: FinUsualOrderedType UFinType :=
 FinOrdUsualOrderedType UFinType UFinOrdType.
Module USet <: MSetInterface.S :=
 MSetRBT.Make UFinOrdUsualOrderedType.
Module UDFS := DFS UFinType UFinOrdUsualOrderedType USet.

Module VFinType <: FinType.
Definition T : finType := V.
End VFinType.

Module VFinOrdType <: FinOrdType VFinType.
Definition ordT : rel V := fun x y => subltn x y.
Definition irr_ordT : irreflexive ordT := fun x => irr_ltn_nat (val x).
Definition trans_ordT : transitive ordT :=
 fun x y z => @trans_ltn_nat (val x) (val y) (val z).
Definition total_ordT : forall x y, [|| ordT x y, x == y | ordT y x] :=
 fun x y => total_ltn_nat (val x) (val y).
End VFinOrdType.

Module VFinOrdUsualOrderedType <: FinUsualOrderedType VFinType :=
 FinOrdUsualOrderedType VFinType VFinOrdType.
Module VSet <: MSetInterface.S :=
 MSetRBT.Make VFinOrdUsualOrderedType.
Module VDFS := DFS VFinType VFinOrdUsualOrderedType VSet.

Module VSetF := Facts VSet.

Section FinnHierarchical.

Variable successors_top : U -> seq U.
Variable successors_bot : V -> seq V.

Variable f'_top : U' -> A_top.
Variable f_top : U -> A_top.

Variable f'_bot : V' -> A_bot.
Variable f_bot : V -> A_bot.

Variable checkable'_bot : pred V'.

Variable p : U -> seq V.

(* defs *)

Definition succs_modifiedU := [seq u <- enum U | f_top u != f'_top (val u)].
Definition succs_impactedU := UDFS.elts_srclosure' successors_top succs_modifiedU.

(*
Definition seq_modifiedU' := [seq (val u) | u <- seq_modifiedU].
Definition seq_freshU' := [seq u <- enum U' | ~~ P_top u].
Definition seq_modified_freshU' := seq_modifiedU' ++ seq_freshU'.
*)

Definition succs_pmodified_V := flatten [seq (p v) | v <- succs_modifiedU].
Definition succs_pimpacted_V := flatten [seq (p v) | v <- succs_impactedU].
Definition succs_mset_pimpacted_V := foldl (fun s v => VSet.add v s) VSet.empty succs_pimpacted_V.

Definition P_V_succs_mset_sub v := VSet.mem v succs_mset_pimpacted_V.
Definition successors_bot_sub (v : V) := [seq v <- successors_bot v | P_V_succs_mset_sub v].

Definition succs_modifiedV_sub := [seq v <- succs_pmodified_V | f_bot v != f'_bot (val v)].
Definition succs_impactedV_sub := VDFS.elts_srclosure' successors_bot_sub succs_modifiedV_sub.
Definition succs_impactedVV'_sub := [seq val v | v <- succs_impactedV_sub].

Definition succs_freshV' := [seq v <- enum V' | ~~ P_bot v].

Definition succs_impacted_fresh_sub := succs_impactedVV'_sub ++ succs_freshV'.

Definition succs_checkable_impacted_fresh_sub :=
  [seq v <- succs_impacted_fresh_sub | checkable'_bot v].

Definition succs_hierarchical_checkable_impacted_fresh :=
  succs_checkable_impacted_fresh_sub.

(* correctness *)

Variable g_top : rel U.

Hypothesis g_top_grev : [rel x y | g_top y x] =2 grel successors_top.

Lemma succs_modifiedU_eq :
  modifiedV f'_top f_top =i succs_modifiedU.
Proof.
move => x.
by rewrite seq_modifiedU_eq.
Qed.

Lemma seq_impactedU_eq :
  impacted g_top^-1 (modifiedV f'_top f_top) =i succs_impactedU.
Proof.
move => x.
apply/impactedVP.
case: ifP.
- move/UDFS.elts_srclosure'Pg => [v Hv] Hc.
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
  apply/UDFS.elts_srclosure'Pg.
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

Lemma succs_pimpacted_V_eq :
  pimpacted_sub_V f'_top g_top f_top ps =i succs_pimpacted_V.
Proof.
move => x.
erewrite seq_pimpacted_V_eq => //.
exact: UDFS.elts_srclosure'Pg.
Qed.

(*
Lemma succs_mset_pimpacted_V_eq :
 forall x, (VSet.mem x succs_mset_pimpacted_V) = (x \in succs_pimpacted_V).
Proof.
*)

End FinnHierarchical.

End OrdinalsHierarchicalCheckableImpacted.
