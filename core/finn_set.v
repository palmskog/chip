Require Import OrderedType.
Require Import MSetInterface.
Require Import MSetFacts.
Require Import MSetRBT.
Require Import String.

From mathcomp
Require Import all_ssreflect.

From chip
Require Import ordtype connect dfs_set string acyclic kosaraju topos check change check_seq.

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

Module OrdinalsRunnableImpacted (Import OT : OrdinalsType).
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

End OrdinalsRunnableImpacted.
