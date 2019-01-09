Require Import String.

From mathcomp
Require Import all_ssreflect.

From chip
Require Import connect acyclic string kosaraju topos close_dfs run change run_seq.

Section Finn.

Local Notation A := [eqType of string].

Variable n : nat.
Variable m' : nat.

Local Notation m := m'.+1.

Hypothesis H_mn : m <= n.

Local Notation V' := 'I_n.

Definition lt_m_pred : pred V' := fun v => val v < m.

Local Notation V := (sig_finType lt_m_pred).

Variable successors : V -> seq V.

Variable f' : V' -> A.
Variable f : V -> A.
Variable runnable' : pred V'.

Definition succs_closure := @rclosure' V.
Definition succs_closureP := rclosure'Pg.
Definition succs_closure_uniq := rclosure'_uniq.

Definition succs_runnable_impacted :=
 seq_runnable_impacted f' f successors runnable' succs_closure.
Definition succs_impacted_fresh :=
 seq_impacted_fresh f' f successors succs_closure.
Definition succs_runnable_impacted_fresh :=
 seq_runnable_impacted_fresh f' f successors runnable' succs_closure.

Variable successors' : V' -> seq V'.

Definition succs_ts :=
 ts_g'rev_imf_runnable_val f' f successors runnable' succs_closure tseq successors'.

Variable (g : rel V).

Hypothesis g_grev : [rel x y | g y x] =2 grel successors.

Variable (g' : rel V').

Hypothesis g'_g'rev : [rel x y | g' y x] =2 grel successors'.

Lemma succs_impacted_fresh_eq :
  impactedV' f' f g =i succs_impacted_fresh.
Proof.
apply: seq_impacted_fresh_eq; eauto.
exact: succs_closureP.
Qed.

Lemma succs_runnable_impacted_fresh_eq :
 runnable_impactedV' f' f g runnable' =i succs_runnable_impacted_fresh.
Proof.
apply: seq_runnable_impacted_fresh_eq; eauto.
exact: succs_closureP.
Qed.

Lemma succs_impacted_fresh_uniq : uniq succs_impacted_fresh.
Proof.
apply: seq_impacted_fresh_uniq => //.
- exact: succs_closureP.
- move => s Hs.
  exact: succs_closure_uniq.
Qed.

Lemma succs_runnable_impacted_fresh_uniq :
  uniq succs_runnable_impacted_fresh.
Proof.
apply: seq_runnable_impacted_fresh_uniq => //.
- exact: succs_closureP.
- move => s Hs.
  exact: succs_closure_uniq.
Qed.

Lemma succs_ts_uniq :
  uniq succs_ts.
Proof.
apply: ts_g'rev_imf_runnable_val_uniq.
exact: tseq_uniq.
Qed.

Lemma in_succs_ts :
  forall x, x \in succs_ts ->
  runnable' x /\ x \in impactedV' f' f g.
Proof.
apply: in_ts_g'rev_imf_runnable_val; eauto.
exact: succs_closureP.
Qed.

Lemma succs_ts_in :
  forall x, runnable' x -> x \in impactedV' f' f g ->
  x \in succs_ts.
Proof.
apply: ts_g'rev_imf_runnable_val_in; eauto.
- exact: succs_closureP.
- exact: tseq_all.
Qed.

Hypothesis g'_acyclic : acyclic g'.

Local Notation gV' := [rel x y : V' | insub_g g x y].

Hypothesis f_equal_g :
  forall v, f v = f' (val v) -> forall v', gV' (val v) v' = g' (val v) v'.

Lemma succs_tseq_before : forall x y,
  x \in impactedV' f' f g -> runnable' x ->
  y \in impactedV' f' f g -> runnable' y ->
  connect g' x y ->
  before succs_ts y x.
Proof.
apply: ts_g'rev_imf_runnable_val_before; eauto.
- exact: succs_closureP.
- exact: tseq_sorted.
- exact: tseq_all.
Qed.

End Finn.
