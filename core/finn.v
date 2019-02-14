Require Import String.

From mathcomp
Require Import all_ssreflect.

From chip
Require Import connect acyclic string kosaraju topos close_dfs check change check_seq check_seq_hierarchical.

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
Variable checkable' : pred V'.

Definition succs_closure := @rclosure' V.
Definition succs_closureP := rclosure'Pg.
Definition succs_closure_uniq := rclosure'_uniq.

Definition succs_checkable_impacted :=
 seq_checkable_impacted f' f successors checkable' succs_closure.
Definition succs_impacted_fresh :=
 seq_impacted_fresh f' f successors succs_closure.
Definition succs_checkable_impacted_fresh :=
 seq_checkable_impacted_fresh f' f successors checkable' succs_closure.

Variable successors' : V' -> seq V'.

Definition succs_ts :=
 ts_g'rev_imf_checkable_val f' f successors checkable' succs_closure tseq successors'.

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
- move => s Hs.
  exact: succs_closure_uniq.
Qed.

Lemma succs_checkable_impacted_fresh_uniq :
  uniq succs_checkable_impacted_fresh.
Proof.
apply: seq_checkable_impacted_fresh_uniq => //.
- exact: succs_closureP.
- move => s Hs.
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

Section FinnHierarchical.

Local Notation A_top := [eqType of string].
Local Notation A_bot := [eqType of string].

Variable n_top : nat.
Variable m'_top : nat.

Local Notation m_top := m'_top.+1.

Hypothesis H_mn_top : m_top <= n_top.

Local Notation U' := 'I_n_top.

Definition lt_m_top_pred : pred U' := fun v => val v < m_top.

Local Notation U := (sig_finType lt_m_top_pred).

Variable successors_top : U -> seq U.

Variable f'_top : U' -> A_top.
Variable f_top : U -> A_top.

Variable n_bot : nat.
Variable m'_bot : nat.

Local Notation m_bot := m'_bot.+1.

Hypothesis H_mn_bot : m_bot <= n_bot.

Local Notation V' := 'I_n_bot.

Definition lt_m_bot_pred : pred V' := fun v => val v < m_bot.

Local Notation V := (sig_finType lt_m_bot_pred).

Variable successors_bot : V -> seq V.

Variable f'_bot : V' -> A_bot.
Variable f_bot : V -> A_bot.
Variable checkable'_bot : pred V'.

Variable p : U -> seq V.

Definition succs_hierarchical_checkable_impacted_fresh :=
  @seq_checkable_impacted_fresh_sub A_top A_bot _ _ f'_top f'_bot _ _ f_top f_bot successors_top successors_bot p checkable'_bot (@rclosure' _) (@rclosure' _).

(*
Variable successors'_top : U' -> seq U'.
Variable (g_top : rel U).
Hypothesis g_top_grev : [rel x y | g_top y x] =2 grel successors_top.
*)

Variable (g_bot : rel V).

Hypothesis g_bot_grev : [rel x y | g_bot y x] =2 grel successors_bot.

(*
Lemma succs_hierarchical_checkable_impacted_fresh_eq :
 checkable_impactedV' f'_bot f_bot g_bot checkable'_bot =i succs_hierarchical_checkable_impacted_fresh.
Proof.
exact: succs_closureP.
Qed.
*)

End FinnHierarchical.
