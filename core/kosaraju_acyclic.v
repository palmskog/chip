From mathcomp
Require Import all_ssreflect.

From chip
Require Import connect acyclic kosaraju.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section KosarajuAcyclicity.

Variable V : finType.
Variable successors : V -> seq V.

Notation g := (grel successors).

Lemma uniq_flatten_kosaraju : uniq (flatten (kosaraju g)).
Proof.
have H := kosaraju_correct g.
move: H.
rewrite /=.
by case.
Qed.

Lemma all_in_flatten_kosaraju : forall v : V, v \in (flatten (kosaraju g)).
Proof.
have H := kosaraju_correct g.
move: H.
rewrite /=.
by case.
Qed.

Lemma class_diconnected_kosaraju :
  forall c, c \in kosaraju g ->
  exists x, forall y, (y \in c) = diconnect g x y.
Proof.
have H := kosaraju_correct g.
move: H.
rewrite /=.
by case.
Qed.

Definition kosaraju_acyclic := sccs_acyclic (@kosaraju V) g.

Lemma kosaraju_acyclicP :
  reflect (acyclic g) kosaraju_acyclic.
Proof.
apply sccs_acyclicP.
- exact: uniq_flatten_kosaraju.
- exact: all_in_flatten_kosaraju.
- exact: class_diconnected_kosaraju.
Qed.

End KosarajuAcyclicity.
