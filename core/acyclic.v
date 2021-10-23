From mathcomp Require Import all_ssreflect.
From chip Require Import connect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Cycles.

Variable V : finType.
Variable g : rel V.

Lemma self_loop_cycle : forall x, g x x -> cycle g [:: x].
Proof.
move => x H_in.
rewrite /cycle /=.
by apply/andP.
Qed.

Lemma diconnect_path_cycle :
  forall x y, x != y -> diconnect g x y -> exists p, cycle g (x :: p).
Proof.
move => x y H_neq /andP /= [H_x H_y].
move/connectP: H_x; case => px H_px H_pl.
move/connectP: H_y; case => py H_py H_pl'.
case: py H_py H_pl' => /=; first by move => H_py H_eq; rewrite H_eq in H_neq; move/negP: H_neq.
move => y' py' /andP [H_in H_py'] H_x.
exists (px ++ belast y' py').
rewrite rcons_cat /= {2}H_x -lastI cat_path -H_pl /=.
apply/andP; split => //.
by apply/andP.
Qed.

Lemma cycle_path_diconnect :
  forall x p, cycle g (x :: p) ->
  x \in g x \/ (exists y, diconnect g x y /\ x != y).
Proof.
move => x p.
move: x.
rewrite /=.
case: p => //=.
- move => x /andP [H_p ?].
  by left.
- move => y p x.
  case H_eq: (x == y).
  * move/eqP: H_eq => H_eq.
    rewrite H_eq.    
    move/andP => [H_in H_p].
    by left.
  * move/negP: H_eq => H_eq.
    move/andP => [H_in H_p].
    right.
    exists y; split; last by apply/negP.
    apply/andP.
    split; first by apply/connectP; exists [:: y]; first by rewrite /=; apply/andP.
    apply/connectP.
    exists (rcons p x); first by [].
    by rewrite last_rcons.
Qed.

End Cycles.

Section Acyclic.

Variable V : finType.
Variable g : rel V.

Definition acyclic := forall x p, path g x p -> ~~ cycle g (x :: p).

Hypothesis g_acyclic: acyclic.

Lemma acyclic_no_self_loop : forall x, ~~ g x x.
Proof.
move => x; apply/negP => Hg.
move/g_acyclic: (self_loop_cycle Hg).
by move/negP; case => /=; apply/and3P.
Qed.

Lemma acyclic_diconnect : forall x y, diconnect g x y -> x = y.
Proof.
move => x y Hd.
case Hx: (x == y); first by apply/eqP.
move/negP/negP: Hx => Hx.
have [p Hc] := diconnect_path_cycle Hx Hd.
have Hp: path g x p by move: Hc; rewrite /= rcons_path; move/andP => [Hp Ha].
by move/negP: (g_acyclic Hp); case.
Qed.

End Acyclic.

Section AcyclicSub.

Variable V : finType.
Variable g : rel V.

Hypothesis g_acyclic : acyclic g.

Variable P : pred V.

Local Notation I := (sig_finType P).

Local Notation gsub := [rel x y : I | g (val x) (val y)].

Lemma gsub_acyclic : acyclic gsub.
Proof.
move => x p.
move/gsub_path.
move/g_acyclic => Hc.
rewrite /= rcons_path.
apply/negP => Hc'.
move/andP: Hc' => [Hp Hg].
move/negP: Hc.
case.
rewrite /= rcons_path.
apply/andP.
split; first by apply/gsub_path.
rewrite /= in Hg.
by rewrite last_map.
Qed.

End AcyclicSub.

Section AcyclicRev.

Variable V : finType.

Variable g : rel V.

Hypothesis g_acyclic : acyclic g.

Local Notation grev := [rel x y | g y x].

Lemma acyclic_rev : acyclic grev.
Proof.
move => x p Hp.
apply/negP => H_c; move: H_c.
move/cycle_path_diconnect.
case.
- move => H_in.
  have Hg: g x x by [].  
  move/self_loop_cycle: Hg => Hg.  
  contradict Hg.
  apply/negP.
  exact: g_acyclic.
- move => [y [Hd Hn]].
  have H_rev: g =2 [rel x y | grev y x] by [].
  have Hd': diconnect g x y.  
  have Heq := eq_diconnect H_rev.
    rewrite Heq.
    move/andP: Hd => [Hc1 Hc2].
    apply/andP.
    by split; apply connect_rev.
  have Hc := diconnect_path_cycle _ Hd'.
  have [p' Hc'] := Hc Hn.
  have Hp': path g x p'.
    rewrite /= in Hc'.
    rewrite rcons_path in Hc'.
    by move/andP:Hc' => [Hp' Hgl].
  contradict Hc'.
  apply/negP.
  exact: g_acyclic.
Qed.

End AcyclicRev.

Section Acyclicity.

Variable V : finType.
Variable sccs : rel V -> seq (seq V).
Variable g : rel V.

Hypothesis uniq_flatten : uniq (flatten (sccs g)).

Hypothesis all_in_flatten : forall v : V, v \in (flatten (sccs g)).

Hypothesis class_diconnected :
  forall c, c \in sccs g ->
  exists x, forall y, (y \in c) = diconnect g x y.

Lemma in_flatten (A : seq (seq V)) s :
  s \in A ->
  subseq s (flatten A).
Proof.
elim: A => //=.
move => vs c IH H_in.
have H_or: s = vs \/ s \in c.
  move/orP: H_in.
  case; first by move/eqP; left.
  by right.
case: H_or => H_in'.
  by rewrite H_in' prefix_subseq.
have IH' := IH H_in'.
have ->: s = [::] ++ s by [].
by apply cat_subseq; first exact: sub0seq.
Qed.

Lemma non_singleton_neq : forall v v' vs,
  [:: v, v' & vs] \in sccs g ->
  v != v'.
Proof.
move => v v' vs H_ks.
apply/negP.
move/eqP => H_eq.
rewrite -H_eq {H_eq} in H_ks.
have H_fl := uniq_flatten.
apply in_flatten in H_ks.
apply subseq_uniq in H_ks => //.
rewrite /= in H_ks.
move/andP: H_ks.
rewrite inE.
move => [H_n H_u].
move/negP: H_n => H_n.
case: H_n.
by apply/orP; left.
Qed.

Lemma non_singleton_cycle : forall v v' vs,
  [:: v, v' & vs] \in sccs g ->
  exists x p, cycle g (x :: p).
Proof.
move => v v' vs H_ks.
have H_c := class_diconnected H_ks.
rewrite /class_diconnected /= in H_c.
move: H_c => /= [x H_y].
have H_v := H_y v.
have H_v' := H_y v'.
have H_neq := non_singleton_neq H_ks.
have H_in_v: v \in [:: v, v' & vs] by rewrite inE; apply/orP; left.
have H_in_v': v' \in [:: v, v' & vs] by rewrite inE; apply/orP; right; apply/orP; left.
rewrite H_v {H_v} in H_in_v.
rewrite H_v' {H_v'} in H_in_v'.
rewrite /diconnect in H_in_v H_in_v'.
move/andP: H_in_v => [H_cn_v H_cn'_v].
move/connectP: H_cn_v => [pv H_pv] H_vl.
move/connectP: H_cn'_v => [p'v H_p'v] H_vl'.
move/andP: H_in_v' => [H_cn_v' H_cn'_v'].
move/connectP: H_cn_v' => [pv' H_pv'] H_v'l.
move/connectP: H_cn'_v' => [p'v' H_p'v'] H_v'l'.
have H_pvv': connect g v v'.
  apply/connectP.
  exists (p'v ++ pv'); last by rewrite last_cat -H_vl'.
  rewrite cat_path.
  rewrite -H_vl'.
  by apply/andP.
have H_p'vv': connect g v' v.
  apply/connectP.
  exists (p'v' ++ pv); last by rewrite last_cat -H_v'l'.
  rewrite cat_path.
  rewrite -H_v'l'.
  by apply/andP.
have H_di: diconnect g v v'.
  rewrite /diconnect.
  by apply/andP.
have [p H_p] := diconnect_path_cycle H_neq H_di.
by exists v, p.
Qed.

Lemma all_in_sccs v : exists vs, vs \in sccs g /\ v \in vs.
Proof.
move/flattenP: (all_in_flatten v).
by case => vs H_vs H_in; exists vs.
Qed.

Lemma diconnect_neq_sccs :
  forall x y, diconnect g x y -> x != y ->
  exists v v' vs, [:: v, v' & vs] \in sccs g.
Proof.
move => x y H_y H_neq.
have [vs [H_vs H_in]] := all_in_sccs x.
have [x' H_c] := class_diconnected H_vs.
have H_eq: x \in vs by [].
have H_c' := H_c x.
rewrite H_c' in H_eq.
have H_di: diconnect g x' y.
  move/andP: H_eq => [H_x'x H_xx'].
  move/andP: H_y => [H_xy H_yx].
  apply/andP; split.
  - move: H_x'x H_xy.
    exact: connect_trans.
  - move: H_yx H_xx'.
    exact: connect_trans.
rewrite -H_c in H_di.
move {H_y H_c H_c' H_eq}.
case: vs H_in H_di H_vs => //.
move => v.
case.
- rewrite 2!inE.
  move/eqP => H_xv.
  rewrite -H_xv.
  move/eqP => H_yx.
  move/negP: H_neq => H_neq.
  case: H_neq.
  by apply/eqP.
- move => v' vs H_x H_y.
  by exists v, v', vs.
Qed.

Definition class_acyclic (c : seq V) :=
match c with
| [::] => true  
| [:: v] => ~~ g v v
| [:: _, _ & _] => false
end.

Definition sccs_acyclic :=
  all [pred c | class_acyclic c] (sccs g).

Lemma sccs_acyclicP :
  reflect (acyclic g) sccs_acyclic.
Proof.
  apply: (iffP idP).
- move/allP => /=.
  move => H_in_ac v p H_p.
  apply/negP => H_ce.
  apply cycle_path_diconnect in H_ce.
  case: H_ce => H_ce.
  * have [vs [H_vs H_v]] := all_in_sccs v.
    move: H_vs H_v.
    move/H_in_ac.
    case: vs => //=.
    move => v'.
    case => //=.
    move/negP.
    rewrite inE => H_in.
    move/eqP => H_eq.
    by rewrite H_eq in H_ce.
  * move: H_ce => [y [H_d H_neq]].
    have [v0 [v1 [vs H_ks]]] := diconnect_neq_sccs H_d H_neq.
    by move/H_in_ac: H_ks.
- move => H_gc.
  apply/allP.
  case => //= v.
  case => //=.
  * move => H_in.
    apply/negP.
    move => H_in'.
    have H_ce: cycle g [:: v] by apply/andP.
    contradict H_ce.
    apply/negP.
    exact: H_gc.
  * move => v' vs.
    move/non_singleton_cycle.
    move => [x [p H_ce]].
    have H_ce' := H_ce.
    rewrite /= in H_ce'.
    rewrite rcons_path in H_ce'.
    move/andP: H_ce' => [H_p H_l].
    contradict H_ce.
    apply/negP.
    exact: H_gc.
Qed.

End Acyclicity.
