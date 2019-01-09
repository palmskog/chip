From mathcomp
Require Import all_ssreflect.

From chip
Require Import extra connect run change acyclic kosaraju topos.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section CheckedSeq.

Variable A : eqType.

Variable V' : finType.

Variable (f' : V' -> A).

Variable P : pred V'.

Local Notation V := (sig_finType P).

Variable (f : V -> A).

Variable grev : V -> seq V.

Variable runnable' : pred V'.

Variable clos : (V -> seq V) -> seq V -> seq V.

Hypothesis closP : forall successors (s : seq V) (x : V),
  reflect
    (exists2 v, v \in s & connect (grel successors) v x)
    (x \in clos successors s).

Hypothesis clos_uniq : forall successors (s : seq V),
  uniq s -> uniq (clos successors s).

Variable ts : forall T : finType, (T -> seq T) -> seq T.

Hypothesis ts_tsorted : forall (T : finType) (successors : T -> seq T),
  tsorted (grel successors) (pred_of_simpl predT) (ts successors).

Hypothesis ts_all : forall (T : finType) successors (x : T), x \in (ts successors).

Hypothesis ts_uniq : forall (T : finType) (successors : T -> seq T), uniq (ts successors).

Definition seq_modifiedV := [seq v <- enum V | f v != f' (val v)].
Definition seq_impactedV := clos grev seq_modifiedV.

Definition seq_impactedV' := [seq (val v) | v <- seq_impactedV].
Definition seq_freshV' := [seq v <- enum V' | ~~ P v].

Definition seq_runnable_impacted := [seq v <- seq_impactedV' | runnable' v].
Definition seq_impacted_fresh := seq_impactedV' ++ seq_freshV'.
Definition seq_runnable_impacted_fresh := [seq v <- seq_impacted_fresh | runnable' v].

Variable g : rel V.

Hypothesis g_grev : [rel x y | g y x] =2 grel grev.

Lemma seq_modifiedV_eq :
  modifiedV f' f =i seq_modifiedV.
Proof.
by move => x; rewrite inE mem_filter mem_enum andb_idr.
Qed.

Lemma seq_freshV'_eq :
 freshV' P =i seq_freshV'.
Proof.
move => x.
rewrite -sub_freshV'.
rewrite mem_filter.
rewrite mem_enum /=.
rewrite andb_idr //.
have H_sp := (insubP [subType of V] x).
destruct H_sp; last by rewrite insubN.
by rewrite i insubT.
Qed.

Lemma seq_impactedV'_eq :
  impactedVV' g (modifiedV f' f) =i seq_impactedV'.
Proof.
move => x.
apply/imsetP.
case: ifP.
- move/mapP => [y Hy] Hx.
  move: Hy.
  move/(closP grev) => [v Hv] Hc.
  move: Hv.
  rewrite -seq_modifiedV_eq => Hv.
  exists y => //.
  apply/impactedVP.
  exists v => //.
  move/connectP: Hc => [p Hp] Hl.
  apply/connectP.
  exists p => //.
  elim: p v Hp {Hv Hl} => //.
  move => v p IH v0.
  rewrite /=.
  move/andP => [Hv Hp].
  apply/andP.
  split; last by apply: IH.
  move: Hv.
  move: (g_grev v0 v).
  by rewrite /= =>->.
- move/negP => Hs.
  move => [y Hy] Hxy.
  case: Hs.
  apply/mapP.
  exists y => //.
  move/impactedVP: Hy => [v Hv] Hc.
  move: Hv; rewrite seq_modifiedV_eq =>  Hv.
  apply/(closP grev).
  exists v => //.
  move/connectP: Hc => [p Hp] Hl.
  apply/connectP.
  exists p => //.
  elim: p v Hp {Hv Hl} => //.
  move => v p IH v0.
  rewrite /=.
  move/andP => [Hv Hp].
  apply/andP.
  split; last by apply: IH.
  move: Hv.
  move: (g_grev v0 v).
  by rewrite /= =>->.
Qed.

Lemma seq_impacted_fresh_eq :
  impactedV' f' f g =i seq_impacted_fresh.
Proof.
move => x.
apply/impactedV'P.
case: ifP.
- rewrite mem_cat.
  move/orP.
  case.
  * rewrite seq_impactedV'_eq => Hv.
    left; split => //.
    move/mapP: Hv => [v Hv] Hvx.
    apply/freshV'P.
    move => Hf.
    move/negP: (Hf v); case.
    by apply/eqP.
  * rewrite mem_filter.
    move/andP.
    move => [Hp Hx].
    right.
    split.
    + rewrite -sub_freshV'.
      have H_sp := (insubP [subType of V] x).
      destruct H_sp => //.
      by move/negP: Hp.
    + apply/imsetP.
      case => v Hv Hvx.
      move/negP: Hp.
      case.
      rewrite Hvx.
      by apply/valP.
- move => Hx.
  case.
  * rewrite seq_impactedV'_eq.
    move => [Hi Hf].
    move/negP: Hx.
    case.
    rewrite mem_cat.
    apply/orP.
    by left.
  * move => [Hf Hi].
    move/negP: Hx.
    case.
    rewrite mem_cat.
    apply/orP.
    right.
    by rewrite -seq_freshV'_eq.
Qed.

Lemma seq_runnable_impacted_fresh_eq :
 runnable_impactedV' f' f g runnable' =i seq_runnable_impacted_fresh.
Proof.
move => x.
rewrite inE.
rewrite mem_filter.
rewrite andbC.
apply andb_id2l => Hc.
by rewrite seq_impacted_fresh_eq.
Qed.

Lemma seq_modifiedV_uniq : uniq seq_modifiedV.
Proof. by rewrite filter_uniq // enum_uniq. Qed.

Lemma seq_impacted_fresh_uniq : uniq seq_impacted_fresh.
Proof.
rewrite cat_uniq.
apply/andP; split.
- rewrite map_inj_uniq; last by apply val_inj.
  apply clos_uniq.
  by apply seq_modifiedV_uniq.
- apply/andP; split; last by rewrite filter_uniq // enum_uniq.
  apply/negP.
  case.
  move/hasP.
  move => /= [x Hx] Hm.
  move: Hx Hm.
  rewrite -seq_freshV'_eq -seq_impactedV'_eq => Hx Hm.
  move/negP: Hx; case; apply/negP.
  move: Hm.
  by apply impactedVV'_freshV'.
Qed.

Lemma seq_runnable_impacted_fresh_uniq : uniq seq_runnable_impacted_fresh.
Proof.
rewrite filter_uniq //.
exact: seq_impacted_fresh_uniq.
Qed.

(* topological sort of whole graph *)

Variable g'rev : V' -> seq V'.

Variable g' : rel V'.

Hypothesis g'_acyclic : acyclic g'.

Hypothesis g'_g'rev : [rel x y | g' y x] =2 grel g'rev.

Definition ts_g'rev := ts g'rev.

Lemma ts_rev_before : forall (x y : V'),
  connect g' x y ->
  before ts_g'rev y x.
Proof.
move => x y Hc.
apply: ts_connect_before; eauto.
- exact: ts_all.
- apply: acyclic_rev.
  move => z p Hp.
  apply/negP.
  case => Hcp.
  have Hpp: path g' z p.
    move: p z Hp {Hcp}.
    elim => //=.
    move => v p IH z.
    move/andP => [Hz Hp].
    have Hz': grel g'rev v z by [].
    move: Hz'.
    rewrite -g'_g'rev /= => Hz'.
    apply/andP.
    split => //.
    exact: IH.
  move/negP: (g'_acyclic Hpp).
  case.
  move: Hcp.
  rewrite /= 2!rcons_path.
  move/andP => [Hcp Hl].
  apply/andP.
  have Hz': grel g'rev z (last z p) by [].
  move: Hz'.
  rewrite -g'_g'rev /= => Hg.
  by split.
- apply/connect_rev.
  rewrite -(@eq_connect _ g') //.
  move => z0 z1.
  have ->: (z0 \in g'rev z1) = grel g'rev z1 z0 by [].
  by rewrite -g'_g'rev.
Qed.

Definition ts_g'rev_runnable_imf :=
 [seq x <- ts_g'rev | x \in seq_runnable_impacted_fresh].

Lemma ts_g'rev_runnable_imf_uniq : uniq ts_g'rev_runnable_imf.
Proof.
apply: filter_uniq.
exact: ts_uniq.
Qed.

Lemma in_ts_g'rev_runnable_imf :
  forall x, x \in ts_g'rev_runnable_imf ->
  runnable' x /\ x \in impactedV' f' f g.
Proof.
move => x.
rewrite mem_filter.
move/andP => [Hs Hx].
move: Hs.
rewrite -seq_runnable_impacted_fresh_eq inE.
by move/andP => [Hss Hxx].
Qed.

Lemma ts_g'rev_runnable_imf_in :
  forall x, runnable' x -> x \in impactedV' f' f g ->
  x \in ts_g'rev_runnable_imf.
Proof.
move => x Hc Hx.
rewrite mem_filter.
apply/andP.
split; last by apply ts_all.
rewrite -seq_runnable_impacted_fresh_eq inE.
by apply/andP; split.
Qed.

Lemma ts_g'rev_runnable_imf_before : forall x y,
  y \in impactedV' f' f g ->
  runnable' y ->
  connect g' x y ->
  before ts_g'rev_runnable_imf y x.
Proof.
move => x y Hc Hy Hc'.
apply: before_filter; last by apply: ts_rev_before.
rewrite mem_filter.
apply/andP; split => //.
rewrite -seq_runnable_impacted_fresh_eq inE; first by apply/andP; split.
exact: ts_all.
Qed.

(* topological sort in subgraph of impacted+fresh vertices *)

Definition pimf : pred V' := fun v => v \in seq_impacted_fresh.

Local Notation V'_imf := (sig_finType pimf).

Local Notation g'_imf := [rel x y : V'_imf | g' (val x) (val y)].

Definition g'rev_imf (v : V'_imf) : seq V'_imf :=
  pmap insub (g'rev (val v)).

Definition ts_g'rev_imf := ts g'rev_imf.

Lemma ts_g'rev_imf_all :
  forall (x : V'_imf), x \in ts_g'rev_imf.
Proof. move => x. exact: ts_all. Qed.

Lemma ts_g'rev_imf_uniq : uniq ts_g'rev_imf.
Proof. exact: ts_uniq. Qed.

Lemma ts_g'rev_imf_before : forall (x y : V'_imf),
  connect g'_imf x y ->
  before ts_g'rev_imf y x.
Proof.
move => x y Hc.
apply: ts_connect_before; eauto.
- exact: ts_all.
- apply: acyclic_rev.
  move => z p Hp.
  apply/negP => Hc'.
  have Hp': path g' (val z) [seq (val v) | v <- p].
    elim: p z Hp {Hc'} => //=.
    move => v p IH z.
    move/andP => [Hz Hp].
    move: Hz.
    rewrite /g'rev_imf => Hz.
    apply/andP.
    split; last by apply: IH.
    suff Hsuff: grel g'rev (val v) (val z) by rewrite -g'_g'rev in Hsuff.
    move: Hz.
    rewrite /=.
    elim: (g'rev _) => //=.
    move => v' l.
    rewrite /oapp /= => IH'.
    have H_sp := (insubP [subType of V'_imf] v').
    destruct H_sp => //=.
    * rewrite insubT.
      move/orP.
      case.
      + move/eqP =>->.
        rewrite SubK in_cons.
        by apply/orP; left.
      + move => Hz.
        rewrite in_cons.
        apply/orP.
        by right; apply: IH'.
    * rewrite insubN //.
      move/IH' => Hz.
      by apply/orP; right.
  move/negP: (g'_acyclic Hp').
  case.
  move: Hc'.
  rewrite /= 2!rcons_path.
  move/andP => [Hc' Hl].
  apply/andP.
  split => //.
  move: Hl.
  rewrite /g'rev_imf /= => Hl.
  suff Hsuff: grel g'rev (val z) (last (sval z) [seq sval v | v <- p]).
    move: Hsuff.
    by rewrite -g'_g'rev.
  rewrite /=.
  move: Hl.
  set l := g'rev _.
  move: l.
  elim: p z {Hp Hp' Hc'} => //=.
  * move => z l.
    elim: l z => //=.
    move => v l IH z.
    rewrite /oapp /=.
    have H_sp := (insubP [subType of V'_imf] v).
    destruct H_sp => //=.
    * rewrite insubT.
      move/orP.
      case.
      + move/eqP =>->.
        rewrite SubK in_cons.
        by apply/orP; left.
      + move => Hz.
        rewrite in_cons.
        apply/orP.
        by right; apply: IH.
    * rewrite insubN //.
      move/IH => Hz.
      by apply/orP; right.
  * move => v l IH v0 l' Hl.
    exact: IH.
- apply: connect_rev.
  rewrite -(@eq_connect _ [rel x y | g' (val x) (val y)]) //.
  move => x' y' /=.
  move: (g'_g'rev (val y') (val x')).
  rewrite /= =>->.
  rewrite /g'rev_imf /=.
  elim: (g'rev _) => //=.
  move => v' l0 IH'.
  rewrite /oapp /=. 
  rewrite in_cons IH'.
  have H_sp := (insubP [subType of V'_imf] v').
  destruct H_sp; first by rewrite insubT.
  rewrite insubN //.
  apply/orP.
  case: ifP; first by move => Hx; right.
  move/negP => Hx.
  move => Hs.
  case: Hs => //.
  move/eqP => Hs.
  rewrite -Hs in i.
  case/negP: i.
  by case: x' {IH' Hx Hs}.
Qed.

Definition ts_g'rev_imf_runnable :=
 [seq x <- ts_g'rev_imf | runnable' (val x)].

Lemma ts_g'rev_imf_runnable_before : forall x y,
  runnable' (val y) ->
  connect g'_imf x y ->
  before ts_g'rev_imf_runnable y x.
Proof.
move => x y Hy Hc.
apply: before_filter; last by apply: ts_g'rev_imf_before.
rewrite mem_filter.
apply/andP.
by split; last by apply: ts_g'rev_imf_all.
Qed.

Definition ts_g'rev_imf_runnable_val :=
 [seq (val x) | x <- ts_g'rev_imf_runnable].

Lemma ts_g'rev_imf_runnable_val_uniq :
  uniq ts_g'rev_imf_runnable_val.
Proof.
rewrite map_inj_uniq; last by apply val_inj.
apply: filter_uniq.
exact: ts_g'rev_imf_uniq.
Qed.

Lemma in_ts_g'rev_imf_runnable_val :
  forall x, x \in ts_g'rev_imf_runnable_val ->
  runnable' x /\ x \in impactedV' f' f g.
Proof.
move => x.
move/mapP => [x' Hx'] Hx.
move: Hx'.
rewrite mem_filter => /andP; move => [Hxc Hxt].
rewrite Hx; split => //.
rewrite seq_impacted_fresh_eq.
move: Hxt.
by case: x' Hx Hxc.
Qed.

Lemma ts_g'rev_imf_runnable_val_in :
  forall x, runnable' x -> x \in impactedV' f' f g ->
  x \in ts_g'rev_imf_runnable_val.
Proof.
move => x Hc.
rewrite seq_impacted_fresh_eq => Hx.
have H_sp := (insubP [subType of V'_imf] x).
destruct H_sp; last by case/negP: i.
apply/mapP.
exists u => //.
rewrite mem_filter.
apply/andP; split; first by rewrite e.
exact: ts_g'rev_imf_all.
Qed.

(* goal: generate sequence as though we did the topological sort for the whole graph *)

Local Notation gV' := [rel x y : V' | insub_g g x y].

Hypothesis f_equal_g :
  forall v, f v = f' (val v) -> forall v', gV' (val v) v' = g' (val v) v'.

(* Outline: if the path from x to y has any non-impacted, non-fresh vertices,
   then those vertices have a path to a modified vertex, and are thus impacted as well *)

Lemma non_impacted_rel : forall (x : V) y,
  val x \notin impactedV' f' f g ->
  g' (val x) y ->
  y \notin impactedV' f' f g.
Proof.
move => x y.
move/impactedV'P => Hx Hg.
apply/impactedV'P.
move => Hy.
case: Hx.
case: Hy.
- move => [Hy Hy'].
  left.
  split; last first.
    apply/freshV'P => Hv.
    move/negP: (Hv x).
    by case.  
  move/imsetP: Hy => [u Hu] Hy.
  case Hf: (f x == f' (val x)); last first.
    move/negP/negP: Hf => Hf.
    apply/imsetP.
    exists x => //.
    apply/impactedVP.
    exists x => //.
    by rewrite inE.
  move/eqP: Hf => Hf.
  move: Hg.
  rewrite Hy.
  rewrite -(f_equal_g Hf) /=.
  have Hg := ginsub_eq g x u.
  move: Hg.
  rewrite /= =><- Hg.
  apply/imsetP.
  exists x => //.
  move/impactedVP: Hu => [v Hv] Hc.
  apply/impactedVP.
  exists v => //.
  apply/connect_rev.
  move/connect_rev: Hc.
  rewrite /=.
  move/connectP => [p Hp] Hl.
  apply/connectP.
  exists (u :: p) => //.
  rewrite /=.
  apply/andP.
  by split.  
- move => [Hy Hy'].
  case Hf: (f x == f' (val x)).
  * move/eqP: Hf => Hf.
    have Hfg := f_equal_g Hf y.
    rewrite /= in Hfg.
    move/freshV'P: Hy => Hy.
    rewrite Hg in Hfg.
    move/negP: Hfg.
    case.    
    rewrite /insub_g /= insubT; first by apply/valP.
    move => Hxp.
    have H_sp := (insubP [subType of V] y).
    destruct H_sp; last by rewrite insubN.
    move/negP: (Hy u); case.
    by apply/eqP.
  * move/negP/negP: Hf => Hf.
    left.
    split.
    + apply/imsetP.
      exists x => //.
      apply/impactedVP.
      exists x => //.
      by rewrite inE.
    + apply/freshV'P => Hv.
      move/negP: (Hv x).
      by case.
Qed.   

Lemma connect_imp :  forall x y,
  y \in impactedV' f' f g ->
  connect g' x y ->
  x \in impactedV' f' f g.
Proof.
move => x y Hy.
move/connectP => [p Hp] Hl.
elim: p x Hp Hl => //=; first by move => x Hp <-.
move => v' p IH x.
move/andP => [Hg Hp] Hl.
have IH' := IH _ Hp Hl.
apply/impactedV'P.
rewrite -sub_freshV'.
have H_sp := (insubP [subType of V] x).
destruct H_sp; last first.
  right.
  split => //.
  apply/imsetP.
  case => x0 Hx0 Hvx.
  case/negP: i.
  rewrite Hvx.
  apply/valP.
left.
split => //.
move: Hg.
rewrite -e => Hg.
case Hc: (_ \in _) => //.
move/negP/negP: Hc => Hc'.
move/negP: IH'.
case.
apply/negP.
move: Hg.
apply/non_impacted_rel.
apply/impactedV'P.
case.
- move => [Hu Hf].
  move/negP: Hc'.
  by case.
- move => [Hu Hf].
  move/freshV'P: Hu => Hu.
  move/negP: (Hu u).
  by case.
Qed.

Lemma connect_g'_imf : forall (x y : V'_imf),
 connect g' (val x) (val y) ->
 connect g'_imf x y.
Proof.
move => x y.
move/connectP => [p Hp] Hl.
have Hx: val x \in impactedV' f' f g.
  rewrite seq_impacted_fresh_eq.
  by apply/valP.
have Hy: val y \in impactedV' f' f g.
  rewrite seq_impacted_fresh_eq.
  by apply/valP.
have Hpi: forall z : V', z \in p -> connect g' z (val y).
  move: Hp Hl {Hx}.
  set vx := val x.
  move: p vx => {x}.
  elim => //=.
  move => v p IH x.
  move/andP => [Hg Hp] Hl z.
  rewrite in_cons.
  move/orP.
  case.
  - move/eqP =>->.
    apply/connectP.
    by exists p.
  - move => Hz.
    by eapply IH; eauto.    
have Hpf: forall z : V', z \in p -> z \in seq_impacted_fresh.
  move => z Hz.
  rewrite -seq_impacted_fresh_eq.
  move: (Hpi _ Hz).
  exact: connect_imp.
apply/connectP.
exists (pmap insub p); last first.
- move {Hp Hx Hy Hpi}.
  elim: p x Hl Hpf => //=; first by move => x; move/val_inj =>->.
  move => x p IH x0 Hl Hpf.
  rewrite /oapp.
  have Hx: x \in seq_impacted_fresh.
    apply: Hpf.
    rewrite in_cons.
    by apply/orP; left.
  have H_sp := (insubP [subType of V'_imf] x).
  destruct H_sp; last by case/negP: i.
  rewrite -e in Hl.
  rewrite -e.
  rewrite insubT; first by rewrite e.
  move => Hp.
  rewrite /=.
  apply: IH; first by rewrite -Hl.
  move => z Hz.
  apply: Hpf.
  rewrite in_cons.
  apply/orP.
  by right.
- move {Hl Hy Hpi Hx}.
  elim: p x Hp Hpf => //=.
  move => v p IH x.
  move/andP => [Hg Hp] Hpf.
  rewrite /oapp /=.
  have Hv: v \in seq_impacted_fresh.
    apply: Hpf.
    rewrite in_cons.
    by apply/orP; left.
  have H_sp := (insubP [subType of V'_imf] v).
  destruct H_sp; last by case/negP: i.
  rewrite -e insubT /=; first by rewrite e.
  move => Hu.
  apply/andP.
  split => //=; first by rewrite e.
  apply: IH.
    rewrite /sval /=.
    case: u e Hu => u Hu Hvu Hpv.
    move: Hvu.
    by rewrite /= =>->.
  move => z Hz.
  apply: Hpf.
  rewrite in_cons.
  by apply/orP; right.
Qed.

Lemma ts_g'rev_imf_runnable_val_before : forall x y,
  x \in impactedV' f' f g -> runnable' x ->
  y \in impactedV' f' f g -> runnable' y ->
  connect g' x y ->
  before ts_g'rev_imf_runnable_val y x.
Proof.
move => x y Hx Hxc Hy Hyc Hc.
have H_sp := (insubP [subType of V'_imf] x).
have H_sp' := (insubP [subType of V'_imf] y).
destruct H_sp; last first.
  case/negP: i.
  rewrite /pimf.
  by rewrite -seq_impacted_fresh_eq.
destruct H_sp'; last first.
  case/negP: i0.
  rewrite /pimf.
  by rewrite -seq_impacted_fresh_eq.
have Hc': connect g' (val u) (val u0).
  by rewrite e e0.
apply connect_g'_imf in Hc'.
have Hyc': runnable' (val u0) by rewrite e0.
have Ht := ts_g'rev_imf_runnable_before Hyc' Hc'.
rewrite /before /index.
rewrite 2!find_map /=.
rewrite /preim /=.
by rewrite -e -e0.
Qed.

End CheckedSeq.
