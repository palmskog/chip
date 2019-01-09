From mathcomp
Require Import all_ssreflect.

From chip
Require Import extra connect kosaraju acyclic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section ToposAcyclic.

Variable V : finType.

Variable g : rel V.

Variable ts : seq V.

Hypothesis ts_tsorted : tsorted g (pred_of_simpl predT) ts.

Hypothesis ts_all : forall x, x \in ts.

Hypothesis g_acyclic : acyclic g.

Lemma ts_nth : forall x y : V,
 connect g x y ->
 before
   ts
   (nth x ts (find (diconnect g x) ts)) y.
Proof.
move => x y.
move: (ts_all x).
by apply ts_tsorted.
Qed.

Lemma acyclic_find_in_diconnect :
  forall s x, x \in s ->
  nth x s (find (diconnect g x) s) = x.
Proof.
elim => //=.
move => y s IH x.
rewrite in_cons.
move/orP.
case; first by move/eqP =>->; case: ifP => //=; move/negP; case; apply: diconnect0.
case Hx: (x == y).
- move/eqP: Hx =>->.
  case: ifP => //.
  move/negP; case.
  exact: diconnect0.
- move/negP/negP: Hx => Hx Hs.
  case: ifP; last by move => Hd; exact: IH.
  move => Hd.
  move/negP/negP/eqP: Hx.
  case.
  move: Hd.
  exact: acyclic_diconnect.
Qed.

Lemma ts_connect_before : forall x y : V,
  connect g x y ->
  before ts x y.
Proof.
move => x y Hc.
move: (ts_nth Hc).
by rewrite acyclic_find_in_diconnect.
Qed.

End ToposAcyclic.

Section ToposTseq.

Variable V : finType.

Variable successors : V -> seq V.

Hypothesis g_acyclic : acyclic (grel successors).

Lemma tseq_sorted :
  tsorted (grel successors) (pred_of_simpl predT) (tseq successors).
Proof. by apply tseq_correct'. Qed.
  
Lemma tseq_all :
  forall x : V, x \in tseq successors.
Proof. by apply tseq_correct'. Qed.

Lemma pdfs_uniq : forall s l x,
  uniq l -> {subset l <= ~: s} ->
  uniq (pdfs successors (s,l) x).2.
Proof.
move => s l x.
move => Hu Hs.
have Hus: uniq l /\ {subset l <= ~: s} by [].
have Hpc := pdfs_correct' successors (s,l) x Hus.
rewrite /= in Hpc.
move: Hpc.
set f := pdfs _ _ _.
case: f => s' l'.
case: ifP => //=.
- by move => Hx; case => Hs'; move =>->.
- by move => Hx [[Hs' Hu'] He].
Qed.

Lemma pdfs_subset : forall s l s' l' x,
  uniq l -> {subset l <= ~: s} ->
  pdfs successors (s,l) x = (s', l') ->
  {subset l' <= ~: s'}.
Proof.
move => s l s' l' x.
move => Hu Hs Hp.
have Hus: uniq l /\ {subset l <= ~: s} by [].
have Hpc := pdfs_correct' successors (s,l) x Hus.
rewrite /= in Hpc.
move: Hpc.
rewrite Hp.
case: ifP => Hx; first by case =>->->.
move => [Hu' [l2 Hl2]].
case: Hl2 => Hxl2 Hs' Hl' Hts Hc.
rewrite Hs' Hl'.
move => y.
rewrite mem_cat.
move/orP; case.
- move => Hy.
  apply/setCP.
  move/setDP => [Hy' Hsy].
  move/negP: Hsy; case.
  by rewrite inE.
- move => Hy.
  apply/setCP.
  case.
  move/setDP => [Hy' Hsy].
  by move/setCP: (Hs _ Hy).
Qed.

Lemma foldr_pdfs_subset : forall l0 (s : {set V}) l s' l',
 uniq l -> {subset l <= ~: s} ->
 foldr (fun x : V => (pdfs successors)^~ x) (s, l) l0 = (s', l') ->
 uniq l' /\ {subset l' <= ~: s'}.
Proof.
elim => //=; first by move => s l' s' l0 Hu Hs; case =><-<-.
move => x l IH s l0 s' l' Hl0 Hs.
set f := foldr _ _ _.
case Hf: f.
have [Hb Ha] := IH _ _ _ _ Hl0 Hs Hf.
have Hu := pdfs_uniq x Hb Ha.
move => Hp.
rewrite Hp /= in Hu.
split => //.
move: Hp.
exact: pdfs_subset.
Qed.
  
Lemma tseq_uniq : uniq (tseq successors).
Proof.
rewrite /tseq.
set f := pdfs _.
set l := enum V.
have ->: l = rev (rev l) by rewrite revK.
rewrite foldl_rev.
have Hu: uniq (rev l) by rewrite rev_uniq; apply: enum_uniq.
move: Hu.
set l' := rev l.
move: l' => {l}.
elim => //=.
move => x l IH.
move/andP => [Hx Hul].
set f' := foldr _ _ _.
case Hf': f'.
have Hue: @uniq V [::] by [].
have Hss: {subset [::] <= ~: [set: V]} by [].
have [Huf Hus] := foldr_pdfs_subset Hue Hss Hf'.
exact: pdfs_uniq.
Qed.

Lemma tseq_connect_before : forall x y : V,
  connect (grel successors) x y ->
  before (tseq successors) x y.
Proof.
move => x y.
apply: ts_connect_before => //.
- exact: tseq_sorted.
- exact: tseq_all.
Qed.

End ToposTseq.

Section ToposTseqRel.

Variable V : finType.

Variable g : rel V.

Hypothesis g_acyclic : acyclic g.

Lemma tseq_rgraph_connect_before : forall x y : V,
  connect g x y ->
  before (tseq (rgraph g)) x y.
Proof.
move => x y Hc.
apply: tseq_connect_before.
- rewrite /acyclic => z p Hp.
  apply/negP.
  case => Hcp.
  have Hpp: path g z p.
    move: p z Hp {Hcp}.
    elim => //=.
    move => z p IH z0.
    rewrite {1}/rgraph mem_enum.
    move/andP => /= [Hz Hp].
    apply/andP; split => //.
    exact: IH.
  move/negP: (g_acyclic Hpp).
  case.
  move: Hcp.
  rewrite /= 2!rcons_path /grel /rgraph /= mem_enum.
  move/andP => [Hpz Hz].
  by apply/andP; split.
- rewrite /grel /rgraph /=.
  erewrite eq_connect; eauto.
  move => x' y'.
  by rewrite /= mem_enum.
Qed.

End ToposTseqRel.
