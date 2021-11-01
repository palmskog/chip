From Coq Require Import OrderedType MSetInterface MSetFacts MSetRBT.
From mathcomp.ssreflect Require Import all_ssreflect.
From chip Require Import ordtype close_dfs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type OrdType.
Parameter T : ordType.
End OrdType.

Module OrdTypeUsualOrderedType (Import OT : OrdType) <: UsualOrderedType.

Definition t : Type := T.
Definition eq := @eq T.
Definition eq_equiv := @eq_equivalence T.

Definition lt : t -> t -> Prop := @ord T.

Lemma lt_strorder : StrictOrder (@ord T).
Proof.
split; first by move => x Hi; rewrite irr in Hi.
by move => x y z; apply: trans.
Qed.

Lemma lt_compat : Proper (eq ==> eq ==> iff) (@ord T).
Proof.
move => x1 y1 Hxy1 x2 y2 Hxy2.
by rewrite Hxy1 Hxy2.
Qed.

Definition compare x y :=
 if x == y then Eq else if @ord T x y then Lt else Gt.

Lemma compare_spec x y : CompSpec eq (@ord T) x y (compare x y).
Proof.
rewrite /compare.
case: ifP; first by move/eqP => Heq; apply CompEq.
move/negP/negP/eqP => Heq.
case: ifP => Hxy; first by apply CompLt.
move/negP: Hxy => Hxy.
apply CompGt.
case/orP: (ord_total x y) => //.
case/orP => //.
by move/eqP.
Qed.

Definition eq_dec (x y  : t) : {x = y}+{x <> y}.
  refine
    (match x == y as exy return (_ = exy -> _) with
     | true => fun H => left _
     | false => fun H => right _
     end (refl_equal _)).
- by move/eqP: H.
- by move/negP/negP/eqP: H.
Defined.

End OrdTypeUsualOrderedType.

Module Type FinType.
Parameter T : finType.
End FinType.

Module Type FinOrdType (Import FT : FinType).
Parameter ordT : rel T.
Parameter irr_ordT : irreflexive ordT.
Parameter trans_ordT : transitive ordT.
Parameter total_ordT : forall x y, x != y -> ordT x y || ordT y x.
End FinOrdType.

Module Type FinUsualOrderedType (FT : FinType) <: UsualOrderedType.
Definition t : Type := FT.T.
Definition eq := @eq t.
Definition eq_equiv := @eq_equivalence t.
Parameter Inline lt : t -> t -> Prop.
Parameter lt_strorder : StrictOrder lt.
Parameter lt_compat : Proper (eq ==> eq ==> iff) lt.
Parameter compare : t -> t -> comparison.
Parameter compare_spec : forall t1 t2, CompSpec eq lt t1 t2 (compare t1 t2).
Parameter eq_dec : forall x y : t, {x = y} + { x <> y }.
End FinUsualOrderedType.

Module FinOrdUsualOrderedType (FT : FinType) (FOT : FinOrdType FT) <: FinUsualOrderedType FT.
  
Module OT.
Definition T : ordType := OrdType FT.T (OrdMixin FOT.irr_ordT FOT.trans_ordT FOT.total_ordT).
End OT.

Module OTUOT := OrdTypeUsualOrderedType OT.

Definition t : Type := FT.T.
Definition eq := @eq t.
Definition eq_equiv := @eq_equivalence t.
Definition lt := OTUOT.lt.
Definition lt_strorder := OTUOT.lt_strorder.
Definition lt_compat := OTUOT.lt_compat.
Definition compare := OTUOT.compare.
Definition compare_spec := OTUOT.compare_spec.
Definition eq_dec := OTUOT.eq_dec.

End FinOrdUsualOrderedType.

Module DFS (Import FT : FinType) (FUOT : FinUsualOrderedType FT) (MS : MSetInterface.S with Module E := FUOT).

Module MSF := Facts MS.

Fixpoint sdfs g n s x :=
  if MS.mem x s then s else
  if n is n'.+1 then foldl (sdfs g n') (MS.add x s) (g x) else s.

Lemma subset_sdfs : forall (g : T -> seq T) n (s : seq T) x ms,
  MS.mem x ms ->
  MS.mem x (foldl (sdfs g n) ms s).
Proof.
move => g n s x ms Hx.
have ->: s = rev (rev s) by rewrite revK.
rewrite foldl_rev.
generalize (rev s) => s'.
move: n s' x ms Hx {s}.
elim => [|n IHn].
- elim => //=.
  move => x s IH y ms Hy.
  by case: ifP => Hm; apply: IH.
- elim => //=.
  move => x s IH y ms Hy.
  case: ifP => Hm; first by apply: IH.
  have ->: g x = rev (rev (g x)) by rewrite revK.
  rewrite foldl_rev.
  apply: IHn.
  apply/MSF.mem_1.
  apply/MSF.add_2.
  apply/MSF.mem_2.
  exact: IH.
Qed.

Lemma dfs_sdfs_in : forall (g : T -> seq T) n (s : seq T) (ms : MS.t) x z,
 (forall y, y \in s = MS.mem y ms) ->
 x \in dfs g n s z = MS.mem x (sdfs g n ms z).
Proof.
move => g.
elim => //=; first by move => s ms x Hy; case: ifP; case: ifP.
move => n IH s ms x z Hy.
case: ifP; case: ifP => //= Hx Hs.
- by apply/idP/idP => Hxy; move/negP: Hx; case; rewrite -Hy.
- by apply/idP/idP => Hxy; move/negP: Hs; case; rewrite Hy.
- suff Hy': forall y, (y \in z :: s) = MS.mem y (MS.add z ms).
    move: Hy'.
    set s' := z :: s.
    set ms' := MS.add z ms.
    set s0 := g z.
    move: s0 s' ms'.
    elim => //=.
    move => z0 s0 IH' s' ms' Hs'.
    by erewrite IH'; eauto.
  move => y.
  rewrite in_cons.
  apply/orP.
  case: ifP => Hm.
  * move/MSF.mem_2: Hm.
    move/MSF.add_3 => Hzy.
    case Hyz: (y == z); first by left.
    right.
    rewrite Hy.
    apply/MSF.mem_1.
    apply Hzy.
    move => Hyz'.
    by move/negP/negP/eqP: Hyz; case.
  * move => Hyz; case: Hyz.
    + move/eqP => Hyz.
      move/negP: Hm.
      case.
      by apply/MSF.mem_1/MSF.add_1.
    + move => Hyz.
      move/negP: Hm.
      case.
      apply/MSF.mem_1/MSF.add_2/MSF.mem_2.
      by rewrite -Hy.
Qed.

Definition srclosure g :=
 foldr (fun x s => sdfs g #|T| s x) MS.empty.

Definition srclosure' g :=
 foldl (sdfs g #|T|) MS.empty.

Lemma rclosure_srclosure : forall g s x,
  x \in rclosure g s = MS.mem x (srclosure g s).
Proof.
move => g.
elim => //=; last by move => x s IH y; apply: dfs_sdfs_in.
move => x.
rewrite in_nil.
apply/idP/idP => //.
move/MSF.mem_2.
by move/MSF.empty_1.
Qed.

Lemma in_foldr_mem : forall g s0 n x,
 x \in foldr (fun x s => dfs g n s x) [::] s0 =
 MS.mem x (foldr (fun x s => sdfs g n s x) MS.empty s0).
Proof.
move => g.
elim => //=; last by move => x s IH n y; erewrite dfs_sdfs_in; eauto.
move => n x.
rewrite in_nil.
case Hm: (MS.mem x MS.empty) => //.
move/MSF.mem_2: Hm.
by move/MSF.empty_1.
Qed.

Lemma srclosure_srclosure' : forall g s x,
 MS.mem x (srclosure g s) = MS.mem x (srclosure' g s).
Proof.
move => g s x.
apply/idP/idP.
- have {2} ->: s = rev (rev s) by rewrite revK.
  rewrite /srclosure /srclosure' foldl_rev.
  rewrite -(in_foldr_mem g s) -(in_foldr_mem g (rev s)) (@closure_eqi _ _ s (rev s)) // => y.
  by move: (has_rev (pred1 y) s); rewrite 2!has_pred1.
- have {1} ->: s = rev (rev s) by rewrite revK.
  rewrite /srclosure' /srclosure foldl_rev.
  rewrite -(in_foldr_mem g s) -(in_foldr_mem g (rev s)) (@closure_eqi _ _ (rev s) s) // => y.
  by move: (has_rev (pred1 y) s); rewrite 2!has_pred1.
Qed.

Lemma rclosure'_srclosure' : forall g s x,
  x \in rclosure' g s = MS.mem x (srclosure' g s).
Proof.
move => g s x.
by rewrite -srclosure_srclosure' -rclosure_srclosure rclosure_rclosure'_i.
Qed.

Definition elts_srclosure g s :=
 MS.elements (srclosure g s).

Definition elts_srclosure' g s :=
 MS.elements (srclosure' g s).

Lemma elements_in_mem : forall s x,
  x \in MS.elements s = MS.mem x s.
Proof.
move => s x.
apply/idP/idP; last first.
- move/MSF.mem_2/MSF.elements_1.
  move/InA_alt => [y [Hx Hy]].
  rewrite Hx; move: Hy.
  set e := MS.elements _.
  elim: e => //=.
  move => z e IH.
  case; first by move =>->; rewrite in_cons; apply: predU1l.
  by rewrite in_cons => Hy; apply predU1r; apply: IH.
- move => Hm.
  apply/MSF.mem_1/MSF.elements_2/InA_alt.
  exists x; split => //; move: Hm.
  set e := MS.elements _.
  elim: e => //.
  move => y e IH.
  rewrite in_cons.
  move/orP; case; first by move/eqP; left.
  move => Hx.
  by right; apply: IH.
Qed.

Lemma elts_srclosureP g (modified : seq T) x :
 reflect
   (exists2 v, v \in modified & connect g v x)
   (x \in elts_srclosure (rgraph g) modified).
Proof.
apply: (iffP idP).
- rewrite elements_in_mem -rclosure_srclosure.
  by move/rclosureP.
- move/rclosureP.
  rewrite rclosure_srclosure.
  by rewrite elements_in_mem.
Qed.

Lemma elts_srclosurePg g (modified : seq T) x :
 reflect
   (exists2 v, v \in modified & connect (grel g) v x)
   (x \in elts_srclosure g modified).
Proof.
apply: (iffP idP).
- rewrite elements_in_mem -rclosure_srclosure.
  by move/rclosurePg.
- move/rclosurePg.
  rewrite rclosure_srclosure.
  by rewrite elements_in_mem.
Qed.

Lemma elts_srclosure'P g (modified : seq T) x :
 reflect
   (exists2 v, v \in modified & connect g v x)
   (x \in elts_srclosure' (rgraph g) modified).
Proof.
apply: (iffP idP).
- rewrite elements_in_mem -rclosure'_srclosure' -rclosure_rclosure'_i.
  by move/rclosureP.
- move/rclosureP.
  rewrite rclosure_srclosure.
  by rewrite srclosure_srclosure' elements_in_mem.
Qed.

Lemma elts_srclosure'Pg g (modified : seq T) x :
  reflect
    (exists2 v, v \in modified & connect (grel g) v x)
    (x \in elts_srclosure' g modified).
Proof.
apply: (iffP idP).
- rewrite elements_in_mem -rclosure'_srclosure' -rclosure_rclosure'_i.
  by move/rclosurePg.
- move/rclosurePg.
  rewrite rclosure_srclosure.
  by rewrite srclosure_srclosure' elements_in_mem.
Qed.

Lemma elts_srclosure_uniq : forall g s,
 uniq (elts_srclosure g s).
Proof.
move => g s.
rewrite /elts_srclosure.
have Hs := MS.elements_spec2w (srclosure g s).
move: Hs.
set e := MS.elements _.
elim: e => //=.
move => x e IH Hn.
inversion Hn; subst.
apply/andP.
split; last by apply: IH.
apply/negP => Hx.
case: H1.
apply/InA_alt.
exists x; split => //.
elim: e Hx {IH Hn H2} => //=.
move => y e IH.
rewrite in_cons.
move/orP; case; first by move/eqP =>->; left.
move => Hx.
by right; apply: IH.
Qed.

Lemma elts_srclosure'_uniq : forall g s,
  uniq (elts_srclosure' g s).
Proof.
move => g s.
rewrite /elts_srclosure' /srclosure'.
have ->: s = rev (rev s) by rewrite revK.
rewrite foldl_rev.
exact: elts_srclosure_uniq.
Qed.

Lemma rclosed_elts_srclosure : forall g s,
  rclosed g (elts_srclosure (rgraph g) s).
Proof.
move => g s.
move => x y Hg.
rewrite 2!elements_in_mem -2!rclosure_srclosure.
exact: rclosed_rclosure.
Qed.

Lemma rclosed_elts_srclosure' : forall g s,
  rclosed g (elts_srclosure' (rgraph g) s).
Proof.
move => g s.
move => x y Hg.
rewrite 2!elements_in_mem -2!rclosure'_srclosure'.
exact: rclosed_rclosure'.
Qed.

End DFS.

Module Type OrdinalFinType <: FinType.
Parameter n : nat.
Definition T : finType := [finType of 'I_n].
End OrdinalFinType.

Module OrdinalFinOrdType (Import OFT : OrdinalFinType) <: FinOrdType OFT.
Definition ordT : rel T := fun x y => ltn x y.
Definition irr_ordT : irreflexive ordT := irr_ltn_nat.
Definition trans_ordT : transitive ordT := trans_ltn_nat.
Definition total_ordT : forall x y, x != y -> ordT x y || ordT y x := semiconn_ltn_nat.
End OrdinalFinOrdType.

(* Instantiation test *)

Module OFT5 <: OrdinalFinType. Definition n := 5. Definition T := [finType of 'I_5]. End OFT5.
Module OFOT5 <: FinOrdType OFT5 := OrdinalFinOrdType OFT5.
Module FUOT5 <: FinUsualOrderedType OFT5 := FinOrdUsualOrderedType OFT5 OFOT5.
Module RBSet5 <: MSetInterface.S := MSetRBT.Make FUOT5.
Module RBDFS5 := DFS OFT5 FUOT5 RBSet5.
