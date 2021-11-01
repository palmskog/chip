From mathcomp.ssreflect Require Import all_ssreflect.
From mathcomp.tarjan Require Import extra acyclic tarjan_rank acyclic_tsorted.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* TODO: prove everything for foldl version *)

Section SeqSet.

Variable V : finType.

Definition enums (s : seq {set V}) := 
 foldr (fun (s0 : {set V}) => cons (enum s0)) [::] s.

Definition enums' (s : seq {set V}) :=
 foldl (fun l (s0 : {set V}) => enum s0 :: l) [::] s.

Lemma enumsP (s : seq {set V}) l :
  reflect
    (exists2 scc, scc \in s & enum scc = l)
    (l \in enums s).
Proof.
apply/(iffP idP).
- rewrite /enums.
  move => Hsc.
  suff Hsuff: exists2 scc, scc \in enum s & enum scc = l.
    move: Hsuff => [scc Hsc'] He.
    move: Hsc'.
    rewrite mem_enum => Hsc'.
    by exists scc.
  move: Hsc.
  elim: s => //=.
  move => s0 l0 IH.
  rewrite in_cons.
  move/orP.
  case.
  * move/eqP =>->.
    exists s0 => //=.
    rewrite mem_enum.
    rewrite in_cons.
    apply/orP.
    by left.
  * move/IH => [scc Hs] He.
    exists scc => //=.
    rewrite mem_enum in_cons.
    apply/orP.
    right.
    by rewrite -mem_enum.
- move => [scc Hscc] He.
  move: He Hscc =><-.
  rewrite /enums /= => Hsc.
  have Hsc': scc \in enum s by rewrite mem_enum.
  move: Hsc'.
  elim: s {Hsc}; first by rewrite mem_enum.
  move => s0 l0 IH.
  rewrite mem_enum in_cons.
  move/orP.
  case.
  * move/eqP =>->.
    rewrite inE.
    by apply/orP; left.
  * rewrite -mem_enum.
    move/IH => Hl.
    by apply/orP; right.
Qed.

Lemma enums_enums'_in s :
  enums s =i enums' s.
Proof.
rewrite /enums /enums'.
have {2}->: s = rev (rev s) by rewrite revK.
rewrite foldl_rev => s0.
apply/enumsP.
case: ifP.
- move/enumsP => [scc Hsc] He.
  exists scc => //.
  move: Hsc.
  by rewrite mem_rev.
- move/enumsP.
  move => He.
  case => x Hx Hex.
  case: He.
  exists x => //.
  by rewrite mem_rev.
Qed.

Lemma enums'P (s : seq {set V}) l :
  reflect
    (exists2 scc, scc \in s & enum scc = l)
    (l \in enums' s).
Proof.
apply/(iffP idP).
- rewrite -enums_enums'_in.
  by move/enumsP.
- move/enumsP.
  by rewrite -enums_enums'_in.
Qed.

Lemma uniq_enums l :
  uniq l ->
  uniq (enums l).
Proof.
elim: l => //=.
move => s l IH.
move/andP => [Hs Hl].
apply/andP.
split; last by apply: IH.
apply/negP => Hen.
move/negP: Hs.
case.
move: Hen.
elim: l {IH Hl} => //=.
move => s0 l IH.
rewrite in_cons.
move/orP.
case.
- move/eqP => Hs.
  suff Hsuff: s = s0.
    rewrite in_cons.
    apply/orP; left.
    by apply/eqP.
  apply/setP.
  move => x.
  by rewrite -mem_enum Hs mem_enum.
- move => He.
  rewrite in_cons.
  apply/orP.
  right.
  exact: IH.
Qed.

Lemma in_uniq_enums l :
  uniq l ->
  forall l0, l0 \in (enums l) -> uniq l0.
Proof.
elim: l => //=.
move => a l IH.
move/andP => [Ha Hl] l0.
rewrite in_cons.
move/orP.
case => //.
- move/eqP =>->.
  exact: enum_uniq.
- move => Hla.
  exact: IH.
Qed.

Lemma uniq_flatten : forall l,
 (forall a, a \in l -> uniq a) ->
 uniq l ->
 {in l &, forall A B : seq V, A != B -> [disjoint A & B]} ->
 uniq (flatten l).
Proof.
elim => //=.
move => a l IH Ha.
move/andP => [Hal Hul] Hd.
rewrite cat_uniq.
apply/and3P.
split.
- apply: Ha.
  by rewrite in_cons; apply/orP; left.
- apply/negP => Hm.
  move/hasP: Hm => [x Hx] /= Ha'.
  move/flattenP: Hx.
  move => [y Hy] Hxy.
  have Hla: a \in a :: l by rewrite in_cons; apply/orP; left.
  have Hly: y \in a :: l by rewrite in_cons; apply/orP; right.
  have Hn: a != y.
    apply/negP => Hn.
    move/eqP: Hn => Hn.
    move: Hn Hal =>->.
    move/negP.
    by case.
  have Hd' := Hd a y Hla Hly Hn.
  move: Hd'.  
  rewrite disjoint_subset.
  move/subsetP => Hd'.
  move/negP: (Hd' _ Ha').
  by case.
- apply: IH => //.
  move => a0 Hl.
  apply: Ha.
  by rewrite in_cons; apply/orP; right.
- move => a' a0 Ha' Ha0 Hneq.
  apply: Hd => //.
  * by rewrite in_cons; apply/orP; right.
  * by rewrite in_cons; apply/orP; right.
Qed.

Variable sc : {set {set V}}.

Hypothesis all_in_cover : forall v : V, v \in cover sc.

Lemma cover_all_in :
  forall v : V, v \in flatten (enums (enum sc)).
Proof.
move => v.
apply/flattenP.
move/bigcupP: (all_in_cover v).
move => [s' Hv] Hs.
exists (enum s'); last by rewrite mem_enum.
apply/enumsP.
exists s' => //.
by rewrite mem_enum.
Qed.

Hypothesis trivIset_sc : trivIset sc.

Lemma in_enums_disjoint :
  forall l l', l \in enums (enum sc) -> l' \in enums (enum sc) ->
    l != l' -> [disjoint l & l'].
Proof.
move/trivIsetP: trivIset_sc => Ht.
move => l l'.
move/enumsP => [s Hs] He.
move/enumsP => [s' Hs'] He' Hl.
move: Hs.
rewrite mem_enum.
move/(Ht s s') => Hts.
move: Hs'.
rewrite mem_enum.
move/Hts.
have Hs: s != s'.
  apply/negP => Hs.
  move/eqP: Hs => Hs.
  move/negP: Hl.
  case.
  rewrite -He -He'.
  by rewrite Hs.
move => Hd.
move/Hd: Hs.
rewrite -He -He' /=.
rewrite 2!disjoint_subset.
move/subsetP => Hs.
apply/subsetP.
move => x.
rewrite mem_enum.
move/Hs.
rewrite /predC /=.
rewrite 2!inE.
by rewrite mem_enum.
Qed.

End SeqSet.
  
Section TarjanSeq.

Variable V : finType.
  
Variable successors : V -> seq V.

Definition tarjans := enums (enum (tarjan successors)).

Definition tarjans' := enums' (enum (tarjan successors)).

Lemma tarjansP sccl :
  reflect
    (exists2 scc, scc \in tarjan successors & enum scc = sccl)
    (sccl \in tarjans).
Proof.
apply/(iffP idP).
- move/enumsP => [scc Hsc] He.
  exists scc => //.
  by rewrite -mem_enum.
- move => [scc Hsc] He.
  apply/enumsP.
  exists scc => //.
  by rewrite mem_enum.
Qed.

End TarjanSeq.

Section TarjanAcyclic.

Variable V : finType.
Variable g : rel V.

Lemma trivIset_tarjan :
  trivIset (tarjan (rgraph g)).
Proof.
rewrite tarjan_correct.
exact: trivIset_sccs.
Qed.

Lemma class_diconnected_tarjan :
  forall c, c \in tarjan (rgraph g) ->
  exists x, forall y, (y \in c) = symconnect g x y.
Proof.
move => c.
rewrite tarjan_correct.
rewrite /sccs /=.
rewrite /equivalence_partition /=.
move/imsetP => [x Hx] Hc.
exists x.
move => y.
rewrite Hc inE.
rewrite andb_idl //.
set g' : rel V := grel (rgraph g).
rewrite -(@eq_symconnect _ g') //.
move => v1 v2.
rewrite /g' /=.
by rewrite mem_enum.
Qed.

Lemma class_diconnected_tarjans :
  forall c, c \in tarjans (rgraph g) ->
  exists x, forall y, (y \in c) = symconnect g x y.
Proof.
move => c.
move/tarjansP => [scc Hsc].
move =><-.
move/class_diconnected_tarjan: Hsc.
move => [x Hy].
exists x.
move => y.
by rewrite mem_enum.
Qed.

Lemma cover_tarjan : cover (tarjan (rgraph g)) = [set: V].
Proof.
rewrite tarjan_correct.
by rewrite cover_sccs.
Qed.

Lemma all_in_cover_tarjan : forall v : V, v \in cover (tarjan (rgraph g)).
Proof.
by move => v; rewrite tarjan_correct cover_sccs.
Qed.

Lemma all_in_flatten_tarjans : forall v : V, v \in flatten (tarjans (rgraph g)).
Proof.
apply: cover_all_in.
exact: all_in_cover_tarjan.
Qed.

Lemma enum_tarjan_non_empty : set0 \notin enum (tarjan (rgraph g)).
Proof.
have Hp := sccs_partition (grel (rgraph g)).
rewrite tarjan_correct.
rewrite /partition in Hp.
move/and3P: Hp.
case => Hc Ht Hs.
by rewrite mem_enum.
Qed.

Lemma uniq_in_tarjans : 
forall a, a \in tarjans (rgraph g) -> uniq a.
Proof.
apply: in_uniq_enums.
exact: enum_uniq.
Qed.

Lemma uniq_flatten_tarjans : uniq (flatten (tarjans (rgraph g))).
Proof.
apply: uniq_flatten.
- move => a Ht.
  exact: uniq_in_tarjans.
- apply: uniq_enums.
  exact: enum_uniq.
- apply: in_enums_disjoint.
  exact: trivIset_tarjan.
Qed.

Definition tarjans_acyclic :=
 sccs_acyclic (fun g => tarjans (rgraph g)) g.

Lemma tarjans_acyclicE : tarjans_acyclic = @acyclic V g.
Proof.
rewrite [LHS]sccs_acyclicE //.
- exact: uniq_flatten_tarjans.
- exact: all_in_flatten_tarjans.
- exact: class_diconnected_tarjans.
Qed.

End TarjanAcyclic.
