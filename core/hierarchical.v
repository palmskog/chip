From mathcomp Require Import all_ssreflect.
From chip Require Import extra connect acyclic closure check change.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Hierarchy.

Variable (A_top : eqType) (A_bot : eqType).

Variable (U' : finType) (V' : finType).

Variable (f'_top : U' -> A_top) (f'_bot : V' -> A_bot).

Variable (P_top : pred U') (P_bot : pred V').

Local Notation U := (sig_finType P_top).

Local Notation V := (sig_finType P_bot).

Variable (g_top : rel U) (g_bot : rel V).

Local Notation g_top_rev := [rel x y | g_top y x].

Local Notation g_bot_rev := [rel x y | g_bot y x].

Variable (f_top : U -> A_top) (f_bot : V -> A_bot).

Variable (checkable : pred V').

Variable (R : eqType).

Variable (check : V' -> R).

Variables (p : U -> {set V}) (p' : U' -> {set V'}).

Hypothesis p_neq : forall (u u' : U), u <> u' -> p u <> p u'.

Hypothesis p'_neq : forall (u u' : U'), u <> u' -> p' u <> p' u'.

Hypothesis p_partition : partition (\bigcup_( u | u \in U ) [set p u]) [set: V].

Hypothesis p'_partition : partition (\bigcup_( u | u \in U' ) [set p' u]) [set: V'].

Hypothesis g_bot_top : forall (v v' : V) (u u' : U),
 u <> u' -> g_bot v v' -> v \in p u -> v' \in p u' -> g_top u u'.

Hypothesis f_top_partition : forall (u : U),
 f_top u = f'_top (val u) -> [set val v | v in p u] = p' (val u).

Hypothesis f_top_bot : forall (u : U),
 f_top u = f'_top (val u) -> forall (v : V), v \in p u -> f_bot v = f'_bot (val v).

Lemma exist_pu_for_v : forall v, exists u, v \in p u.
Proof.
move => v.
have Hp := p_partition.
move/andP: Hp => [Hp Hp'].
rewrite /cover in Hp.
rewrite /cover in Hp.
have Hvi: v \in [set: V] by [].
move/eqP: Hp => Hp.
rewrite -Hp in Hvi.
move/bigcupP: Hvi => [vs Hc] Hvvs.
move/bigcupP: Hc => [u Hu] Huvs.
move/set1P: Huvs => Huvs.
exists u.
by rewrite -Huvs.
Qed.

Lemma exist_list_pu_for_seq_v : forall (vs : seq V),
 exists vus, unzip1 vus = vs /\ forall v u, (v,u) \in vus -> v \in p u.
elim; first by exists [::]; split.
move => v l [vus [Hvu Hp]].
have [u Hu] := exist_pu_for_v v.
exists ((v,u) :: vus).
split; first by rewrite /= Hvu.
move => v0 u0.
rewrite in_cons.
move/orP.
case; first by move/eqP; case =>->->.
by move/Hp.
Qed.

Fixpoint adjundup (u : U) (s : seq U) :=
  if s is x :: s' then
    if u == x then adjundup u s'
    else x :: adjundup x s'
  else [::].

Lemma exist_p'u_for_v : forall v, exists u, v \in p' u.
Proof.
move => v.
have Hp := p'_partition.
move/andP: Hp => [Hp Hp'].
rewrite /cover in Hp.
rewrite /cover in Hp.
have Hvi: v \in [set: V'] by [].
move/eqP: Hp => Hp.
rewrite -Hp in Hvi.
move/bigcupP: Hvi => [vs Hc] Hvvs.
move/bigcupP: Hc => [u Hu] Huvs.
move/set1P: Huvs => Huvs.
exists u.
by rewrite -Huvs.
Qed.

Definition impacted_U : {set U} := impacted g_top^-1 (modifiedV f'_top f_top).

Definition pimpacted_V : {set V} := \bigcup_( u | u \in impacted_U ) (p u).

Lemma connect_rev_v_u : forall x v u u',
  x \in p u ->  
  v \in p u' ->
  connect g_bot_rev v x ->
  connect g_top_rev u' u.
Proof.
move => x v u u' Hx Hv.
move/connect_rev.
rewrite /=.
have ->: connect [rel x0 y | g_bot x0 y] x v = connect g_bot x v by [].
move => Hc.
have ->: g_top_rev = [rel x y | g_top y x] by [].
apply/connect_rev.
move/connectP: Hc => [vs Hvs] Hl.
have [uvs [Huz Hin]] := exist_list_pu_for_seq_v vs.
move: Hvs Hl.
rewrite -Huz {Huz vs} => Hp Hl.
apply/connectP.
exists (adjundup u (unzip2 uvs)).
- clear Hl Hv u' v.
  elim: uvs u x Hx Hin Hp => //.
  case => v1 u1 uvs IH u x Hx.
  rewrite [unzip1 _]/=.
  rewrite [unzip2 _]/=.
  move => Hin.
  rewrite /=.
  move/andP => [Hg Hp].
  case: ifP.
  * move/eqP => Hu.
    move: Hu Hin =><- {u1}.
    move => Hin.
    move: Hp.
    apply: IH.
    + apply: Hin.
      by apply/orP; left.
    + move => v u0 Hin'.
      apply: Hin.
      apply/orP.
      by right.
  * rewrite /=.
    move/negP/negP/eqP => Hu.
    apply/andP.
    have Hv1: v1 \in p u1.
      apply: Hin.
      apply/orP.
      by left.    
    split; first by eapply g_bot_top; eauto.
    have Hin': forall (v0 : V) (u0 : U), (v0, u0) \in uvs -> v0 \in p u0.
      move => v0 u0 Hin'.
      apply: Hin.
      rewrite inE.
      apply/orP.
      by right.
    exact: IH _ _ Hv1 Hin' Hp.
- elim: uvs u u' x v Hx Hv Hin Hp Hl => //.
  * move => u u' x v Hx Hv.
    rewrite [unzip1 _]/=.
    rewrite [unzip2 _]/=.
    rewrite [adjundup _ _]/=.
    rewrite 2![last _ _]/=.
    move => Hin Ht Hvx.
    move: Hvx Hv =>-> {v Ht Hin}.
    move => Hp.
    case Hu: (u' == u); first by move/eqP: Hu.
    move/negP/negP/eqP: Hu => Hu.
    have Hneq := p_neq Hu.
    have Hpp := p_partition.
    move/andP: Hpp => [Hc Hpp].
    move/andP: Hpp => [Htr H0].
    move/trivIsetP: Htr => Htr.
    have Hpu: p u \in \bigcup_(u1 in U) [set p u1].
      apply/bigcupP.
      exists u; first by [].
      by rewrite in_set1.
    have Hpu': p u' \in \bigcup_(u1 in U) [set p u1].
      apply/bigcupP.
      exists u'; first by [].
      by rewrite in_set1.
    have Hneq': p u != p u'.
      apply/negP/negP/eqP => Hpp.
      by case: Hneq.
    have Hpp := Htr _ _ Hpu Hpu' Hneq'.
    move/setDidPl: Hpp => Hpp.
    move: Hx.
    rewrite -Hpp.
    move/setDP => [Hx Hx'].
    move/negP: Hx'.
    by case.
  * case => v1 u1 uvs IH u u' x v Hx Hv.
    rewrite [unzip1 _]/=.
    rewrite [unzip2 _]/=.
    rewrite [adjundup _ _]/=.
    move => Hin.
    move/andP => [Hg Hp].
    move: Hp.
    rewrite -/(path _ _) => Hp.
    rewrite [last _ _]/=.
    move => Hl.
    case: ifP => Hu.
    + move/eqP: Hu => Hu.
      move: Hx.      
      rewrite Hu {Hu u} => Hu.
      have Hv1: v1 \in p u1.
        apply: Hin.
        rewrite inE.
        apply/orP.
        by left.
      have Hin': forall (v0 : V) (u0 : U), (v0, u0) \in uvs -> v0 \in p u0.
        move => v0 u0 Hin'.
        apply: Hin.
        rewrite inE.
        apply/orP.
        by right.
      exact: IH u1 u' v1 v Hv1 Hv Hin' Hp Hl.
    + rewrite /=.
      move/negP/negP/eqP: Hu => Hu.
      have Hv1: v1 \in p u1.
        apply: Hin.
        rewrite inE.
        apply/orP.
        by left.
      have Hin': forall (v0 : V) (u0 : U), (v0, u0) \in uvs -> v0 \in p u0.
        move => v0 u0 Hin'.
        apply: Hin.
        rewrite inE.
        apply/orP.
        by right.
      exact: IH u1 u' v1 v Hv1 Hv Hin' Hp Hl.
Qed.

Lemma neq_connect_in_pimpacted_V : forall x v,
 f_bot v <> f'_bot (val v) -> connect g_bot_rev v x -> x \in pimpacted_V.
Proof.
move => x v Hv Hc.
apply/bigcupP.
have [u Hu] := exist_pu_for_v x.
exists u; last by [].
have Hp := p_partition.
move/andP: Hp => [Hcv Hp'].
move/eqP: Hcv => Hcv.
apply/impactedVP.
have Hvi: v \in [set: V] by [].
rewrite -Hcv in Hvi.
move/bigcupP: Hvi => [xs Hc'] Hvvs.
move/bigcupP: Hc' => [u' Hu'] Huvs.
move/set1P: Huvs => Huvs.
move: Huvs Hvvs =>->.
move => Hvx.
exists u'.
- rewrite inE.
  apply/negP.
  move => Hf.
  move/eqP: Hf.
  move/f_top_bot => Hf.
  case: Hv.
  exact: Hf.
- move: Hc.
  exact: connect_rev_v_u.
Qed.

Lemma impactedV_in_pimpacted_V :
  forall x, x \in impacted g_bot^-1 (modifiedV f'_bot f_bot) ->
       x \in pimpacted_V.
Proof.
move => x.
move/impactedVP.
case => v Hm Hc.
move/not_modifiedP: Hm.
move => Hf.
move/negP/eqP: Hf => Hf.
move: Hf Hc.
exact: neq_connect_in_pimpacted_V.
Qed.

Definition impacted_U' : {set U'} := impactedV' f'_top f_top g_top.

Definition pimpacted_V' : {set V'} := \bigcup_( u | u \in impacted_U' ) (p' u).

Lemma pimpacted_V'_fresh :
  forall v, v \in freshV' P_bot -> v \in pimpacted_V'.
Proof.
move => v'.
move/freshV'P => Hv.
apply/bigcupP.
have [u' Hu] := exist_p'u_for_v v'.
exists u'; last by [].
case Hfr: (u' \in freshV' P_top).
- move/negP/negP: Hfr => Hfr.
  apply/impactedV'P.
  right.
  split => //.
  apply/negP.
  move => Hu'.
  move/imsetP: Hu' => [u Hi] Hu'.
  move/freshV'P: Hfr.
  move => Hvu.
  have Hvu' := Hvu u.
  case/negP: Hvu'.
  by apply/eqP.
- move/negP/negP: Hfr => Hfr.
  apply/impactedV'P.
  left.
  split => //.
  move/negP: Hfr.
  rewrite -sub_freshV'.  
  move/negP/negPn.
  have H_sp := (insubP [subType of U] u').
  destruct H_sp; last by [].
  move => Hs.
  apply/imsetP.
  exists u; last by [].
  apply/impactedVP.
  exists u; last by [].
  apply/not_modifiedP.
  move/eqP.
  move/f_top_partition => Hvs.
  rewrite e in Hvs.
  move: Hu.
  rewrite -Hvs.
  move/imsetP => [v Hi] Hv'.
  have Hvv' := Hv v.
  move/negP: Hvv'.
  case.
  by apply/eqP.
Qed.

Lemma pimpacted_V'_impactedVV' :
  forall v, v \in impactedVV' g_bot (modifiedV f'_bot f_bot) ->
  v \in pimpacted_V'.
Proof.
move => v'.
move/imsetP => [v Hi] Hv.
have Hi' := impactedV_in_pimpacted_V Hi.
move/bigcupP: Hi' => [u Hu] Huv.
apply/bigcupP.
have [u' Hu'] := exist_p'u_for_v v'.
exists u'; last by [].
case Hfr: (u' \in freshV' P_top).
- move/negP/negP: Hfr => Hfr.
  apply/impactedV'P.
  right; split => //.
  apply/negP => Hui.
  move/freshV'P: Hfr => Hfr.
  move/imsetP: Hui => [u'' Hu''] Hvu.
  have Hfr' := Hfr u''.
  move/negP: Hfr'.
  case.
  by apply/eqP.
- move/negP/negP: Hfr.
  move/negP.
  rewrite -sub_freshV'.
  move/negP/negPn.
  have H_sp := (insubP [subType of U] u').
  destruct H_sp; last by [].
  move => Hs.
  case Hu0: (u0 == u).
  * move: e.
    move/eqP: Hu0 =>->.    
    move => Hvu.
    rewrite /impacted_U' /impactedV'.
    apply/setUP.
    left.
    apply/imsetP.
    by exists u.
  * move/negP/negP/eqP: Hu0 => Hu0.
    case Hf: (f_top u0 == f'_top (val u0)).
    + move/eqP: Hf.
      move/f_top_partition => Hst.
      move: Hst.
      rewrite e.
      have H_neq: val u <> u'.
        rewrite -e => Huu.        
        apply val_inj in Huu.
        by rewrite Huu in Hu0.
      move => Hp.
      rewrite -Hp in Hu'.
      move/imsetP: Hu' => [x Hvp] Hvx.
      rewrite Hvx in Hv.
      apply val_inj in Hv.
      rewrite Hv in Hvp.
      have Hpp := p_partition.
      move/andP: Hpp => [Hpp Hpp'].
      move/andP: Hpp' => [Hpp' Hpp''].
      move/trivIsetP: Hpp'.
      have Hpu: p u \in \bigcup_(u1 in U) [set p u1].
        apply/bigcupP.
        exists u; first by [].
        by rewrite in_set1.
      have Hpu0: p u0 \in \bigcup_(u1 in U) [set p u1].
        apply/bigcupP.
        exists u0; first by [].
        by rewrite in_set1.
      move => Hpp'.
      have H_p := Hpp' _ _ Hpu Hpu0.
      case Hpe: (p u == p u0).
        move/eqP: Hpe => Hpe.
        apply sym_eq in Hpe.
        contradict Hpe.
        exact: p_neq.
      move/negP/negP: Hpe.
      move/H_p.
      move/setDidPl => H_pp.
      rewrite -H_pp /= in Huv.
      move/setDP: Huv => [Hvpp Hvvp].
      move/negP: Hvvp.
      by case.
    + move/negP/negP/eqP: Hf => Hf.
      rewrite /impacted_U'.
      apply/setUP.
      left.
      apply/imsetP.
      exists u0; last by [].
      apply/impactedVP.
      exists u0; last by [].
      apply/not_modifiedP.
      by apply/negP/eqP.
Qed.

Lemma pimpacted_V'_impactedV' :
  forall v, v \in impactedV' f'_bot f_bot g_bot -> v \in pimpacted_V'.
Proof.
move => v.
move/impactedV'P.
case; move => [Ha Hb].
- exact: pimpacted_V'_impactedVV'.
- exact: pimpacted_V'_fresh.
Qed.

Definition checkable_pimpacted_V' :=
 [set v in pimpacted_V' | checkable v].

Definition checkable_pimpacted_fresh : seq V' :=
 enum checkable_pimpacted_V'.

Definition check_pimpacted_V'_cert :=
 [seq (v, check v) | v <- checkable_pimpacted_fresh].

Lemma check_pimpacted_V'_certP v r :
  reflect
    (checkable v /\ check v == r /\ v \in pimpacted_V')
    ((v,r) \in check_pimpacted_V'_cert).
Proof.
apply: (iffP idP).
- move/mapP => [v' Hv'].
  move: Hv'.
  rewrite mem_enum in_set.
  move/andP => [Hp Hc].
  by case =>->->.
- move => [Hc [Hcr Hv]].
  move/eqP: Hcr =><-.
  apply/mapP.
  exists v; last by [].
  rewrite mem_enum in_set.
  by apply/andP; split.
Qed.

Lemma check_pimpacted_V'_cert_uniq :
  uniq [seq vr.1 | vr <- check_pimpacted_V'_cert].
Proof.
rewrite map_inj_in_uniq.
- rewrite map_inj_uniq; first by rewrite enum_uniq.
  by move => x y; case.
- case => v1 r1.
  case => v2 r2.
  move => H1 H2 /= Heq.
  move: Heq H1 H2 =>-<-.
  move/mapP => [v1' Hv1' Hc1].
  rewrite mem_enum in Hv1'.
  case: Hc1 =><- Hr1.
  move/mapP => [v2' Hv2' Hc2].
  rewrite mem_enum in Hv2'.
  case: Hc2 =><- Hr2.
  by rewrite Hr1 Hr2.
Qed.

End Hierarchy.
