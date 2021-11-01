From mathcomp.ssreflect Require Import all_ssreflect.
From mathcomp.tarjan Require Import extra acyclic.
From chip Require Import closure check.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma uniq_prod_eq : 
 forall (T1 T2 : eqType) (s : seq (T1 * T2)) (x : T1) (y z : T2),
  uniq [seq xy.1 | xy <- s] -> (x, y) \in s -> (x, z) \in s ->
  y = z.
Proof.
move => T1 T2.
elim => //=.
case => x y s IH /= x0 y0 z.
move/andP => [Hx Hu].
rewrite 2!in_cons.
move/orP; case => Hx0; move/orP; case => Hy0.
- move/eqP: Hx0; case.
  move/eqP: Hy0; case.
  by move =>->->.
- move/eqP: Hx0 Hy0; case.
  move =>->-> Hx'.
  move/negP: Hx.
  case.
  apply/mapP.
  by exists (x, z).
- move/eqP: Hy0 Hx0; case.
  move =>->-> Hx'.
  move/negP: Hx.
  case.
  apply/mapP.
  by exists (x, y0).
- move: Hx0 Hy0.
  exact: IH.
Qed.

Section Changed.

(* artifact *)
Variable A : eqType.

(* paths *)
Variable V' : finType.

Variable P : pred V'.

Local Notation V := (sig_finType P).

Variable f' : V' -> A.

Variable f : V -> A.

Variable g' : rel V'.

Local Notation g'rev := [rel x y | g' y x].

Variable g : rel V.

Local Notation grev := [rel x y | g y x].

Variable checkable' : pred V'.

Variable checkable : pred V.

Variable R : eqType.

Variable check' : V' -> R.

Variable check : V -> R.

Definition insub_g (x y : V') :=
match insub x, insub y with
| Some x', Some y' => g x' y'
| _, _ => false
end.

Local Notation gV' := [rel x y : V' | insub_g x y].

Local Notation gV'rev := [rel x y | gV' y x].

Lemma ginsubexP (x y : V') :
  reflect (exists x' y' : V, val x' = x /\ val y' = y /\ g x' y') (gV' x y).
Proof.
apply: (iffP idP).
- rewrite /gV' /=.
  rewrite /insub_g.
  have H_sp := (insubP [subType of V] x).
  destruct H_sp.
  * rewrite insubT //.
    have H_sp := (insubP [subType of V] y).
    destruct H_sp.
    + rewrite insubT.
      by exists (Sub x i), (Sub y i0).
    + by rewrite insubN.
  * by rewrite insubN.
- case => x'; case => y'.
  move => [Hx [Hy Hg]].
  rewrite /gV' /=.
  rewrite /insub_g.
  case: x' Hx Hg => /= x0 Px0 -<-.
  case: y' Hy => /= y0 Py0 -<-.
  by rewrite (insubT _ Px0) (insubT _ Py0).
Qed.

Lemma grevinsubexP (x y : V') :
  reflect (exists x' y' : V, val x' = x /\ val y' = y /\ grev x' y') (gV'rev x y).
Proof.
apply: (iffP idP).
- rewrite /= => Hs.
  move/ginsubexP: Hs.
  move=> [y' [x' [Hx [Hy Hxy]]]].
  by exists x', y'.
- rewrite /=.
  move => [y' [x' [Hy [Hx Hxy]]]].
  apply/ginsubexP.
  by exists x', y'.
Qed.

Lemma ginsubP x y :
  reflect (g x y) (gV' (val x) (val y)).
Proof.
apply: (iffP idP).
- move/ginsubexP.
  move => [x' [y' [Hx [Hy Hxy]]]].
  move/val_inj: Hx =>-<-.
  by move/val_inj: Hy =>-<-.
- move => Hg.
  apply/ginsubexP.
  by exists x, y.
Qed.

Lemma ginsub_eq x y :
  g x y = gV' (val x) (val y).
Proof.
by apply/idP/ginsubP.
Qed.

(* Assumption: dependencies are the same if artifact is the same *)
Hypothesis f_equal_g :
  forall v, f v = f' (val v) -> forall v', gV' (val v) v' = g' (val v) v'.

(* Assumption: checknability is the same if artifact is the same *)
Hypothesis checkable_V_V' :
  forall v, f v = f' (val v) -> checkable v = checkable' (val v).

(*
Assumption:
if the dependency (sub)graph rooted in a checkable vertex
is well-founded and unchanged, then the outcome of checkning
the vertex (in the new graph) is the same as the old outcome
 *)
Hypothesis check_V_V' :
  forall v, checkable v -> checkable' (val v) ->
  (forall v', connect gV' (val v) v' = connect g' (val v) v') ->
  (forall v', connect gV' (val v) (val v') -> f v' = f' (val v')) ->
  check v = check' (val v).

Variable V_result_cert : seq (V * R).

Hypothesis V_result_certP :
  forall v r, reflect (checkable v /\ check v = r) ((v,r) \in V_result_cert).

Hypothesis V_result_cert_uniq : uniq [seq vr.1 | vr <- V_result_cert].

Lemma V_result_cert_complete :
  forall v r, checkable v -> check v == r -> (v,r) \in V_result_cert.
Proof.
move => v r Hc.
move/eqP => Hr.
by apply/V_result_certP.
Qed.

Lemma V_result_cert_sound :
  forall v r, (v,r) \in V_result_cert -> checkable v /\ check v == r.
Proof.
move => v r.
move/V_result_certP => [Hc Hr].
by move/eqP: Hr => Hr.
Qed.

Definition V'_result_filter_cert :=
 [seq (val vr.1, vr.2) | vr <- V_result_cert & val vr.1 \notin impactedVV' g (modifiedV f' f)].

Lemma V_result_filter_cert_checkable' :
  forall (v : V') (r : R), (v,r) \in V'_result_filter_cert -> checkable' v.
Proof.
move => v r.
move/mapP.
move => [[v' r'] Hv'].
case.
move =>->.
move => Hb; move: Hv'.
rewrite -Hb {Hb}.
rewrite mem_filter /=.
move/andP => [Hr Hin].
have Hi': (val v' \notin impactedVV' g (modifiedV f' f)).
  apply/negP.
  move => Hv.
  move/negP: Hr.
  by case.
move/imsetP: Hi'.
move => Hvb.
have Hv': v' \notin impacted g^-1 (modifiedV f' f).
  apply/negP.
  move => Hv'.
  case: Hvb.
  by exists v'.
move/impactedVP: Hv'.
move => Hm.
move/V_result_certP: Hin.
move => [Hvc Hc].
case Hf: (f v' == f' (val v')).
  move/eqP: Hf.
  by move/checkable_V_V'=>-<-.
move/negP/negP: Hf => Hf.
case: Hm.
exists v'; first by rewrite in_set.
apply/connectP.
by exists [::].
Qed.

Definition check_all_cert :=
  check_impactedV'_cert f' f g checkable' check' ++ V'_result_filter_cert.

Lemma check_all_cert_cases :
  forall v r, (v, r) \in check_all_cert ->
 ((v, r) \in check_impactedV'_cert f' f g checkable' check' /\ (v, r) \notin V'_result_filter_cert) \/
 ((v, r) \in V'_result_filter_cert /\ (v,r) \notin check_impactedV'_cert f' f g checkable' check').
Proof.
move => v b.
rewrite mem_cat.
move/orP.
case => Hi.
- left; split => //.
  move/check_impactedV'_certP: Hi.
  move => [Hc [Hv Hi]].
  apply/negP => Hp.
  move: Hp.
  move/mapP.
  case => [[v' b'] Hb].
  rewrite /=.
  case.
  move => Hv' Hb'.
  subst.
  move: Hb.
  rewrite mem_filter /=.
  move/andP => [Hp Hp'].
  move/negP: Hp.
  case.
  move/impactedV'P: Hi.
  case; move => [Hi Hi'] //.
  move/freshV'P: Hi => Hi.
  have Hv' := Hi v'.
  move/negP: Hv'.
  case.
  by apply/eqP.
- right; split => //.
  apply/negP.
  move => Hm.
  move/check_impactedV'_certP: Hm.
  move/mapP: Hi.
  move => [[v' b'] Hb] /=.
  case.
  move => Hv' Hb'.
  subst.
  move: Hb.
  rewrite mem_filter /=.
  move/andP => [Hb Hc].
  move => [Hc1 [Hc2 Hi2]].
  move/negP: Hb.
  case.
  move/impactedV'P: Hi2.
  case; move => [Hi Hi'] //.
  move/freshV'P: Hi => Hi.
  have Hv' := Hi v'.
  move/negP: Hv'.
  case.
  by apply/eqP.
Qed.

Definition check_all_cert_V' :=
 [seq vr.1 | vr <- check_all_cert].

Lemma check_all_cert_V'_uniq : uniq check_all_cert_V'.
Proof.
rewrite map_inj_in_uniq.
- rewrite cat_uniq.
  apply/andP.
  split; last (apply/andP; split).
  * have Hu := check_impactedV'_cert_uniq f' f g checkable' check'.
    move: Hu.
    exact: map_uniq.
  * apply/negP.
    move/hasP => [vr Hvr].
    move/mapP: Hvr => [vr' Hvr'].
    case: vr' Hvr' => v' r'.
    rewrite mem_filter.
    case: vr => /= v r.
    move/andP => [Hv Hvr].
    case => Hv'; move =>-> {r}.
    move/mapP => [v0 Hv0].
    case => Hvv0 Hr'.
    rewrite mem_enum -Hvv0 in Hv0.
    move/negP: Hv.
    case.
    rewrite in_set in Hv0.
    move/andP: Hv0 => [Hvi Hvc].
    rewrite in_set in Hvi.
    move/orP: Hvi.
    case; first by rewrite Hv'.
    move/freshV'P => Hvv.
    have Hvv' := Hvv v'.
    move/negP: Hvv'.
    case.
    by rewrite Hv'.
  * have Hm := map_uniq V_result_cert_uniq.
    rewrite map_inj_in_uniq; first by rewrite filter_uniq.
    case => v1 r1.
    case => v2 r2.
    rewrite /= => Hv1 Hv2.
    case.
    by move/val_inj =><-<-.
- case => v1 r1.
  case => v2 r2.
  rewrite /= 2!mem_cat.
  move/orP.
  case => Hv1; move/orP.
  * case => Hv2 Hv.
    + move: Hv Hv1 Hv2 =><-.
      move/mapP => [v1' Hv1' Hc1].
      rewrite mem_enum in Hv1'.
      case: Hc1 =><- Hr1.
      move/mapP => [v2' Hv2' Hc2].
      rewrite mem_enum in Hv2'.
      case: Hc2 =><- Hr2.
      by rewrite Hr1 Hr2.
    + move: Hv Hv1 Hv2 =><-.
      move/mapP => [v1' Hv1' Hc1].
      case: Hc1 Hv1' =><-.
      rewrite mem_enum => Hc.
      rewrite in_set.
      move/andP => [Hi H'c].
      move/mapP => [v' Hv' Heq].
      case: v' Hv' Heq => v2' r2'.
      rewrite mem_filter.
      move/andP => [Hv2' HV].
      case => Hv1 Hr2.
      rewrite /= in Hv2'.
      move/negP: Hv2'.
      case.
      rewrite -Hv1.
      rewrite in_set in Hi.
      move/orP: Hi.
      case => //.
      move/freshV'P => Hv.
      have Hv' := Hv v2'.
      move/negP: Hv'.
      case.
      apply/eqP.
      by rewrite Hv1.
  * case => Hv2 Hv.
    + move: Hv Hv1 Hv2.
      move =><-.
      move/mapP => [v1' Hv1' Hc1].
      case: v1' Hc1 Hv1' => v1' r1'.
      case =>->->.
      rewrite mem_filter.
      move/andP => [Hi H'c].
      move/mapP => [v' Hv' Heq].
      case: Heq Hv'.
      rewrite mem_enum.
      move =><-->.
      move => Hc.
      move/negP: Hi.
      case.
      rewrite in_set in Hc.
      move/andP: Hc => [Hi Hc].
      rewrite in_set in Hi.
      move/orP: Hi.
      case => //.
      move/freshV'P => Hv'.
      have Hv'' := Hv' v1'.
      move/negP: Hv''.
      by case.
    + move: Hv1 Hv2.
      move/mapP.
      case; case => v1' r1'.
      rewrite mem_filter.
      move/andP => [Hi Hv'].
      case.
      move => H_eq_v H_eq_r.
      move/mapP.
      case; case => v2' r2'.
      rewrite mem_filter.
      move/andP => [Hi' Hv''].
      case => H_eq_v' H_eq_r'.
      rewrite Hv in H_eq_v, H_eq_v'.
      rewrite H_eq_v in H_eq_v'.
      apply val_inj in H_eq_v'.
      rewrite -H_eq_v' in Hv''.
      rewrite Hv H_eq_r H_eq_r'.
      have Hu := uniq_prod_eq V_result_cert_uniq Hv' Hv''.
      by rewrite -Hu.
Qed.

Lemma check_all_cert_complete :
  forall (v : V'), checkable' v -> v \in check_all_cert_V'.
Proof.
move => v Hc.
have H_sp := (insubP [subType of V] v).
destruct H_sp.
- (* 1. V'_result_filter_cert 2. impactedVV' *)
  have Hv: v \notin freshV' P.
    apply/negP.
    move => Hv.
    move/freshV'P: Hv => Hv.
    move/negP: (Hv u) => Hv'.
    case: Hv'.
    by apply/eqP.
  apply/mapP.
  (* outline:
     - either in filtered or impacted
     - if in filtered, take check u
     - if in impacted, take check' v
  *)
  case Hv': (v \in impactedV' f' f g).
  - have Hv'': v \in impactedV' f' f g by [].
    move {Hv'}.
    exists (v, check' v); last by [].
    rewrite mem_cat.
    apply/orP.
    left.
    apply/check_impactedV'_certP.
    by split.
  - have Hv'': v \notin impactedV' f' f g by apply/negP; rewrite Hv'.
    move {Hv'}.
    exists (v, check u); last by [].
    rewrite mem_cat.
    apply/orP.
    right.
    apply/mapP.
    exists (u, check u); last by rewrite /= e.
    rewrite mem_filter.
    apply/andP.
    rewrite /= in e.
    rewrite /=.
    split.
    * move/impactedV'P: Hv'' => Hv''.
      apply/negP.
      move => Hu.
      case: Hv''.
      left.
      split => //.
      by rewrite -e.
    * apply/V_result_certP.
      split => //.
      suff H_suff: f u = f' (val u) by rewrite checkable_V_V' //= e.
      apply/eqP.
      apply/not_modifiedP.
      apply/negP.
      move => Hu.
      move/negP: Hv'' => Hv''.
      case: Hv''.
      apply/impactedV'P.
      left.
      split => //.
      apply/imsetP.
      exists u; last by [].
      apply/impactedVP.
      by exists u.
- (*3. fresh *)
  have Hv: v \in freshV' P.
    rewrite -sub_freshV'.
    move/negP: i => Hp.
    apply/negP => Hs.
    case: Hp.
    have H_sp := (insubP [subType of V] v).
    move: Hs.
    by destruct H_sp.
  apply/mapP.
  exists (v, check' v) => //.
  rewrite mem_cat.
  apply/orP.
  left.
  apply/check_impactedV'_certP.
  split => //.
  split => //.
  apply/impactedV'P.
  right.
  split => //.
  apply/negP.
  by move/impactedVV'_freshV'/negP.
Qed.

Lemma connect_gV'_rev u :
  (forall v : V, connect grev v u -> forall v', gV' (val v) v' = g' (val v) v') ->
  (forall v : V, connect grev v u -> f v == f' (val v)) ->
  forall v', connect gV' (val u) v' = connect g' (val u) v'.
Proof.
move => Hv.
have Hv': forall v : V, connect g u v -> forall v', gV' (val v) v' = g' (val v) v'.
  move => v' Hc.
  apply: Hv.
  by rewrite connect_rev.
move {Hv}.
move => Hvf.
have Hvf': forall v' : V, connect g u v' -> f v' == f' (val v').
  move => v' Hc.
  apply: Hvf.
  by rewrite connect_rev.
move {Hvf}.
move => v'.
have H_eq: f u = f' (val u).
  apply/eqP.
  apply: Hvf'.
  apply/connectP.
  by exists [::].
apply/connectP.
case: ifP.
- case/connectP => p Hp Hl.
  have H_eq' := f_equal_g H_eq.
  exists p; last by [].
  clear Hl H_eq.
  elim: p u Hp Hv' Hvf' H_eq' => //=.
  move => v0 p IH u.
  move/andP => [Hg Hp] Hc Hc' Hg'.
  apply/andP.
  rewrite -Hg' in Hg.
  split.
  * move/ginsubexP: Hg => [x [y [Hx [Hy Hxy]]]].
    rewrite -Hy.
    rewrite ginsub_eq in Hxy.
    by rewrite /gV' /= Hx in Hxy.
  * move/ginsubexP: Hg => [x [y [Hx [Hy Hxy]]]].
    rewrite -Hy.
    apply: IH => //; first by rewrite Hy.
    + apply val_inj in Hx.
      rewrite Hx in Hxy.
      move => v1 Hc1.
      apply: Hc.
      move/connectP: Hc1 => [p' Hp'] Hl.
      apply/connectP.
      exists (y :: p'); last by [].
      exact/andP.
    + apply val_inj in Hx.
      rewrite Hx in Hxy.
      move => v1 Hc1.
      apply: Hc'.
      move/connectP: Hc1 => [p' Hp'] Hl.
      apply/connectP.
      exists (y :: p'); last by [].
      exact/andP.
    + apply val_inj in Hx.
      rewrite Hx in Hxy.
      apply f_equal_g.
      apply/eqP.
      apply: Hc'.
      apply/connectP.
      exists [:: y]; last by [].
      exact/andP.
- move/connectP.
  move => Hex Hex'.
  case: Hex.
  case: Hex' => p Hp Hl.
  have H_eq' := f_equal_g H_eq.
  exists p; last by [].
  clear Hl H_eq.
  elim: p u Hp Hv' Hvf' H_eq' => //=.
  move => v0 p IH u.
  move/andP => [Hg Hp] Hc Hc' Hg'.
  apply/andP.
  move/ginsubexP: Hg => [x [y [Hx [Hy Hxy]]]].
  split.
  - rewrite -Hg' -Hy.
    apply/ginsubP.
    by move/val_inj: Hx =><-.
  - rewrite -Hy.
    rewrite -Hy in Hp.
    apply: IH => //.
    * move => v1 Hc1.
      apply: Hc.
      move/val_inj: Hx =><-.
      move/connectP: Hc1 => [p' Hp'] Hl.
      apply/connectP.
      exists (y :: p'); last by [].
      exact/andP.
    * move => v1 Hc1.
      apply: Hc'.
      move/val_inj: Hx =><-.
      move/connectP: Hc1 => [p' Hp'] Hl.
      apply/connectP.
      exists (y :: p'); last by [].
      exact/andP.
    * apply: Hc.
      move/val_inj: Hx =><-.
      apply/connectP.
      exists [:: y]; last by [].
      exact/andP.
Qed.

Lemma connect_f_f'_eq u v0 : 
  (forall v' : V, connect grev v' u -> f v' == f' (val v')) ->
  connect gV' (val u) (val v0) ->
  f v0 = f' (val v0).
Proof.
move => Hgc Hc.
apply/eqP.
apply: Hgc.
rewrite connect_rev.
move: Hc.
move/connectP => [p Hp] Hl.
apply/connectP.
exists (foldr (fun x (p' : seq V) => if insub x is Some x' then x' :: p' else p') [::] p).
- rewrite /=.
  elim: p u v0 Hp Hl => //=.
  move => v p IH u v0.
  move/andP => [Hi Hp] Hl.
  move: Hi.
  rewrite /insub_g.
  have H_sp := (insubP [subType of V] (sval u)).
  move: H_sp.
  case => //.
  move => u0 HPu.  
  move/val_inj =>-> {u0}.
  have H_sp := (insubP [subType of V] v).
  move: H_sp.
  case => //.
  move => u0 HPv Heq Hg.
  rewrite /=.
  apply/andP.
  split => //.
  rewrite -Heq in Hp, Hl.
  by apply: IH; eauto.
- rewrite /=.
  elim: p u v0 Hp Hl => //=; first by move => u v0 Hl; apply val_inj.
  move => v p IH u v0.
  move/andP => [Hi Hp] Hl.
  move: Hi.
  rewrite /insub_g.
  have H_sp := (insubP [subType of V] (sval u)).
  move: H_sp.
  case => //.
  move => u0 HPu.  
  move/val_inj =>-> {u0}.
  have H_sp := (insubP [subType of V] v).
  move: H_sp.
  case => //.
  move => u0 HPv Heq Hg.
  rewrite /=.
  by apply IH; rewrite Heq.
Qed.

Lemma check_all_cert_sound :
  forall (v : V') (r : R), (v,r) \in check_all_cert ->
  checkable' v /\ check' v = r.
Proof.
move => v r.
move/check_all_cert_cases.
case.
- (* impacted case *)
  move => [Hi Hr].
  move/check_impactedV'_cert_check: Hi => [Hi [Hi' Hi'']].
  by move/eqP: Hi'.
- (* unimpacted case *)
  move => [Hi Hr].
  have Hc: checkable' v.
    move: Hi.
    exact: V_result_filter_cert_checkable'.
  split => //. 
  move/mapP: Hi.
  case; case => u b'.
  move => Hu.
  case => Hu'.
  move => Hb.
  move: Hb Hu=><- {b'}.
  rewrite mem_filter.
  move/andP.
  rewrite /=.
  move => [Hi Hu].
  have Hv: v \notin freshV' P.
    apply/negP.
    move => Hv.
    move/freshV'P: Hv => Hv.
    move/negP: (Hv u) => Hv'.
    case: Hv'.
    by apply/eqP.  
  move/V_result_certP: Hu.
  move => [Hca Hch].
  have Him' := Hi.
  move: Him'.
  move/imsetP.
  move => Hx.
  have Him': u \notin impacted g^-1 (modifiedV f' f).
    apply/negP => Him'.
    case: Hx.
    by exists u.
  have Him'' := Him'.
  move/impactedVP: Him''.
  move => Hx'.
  have Hum: u \notin modifiedV f' f.
    apply/negP.
    move => Hu.
    case: Hx'.
    exists u; first by [].
    apply/connectP.
    by exists [::].
  have Hall: forall v', connect grev v' u -> v' \notin modifiedV f' f.
    move => v' Hc'.
    apply/negP => Hv'.
    case: Hx'.
    by exists v'.
  move: Hall {Hx' Hi Hx} => Hall.
  have Hu'': f u == f' (val u) by apply/not_modifiedP.
  have Hall': forall v', connect grev v' u -> f v' == f' (val v').
    move => v' Hc'.
    apply/not_modifiedP.
    by apply Hall.
  have Hallg': forall v, connect grev v u -> forall v', gV' (val v) v' = g' (val v) v'.
    move => v' Hc'.
    apply f_equal_g.
    apply/eqP.
    exact: Hall'.
  rewrite -Hch.
  rewrite Hu'.
  apply sym_eq.
  apply check_V_V' => //.
  * rewrite -checkable_V_V' //.
    apply/eqP.
    by apply: Hall'.
  * exact: connect_gV'_rev.
  * move => v0.
    exact: connect_f_f'_eq.
Qed.

End Changed.

Section Other.

Variable A : eqType.
Variable V' : finType.
Variable P : pred V'.
Local Notation V := (sig_finType P).
Variable f' : V' -> A.
Variable f : V -> A.
Variable checkable' : pred V'.
Variable checkable : pred V.
Variable R : eqType.
Variable check : V -> R.
Variable check' : V' -> R.
Variables (g1 : rel V) (g2 : rel V).
Variable g' : rel V'.

Local Notation g1V' := [rel x y : V' | insub_g g1 x y].

Hypothesis g1_g2_connect : connect g1 =2 connect g2.

Hypothesis f_equal_g1 :
  forall v, f v = f' (val v) -> forall v', g1V' (val v) v' = g' (val v) v'.

Hypothesis checkable_V_V' :
  forall v, f v = f' (val v) -> checkable v = checkable' (val v).

Hypothesis check_V_V' :
  forall v, checkable v -> checkable' (val v) ->
  (forall v', connect g1V' (val v) v' = connect g' (val v) v') ->
  (forall v', connect g1V' (val v) (val v') -> f v' = f' (val v')) ->
  check v = check' (val v).

Variable V_result_cert : seq (V * R).
Hypothesis V_result_certP :
  forall (v : V) (r : R), reflect (checkable v /\ check v = r) ((v,r) \in V_result_cert).
Hypothesis V_result_cert_uniq : uniq [seq vr.1 | vr <- V_result_cert].

Lemma check_all_cert_V'_uniq_g2 : uniq (check_all_cert_V' f' f g2 checkable' check' V_result_cert).
Proof.
rewrite /check_all_cert_V' /check_all_cert /check_impactedV'_cert /checkable_impacted_fresh.
erewrite <- connect_checkable_impactedV'; eauto.
rewrite /V'_result_filter_cert /impactedVV'.
erewrite <- connect_impactedV_eq; eauto.
exact: check_all_cert_V'_uniq.
Qed.

Lemma check_all_cert_complete_g2 :
  forall v, checkable' v -> v \in check_all_cert_V' f' f g2 checkable' check' V_result_cert.
Proof.
move => v Hc.
rewrite /check_all_cert_V' /check_all_cert /check_impactedV'_cert /checkable_impacted_fresh.
erewrite <- connect_checkable_impactedV'; eauto.
rewrite /V'_result_filter_cert /impactedVV'.
erewrite <- connect_impactedV_eq; eauto.
by apply: check_all_cert_complete; eauto.
Qed.

Lemma check_all_cert_sound_g2 :
  forall (v : V') (r : R), (v,r) \in check_all_cert f' f g2 checkable' check' V_result_cert ->
  checkable' v /\ check' v = r.
Proof.
move => v r.
rewrite /check_all_cert /check_impactedV'_cert /checkable_impacted_fresh.
erewrite <- connect_checkable_impactedV'; eauto.
rewrite /V'_result_filter_cert /impactedVV'.
erewrite <- connect_impactedV_eq; eauto.
by apply: check_all_cert_sound; eauto.
Qed.

End Other.
