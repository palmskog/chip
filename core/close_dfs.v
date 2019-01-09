From mathcomp
Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section DFSearch.

Variable T : finType.

Lemma closureP (g : rel T) (s : pred T) x :
  reflect (exists2 v, v \in s & connect g x v) (x \in closure g s).
Proof.
apply: (iffP idP).
- move/existsP => [y Hy].
  move/andP: Hy => [Hc Hy].
  by exists y.
- move => [v Hv] Hc.
  apply/existsP.
  exists v.
  by apply/andP.
Qed.

Definition rclosed (g : rel T) (a : seq T) :=
  forall x y, g x y -> x \in a -> y \in a.

Lemma rclosed_connect : forall (g : rel T) (s : seq T),
 rclosed g s -> forall x y, connect g x y -> x \in s -> y \in s.
Proof.
move => g s Hr x y.
move/connectP => [p Hp] Hl.
elim: p x Hp Hl => //=; first by move => Hp Hx; move =>->.
move => z p IH x.
move/andP => [Hz Hp] Hl Hx.
have Hzg := Hr _ _ Hz Hx.
move: Hzg.
exact: IH.
Qed.

Definition rclosure (g : T -> seq T) :=
 foldr (fun x s => dfs g #|T| s x) [::].

Definition rclosure' (g : T -> seq T) :=
 foldl (dfs g #|T|) [::].

Lemma rclosure_exist : forall g s x,
  x \in rclosure (rgraph g) s ->
  exists2 v : T, v \in s & connect g v x.
Proof.
move => g.
elim => //=.
move => x s IH y Hyd.
case Hy: (y \in rclosure (rgraph g) s).
  move/idP: Hy.
  move/IH => [v Hv] Hc.
  exists v => //.
  rewrite in_cons.
  apply/orP.
  by right.
move/negP/negP: Hy => Hy.
move/dfs_pathP: Hyd => Hd.
have Ht: #|T| <= #|rclosure (rgraph g) s| + #|T| by exact: leq_addl.
have Hd' := Hd Ht Hy.
destruct Hd'.
exists x; first by rewrite in_cons; apply/orP; left.
apply/connectP.
exists p => //.
move: H.
rewrite /grel /rgraph /=.
elim: p x {H0 H1 Hd} => //=.
move => z p IH' x.
rewrite mem_enum.
move/andP => [He Hp].
apply/andP.
split => //.
exact: IH'.
Qed.

Lemma dfs_in : forall (g : T -> seq T) n s x y,
 x \in s ->
 x \in dfs g n s y.
Proof.
move => g.
case => /=; first by move => s x Hs; case: ifP.
move => n s x y Hx.
case: ifP => //.
move/negP/negP => Hs.
move/subsetP: (subset_dfs g n (y :: s) (g y)) => Hsb.
apply: Hsb.
rewrite in_cons.
by apply/orP; right.
Qed.

Lemma dfs_subset : forall (g : T -> seq T) n s x,
  s \subset dfs g n s x.
Proof.
move => g.
case => //=.
- move => s x.
  by case: ifP => Hx; apply/subsetP.
- move => n s x.
  case: ifP => Hx; first by apply/subsetP.
  move/negP/negP: Hx => Hx.
  move/subsetP: (subset_dfs g n (x :: s) (g x)) => Hs.
  apply/subsetP.
  move => y Hy.
  apply Hs.
  rewrite in_cons.
  by apply/orP; right.
Qed.

Lemma rclosed_rclosure : forall g s,
  rclosed g (rclosure (rgraph g) s).
Proof.
move => g.
elim => //=.
move => x s IH.
move => y z Hg.
case Hy: (y \in rclosure (rgraph g) s).
  move/idP: Hy.
  move/(IH _ z Hg) => Hz Hy.
  exact: dfs_in.
move/negP/negP: Hy => Hcx.
move => Hcy.
have Ht: #|T| <= #|rclosure (rgraph g) s| + #|T| by exact: leq_addl.
case Hz: (z \in rclosure (rgraph g) s); first by apply: dfs_in.
move/negP/negP: Hz => Hz.
apply/dfs_pathP => //.
move/dfs_pathP: Hcy => Hcy.
case (Hcy Ht Hcx) => [p Hp] Hl Hd.
rewrite disjoint_cons in Hd.
move/andP: Hd => [Hx Hd].
exists (rcons p z).
- rewrite /grel /rgraph /=.
  rewrite rcons_path /=.
  rewrite -Hl.
  apply/andP.
  split => //.
  by rewrite mem_enum.
- by rewrite last_rcons.
- rewrite disjoint_cons.
  apply/andP.
  split => //.    
  rewrite disjoint_has.
  elim: p Hd {Hp Hl} => //=.
  * move => Hd.
    apply/negP.
    case.
    move/orP.
    case => //.
    move => Hz'.
    by move/negP: Hz; case.
  * move => z0 p IH'.
    rewrite disjoint_cons.
    move/andP => [Hz0 Hd].
    apply/norP.
    split => //.
    exact: IH'.
Qed.

Lemma dfs_in_in : forall (g : T -> seq T) s x,
  x \in dfs g #|T| s x.
Proof.
move => g s x.
case Hx: (x \in s); first by apply dfs_in.
move/negP/negP: Hx => Hx.
apply/dfs_pathP => //.
- exact: leq_addl.
- exists [::] => //.
  rewrite disjoint_has.
  rewrite /=.
  apply/norP.
  by split.
Qed.

Lemma subset_closure : forall g s,
 s \subset rclosure (rgraph g) s.
Proof.
move => g.
elim => //= x s IH.
move/subsetP: IH => IH.
apply/subsetP.
move => y.
rewrite in_cons.
move/orP; case.
- move/eqP =>-> {y}.
  exact: dfs_in_in.
- move => Hy.
  apply IH in Hy.
  exact: dfs_in.
Qed.

Lemma rclosureP g (modified : seq T) x :
  reflect
    (exists2 v, v \in modified & connect g v x)
    (x \in rclosure (rgraph g) modified).
Proof.
apply: (iffP idP); first by move => Hx; apply: rclosure_exist.
move => [v Hm] Hc.
have Hcl := @rclosed_rclosure g modified.
move: Hcl.
move/rclosed_connect => Hcl.
move/Hcl: Hc.
apply.
move/subsetP: (subset_closure g modified) => Hp.
exact: Hp.
Qed.

Lemma dfs_eq_in : forall (g1 g2 : T -> seq T) n s x,
 x \in s ->
 dfs g1 n s x =i dfs g2 n s x.
Proof.
move => g1 g2.
elim => //=.
move => n IH s x Hg Hs.
case: ifP => //.
move/negP.
by case.
Qed.

Lemma dfs_mem : forall (g1 g2 : T -> seq T) s x,
    g1 =1 g2 ->
    dfs g1 #|T| s x =i dfs g2 #|T| s x.
Proof.
move => g1 g2 s x Hg y.
case Hy: (y \in s).
  move/idP: Hy => Hy.
  have Hd1 := dfs_in g1 #|T| x Hy.
  have Hd2 := dfs_in g2 #|T| x Hy.
  move: Hd1 Hd2.
  by case (y \in dfs g1 #|T| s x).
move/negP/negP: Hy => Hy.
have Hn: #|T| <= #|s| + #|T| by apply: leq_addl.
apply/dfs_pathP/idP => //.
- case => p Hp Hl Hd.
  apply/dfs_pathP => //.
  exists p => //.
  elim: p x Hp {Hl Hd} => //=.
  move => z p IH x.
  move/andP => [Hg1 Hp].
  apply/andP.
  split; last by apply: IH.
  by rewrite -Hg.
- move/dfs_pathP => Hd.
  move/Hd: Hn => Hd'.
  move/Hd': Hy.
  case => p Hp Hl Hds.
  exists p => //.
  elim: p x Hp {Hl Hd Hd' Hds} => //=.
  move => z p IH x.
  move/andP => [Hg1 Hp].
  apply/andP.
  split; last by apply: IH.
  by rewrite Hg.
Qed.

Lemma dfs_mem' : forall (g1 g2 : T -> seq T) s x,
    (forall x, g1 x =i g2 x) ->
    dfs g1 #|T| s x =i dfs g2 #|T| s x.
Proof.
move => g1 g2 s x Hg y.
case Hy: (y \in s).
  move/idP: Hy => Hy.
  have Hd1 := dfs_in g1 #|T| x Hy.
  have Hd2 := dfs_in g2 #|T| x Hy.
  move: Hd1 Hd2.
  by case (y \in dfs g1 #|T| s x).
move/negP/negP: Hy => Hy.
have Hn: #|T| <= #|s| + #|T| by apply: leq_addl.
apply/dfs_pathP/idP => //.
- case => p Hp Hl Hd.
  apply/dfs_pathP => //.
  exists p => //.
  elim: p x Hp {Hl Hd} => //=.
  move => z p IH x.
  move/andP => [Hg1 Hp].
  apply/andP.
  split; last by apply: IH.
  by rewrite -Hg.
- move/dfs_pathP => Hd.
  move/Hd: Hn => Hd'.
  move/Hd': Hy.
  case => p Hp Hl Hds.
  exists p => //.
  elim: p x Hp {Hl Hd Hd' Hds} => //=.
  move => z p IH x.
  move/andP => [Hg1 Hp].
  apply/andP.
  split; last by apply: IH.
  by rewrite Hg.
Qed.

Lemma subset_rclose : forall (g : T -> seq T) s s0,
 s \subset foldr (fun x s => dfs g #|T| s x) s s0.
Proof.
move => g s s0.
elim: s0 s => //=.
move => x s IH s0.
apply/subsetP => y Hy.
apply: dfs_in.
move/subsetP: (IH s0) => Hs.
exact: Hs.
Qed.

Lemma rclose_subset : forall (g : T -> seq T) s s0,
 s \subset foldr (fun x s => dfs g #|T| s x) s0 s.
Proof.
move => g.
elim => //=; first by move => s0; apply/subsetP.
move => x s IH s0.
apply/subsetP.
move => y.
rewrite in_cons.
move/orP; case.
- move/eqP =>->.
  exact: dfs_in_in.
- move => Hy.
  apply: dfs_in.
  move/subsetP: (IH s0) => Hs.
  exact: Hs.
Qed.

Lemma dfs_mems : forall (g : T -> seq T) s1 s2 x,
    s1 =i s2 ->
    dfs g #|T| s1 x =i dfs g #|T| s2 x.
Proof.
move => g s1 s2 x Hs y.
case Hy: (y \in s1).
  move/idP: Hy => Hy.
  have Hd1 := dfs_in g #|T| x Hy.
  rewrite Hs in Hy.
  have Hd2 := dfs_in g #|T| x Hy.
  move: Hd1 Hd2.
  by case (y \in dfs _ #|T| _ x).
move/negP: Hy => Hy.
have Hy' : ~ y \in s2.
  move => Hy'.
  rewrite -Hs in Hy'.
  by case: Hy.
move/negP: Hy => Hy.
move/negP: Hy' => Hy'.
have Hn: #|T| <= #|s1| + #|T| by apply: leq_addl.
have Hn': #|T| <= #|s2| + #|T| by apply: leq_addl.
apply/dfs_pathP/idP => //.
- case => p Hp Hl Hd.
  apply/dfs_pathP => //.
  exists p => //.
  move: Hd.
  rewrite 2!disjoint_cons.
  move/andP => [Hx Hd].
  apply/andP.
  split; first by rewrite -Hs.
  elim: p Hd {Hp Hl} => //=.
  move => z p Hd.
  rewrite 2!disjoint_cons.
  rewrite Hs.
  move/andP => [Hz Hd'].
  apply/andP.
  split => //.
  exact: Hd.
- move/dfs_pathP => Hd.
  move/Hd: Hn' => Hd'.
  move/Hd': Hy'.
  case => p Hp Hl Hds.
  exists p => //.
  move: Hds.
  rewrite 2!disjoint_cons.
  move/andP => [Hx Hd0].
  apply/andP.
  split; first by rewrite Hs.
  elim: p Hd0 {Hp Hl} => //=.
  move => z p Hd0.
  rewrite 2!disjoint_cons.
  rewrite Hs.
  move/andP => [Hz Hd1].
  apply/andP.
  split => //.
  exact: Hd0.
Qed.

Lemma closure_g : forall g1 g2 s,
  (forall x, g1 x =i g2 x) ->
  rclosure g1 s =i rclosure g2 s.
Proof.
move => g1 g2 s Hg.
move: s.
elim => //=.
move => x s IH y.
by rewrite (dfs_mems _ _ IH) (@dfs_mem' g1 g2).
Qed.

Lemma rclosurePg g (modified : seq T) x :
  reflect
    (exists2 v, v \in modified & connect (grel g) v x)
    (x \in rclosure g modified).
Proof.
apply: (iffP idP).
- move => Hx.
  apply: rclosure_exist.
  have Hg := @closure_g g (rgraph (grel g)).
  rewrite -Hg //.
  move => y s.
  by rewrite /rgraph /grel mem_enum.
- move/rclosureP.
  have Hg := @closure_g g (rgraph (grel g)).
  rewrite -Hg //.
  move => y s.
  by rewrite /rgraph /grel mem_enum.
Qed.

Lemma closure_eqi : forall (g : T -> seq T) s1 s2,
  s1 =i s2 ->
  rclosure g s1 =i rclosure g s2.
Proof.
move => g s1 s2 Hs x.
apply/rclosurePg/idP.
- move => [v Hv] Hc.
  apply/rclosurePg.
  exists v => //.
  by rewrite -Hs.
- move/rclosurePg.
  move => [v Hv] Hc.
  exists v => //.
  by rewrite Hs.
Qed.

Lemma rclosure_in_lr : forall (g : T -> seq T) s x,
  x \in foldl (dfs g #|T|) [::] s ->
  x \in foldr (fun x s => dfs g #|T| s x) [::] s.
Proof.
move => g s x.
have {1} ->: s = rev (rev s) by rewrite revK.
rewrite foldl_rev.
rewrite (@closure_eqi _ s (rev s)) //.
move => y.
have Hs := has_rev (pred1 y) s.
by rewrite 2!has_pred1 in Hs.
Qed.

Lemma rclosure_in_rl : forall (g : T -> seq T) s x,
  x \in foldr (fun x s => dfs g #|T| s x) [::] s ->
  x \in foldl (dfs g #|T|) [::] s.
Proof.
move => g s x.
have {2} ->: s = rev (rev s) by rewrite revK.
rewrite foldl_rev.
rewrite (@closure_eqi _ s (rev s)) //.
move => y.
have Hs := has_rev (pred1 y) s.
by rewrite 2!has_pred1 in Hs.
Qed.

Lemma rclosure_rclosure'_i : forall g s,
  rclosure g s =i rclosure' g s.
Proof.
move => g s x.
case Hx: (x \in _); case Hx': (x \in _) => //.
- move/negP: Hx'.
  case.
  exact: rclosure_in_rl.
- move/negP: Hx.
  case.
  exact: rclosure_in_lr.
Qed.

Lemma rclosure'P g (modified : seq T) x :
  reflect
    (exists2 v, v \in modified & connect g v x)
    (x \in rclosure' (rgraph g) modified).
Proof.
apply: (iffP idP).
- rewrite -rclosure_rclosure'_i.
  by move/rclosureP.
- move => Hx.
  rewrite -rclosure_rclosure'_i.
  by apply/rclosureP.
Qed.

Lemma rclosed_rclosure' : forall g s,
  rclosed g (rclosure' (rgraph g) s).
Proof.
move => g s x y Hg.
rewrite -2!rclosure_rclosure'_i.
exact: rclosed_rclosure.
Qed.

Lemma rclosure'Pg g (modified : seq T) x :
  reflect
    (exists2 v, v \in modified & connect (grel g) v x)
    (x \in rclosure' g modified).
Proof.
apply: (iffP idP).
- rewrite -rclosure_rclosure'_i.
  by move/rclosurePg.
- move/rclosurePg.
  by rewrite rclosure_rclosure'_i.
Qed.

Lemma dfs_uniq : forall (g : T -> seq T) n s v,
 uniq s ->
 uniq (dfs g n s v).
Proof.
move => g.
elim => //=; first by move => s v; case: ifP.
move => n IH s v Hs.
have ->: g v = rev (rev (g v)) by rewrite revK.
case: ifP => //.
move/negP/negP => Hv.  
rewrite foldl_rev.
generalize (rev (g v)).
elim => //=; first by apply/andP; split.
move => y s' Hu.
exact: IH.
Qed.

Lemma rclosure_uniq : forall (g : T -> seq T) s,
  uniq s ->
  uniq (rclosure g s).
Proof.
move => g.
elim => //=.
move => x s IH.
move/andP => [Hx Hs].
apply: dfs_uniq.
exact: IH.
Qed.

Lemma rclosure'_uniq : forall (g : T -> seq T) s,
  uniq s ->
  uniq (rclosure' g s).
Proof.
move => g s.
rewrite /rclosure'.
have {2} ->: s = rev (rev s) by rewrite revK.
rewrite foldl_rev.
move => Hs.
apply: rclosure_uniq.
by rewrite rev_uniq.
Qed.

Definition rclosures g (s : {set T}) : {set T} :=
  finset (mem (rclosure (rgraph g) (enum s))).

Lemma rclosuresP (g : rel T) (modified : {set T}) x  :
  reflect
    (exists2 v, v \in modified & connect g v x)
    (x \in rclosures g modified).
Proof.
apply: (iffP idP).
- rewrite /rclosures 2!inE.
  move/rclosureP.
  move => [v Hv] Hc.
  rewrite mem_enum in Hv.
  by exists v.
- move => [v Hv] Hc.
  have Hv': v \in enum modified by rewrite mem_enum.
  have Hex: exists2 v, v \in enum modified & connect g v x by exists v.
  move/rclosureP: Hex => Hcl.
  by rewrite /rclosures 2!inE.
Qed.

Lemma rclosures_connect : forall g s,
 forall x y, connect g x y -> x \in (rclosures g s) -> y \in (rclosures g s).
Proof.
move => g s x y Hc.
have Hc' := rclosed_connect (@rclosed_rclosure g (enum s)) Hc.
move => Hx.
rewrite /rclosures inE /=.
apply: Hc'.
move: Hx.
by rewrite inE.
Qed.

Definition rclosures' g (s : {set T}) : {set T} :=
  finset (mem (rclosure' (rgraph g) (enum s))).

Lemma rclosures'P (g : rel T) (modified : {set T}) x  :
  reflect
    (exists2 v, v \in modified & connect g v x)
    (x \in rclosures' g modified).
Proof.
apply: (iffP idP).
- rewrite /rclosures' 2!inE.
  move/rclosure'P.
  move => [v Hv] Hc.
  rewrite mem_enum in Hv.
  by exists v.
- move => [v Hv] Hc.
  have Hv': v \in enum modified by rewrite mem_enum.
  have Hex: exists2 v, v \in enum modified & connect g v x by exists v.
  move/rclosure'P: Hex => Hcl.
  by rewrite /rclosures 2!inE.
Qed.

Lemma rclosures'_connect : forall g s,
 forall x y, connect g x y -> x \in (rclosures' g s) -> y \in (rclosures' g s).
Proof.
move => g s x y Hc.
have Hc' := rclosed_connect (@rclosed_rclosure' g (enum s)) Hc.
move => Hx.
rewrite /rclosures' inE /=.
apply: Hc'.
move: Hx.
by rewrite inE.
Qed.

End DFSearch.
