From mathcomp Require Import all_ssreflect.
From chip
Require Import extra connect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Kosaraju.

Variable T : finType.

Implicit Types s : {set T}.

Section Pdfs.

Variable successors : T -> seq T.

Fixpoint rpdfs m (p : {set T} * seq T) x :=
  if x \notin p.1 then p else
  if m is m1.+1 then
    let p1 := foldl (rpdfs m1) (p.1 :\ x, p.2) (successors x) in (p1.1, x :: p1.2)
  else p.

Definition pdfs := rpdfs #|T|.

Definition tseq := (foldl pdfs (setT, [::]) (enum T)).2.

Local Notation "x -[ l ]-> y" :=
  (connect (rel_of_simpl_rel (relto l (grel successors))) x y)
  (at level 10, format "x  -[ l ]->  y").
Local Notation "x -[]-> y" := (connect (grel successors) x y)
  (at level 10, format "x  -[]->  y").
Local Notation "x =[ l ]= y" := (diconnect (relto l (grel successors)) x y)
  (at level 10, format "x  =[ l ]=  y").
Local Notation "x =[]= y" := (diconnect (grel successors) x y)
  (at level 10, format "x  =[]=  y").
Local Notation "TS[ a , l ]" := (tsorted (grel successors) a l)
  (at level 10, format "TS[ a ,  l ]").
Local Notation "TS[ l ]" := (tsorted (grel successors) (pred_of_simpl predT) l)
  (at level 10, format "TS[ l ]").

Lemma pdfs_correct' (p : {set T} * seq T) x :
  let (s, l) := p in 
  uniq l /\  {subset l <= ~: s} ->
  let p1 := pdfs p x in
  let (s1, l1) := p1 in
  if x \notin s then p1 = p else
       [/\ #|s1| <= #|s| & uniq l1]
    /\
       exists l2 : seq T,
       [/\ x \in l2, s1 = s :\: [set y in l2], l1 = l2 ++ l, 
           TS[[pred x in s], l2] &
           forall y, y \in l2 -> x -[[pred x in s]]-> y].
Proof.
rewrite /pdfs.
have: #|p.1| <= #|T| by apply/subset_leq_card/subsetP=> i.
elim: #|T| x p => /= [x [s l]|n IH x [s l]]/=.
  rewrite leqn0 => /eqP/cards0_eq-> [HUl HS].
  by rewrite inE.
have [xIs Hl [HUl HS]/=|xNIs Hl [HUl HS]//] := boolP (x \in s).
set p := (_, l); set F := rpdfs _; set L := successors _.
have: 
     [/\ #|p.1| < #|s| & uniq p.2]
  /\
     exists l2,
      [/\  
           x \notin p.1, 
           p.1 = (s :\ x) :\: [set z in l2], 
           p.2 = l2 ++ l, TS[[predD1 s & x], l2] &
           forall y, y \in l2 -> x -[[predD1 s & x]]-> y
      ].
  split; [split => // | exists [::]; split => //=].
  - by rewrite /p /= [#|s|](cardsD1 x) xIs.
  - by rewrite !inE eqxx.
  - by rewrite setD0.
  by exact: tsorted_nil.
have: forall y, (grel successors) x y -> (y \notin p.1) || (y \in L).
  by move => y; rewrite /= orbC => ->.
have: forall y, (y \in L) -> (grel successors) x y by move=> y.
rewrite {}/p.
elim: L (_, _) => /=
    [[s1 l1] /= _ yIp [[sSs1 Ul1] [l2 [xIs1 s1E l1E Rwl2 xCy]]]|
    y l' IH1 [s1 l1] /= Rx yIp [[sSs1 Ul1] [l2 [xIs1 s1E l1E Rwl2 xCy]]]].
  split; [split=> // |exists (x :: l2); split] => // [||||||y].
  - rewrite subset_leqif_cards // s1E.
    by apply: subset_trans (subsetDl _ _) (subD1set _ _).
  - rewrite Ul1 andbT l1E mem_cat negb_or.
    have [/= Dl2 _] := Rwl2.
    have /subsetP/(_ x)/implyP/=  := Dl2.
    rewrite !inE /= eqxx implybF => ->.
    have  /implyP := HS x.
    by rewrite !inE xIs implybF.
  - by rewrite inE eqxx.
  - by apply/setP => z; rewrite s1E !inE negb_or andbC andbAC.
  - by rewrite l1E.
  - apply: tsorted_cons_r => // [y yInl2|y /yIp].
    rewrite connect_to_C1_id
           (eq_connect (_ : _ =2 (relto [predD1 s & x] (grel successors)))) ?xCy //.
      by move=> x1 y1; rewrite /= !inE andbA.
    rewrite orbF s1E 3!inE negb_and => /orP[]; first by rewrite negbK.
    by rewrite !inE negb_and => /orP[] /negPf->.
  rewrite inE => /orP[/eqP->|yIl2].
    by apply: connect0.
  apply: connect_to_sub (xCy _ yIl2); apply/subsetP => i /=.
  by rewrite !inE => /andP[].
have F1 : #|s1| <= n.
  by rewrite -ltnS (leq_trans _ Hl).
have F2 : {subset l1 <= ~: s1}.
  move=> i; rewrite l1E s1E !inE mem_cat => /orP[->//|/HS].
  by rewrite inE => /negPf->; rewrite !andbF.
have := IH y (s1, l1) F1 (conj Ul1 F2).
rewrite /F /=; case: rpdfs => s3 l3 /= Hv.
apply: IH1 => [z zIl|z Rxz /=|]; first by apply: Rx; rewrite inE zIl orbT.
  case: (boolP (y \in s1)) Hv =>
       [yIs1/= [[Ss1s3 Ul3] [l4 [yIl4 s3E l3E Rwl4 Cyz]]]
       |yNIs1/= [-> _]]; last first. 
    case/orP: (yIp _ Rxz) => [->//|].
    by rewrite inE => /orP[/eqP->|->]; [rewrite yNIs1|rewrite orbT].
  rewrite s3E !inE !negb_and.
  case/orP: (yIp _ Rxz) => [->//|]; first by rewrite orbT.
  rewrite inE => /orP[/eqP->|->]; last by rewrite orbT.
  by rewrite yIl4.
case: (boolP (y \in s1)) Hv =>
      [yIs1 [[Ss1s3 Ul3] [l4 [yIl4 s3E l3E Rwl4 Cyz]]]
      |yNIs1 [-> ->]]; last first.
  by split=> //; exists l2; split.
split; [split=> //= | exists (l4 ++ l2); split => //= [||||z]]. 
- by apply: leq_ltn_trans Ss1s3 _.
- by rewrite s3E s1E !inE eqxx !andbF.
- by apply/setP => i; rewrite s3E s1E !inE mem_cat negb_or -!andbA.
- by rewrite l3E l1E catA.
- apply: tsorted_cat => //.
  apply: eq_tsorted Rwl4 => i.
  by rewrite /= s1E !inE.
rewrite mem_cat => /orP[] zIl4; last by apply: xCy.
apply: connect_trans (_: y -[_]-> z); last first.
  apply: connect_to_sub (Cyz _ zIl4); apply/subsetP => i.
  by rewrite /= s1E !inE => /andP[].
apply: connect_to1 (Rx _ _); rewrite !inE ?eqxx //.
by move: yIs1; rewrite s1E !inE=> /and3P[_ ->].
Qed.

Lemma pdfs_connect' s x : 
  x \in s ->
  let (s1, l1) := pdfs (s, [::]) x in
  [/\ uniq l1, s1 = s :\: [set z in l1], l1 \subset s &
      forall y, y \in l1 = x -[[pred u in s]]-> y].
Proof.
move=> xIs.
set p := (_, _).
have UN : [/\ uniq p.2 & {subset p.2 <= ~: p.1}] by [].
case: pdfs (pdfs_correct' (_, _) x UN) => s1 l1.
rewrite xIs => /=[[[_ Ul1] [l2 [xIl2 s1E l1E WH Cy]]]].
split => // [||y].
- by apply/setP=> i; rewrite s1E l1E !inE cats0.
- apply/subsetP=> z.
  rewrite l1E cats0.
  by have [/subsetP/(_ z)/=] := WH.
apply/idP/idP => [|H].
  by rewrite l1E cats0; exact: Cy.
rewrite l1E cats0.
by have [_ /(_ x y xIl2 H)] := WH.
Qed.

(* The sequence is topologically sorted and contains all the nodes *)
Lemma tseq_correct' : TS[tseq] /\ forall x, x \in tseq.
Proof.
suff: [/\
        {subset (setT : {set T}, [::]).2  <= tseq},
        TS[tseq] &
         forall x : T, x \in (enum T) ->  x \in tseq].
  case=> H1 H2 H3; split => // x.
  by rewrite H3 // mem_enum.
rewrite /tseq; set F := foldl _; set p := (_, _).
have : TS[p.2] by apply: tsorted_nil.
have: p.1 = ~: [set x in p.2].
  by apply/setP=> i; rewrite /= !inE.
have: uniq p.2 by [].
elim: (enum T) p => /= [|y l IH [s1 l1] HUl1 /= Hi Rw].
  by split.
have HS : {subset l1 <= ~: s1}.
  by move=> i; rewrite Hi !inE negbK.
have :=  pdfs_correct' (_, _) y (conj HUl1 HS).
have [yIs1|yNIs1] := boolP (y \in s1); last first.
  case: pdfs => s2 l2 [-> ->].
  have /= [Sl2 HR xI] := IH (s1,l1) HUl1 Hi Rw.
  split => // x.
  rewrite inE => /orP[/eqP->|xIl]; last by apply: xI.
  apply: Sl2.
  by move: yNIs1; rewrite Hi !inE negbK.
case: pdfs => s2 l2 /= [[Ss1s2 Ul2] [l3 [yIl3 s2E l2E RWl3 Cyz]]].
case: (IH (s2, l2)) => //= [|| Sl2F RwF FI]. 
- by apply/setP=> i; rewrite s2E Hi l2E !inE mem_cat negb_or.
- rewrite l2E; apply: (tsorted_cat Rw).
  apply: eq_tsorted RWl3 => i.
  by rewrite /= Hi !inE andbT.
split=> // [i iIl1|x]; first by rewrite Sl2F // l2E mem_cat iIl1 orbT.
rewrite inE => /orP[/eqP->|//]; last exact: FI.
by apply: Sl2F; rewrite l2E mem_cat yIl3.
Qed.

End Pdfs.

Section Stack.

Variable r : rel T.

Local Notation "x -[ l ]-> y" := 
  (connect (rel_of_simpl_rel (relto l r)) x y) 
  (at level 10, format "x  -[ l ]->  y").
Local Notation "x -[]-> y" := (connect r x y) 
  (at level 10, format "x  -[]->  y").
Local Notation "x =[ l ]= y" := (diconnect (relto l r) x y) 
  (at level 10, format "x  =[ l ]=  y").
Local Notation "x =[]= y" := (diconnect r x y) 
  (at level 10, format "x  =[]=  y").
Local Notation "TS[ a , l ]" := (tsorted r a l) 
  (at level 10, format "TS[ a ,  l ]").
Local Notation "TS[ l ]" := (tsorted r (pred_of_simpl predT) l) 
  (at level 10, format "TS[ l ]").

Lemma pdfs_correct (p : {set T} * seq T) x :
  let (s, l) := p in 
  uniq l /\  {subset l <= ~: s} ->
  let p1 := pdfs (rgraph r) p x in
  let (s1, l1) := p1 in
  if x \notin s then p1 = p else
       [/\ #|s1| <= #|s| & uniq l1]
    /\
       exists l2 : seq T,
       [/\ x \in l2, s1 = s :\: [set y in l2], l1 = l2 ++ l, 
           TS[[pred x in s], l2] &
           forall y, y \in l2 -> x -[[pred x in s]]-> y].
Proof.
rewrite /pdfs.
have: #|p.1| <= #|T| by apply/subset_leq_card/subsetP=> i.
elim: #|T| x p => /= [x [s l]|n IH x [s l]]/=.
  rewrite leqn0 => /eqP/cards0_eq-> [HUl HS].
  by rewrite inE.
have [xIs Hl [HUl HS]/=|xNIs Hl [HUl HS]//] := boolP (x \in s).
set p := (_, l); set F := rpdfs _ _; set L := rgraph _ _.
have: 
     [/\ #|p.1| < #|s| & uniq p.2]
  /\
     exists l2,
      [/\  
           x \notin p.1, 
           p.1 = (s :\ x) :\: [set z in l2], 
           p.2 = l2 ++ l, TS[[predD1 s & x], l2] &
           forall y, y \in l2 -> x -[[predD1 s & x]]-> y
      ].
  split; [split => // | exists [::]; split => //=].
  - by rewrite /p /= [#|s|](cardsD1 x) xIs.
  - by rewrite !inE eqxx.
  - by rewrite setD0.
  by exact: tsorted_nil.
have: forall y, r x y -> (y \notin p.1) || (y \in L).
  by move=> y; rewrite [_ \in rgraph _ _]rgraphK orbC => ->.
have: forall y, (y \in L) -> r x y.
  by move=> y; rewrite [_ \in rgraph _ _]rgraphK.
rewrite {}/p.
elim: L (_, _) => /=
    [[s1 l1] /= _ yIp [[sSs1 Ul1] [l2 [xIs1 s1E l1E Rwl2 xCy]]]|
    y l' IH1 [s1 l1] /= Rx yIp [[sSs1 Ul1] [l2 [xIs1 s1E l1E Rwl2 xCy]]]].
  split; [split=> // |exists (x :: l2); split] => // [||||||y].
  - rewrite subset_leqif_cards // s1E.
    by apply: subset_trans (subsetDl _ _) (subD1set _ _).
  - rewrite Ul1 andbT l1E mem_cat negb_or.
    have [/= Dl2 _] := Rwl2.
    have /subsetP/(_ x)/implyP/=  := Dl2.
    rewrite !inE /= eqxx implybF => ->.
    have  /implyP := HS x.
    by rewrite !inE xIs implybF.
  - by rewrite inE eqxx.
  - by apply/setP => z; rewrite s1E !inE negb_or andbC andbAC.
  - by rewrite l1E.
  - apply: tsorted_cons_r => // [y yInl2|y /yIp].
    rewrite connect_to_C1_id
           (eq_connect (_ : _ =2 (relto [predD1 s & x] r))) ?xCy //.
      by move=> x1 y1; rewrite /= !inE andbA.
    rewrite orbF s1E 3!inE negb_and => /orP[]; first by rewrite negbK.
    by rewrite !inE negb_and => /orP[] /negPf->.
  rewrite inE => /orP[/eqP->|yIl2].
    by apply: connect0.
  apply: connect_to_sub (xCy _ yIl2); apply/subsetP => i /=.
  by rewrite !inE => /andP[].
have F1 : #|s1| <= n.
  by rewrite -ltnS (leq_trans _ Hl).
have F2 : {subset l1 <= ~: s1}.
  move=> i; rewrite l1E s1E !inE mem_cat => /orP[->//|/HS].
  by rewrite inE => /negPf->; rewrite !andbF.
have := IH y (s1, l1) F1 (conj Ul1 F2).
rewrite /F /=; case: rpdfs => s3 l3 /= Hv.
apply: IH1 => [z zIl|z Rxz /=|]; first by apply: Rx; rewrite inE zIl orbT.
  case: (boolP (y \in s1)) Hv =>
       [yIs1/= [[Ss1s3 Ul3] [l4 [yIl4 s3E l3E Rwl4 Cyz]]]
       |yNIs1/= [-> _]]; last first. 
    case/orP: (yIp _ Rxz) => [->//|].
    by rewrite inE => /orP[/eqP->|->]; [rewrite yNIs1|rewrite orbT].
  rewrite s3E !inE !negb_and.
  case/orP: (yIp _ Rxz) => [->//|]; first by rewrite orbT.
  rewrite inE => /orP[/eqP->|->]; last by rewrite orbT.
  by rewrite yIl4.
case: (boolP (y \in s1)) Hv =>
      [yIs1 [[Ss1s3 Ul3] [l4 [yIl4 s3E l3E Rwl4 Cyz]]]
      |yNIs1 [-> ->]]; last first.
  by split=> //; exists l2; split.
split; [split=> //= | exists (l4 ++ l2); split => //= [||||z]]. 
- by apply: leq_ltn_trans Ss1s3 _.
- by rewrite s3E s1E !inE eqxx !andbF.
- by apply/setP => i; rewrite s3E s1E !inE mem_cat negb_or -!andbA.
- by rewrite l3E l1E catA.
- apply: tsorted_cat => //.
  apply: eq_tsorted Rwl4 => i.
  by rewrite /= s1E !inE.
rewrite mem_cat => /orP[] zIl4; last by apply: xCy.
apply: connect_trans (_: y -[_]-> z); last first.
  apply: connect_to_sub (Cyz _ zIl4); apply/subsetP => i.
  by rewrite /= s1E !inE => /andP[].
apply: connect_to1 (Rx _ _); rewrite !inE ?eqxx //.
by move: yIs1; rewrite s1E !inE=> /and3P[_ ->].
Qed.

Lemma pdfs_connect s x : 
  x \in s ->
  let (s1, l1) := pdfs (rgraph r) (s, [::]) x in
  [/\ uniq l1, s1 = s :\: [set z in l1], l1 \subset s &
      forall y, y \in l1 = x -[[pred u in s]]-> y].
Proof.
move=> xIs.
set p := (_, _).
have UN : [/\ uniq p.2 & {subset p.2 <= ~: p.1}] by [].
case: pdfs (pdfs_correct (_, _) x UN) => s1 l1.
rewrite xIs => /=[[[_ Ul1] [l2 [xIl2 s1E l1E WH Cy]]]].
split => // [||y].
- by apply/setP=> i; rewrite s1E l1E !inE cats0.
- apply/subsetP=> z.
  rewrite l1E cats0.
  by have [/subsetP/(_ z)/=] := WH.
apply/idP/idP => [|H].
  by rewrite l1E cats0; exact: Cy.
rewrite l1E cats0.
by have [_ /(_ x y xIl2 H)] := WH.
Qed.

(* The sequence is topologically sorted and contains all the nodes *)
Lemma tseq_correct : TS[tseq (rgraph r)] /\ forall x, x \in tseq (rgraph r).
Proof.
suff: [/\
        {subset (setT : {set T}, [::]).2  <= tseq (rgraph r)},
        TS[tseq (rgraph r)] &
         forall x : T, x \in (enum T) ->  x \in tseq (rgraph r)].
  case=> H1 H2 H3; split => // x.
  by rewrite H3 // mem_enum.
rewrite /tseq; set F := foldl _; set p := (_, _).
have : TS[p.2] by apply: tsorted_nil.
have: p.1 = ~: [set x in p.2].
  by apply/setP=> i; rewrite /= !inE.
have: uniq p.2 by [].
elim: (enum T) p => /= [|y l IH [s1 l1] HUl1 /= Hi Rw].
  by split.
have HS : {subset l1 <= ~: s1}.
  by move=> i; rewrite Hi !inE negbK.
have :=  pdfs_correct (_, _) y (conj HUl1 HS).
have [yIs1|yNIs1] := boolP (y \in s1); last first.
  case: pdfs => s2 l2 [-> ->].
  have /= [Sl2 HR xI] := IH (s1,l1) HUl1 Hi Rw.
  split => // x.
  rewrite inE => /orP[/eqP->|xIl]; last by apply: xI.
  apply: Sl2.
  by move: yNIs1; rewrite Hi !inE negbK.
case: pdfs => s2 l2 /= [[Ss1s2 Ul2] [l3 [yIl3 s2E l2E RWl3 Cyz]]].
case: (IH (s2, l2)) => //= [|| Sl2F RwF FI]. 
- by apply/setP=> i; rewrite s2E Hi l2E !inE mem_cat negb_or.
- rewrite l2E; apply: (tsorted_cat Rw).
  apply: eq_tsorted RWl3 => i.
  by rewrite /= Hi !inE andbT.
split=> // [i iIl1|x]; first by rewrite Sl2F // l2E mem_cat iIl1 orbT.
rewrite inE => /orP[/eqP->|//]; last exact: FI.
by apply: Sl2F; rewrite l2E mem_cat yIl3.
Qed.

End Stack.

Section Program.

Variable r : rel T.

Definition kosaraju :=
  let f := pdfs (rgraph [rel x y | r y x]) in 
  (foldl  (fun (p : {set T} * seq (seq T)) x => if x \notin p.1 then p else 
                      let p1 := f (p.1, [::]) x in  (p1.1, p1.2 :: p.2))
          (setT, [::]) (tseq (rgraph r))).2.

Lemma kosaraju_correct :
 let l := flatten kosaraju in
 [/\ uniq l, forall i, i \in l &
     forall c : seq T, c \in kosaraju ->
        exists x, forall y, (y \in c) = (connect r x y && connect r y x)].
Proof.
rewrite /kosaraju.
set f := pdfs (rgraph [rel x y | r y x]).
set g := fun p x => if _ then _ else _.
set p := (_, _).
have: uniq (flatten p.2) by [].
have: forall c, c \in (flatten p.2) ++ (tseq (rgraph r)).
  by move=>c; case: (tseq_correct r) => _ /(_ c).
have: forall c, c \in p.2 -> 
                exists x, c =i (diconnect (relto predT r) x) by [].
have: ~: p.1 =i flatten p.2.
 by move=> i; rewrite !inE in_nil.
have: tsorted r (predT : pred T) [seq i <- tseq (rgraph r) | i \in p.1].
  have->: [seq i <- tseq (rgraph r) | i \in p.1] = tseq (rgraph r).
    by apply/all_filterP/allP=> y; rewrite inE.
  by case: (tseq_correct r).
elim: tseq p => [[s l]/= HR HI HE HFI HUF|].
  split=> // i.
  by have := HFI i; rewrite cats0.
move=> x l IH [s1 l1] HR HI HE HFI HUF.
rewrite /g /f /=.
have [xIs1|xNIs1] := boolP (x \in s1); last first.
  apply: IH => //= [|i]; first by move: HR; rewrite /= (negPf xNIs1).
  have:= HFI i; rewrite !mem_cat inE /=.
  by case: eqP => //->; rewrite -HI !inE xNIs1.
have := (@pdfs_connect ([rel x y | r y x]) s1 x xIs1).
case: pdfs => s2 l2 /= [Ul2 s2E Dl2 xCy].
move: HR; rewrite /= xIs1; set L := [seq _ <- _ | _] => HR.
have l2R : l2 =i (diconnect r x).
  move=> y.
  rewrite xCy -(@connect_to_rev _ r L setT) //.
  - rewrite -tsorted_diconnect //.
      rewrite -topredE /=.
      by apply: eq_diconnect => i j; rewrite /= !inE.
    by apply: eq_tsorted HR => i; rewrite  !inE //= topredE inE.
  - by apply/subsetP.    
  - move=> i; rewrite /= !inE mem_filter.
    have := HFI i; rewrite /= mem_cat -HI /= !inE.
    case: (_ =P _) => [->|] /=; first by rewrite xIs1.
    by case: (_ \in _).
 by apply: eq_tsorted HR => i; rewrite // inE topredE inE.
apply: IH => [|i|i|i|] //=.
- suff->: [seq i <- l | i \in s2] =
          [seq i <- x :: L | ~~ diconnect r x i].
    by apply: tsorted_inv.
  rewrite /= diconnect0 /=.
  rewrite -filter_predI.
  apply: eq_filter => y /=.
  by rewrite s2E !inE l2R.
- by rewrite s2E !mem_cat !inE -HI negb_and negbK inE.
- by rewrite inE => /orP[/eqP->|//]; [exists x | apply: HE].
- have:= HFI i.
  rewrite /= !mem_cat !inE => /or3P[->|/eqP->|->].
  - by rewrite orbT.
  - by rewrite xCy connect0.
  by rewrite !orbT.
rewrite cat_uniq Ul2 HUF /= andbT.
apply/hasPn => i /=.
have/subsetP/(_ i)/= := Dl2.
by rewrite -HI /= !inE; do 2 case: (_ \in _).
Qed.

End Program.

End Kosaraju.

