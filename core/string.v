From mathcomp.ssreflect Require Import all_ssreflect.
From Coq Require Import Ascii String.

Definition eq_ascii (a a' : ascii) := nat_of_ascii a == nat_of_ascii a'.

Lemma eq_asciiP : Equality.axiom eq_ascii.
Proof.
move => x y; apply: (iffP idP); last by move =>->; apply/eqP.
move/eqP; rewrite -{2}(ascii_nat_embedding x); move =>->.
by rewrite ascii_nat_embedding.
Qed.

Definition ascii_eqMixin := EqMixin eq_asciiP.
Canonical ascii_eqType := Eval hnf in EqType ascii ascii_eqMixin.

Fixpoint seq_of_string s :=
if s is String c s' then c :: seq_of_string s' else [::].

Fixpoint string_of_seq s :=
if s is c :: s' then String c (string_of_seq s') else EmptyString.

Lemma seq_of_stringK : cancel seq_of_string string_of_seq.
Proof. by elim=> [|c s /= ->]. Qed.

Definition eq_string (s s' : string) := seq_of_string s == seq_of_string s'.

Lemma eq_stringP : Equality.axiom eq_string.
Proof.
move => x y; apply: (iffP idP); last by move =>->; apply/eqP.
move/eqP; rewrite -{2}(seq_of_stringK x); move =>->.
by rewrite seq_of_stringK.
Qed.

Definition string_eqMixin := EqMixin eq_stringP.
Canonical string_eqType := Eval hnf in EqType string string_eqMixin.
