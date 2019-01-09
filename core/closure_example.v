From mathcomp
Require Import all_ssreflect.

From chip
Require Import extra connect acyclic kosaraju_acyclic closure.

Inductive food :=
| rigatoni_arrabiata
| rigatoni
| sauce
| tomato_puree
| red_pepper
| garlic.

Definition eq_food (f f' : food) :=
match f, f' with
| rigatoni_arrabiata, rigatoni_arrabiata => true
| rigatoni, rigatoni => true
| sauce, sauce => true
| tomato_puree, tomato_puree => true
| red_pepper, red_pepper => true
| garlic, garlic => true
| _, _ => false
end.

Lemma eq_foodP : Equality.axiom eq_food.
Proof.
case.
- case; try by constructor 2.
  by constructor 1.
- case; try by constructor 2.
  by constructor 1.
- case; try by constructor 2.
  by constructor 1.
- case; try by constructor 2.
  by constructor 1.
- case; try by constructor 2.
  by constructor 1.
- case; try by constructor 2.
  by constructor 1.
Defined.

Definition food_eqMixin :=
  Eval hnf in EqMixin eq_foodP.
Canonical food_eqType :=
  Eval hnf in EqType food food_eqMixin.

Definition food_pickle f :=
match f with
| rigatoni_arrabiata => 0
| rigatoni => 1
| sauce => 2
| tomato_puree => 3
| red_pepper => 4
| garlic => 5
end.

Definition food_unpickle n :=
match n with
| 0 => Some rigatoni_arrabiata
| 1 => Some rigatoni
| 2 => Some sauce
| 3 => Some tomato_puree
| 4 => Some red_pepper
| 5 => Some garlic
| _ => None
end.

Lemma food_pcancel : pcancel food_pickle food_unpickle.
Proof. by case. Defined.

Definition food_choiceMixin :=
  PcanChoiceMixin food_pcancel.
Canonical food_choiceType :=
  Eval hnf in ChoiceType food food_choiceMixin.

Definition food_countMixin :=
  CountMixin food_pcancel.
Canonical food_countType :=
  Eval hnf in CountType food food_countMixin.

Definition food_enum :=
[:: rigatoni_arrabiata; rigatoni; sauce; tomato_puree; red_pepper; garlic].

Lemma food_finite : Finite.axiom food_enum.
Proof. by case. Defined.

Definition food_finMixin :=
  FinMixin food_finite.
Canonical food_finType :=
  Eval hnf in FinType food food_finMixin.

Definition food_depends f :=
match f with
| rigatoni_arrabiata => [:: rigatoni; sauce]
| rigatoni => [::]
| sauce => [:: tomato_puree; red_pepper; garlic]
| tomato_puree => [::]
| red_pepper => [::]
| garlic => [::]
end.

Definition food_rel := grel food_depends.

Definition food_acyclic := kosaraju_acyclic food_depends.

Notation food_rel_rev := [rel x y | food_rel y x].

Definition food_rev_impacted := impacted food_rel_rev.
