(** This file defines the countable types. There is some liberty in
    the notion of countable in a constructive setting. In this file we
    choose countable types to be equipped with a retraction into the
    natural number (which, because of [ConstructiveEpsilon], is
    equivalent to a surjection from natural number and decidable
    equality). Decidability of equality plays an important role in the
    design of concrete quotients of countable types, both to lift
    [ConstructiveEpsilon] and to define quotients.

    A type [A] is called countable if [option A] is a retract of the
    natural numbers. When [A] is inhabited, then it is equivalent to a
    retraction of [A] into the natural numbers, but this definition
    also includes the empty set.

    Being countable is defined here as a type class, making the
    hypothesis that the chosen retraction is unlikely to be tractable
    (few of the instances defined in this file are) and that it's not
    to be used in a real program, where some control will be
    needed. *)

Require Import FinSet.Quotients.Retract.
Require Import Coq.NArith.NArith.


Class Countable A := countable : Retract nat (option A).

(** We also use an inhabitation type class, which will help avoid the
    [option] type in our calculation. *)
Class Inhabited A := inhabitant : A.

Definition to_nat {A} {_:Countable A} {_:Inhabited A} : A -> nat :=
  (retract_nat_inh countable inhabitant).(inj).
Definition of_nat {A} {_:Countable A} {_:Inhabited A} : nat -> A :=
  (retract_nat_inh countable inhabitant).(proj).

Lemma nat_retract A {_:Countable A} {_:Inhabited A} : forall x, of_nat (to_nat x) = x.
Proof.
  intros *. unfold of_nat, to_nat.
  now rewrite !retract.
Qed.

(** The typical way of proving that a type is countable is to exhibit
    a retraction towards a known countable type. *)
Program Definition countable_of_retract {A B} {_:Countable A} (r:Retract A B) : Countable B :=
  Retract.compose countable (Retract.opt_lift r).


(** * Countable instances *)

Instance countable_nat : Countable nat := retract_nat_opt Retract.id.
Instance countable_n   : Countable N := retract_nat_opt retract_nat_N.

Program Instance countable_empty_set : Countable Empty_set := {|
  inj x := 0;
  proj x := None
|}.
Next Obligation.
  intros [ [] | ].
  reflexivity.
Qed.
