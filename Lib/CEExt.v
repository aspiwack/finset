(** This file contains extensions of the [ConstructiveEpsilon] library
    of Coq. Primarily, this is about supporting the [DProp] library
    instead of explicit usage of [sumbool]. In addition this files
    provides additional lemmas about [ConstructiveEpsilon], in
    particular the extensionality of the choice procedure. *)


Require Coq.Logic.ConstructiveEpsilon.
Require Import FinSet.Lib.DProp.
Import Coq.Classes.Morphisms.

(** * A [DProp] interface *)

Section Choice.

Context {A:Type} (to_nat:A->nat) (of_nat:nat->A).
Context (retract:forall x, of_nat(to_nat x) = x).
Context(P:A->DProp).

(** Indefinite description for inhabited countable types. *)
Definition choice : (exists x, P x) -> { x:A | P x } :=
  ConstructiveEpsilon.constructive_indefinite_ground_description
            A to_nat of_nat retract P (fun x=> dec_alt (P x))
.

(** [choose] is a choice operator on every inhabited countable
    type. The main result in this file is that [choose] only depends
    on the extension of [P] (and the encoding). *)
Definition choose (h:exists x, P x) : A := proj1_sig (choice h).

Lemma choose_spec : forall h, P (choose h).
Proof.
  intros **. unfold choose.
  apply proj2_sig.
Qed.

End Choice.
Arguments choose_spec A to_nat of_nat retract P h : clear implicits.


(** * [choose] is extensional *)

Lemma linear_search_ext : forall P P_dec Q Q_dec n w v, (forall x, P x <-> Q x) ->
         proj1_sig (ConstructiveEpsilon.linear_search P P_dec n w) =
         proj1_sig (ConstructiveEpsilon.linear_search Q Q_dec n v).
Proof.
  intros until Q_dec. fix 2. intros n [h₀ | h₁] [h₀'|h₁'] h.
  all:cbn.
  all:destruct (P_dec n) as [p|np], (Q_dec n) as [q|nq];cbn.
  all:try reflexivity.
  all:try solve[rewrite h in p; destruct (nq p)].
  all:try solve[rewrite <- h in q; destruct (np q)].
  all:apply linear_search_ext. all: assumption.
Qed.


Section ChoiceExt.

Context (A:Type).

Local Notation "'Π' x y ':' R ',' S" := (respectful_hetero _ _ _ _ R%signature (fun x y => S)%signature) (at level 200, x ident, y ident).

Lemma choose_ext : Proper
  (Π to_nat₁ to_nat₂ : eq==>eq,
   Π of_nat₁ of_nat₂ : eq==>eq,
   Π _ _ : (fun _ _ => True),
   Π P P' : eq==>eq_dprop,
   Π _ _ : (fun _ _ => True),
   @eq A) choose.
Proof.
  unfold Proper, respectful_hetero, respectful.
  intros to_nat₁ to_nat₂ h_to_nat
         of_nat₁ of_nat₂ h_of_nat
         retract₁ retract₂ _
         P P' hp
         [x hx] [y hy] _.
  unfold choose,choice,
         ConstructiveEpsilon.constructive_indefinite_ground_description.
  cbn.
  unfold ConstructiveEpsilon.P', ConstructiveEpsilon.P'_decidable.
  match goal with
  | |- proj1_sig (let (_,_) := ?X in _) = proj1_sig (let (_,_) := ?Y in _) =>
    enough (proj1_sig X = proj1_sig Y) as h₀
                  by (destruct X,Y;cbn in h₀|-*;now eauto)
  end.
  apply linear_search_ext. intros **.
  apply hp. eauto.
Qed.

End ChoiceExt.