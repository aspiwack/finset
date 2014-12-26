(** In this file we define concrete quotients in the style of Cyril
    Cohen. The central remark is that for countable types (or, for
    that matter any type supporting constructive indefinite
    description and having decidable equality, which is "almost" the
    same) quotients by decidable equivalence relations can be
    constructed using only the native equality of Coq. These quotients
    have the pleasant additional property of being retracts of the
    original type. *)

Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import FinSet.Lib.DProp.
Require Import FinSet.Quotients.Countable.
Require Import FinSet.Quotients.Retract.

(** The quotient of [A] by [R] maps [x] to the canonical
    representative of the equivalence class [R x] (which is given by
    definite description). The definition of [Quotient R] requires
    that [R] is reflexive to ensure that [R x] is non-empty, of
    course, it is only really useful when [R] is an
    equivalence. Indeed, symmetry and transitivity will ensure that [R
    x] and [R y] are equivalent by [R x y], which, by extensionality
    of [choose] will ensure the canonical representative of [R x] and
    [R y] are indeed equal. The use of [Canonize] in the definition
    makes it so that extensional equality on [Quotient R] is Coq's
    primitive equality. *)
Program Definition Quotient {A} {_:Countable A} (R:A->A->DProp) {_:Reflexive R} : Type :=
  { x:A | Canonize (eq_countable (choose (R x) _) x) }.

Program Definition quotient {A} {_:Countable A} (R:A->A->DProp) {_:Equivalence R} :
      Retract A (Quotient R) := {|
  inj  x := x;
  proj x := choose (R x) _
|}.
Next Obligation.
  intros **.
  now eexists.
Defined.
Next Obligation.
  intros **.
  apply canonize_spec. cbn.
  apply choose_ext. all:[>unfold respectful|trivial].
  intros y ? <-. cbn.
  pose proof (choose_spec _ _ (R x)) as <-. (* The one (implicit) use of symmetry and transitivity. *)
  reflexivity.
Qed.
Next Obligation.
  intros A ? R ? [x hx]. cbn.
  apply EqdepFacts.eq_dep_eq_sig, EqdepFacts.eq_dep1_dep.
  refine (EqdepFacts.eq_dep1_intro _ _ _ _ _ _ _ _); cycle 1.
  { apply irrelevant_canonize. }
  rewrite canonize_spec in hx. cbn in hx.
  symmetry. exact hx.
Qed.


(** * Universal property of quotients *)

Lemma universal A (_:Countable A) (R:A->A->DProp) (_:Equivalence R) :
  forall x, R ((quotient R).(inj) ((quotient R).(proj) x)) x.
Proof.
  intros x. cbn. symmetry.
  apply choose_spec.
Qed.

Instance proj_proper A (_:Countable A) (R:A->A->DProp) (_:Equivalence R) :
  Proper (R==>eq) (quotient R).(proj).
Proof.
  intros x y hr. cbn.
  apply EqdepFacts.eq_dep_eq_sig, EqdepFacts.eq_dep1_dep.
  refine (EqdepFacts.eq_dep1_intro _ _ _ _ _ _ _ _); cycle 1.
  { apply irrelevant_canonize. }
  apply choose_ext;[>|trivial]. intros z ? <-. cbn.
  rewrite hr. reflexivity.
Qed.


(** * Extentionality of quotient equality *)

Lemma quotient_ext A (_:Countable A)
      (R:A->A->DProp) (_:Equivalence R) (u v: Quotient R):
  R ((quotient R).(inj) u) ((quotient R).(inj) v) -> u=v.
Proof.
  intros h.
  rewrite <- retract with (r:=quotient R).
  rewrite <- h.
  rewrite retract with (r:=quotient R).
  reflexivity.
Qed.


(** * Quotients are countable *)

Instance quotient_countable A (_:Countable A) (R:A->A->DProp) (_:Equivalence R)
     : Countable (Quotient R) :=
  Retract.compose countable (Retract.opt_lift (quotient R)).

Instance quotient_inhabited A (_:Countable A) (_:Inhabited A) (R:A->A->DProp) (_:Equivalence R)
     : Inhabited (Quotient R) :=
  (quotient R).(proj) inhabitant.