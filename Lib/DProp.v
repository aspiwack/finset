Require Coq.Logic.EqdepFacts.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Coq.Setoids.Setoid.
Require Coq.Bool.Sumbool.

Record DProp := {
  Holds :> Prop;
  Denies : Prop;
  dec :> { Holds } + { Denies };
  contradictory : Holds -> Denies -> False
}.
Arguments contradictory {_} _ _.

(** * Basic properties and tactics *)

Lemma denies_spec : forall (A:DProp), Denies A <-> ~A.
Proof.
  intros A.
  split.
  + intros n p.
    exact (contradictory p n).
  + destruct (dec A) as [p | n];cycle 1.
    { easy. }
    contradiction.
Qed.

Ltac contradictory :=
  solve [
      contradiction |
      elimtype False ; eauto using contradictory
  ]
.

(* arnaud: this should not be done by default when importing DProp *)
Obligation Tactic :=
  try solve [intuition eauto using contradictory].

(** This should probably in Coq's [sumbool] files. This notation
    coerces a proof [p:{A}+{B}] into a proof of [{A'}+{B'}] with the
    proof obligations [A->A'] and [B->B']. *)
Notation dec_lift p := (match p return _ with left h => left _ | right n => right _ end).

(** [DProp] are decidable propositions in the usual sense. *)
Program Definition dec_alt (P:DProp) : {P}+{~P} := dec_lift (dec P).

(** * Equality *)

(** In a decidable proposition, the [dec] field is "proof irrelevant"
    if the propositions are. In particular if equivalent propositions
    are equal (propositional extensionality, which happens to imply
    proof irrelevance of propositions), then Coq's equality is the
    appropriate one for [DProp]. *)
Remark dec_irrelevant : (forall (P:Prop) (x y:P), x=y) -> forall P Q (a b:{P}+{Q}), (P -> Q -> False) -> a=b.
Proof.
  intros irr P Q [a|a] [b|b] h.
  all:try solve[destruct (h a b)|destruct (h b a)].
  all:now f_equal.
Qed.

(** In vanilla Coq, the appropriate notion of equality for [DProp] is
    equivalence of the [Holds] field (equivalently, of the [Denies]
    field). *)
Definition eq_dprop : DProp -> DProp -> Prop := iff.
Arguments eq_dprop P Q /.

Instance eq_dprop_eq : Equivalence eq_dprop.
Proof.
  unfold eq_dprop.
  split.
  + intros x.
    reflexivity.
  + intros x y h.
    symmetry. assumption.
  + intros x y z h₁ h₂.
    etransitivity. all:eassumption.
Qed.


(** The rewrite tactics needs some instances defined to work properly
    with strongly decidable propositions as drop-in replacement of
    regular propositions. Following the setoid rewrite library in
    [Coq.Classes.RelationClasses], there should be a series of lemma,
    but as part of this library, we shall be content with the case of
    equivalence relations (which is derived from more basic lemmas in
    the case of regular propositions). *)
Instance dprop_proper A (R:A->A->DProp) (_:Equivalence R) :
  Proper (R ==> R ==> eq_dprop) R.
Proof.
  intros x y h₁ z w h₂. unfold eq_dprop.
  split.
  + intros h₃.
    etransitivity.
    * symmetry; eassumption.
    * etransitivity. all:eassumption.
  + intros h₃.
    etransitivity.
    * eassumption.
    * etransitivity. all:[>|symmetry]. all:eassumption.
Qed.

Instance holds_proper : Proper (eq_dprop==>iff) Holds.
Proof.
  intros p q h. exact h.
Qed.

Instance denies_proper : Proper (eq_dprop==>iff) Denies.
Proof.
  intros p q h. unfold eq_dprop in h.
  now rewrite !denies_spec,h.
Qed.


(** * Connectives *)

Program Definition DTrue : DProp := {|
  Holds := True ;
  Denies := False ;
  dec := left I
|}.

Program Definition DFalse : DProp := {|
  Holds := False ;
  Denies := True ;
  dec := right I
|}.

Program Definition DAnd (A B:DProp) : DProp := {|
  dec := Sumbool.sumbool_and _ _ _ _ (dec A) (dec B)
|}.
Notation "A && B" := (DAnd A B).

Program Definition DOr (A B:DProp) : DProp := {|
  dec := Sumbool.sumbool_or _ _ _ _ (dec A) (dec B)
|}.
Notation "A || B" := (DOr A B).

(** Notice that [Holds (DNot (DNot A))] is convertible to [Holds A]. *)
Program Definition DNot (A:DProp) : DProp := {|
  dec := Sumbool.sumbool_not _ _ (dec A)
|}.

Lemma dnot_spec : forall A, DNot A <-> ~A.
Proof.
  apply denies_spec.
Qed.


(** * Proof irrelevance *)

(** [DProp]-s are not proof irrelevant in general (they are if all
    propositions are proof irrelevant). But there is an equivalent
    proposition which is proof irrelevant. *)
Definition Canonize (P:DProp) : Prop := if (dec P) then True else False.

Lemma canonize_spec (P:DProp) : Canonize P <-> P.
Proof.
  unfold Canonize.
  destruct (dec P).
  + tauto.
  + rewrite denies_spec in d.
    tauto.
Qed.

Lemma irrelevant_canonize (P:DProp) : forall x y:Canonize P, x=y.
Proof.
  unfold Canonize. destruct (dec P).
  + intros [] []. reflexivity.
  + intros [].
Qed.

(** * Booleans *)

(** An alternative coercion from booleans to proposition with respect
    to those in the standard library ([if b then True else False] and
    [b=true]). All three definitions are equivalent, and give rise to
    proof irrelevant propositions. *)
Inductive Is_true : bool -> Prop :=
  | true_is_true : Is_true true.

Definition elim_is_true_false A (f:Is_true false) : A :=
  match f with end.

(** This proof is a simplified variant of Hedberg's proof of
    irrelevance of decidable equality. *)
Remark irrelevant_is_true : forall b (x y:Is_true b), x = y.
(* begin show *)
Proof.
  set (ν := fun b =>
              match b with
              | true => fun _ => true_is_true
              | false => elim_is_true_false _
              end).
  intros *.
  transitivity (ν b x).
  + destruct x. reflexivity.
  + destruct y. reflexivity.
Qed.
(* end show *)

(** [Is_true b] is, of course, a decidable proposition. We declare it
    as an implicit coercion. *)
Program Definition dprop_of_bool (b:bool) : DProp := {| Holds := Is_true b ; Denies := ~Is_true b |}.
Next Obligation.
  destruct b.
  + left. exact true_is_true.
  + right. intros h.
    apply elim_is_true_false.
    exact h.
Defined.
Arguments dprop_of_bool_obligation_1 _ /.

Coercion dprop_of_bool : bool >-> DProp.

(** * Subset types *)

Lemma dsigma_ext A (P:A->DProp) :
  forall (x y:{x:A | Canonize (P x)}), proj1_sig x = proj1_sig y -> x = y.
Proof.
  intros [x hx] [y hy] h. cbn in *.
  apply EqdepFacts.eq_dep_eq_sig, EqdepFacts.eq_dep1_dep.
  refine (EqdepFacts.eq_dep1_intro _ _ _ _ _ _ _ _); cycle 1.
  { apply irrelevant_canonize. }
  auto.
Qed.
  

(** * Tactics *)

(** [ddecide t h] simplifies a decidable proposition using its
    decision procedure. Fails if [t] doesn't evaluate to a
    value. Creates an hypothesis named [h] with the statement that the
    decision proved. *)
Ltac ddecide t h :=
  let t' := constr:(dec t) in
  let t'' := eval cbn in t' in
  match t'' with
  | left ?p => pose proof p as h
  | right ?n => pose proof n as h
  end
.