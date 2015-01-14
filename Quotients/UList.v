(** This file defines a high level interface for lists with no
    duplicates of types with decidable equality. They form a retract
    of lists. *)

Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import FinSet.Lib.DProp.
Require Import FinSet.Lib.ListSet.
Require Import FinSet.Quotients.Retract.
Require Import FinSet.Quotients.Countable.

Definition UList (A:Type) (R:A->A->DProp) : Type :=
  { l:list A | Canonize (nodup R l) }.
Arguments UList : simpl never.

Program Definition ulist {A} {R:A->A->DProp} :
 Retract (list A) (UList A R) := {|
  inj l := l;
  proj l := deduplicate R l
|}.
Next Obligation.
  intros **. rewrite canonize_spec.
  apply deduplicate_nodup.
Qed.
Next Obligation.
  intros A R [l hl]. cbn.
  apply dsigma_ext. cbn. rewrite canonize_spec in hl.
  induction l as [|a l ihl].
  { easy. }
  cbn -[DNot]. f_equal.
  cbn -[mem_list] in hl. destruct hl as [hl₁ hl₂].
  rewrite ihl; cycle 1.
  { assumption. }
  clear ihl.
  induction l as [|b l ihl].
  { easy. }
  cbn -[DNot]. destruct dec as [hr|hr];cycle 1.
  { cbn -[mem_list] in hr.
    rewrite mem_list_cons in hl₂. cbn in hl₂.
    destruct hl₂ as [hl₂ _].
    contradictory. }
  f_equal.
  apply ihl.
  + apply hl₁.
  + rewrite mem_list_cons in hl₂. apply hl₂.
Qed.

Lemma ulist_ext A R :
  forall l₁ l₂:UList A R, ulist.(inj) l₁ = ulist.(inj) l₂ -> l₁ = l₂.
Proof. apply dsigma_ext. Qed.

Lemma ulist_nodup A R : forall l:UList A R, nodup R (ulist.(inj) l).
Proof.
  intros [l hl]. cbn.
  now (rewrite canonize_spec in hl).
Qed.

Lemma ulist_eq_set A (R:A->A->DProp) (e:Equivalence R) :
  forall l:list A, eq_set_list R ((ulist (R:=R)).(inj) (ulist.(proj) l)) l.
Proof.
  intros l. cbn [inj proj ulist proj1_sig].
  now rewrite <- deduplicate_eq_set_list.
Qed.


(** * Set equality *)

Definition eq_set_ulist {A} R (l₁ l₂:UList A R) : DProp :=
  eq_set_list R (ulist.(inj) l₁) (ulist.(inj) l₂).

Instance eq_set_eq A (R:A->A->DProp) :
  Equivalence R -> Equivalence (eq_set_ulist R).
Proof.
  intros e. split. all:unfold Reflexive,Symmetric,Transitive,eq_set_ulist.
  + intros **. reflexivity.
  + intros **. symmetry. assumption.
  + intros **. etransitivity. all:eassumption.
Qed.

Instance ulist_proper A (R:A->A->DProp) (e:Equivalence R) :
  Proper (eq_set_ulist R ==> eq_set_list R) ulist.(inj).
Proof.
  unfold Proper, respectful, eq_set_ulist.
  easy.
Qed.

(** * Instances *)

Instance ulist_countable A R (_:Countable A) : Countable (UList A R) :=
  countable_of_retract ulist.

Instance ulist_inhabited A R : Inhabited (UList A R) := ulist.(proj) nil.