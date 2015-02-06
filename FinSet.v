(** Finite sets of countable types can be be defined such that
    extensional set equality is strict equality (using Cyril Cohen's
    quotient construction). *)

Require Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import FinSet.Lib.ListSet.
Require Import FinSet.Quotients.UList.
Require Import FinSet.Lib.DProp.
Require Import FinSet.Quotients.Countable.
Require Import FinSet.Quotients.Retract.
Require Import FinSet.Quotients.Quotient.


Definition T (A:Type) {_:Countable A} : Type := Quotient (eq_set_ulist eq_countable).

Instance set_countable (A:Type) {_:Countable A} : Countable (T A).
Proof. typeclasses eauto. Defined.

(** * Low level interface *)

Definition listset {A} {_:Countable A} : Retract (list A) (T A) :=
  Retract.compose ulist (quotient (eq_set_ulist eq_countable)).

Lemma set_quotient A (_:Countable A) : forall x,
  eq_set_list eq_countable (listset.(inj) (listset.(proj) x)) x.
Proof.
  intros x. unfold listset,compose. cbn [inj proj].
  rewrite Quotient.universal.
  apply ulist_eq_set.
  { typeclasses eauto. }
Qed.

Lemma set_nodup A (_:Countable A) :
  forall x, nodup eq_countable (listset.(inj) x).
Proof.
  intros x. unfold listset,compose. cbn [inj].
  apply ulist_nodup.
Qed.
  

(** * Quantifiers *)

Section Quantifiers.

 Context {A} {CA:Countable A}.

 (** Set membership. A decidable proposition. *)
 Definition mem (x:A) (u:T A) : DProp := mem_list eq_countable x (listset.(inj) u).
 Local Notation "x ∈ u" := (mem x u) (at level 10).

 Lemma mem_spec x u : x∈u <-> mem_list eq_countable x (listset.(inj) u).
 Proof.
   unfold mem.
   apply mem_eq_set_list.
   { typeclasses eauto. }
   reflexivity.
 Qed.

 Lemma mem_spec_in x u : x∈u <-> List.In x (listset.(inj) u).
 Proof.
   rewrite mem_spec. cbn.
   now rewrite <- in_is_mem.
 Qed.

 Global Instance in_eq_set : Proper (eq==>eq_set_list eq_countable==>iff) (@List.In A).
 Proof.
   intros x ? <- l₁ l₂ hl.
   rewrite !in_is_mem.
   now refine (mem_eq_set_list A _ _ _ _ _ _).
 Qed.

 (** Bounded existential quantifier on decidable propositions. *)
 Program Definition dexists (u:T A) (P:A->DProp) : DProp := {|
   Holds := exists x, x∈u /\ P x ;
   Denies := forall x, x∈u -> DNot (P x) ;
   dec := dec_lift (dec (ListSet.dexists P u))
 |}.
 Next Obligation.
   intros * [m h].
   exists (of_mem m).
   split; cycle 1.
   { exact h. }
   unfold mem,mem_list. cbn.
   now exists m.
 Qed.
 Next Obligation.
   intros * h x hx. cbn in h.
   set (m := mem_of_mem_list eq_countable (listset.(inj) u) x hx).
   specialize (h m). subst m.
   pose proof (mem_of_mem_list_spec _ _ _ x hx) as ->.
   exact h.
 Qed.
 Next Obligation.
   intros * [x [p h]] n.
   eauto using contradictory.
 Qed.

 (** Bounded existential quantifier on decidable propositions. *)
 Program Definition dforall (u:T A) (P:A->DProp) : DProp :=
   DNot (dexists u (fun x => DNot (P x))).

End Quantifiers.

Arguments mem : simpl never.
Arguments mem_spec : clear implicits.
Arguments mem_spec_in : clear implicits.

Module MembershipNotation.

 Notation "x ∈ u" := (mem x u) (at level 10).

End MembershipNotation.
Import MembershipNotation.


(** * Set-theoretical operations *)


Import List.ListNotations.
Local Open Scope list_scope.


(** ** Generic set builders *)

Section SetOperations.

 Context {A} {CA:Countable A}.
 Context {B} {CB:Countable B}.

 Definition empty : T A := listset.(proj) [].

 Lemma empty_spec : forall x, ~x∈empty.
 Proof.
   intros x n. unfold empty in n.
   rewrite mem_spec, set_quotient in n.
   eauto.
 Qed.

 Lemma empty_spec_iff : forall x, x∈empty <-> False.
 Proof.
   intros x.
   split.
   + apply empty_spec.
   + intros [].
 Qed.

 Definition singleton (a:A) : T A := listset.(proj) [a].

 Lemma singleton_spec : forall x a, x∈(singleton a) <-> x=a.
 Proof.
   intros *. unfold singleton. rewrite mem_spec_in, set_quotient.
   cbn. intuition.
 Qed.

 Corollary singleton_self : forall a, a∈(singleton a).
 Proof.
   intros a.
   now rewrite singleton_spec.
 Qed.

 Definition union (u₁ u₂:T A) : T A := listset.(proj) (listset.(inj) u₁++ listset.(inj) u₂).

 Lemma union_spec : forall x u₁ u₂, x∈(union u₁ u₂) <-> x∈u₁ \/ x∈u₂.
 Proof.
   intros *. unfold union.
   rewrite mem_spec,set_quotient.
   rewrite mem_list_app. unfold mem.
   reflexivity.
 Qed.

 (** Union over a finite set of finite sets. Together with [singleton]
     forms a monad (restricted to countable types). This monad allows
     to build sets by comprehension. *)
 Definition Union (u:T A) (F:A->T B) : T B :=
   listset.(proj) (List.flat_map (fun x => listset.(inj) (F x)) (listset.(inj) u)).

 Lemma Union_spec u F x : x ∈ (Union u F) <-> exists y, y∈u /\ x ∈ (F y).
 Proof.
   unfold Union. rewrite mem_spec_in,  set_quotient.
   rewrite List.in_flat_map.
   split.
   + intros [a [ha₁ ha₂]]. eexists.
     rewrite !mem_spec_in.
     intuition eauto.
   + intros [a [ha₁ ha₂]].
     rewrite mem_spec_in in ha₁. rewrite mem_spec_in in ha₂.
     intuition eauto.
 Qed.

End SetOperations.

Arguments empty : simpl never.
Arguments singleton : simpl never.
Arguments union : simpl never.
Arguments Union : simpl never.
Arguments empty_spec : clear implicits.
Arguments empty_spec_iff : clear implicits.
Arguments singleton_spec : clear implicits.
Arguments union_spec : clear implicits.
Arguments Union_spec : clear implicits.


(** [guard P] is the last component of the comprehension syntax. It
    lifts a proposition to a subset of the singleton type.  It is used
    to implement the "such that" clause of comprehension. *)
Definition guard (P:DProp) : T unit :=
  if (dec P) then (listset).(proj) [tt] else empty.
Arguments guard : simpl never.

Lemma guard_spec_tt P : tt∈(guard P) <-> P.
Proof.
  unfold guard.
  destruct (dec P) as [p|n].
  + rewrite mem_spec, set_quotient.
    ddecide (mem_list eq_countable tt [tt]) h. cbn.
    intuition.
  + generalize (empty_spec _ _ tt).
    intuition contradictory.
Qed.

Lemma guard_spec P : forall x, x∈(guard P) <-> P.
Proof.
  intros []. apply guard_spec_tt.
Qed.

Lemma guard_Union A (_:Countable A) P (u:T A) :
  forall x, x∈(Union (guard P) (fun _ => u)) <-> x∈u /\ P.
Proof.
  intros x.
  rewrite Union_spec.
  split.
  + intros [[] [p h]].
    rewrite guard_spec in p. tauto.
  + intros ?. exists tt.
    rewrite guard_spec. tauto.
Qed.

(** ** Notations for comprehension *)

Module ComprehensionNotations.

 Delimit Scope comprehension with comprehension.

 Notation "u '⍪' x '∈' v" := (Union v (fun x => u))
       (at level 50, x ident, v at level 20, right associativity) : comprehension.
 Notation "u 'ﬆ' p" := (Union (guard p) (fun _ => u))
       (at level 50, p at level 20, right associativity) : comprehension.
 Notation "a '\' " := (singleton a) (at level 20) : comprehension.
 Notation "'⦃' x '⦄'" := (x%comprehension).


End ComprehensionNotations.

Import ComprehensionNotations.

(** ** Derived operations *)

Definition inter {A} {_:Countable A} (u₁ u₂:T A) : T A := ⦃ x \ ﬆ x∈u₂ ⍪ x∈u₁  ⦄.
Arguments inter : simpl never.

Lemma inter_spec A (_:Countable A) (u₁ u₂:T A) :
  forall x, x ∈ (inter u₁ u₂) <-> x∈u₁ /\ x∈u₂.
Proof.
  intros x. unfold inter.
  rewrite Union_spec.
  split.
  + intros [x' [h₁ h₂]].
    rewrite guard_Union,singleton_spec in h₂. destruct h₂ as [<- h₂].
    intuition.
  + intros [h₁ h₂].
    exists x.
    rewrite guard_Union,singleton_spec.
    intuition.
Qed.


(** * Extensionality *)

Definition subset {A} {_:Countable A} (u v:T A) : DProp := dforall u (fun x => x∈v).

Lemma double_inclusion A (_:Countable A) (u v:T A) :
  subset u v -> subset v u -> u = v.
Proof.
  intros h₁ h₂. cbn in *.
  apply quotient_ext. unfold mem in *. cbn in *.
  intuition eauto.
Qed.

Instance PreOrder A (_:Countable A) : PreOrder subset.
Proof.
  split.
  + unfold Reflexive. cbn. intuition eauto.
  + unfold Transitive. cbn. intuition eauto.
Qed.

Lemma set_ext A (_:Countable A) (u v:T A) : (forall x, x∈u <-> x∈v) -> u=v.
Proof.
  intros h.
  apply double_inclusion. all: cbn.
  all: eapply h.
Qed.


(** * Standard notations *)

Module SetNotations.

  Notation "∅"       := empty.
  Notation "u₁ ∪ u₂" := (union u₁ u₂) (at level 40, left associativity).
  Notation "u₁ ∩ u₂" := (inter u₁ u₂) (at level 40, left associativity).

  Notation "u ⊆ v"  := (subset u v)  (at level 70, no associativity).

End SetNotations.

Import SetNotations.


(** * Algebraic properties *)

Hint Rewrite union_spec inter_spec empty_spec_iff singleton_spec : set_simplify.
Hint Rewrite guard_Union Union_spec : set_simplify.

Ltac set_intuition :=
  intros **;
  apply set_ext; intros ?; autorewrite with set_simplify in *; intuition eauto.

Section Algebraic.

 Context (A:Type) (cA:Countable A).

 (** ** Equational laws *)

 Lemma union_assoc (v₁ v₂ v₃:T A) : v₁∪(v₂∪v₃) = (v₁∪v₂)∪v₃.
 Proof. set_intuition. Qed.

 Lemma union_empty_left_unit (v:T A) : ∅ ∪ v = v.
 Proof. set_intuition. Qed.

 Lemma union_empty_right_unit (v:T A) : v ∪ ∅ = v.
 Proof. set_intuition. Qed.

 Lemma union_commutative (v₁ v₂:T A) : v₁∪v₂ = v₂∪v₁.
 Proof. set_intuition. Qed.

 Lemma union_idempotent (v:T A) : v∪v = v.
 Proof. set_intuition. Qed.

 (** Note: intersection does not, in general, have a neutral
     element. Indeed, it would be a set with all the elements of the
     type, which is not necessarily finite. *)
 Lemma inter_assoc (u₁ u₂ u₃:T A) : u₁∩(u₂∩u₃) = (u₁∩u₂)∩u₃.
 Proof. set_intuition. Qed.

 Lemma inter_commutative (u₁ u₂:T A) : u₁∩u₂ = u₂∩u₁.
 Proof. set_intuition. Qed.

 Lemma inter_idempotent (u:T A) : u∩u = u.
 Proof. set_intuition. Qed.

 Lemma union_inter_distr (u₁ u₂ v:T A) : (u₁∩u₂)∪v = (u₁∪v) ∩ (u₂∪v).
 Proof. set_intuition. Qed.

 Lemma inter_union_distr (v₁ v₂ u:T A) : (v₁∪v₂)∩u = (v₁∩u)∪(v₂∩u).
 Proof. set_intuition. Qed.

 (** ** Order-related laws *)

 Lemma empty_bottom : forall u, ∅ ⊆ u.
 Proof.
   intros u x. cbn [DNot Holds Denies].
   autorewrite with set_simplify. tauto.
 Qed.

 Lemma union_sup (v₁ v₂:T A) : forall u, v₁∪v₂ ⊆ u <-> v₁⊆u /\ v₂⊆u.
 Proof.
   intros u. split.
   + intros h. split.
     all: intros x. all: cbn.
     all: specialize (h x). all: cbn in h.
     all:autorewrite with set_simplify in h.
     all:tauto.
   + intros [h₁ h₂] x. cbn.
     specialize (h₁ x); specialize (h₂ x). cbn in h₁,h₂.
     autorewrite with set_simplify.
     tauto.
 Qed.

 Lemma inter_inf (u₁ u₂:T A) : forall v, v ⊆ u₁∩u₂ <-> v⊆u₁ /\ v⊆u₂.
 Proof.
   intros v. split.
   + intros h. split.
     all: intros x. all: cbn.
     all: specialize (h x). all: cbn in h.
     all:autorewrite with set_simplify in h.
     all:tauto.
   + intros [h₁ h₂] x. cbn.
     specialize (h₁ x); specialize (h₂ x). cbn in h₁,h₂.
     autorewrite with set_simplify.
     tauto.
 Qed.

End Algebraic.


(** * Categorical combinators *)

(** Laws yet to prove: [map id u = u] and [map (f∘g) u = map f (map g u)]. *)
Definition map {A B} {_:Countable A} {_:Countable B} (f:A->B) (u:T A) : T B :=
  ⦃ f x \ ⍪ x∈u  ⦄.

(** Laws yet to prove: [join (singleton u) = u], [join (map singleton u) = u]
    and [join (join u) = join (map join u)]. *)
Definition join {A} {_:Countable A} (u:T (T A)) : T A :=
  ⦃ x \ ⍪ x∈y ⍪ y∈u  ⦄.


(** * Notations *)

Module Notations.
  Export MembershipNotation.
  Export SetNotations.
  Export ComprehensionNotations.
End Notations.