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

Require Import DProp.
Require FinSet.Lib.CEExt.
Require Import FinSet.Quotients.Retract.
Require Import Coq.NArith.NArith.

Import List.ListNotations.
Local Open Scope list_scope.


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

(** In some more advanced cases, we may need [B] to be lifted to
    provide a default element. *)
Program Definition countable_of_opt_retract
        {A B} {_:Countable A} (r:Retract A (option B)) : Countable B :=
  Retract.opt_compose countable r.

(** Countable types have decidable equality: it is sufficient to test
    the equality of their code. *)
Program Definition countable_eq_dec {A} {_:Countable A} (x y:A) : {x=y}+{x<>y} :=
  dec_lift (
      PeanoNat.Nat.eq_dec
        (countable.(inj) (Some x))
        (countable.(inj) (Some y)))
.
Next Obligation.
  intros * h.
  apply f_equal with (f:=countable.(proj)) in h.
  rewrite !retract in h.
  congruence.
Qed.
Next Obligation.
  intros * h.
  congruence.
Qed.

Program Definition eq_countable {A} {_:Countable A} (x y:A) : DProp := {|
  dec := countable_eq_dec x y
|}.

(** * Inhabited instances *)

Instance inhabited_unit : Inhabited unit := tt.
Instance inhabited_option A : Inhabited (option A) := None.
Instance inhabited_list   A : Inhabited (list   A) := [].

Instance inhabited_pair {A B} {_:Inhabited A} {_:Inhabited B} : Inhabited (A*B) :=
  (inhabitant,inhabitant).

Instance inhabited_sum_left  {A B} {_:Inhabited A} : Inhabited (A+B) := inl inhabitant.
Instance inhabited_sum_right {A B} {_:Inhabited B} : Inhabited (A+B) := inr inhabitant.


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

(** Lists of a countable type are countable. The essential component
    is [Retract.retract_N_list_nat]. This particular instance will be
    used to define most others. *)
Instance countable_list {A} {_:Countable A} : Countable (list A).
Proof.
  refine (countable_of_retract (A:=list nat) _).
  { exact (countable_of_retract retract_N_list_nat). }
  refine {| inj  := List.map (fun x => countable.(inj) (Some x));
            proj := List.flat_map (fun x => match countable.(proj) x with
                                            | Some x => [x]
                                            | None   => []
                                            end)
         |}.
  intros l.
  rewrite List.flat_map_concat_map, List.map_map.
  transitivity (List.concat (List.map (fun x => [x]) l)). all:cycle 1.
  { induction l as [ | a l hl ].
    + cbn. reflexivity.
    + cbn. rewrite hl. reflexivity. }
  f_equal.
  apply List.map_ext. intros x.
  now rewrite retract.
Defined.

Program Instance countable_unit : Countable unit :=
  countable_of_retract {|
      inj  x := [];
      proj x := tt
  |}
.
Next Obligation. now intros []. Qed.

(** This could be established using [Retract.retract_nat_opt]. But to
    demonstrate how lists can be used, we shall prefer a definition
    based on lists. *)
Program Instance countable_option {A} {_:Countable A} : Countable (option A) :=
   countable_of_retract {|
       inj  x := match x return _ with
                 | Some x => [x]
                 | None   => []
                 end;
       proj l := match l return _ with
                 | [x] => Some x
                 | []  => None
                 | _ => None
                 end
     |}.
Next Obligation.
  intros A ? [x|].
  all:reflexivity.
Qed.

Program Instance countable_pair {A B} {_:Countable A} {_:Countable B} : Countable (A*B) :=
  countable_of_opt_retract {|
      inj  x := match x return _ with
                | Some(a,b) => [to_nat (Some a);to_nat (Some b)]
                | None      => []
                end;
      proj l := match l return _ with
                | [] => None
                | [a;b] => match of_nat a , of_nat b return _ with
                           | Some a',Some b' => Some (a',b')
                           | _      ,_       => None
                           end
                | _ => None
                end
    |}.
Next Obligation.
  intros A B ? ? [[a b]|].
  + now rewrite !nat_retract.
  + reflexivity.
Qed.

Program Instance countable_sum {A B} {_:Countable A} {_:Countable B} : Countable (A+B) :=
  countable_of_opt_retract {|
      inj  x := match x return _ with
                | Some (inl a) => [0;to_nat (Some a)]
                | Some (inr b) => [1;to_nat (Some b)]
                | None         => []
                end;
      proj l := match l return _ with
                | []    => None
                | [0;a] => match of_nat a return _ with
                           | Some a' => Some (inl a')
                           | _ => None
                           end
                | [1;b] => match of_nat b return _ with
                           | Some b' => Some (inr b')
                           | _ => None
                           end
                | _ => None
                end
    |}.
Next Obligation.
  intros A B ? ? [[a|b]|].
  all:rewrite ?nat_retract.
  all: reflexivity.
Qed.


(** * Constructive indefinite description *)

(** The results of [CEExt] can be lifted to countable types. This
    liting is not quite the identity because of the extra [option] in
    the definition of countable types. *)

(** The main ingredient of the lifting is a lifting of (decidable)
    predicate to the option type, such that [{x:A|P x}] is isomorphic
    to [{x:option A|Liftp P x}]. *)

Definition Liftp {A} (P:A->DProp) : option A -> DProp := fun x =>
  match x with
  | Some a => P a
  | None   => DFalse
  end
.

Lemma Liftp_exists {A} {P:A->DProp} : (exists x, P x) -> exists x, Liftp P x.
Proof.
  intros [x h].
  now exists (Some x).
Qed.

Program Definition liftp_extract {A} {P:A->DProp} (x : {x|Liftp P x}) : {x|P x} :=
  match x return Liftp P x -> {x|P x} with
  | Some x => fun h => x
  | None => fun h => _
  end _
.
Next Obligation.
  cbn.
  intros ? ? ? [].
Qed.
Next Obligation.
  intros **.
  apply proj2_sig.
Defined.

Lemma liftp_extract_ext A (P:A->DProp) P' (x:{x|Liftp P x}) (y:{y|Liftp P' y}) :
  proj1_sig x = proj1_sig y -> proj1_sig (liftp_extract x) = proj1_sig (liftp_extract y).
Proof.
  destruct x as [[x|] hx], y as [[y|] hy]. all:cbn in *.
  all:try contradiction.
  congruence.
Qed.

Section Choice.

 Context {A} {cA:Countable A}.
 Context (P:A->DProp).

 Definition choice (h:exists x, P x) : {x|P x} :=
   liftp_extract (
       CEExt.choice
         countable.(inj)
         countable.(proj)
         countable.(retract _ _)
         (Liftp P)
         (Liftp_exists h))
 .

 Definition choose (h:exists x, P x) : A := proj1_sig (choice h).

 Lemma choose_spec : forall h, P (choose h).
 Proof.
   intros **. unfold choose.
   apply proj2_sig.
 Qed.

End Choice.
Arguments choose_spec A cA P h : clear implicits.


Section ChoiceExt.

 Import Morphisms.

 Context (A:Type) (cA:Countable A).

 Local Notation "'Π' x y ':' R ',' S" := (respectful_hetero _ _ _ _ R%signature (fun x y => S)%signature) (at level 200, x ident, y ident).

 Lemma choose_ext : Proper (Π P P' : eq==>eq_dprop, Π _ _:(fun _ _ => True), @eq A) choose.
 Proof.
   unfold Proper,respectful_hetero,respectful,choose,choice.
   intros P P' hP eP eP' _.
   apply liftp_extract_ext.
   apply CEExt.choose_ext. all:unfold respectful.
   all: eauto.
   congruence.
   { intros [x|] [y|] [=]. all:subst;cbn in hP|-*.
     + eauto.
     + tauto. }
 Qed.

End ChoiceExt.