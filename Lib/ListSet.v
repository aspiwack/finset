(** Using [DProp] to implement the decidable set-equality of
    lists. This is certainly not the most minimal implementation, as
    most of it could be lifted from Coq's standard library. But it is
    very self-contained, and was rather fun to write. *)

Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import FinSet.Lib.DProp.


(** * Inductive member predicate *)

(** The point of this predicate is to avoid using full-blown equality
    to define members. Indeed, the indices are patterns, which can be
    handled by well-crafted return predicates of pattern matching. *)
Inductive Mem {A:Type} : list A -> Type :=
| head : forall x {l}, Mem (x::l)
| tail : forall {x l}, Mem l -> Mem (x::l)
.

Definition no_mem_empty A : forall B, @Mem A [] -> B :=
  fun B c => match c with end.

Ltac use_no_mem_empty :=
  lazymatch goal with
  | h:@Mem _ [] |- _ => eapply no_mem_empty; exact h
  end.

Hint Extern 1 => use_no_mem_empty.

Fixpoint of_mem {A} {l:list A} (m:Mem l) : A :=
  match m with
  | head x => x
  | tail m' => of_mem m'
  end
.


(** The members of a list are thoses [x] such that [In x l]. It will
    give the appropriate glue when we use membership predicates and
    equality to specify operations. *)
Lemma in_is_mem A (l:list A) (x:A) : In x l <-> exists m:Mem l, x=of_mem m.
Proof.
  induction l as [|a l hl].
  + cbn. split.
    * intuition.
    * intros [? _]. contradictory.
  + cbn. split.
    * intros [<-|h].
      - now exists (head a).
      - apply hl in h. destruct h as [m h].
        now exists (tail m).
    * intros [m ->]. revert hl.
      refine match m with head a => _ | tail m => _ end.
      - cbn. intuition.
      - cbn. intros hl.
        right.
        apply hl.
        now exists m.
Qed.


(** * Decidable quantifiers on lists members *)

Program Fixpoint exists_dec {A:Type} (P:A->DProp) (l:list A) : {exists x:Mem l, P (of_mem x)} + {forall x:Mem l, DNot (P (of_mem x))} :=
  match l return _ with
  | [] => right _
  | a::q => dec_lift (Sumbool.sumbool_or _ _ _ _ (P a) (exists_dec P q))
  end
.
Next Obligation.
  intros * _ * h.
  destruct h as [h|[m h]].
  + exists (head a). cbn.
    assumption.
  + exists (tail m). cbn.
    assumption.
Qed.
Next Obligation.
  intros * _ * h m. revert h.
  refine match m with
         | head x => _
         | tail m => _
         end.
  + intros h. cbn.
    apply h.
  + intros h. cbn.
    apply h.
Qed.

Program Definition dexists {A:Type} (P:A->DProp) (l:list A) : DProp := {|
  dec := exists_dec P l
|}.
Next Obligation.
  intros * [m he] hu.
  specialize (hu m).
  contradictory.
Qed.

Definition dforall {A:Type} (P:A->DProp) (l:list A) : DProp :=
  DNot (dexists (fun x=> DNot (P x)) l)
.


(** * Set-like decidable relations on lists *)

(** ** Decidable membership predicate *)

Definition mem_list {A:Type} (E:A->A->DProp) (x:A) :=
  dexists (E x).

Remark no_mem_list_empty A E x : forall B, @mem_list A E x [] -> B.
Proof.
  intros B c. elimtype False.
  destruct c as [c _].
  auto.
Qed.

Ltac use_no_mem_list_empty :=
  lazymatch goal with
  | h:Holds (@mem_list _ _ _ []) |- _ => eapply no_mem_list_empty; exact h
  end.

Hint Extern 1 => use_no_mem_list_empty.

Lemma mem_list_right {A:Type} (E:A->A->DProp) (x y:A) (l:list A) :
  mem_list E x l -> mem_list E x (y::l).
Proof.
  intros [m h].
  exists (tail m). cbn.
  assumption.
Qed.

Lemma mem_list_left {A:Type} (E:A->A->DProp) (x y:A) (l:list A) :
  E x y -> mem_list E x (y::l).
Proof.
  intros h. cbn.
  exists (head y). cbn.
  assumption.
Qed.

Corollary mem_list_cons {A:Type} (E:A->A->DProp) (x y:A) (l:list A) :
  eq_dprop (mem_list E x (y::l)) (E x y || mem_list E x l).
Proof.
  split; cycle 1.
  { intros [h|h].
    all:eauto using mem_list_right,mem_list_left. }
  intros [m h]. revert h.
  refine match m with head y' => _ | tail m' => _ end. all:cbn -[mem_list].
  + intuition.
  + intros hm. right.
    exists m'. assumption.
Qed.

Lemma mem_list_app {A:Type} (E:A->A->DProp) (x:A) (l₁ l₂:list A) :
  eq_dprop (mem_list E x (l₁++l₂)) (mem_list E x l₁ || mem_list E x l₂).
Proof.
  induction l₁ as [|y l₁ hl₁].
  + cbn [app]. cbn -[mem_list]. intuition.
  + cbn [app]. rewrite !mem_list_cons,hl₁.
    cbn -[mem_list]. intuition.
Qed.

Program Fixpoint mem_of_mem_list {A:Type} (E:A->A->DProp) (l:list A) (x:A) : mem_list E x l -> Mem l :=
  match l return mem_list E x l -> Mem l with
  | [] => fun h => _
  | a::q => fun h => if dec (E x a) then head a
                     else tail (mem_of_mem_list E q x _)
  end
.
Next Obligation.
  intros * _ a q x [m h₁] h₂. cbn in h₂|-*. revert h₁ h₂.
  refine match m with head y => _ | tail m' => _ end. all: intros h₁ h₂.
  + cbn in h₁. contradictory.
  + cbn in h₁.
    now exists m'.
Qed.

Lemma mem_of_mem_list_spec A (E:A->A->DProp) (l:list A) (x:A) (h:mem_list E x l) : E x (of_mem (mem_of_mem_list E l x h)).
Proof.
  induction l as [|a q hq].
  + elimtype False.
    now destruct h as [c _].
  + cbn -[mem_list]. destruct (dec (E x a)) as [p|n].
    * cbn. assumption.
    * cbn -[mem_list].
      apply hq.
Qed.

(** ** Inclusion and equivalence *)

Definition included_list {A:Type} (E:A->A->DProp) (l₁ l₂:list A) : DProp :=
  dforall (fun x => mem_list E x l₂) l₁.

Instance included_list_preorder A (E:A->A->DProp) :
     PreOrder E -> PreOrder (included_list E).
Proof.
  intros P.
  split.
  + intros l. cbn.
    intros m. exists m.
    reflexivity.
  + intros l₁ l₂ l₃ h₁ h₂.
    cbn in h₁,h₂|-*.
    intros m₁.
    specialize (h₁ m₁). destruct h₁ as [m₂ h₁].
    specialize (h₂ m₂). destruct h₂ as [m₃ h₂].
    exists m₃.
    etransitivity; eauto.
Qed.

Corollary mem_included_list A (E:A->A->DProp) (_:Transitive E) : forall x l₁ l₂,
   included_list E l₁ l₂ -> Basics.impl (mem_list E x l₁) (mem_list E x l₂).
Proof.
  intros * hi hm. cbn -[mem_list] in hi. cbn in hm.
  destruct hm as [m₁ hm]. specialize (hi m₁). cbn in hi.
  destruct hi as [m₂ hi]. cbn.
  exists m₂.
  etransitivity. all:eassumption.
Qed.

Definition eq_set_list {A:Type} (E:A->A->DProp) (l₁ l₂:list A) : DProp :=
  included_list E l₁ l₂ && included_list E l₂ l₁.

Instance equivalence_preorder A (R:A->A->Prop) (_:Equivalence R) : PreOrder R.
Proof.
  split.
  + apply Equivalence_Reflexive.
  + apply Equivalence_Transitive.
Qed.

Instance eq_set_list_eq A (E:A->A->DProp) :
     Equivalence E -> Equivalence (eq_set_list E).
Proof.
  intros EQ.
  split.
  + intros l.
    split. all:reflexivity.
  + intros l₁ l₂ h.
    split. all:apply h.
  + intros l₁ l₂ l₃ h₁ h₂.
    split.
    all:etransitivity. all:eapply h₁||eapply h₂.
Qed.

Corollary mem_eq_set_list A (E:A->A->DProp) (_:Transitive E): forall l₁ l₂ x,
  eq_set_list E l₁ l₂ -> (mem_list E x l₁ <-> mem_list E x l₂).
Proof.
  intros * [hi hr].
  split.
  + erewrite mem_included_list;[|try eassumption..].
    trivial.
  + erewrite mem_included_list;[|try eassumption..].
    trivial.
Qed.

Instance mem_eq_set_list_proper A (E:A->A->DProp) (_:Transitive E) :
  Proper (eq ==> eq_set_list E ==> eq_dprop) (mem_list E).
Proof.
  intros x ? <- l₁ l₂ hl. unfold eq_dprop.
  eauto using mem_eq_set_list.
Qed.


(** * List without duplicates *)

Fixpoint nodup {A} (R:A->A->DProp) (l:list A) : DProp :=
  match l with
  | [] => DTrue
  | a::l => nodup R l && DNot (mem_list R a l)
  end
.

Fixpoint deduplicate {A} (R:A->A->DProp) (l:list A) : list A :=
  match l with
  | [] => []
  | a::l =>
    let dl :=
      List.filter
        (fun x => if dec (DNot (R a x)) then true else false)
        (deduplicate R l)
    in
    a::dl
  end
.

Lemma filter_sub A R l (p:A->bool) :
  forall x, mem_list R x (filter p l) -> mem_list R x l.
Proof.
  induction l as [|a l hl].
  + cbn -[mem_list]. eauto.
  + cbn -[mem_list]. intros x. destruct (p a).
    * rewrite !mem_list_cons. cbn -[mem_list]. intuition.
    * eauto using mem_list_right.
Qed.

Lemma filter_nodup A R (l:list A) : forall p:A->bool,
  nodup R l -> nodup R (filter p l).
Proof.
  intros p.
  induction l as [|a l hl].
  + cbn. trivial.
  + cbn -[mem_list]. destruct (p a).
    * cbn -[mem_list]. rewrite !denies_spec.
      intuition eauto using filter_sub.
    * intuition.
Qed.

Lemma deduplicate_nodup A R (l:list A) : nodup R (deduplicate R l).
Proof.
  induction l as [ | a l hl].
  + cbn. trivial.
  + cbn -[DNot]. split.
    * eauto using filter_nodup.
    * revert hl. induction (deduplicate R l) as [|x l' hl'].
      - cbn. auto.
      - cbn -[DNot mem_list]. destruct dec as [hr|_];cycle 1.
        { intuition. }
        cbn -[mem_list] in *. rewrite mem_list_cons. cbn -[mem_list].
        intuition.
Qed.

Lemma deduplicate_eq_set_list A (R:A->A->DProp) (l:list A) :
  Equivalence R -> eq_set_list R l (deduplicate R l).
Proof.
  (* spiwack: This proof is much longer than it should be, reflecting
     my dedication to avoiding equality… *)
  intros e. cbn -[mem_list]. split.
  + revert l. fix 2. intros l m.
    refine match m with head a => _ | @tail _ _ l' m' => _ end.
    * cbn [deduplicate of_mem].
      apply mem_list_left. reflexivity.
    * set (hl := deduplicate_eq_set_list _ m'). clearbody hl.
      cbn [of_mem deduplicate].
      rewrite mem_list_cons. cbn -[mem_list DNot].
      generalize (deduplicate R l') (of_mem m') hl. clear -e.
      { intros l. induction l as [|b l hl].
        + eauto.
        + intros x. cbn [filter].
          destruct dec as [hr|hr].
          * rewrite !mem_list_cons. cbn -[mem_list DNot].
            intros [h|h].
            - intuition.
            - apply hl in h. intuition.
          * rewrite mem_list_cons. cbn -[mem_list DNot]. cbn in hr.
            intros [h|h].
            - left. etransitivity. all:((idtac+symmetry);eassumption).
            - intuition. }
  + assert
      (forall l x, mem_list R x (deduplicate R l) -> mem_list R x l) as incl.
    { clear. intros l. induction l as [|a l hl].
      + cbn -[mem_list]. eauto.
      + intros x. cbn [deduplicate].
        rewrite !mem_list_cons. cbn -[mem_list DNot].
        intuition eauto using filter_sub. }
    intros m. generalize l (deduplicate R l) m (incl l). clear -e.
    intros l₁ l₂ m. induction m as [a l₂|a l₂ m hm].
    * cbn -[mem_list]. intros h. apply h.
      apply mem_list_left. reflexivity.
    * cbn -[mem_list]. eauto using mem_list_right.
Qed.
