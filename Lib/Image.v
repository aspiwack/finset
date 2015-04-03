(** List with the same size of another list. This constitutes the
    prototype of finite functions. This module is inspired by the
    [ffun] module in Ssreflect. Ssreflect's [ffun] is somehow smarter
    though, as it restricts its attention to lists without duplicate
    in a type with decidable equality, so that there are stronger
    extensionality principles. *)

Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import FinSet.Lib.DProp.
Require FinSet.Lib.ListSet.

Inductive T {A B:Type} : list A -> Type :=
| inil : T []
| icons {a l} (b:B) (q:T l) : T (a::l)
.
Arguments T {A} B l : clear implicits.

Fixpoint to_list {A B} {l:list A} (q:T B l) : list B :=
  match q with
  | inil => []
  | icons b q => b::(to_list q)
  end
.

Lemma ext A B (l:list A) :
  forall q₁ q₂:T B l, to_list q₁ = to_list q₂ -> q₁ = q₂.
Proof.
  intros q₁. induction q₁ as [ ? ? | ? ?  b₁ q₁ hq₁].
  + intros q₂. refine match q₂ with inil => _ end.
    reflexivity.
  + intro q₂. revert b₁ q₁ hq₁.
    refine match q₂ with icons b₂ q₂ => _ end. intros b₁ q₁ hq₁. cbn.
    intros [= <- h]. f_equal.
    eauto.
Qed.


(** [Image.T] can be read as an association list with the domain as
    keys. In this variant we return a default value when there is no
    corresponding key. *)
Fixpoint assoc {A B} {l:list A} (E:A->A->DProp) (d:B) (q:T B l) (x:A) : B :=
  match l return T B l -> B with
  | [] => fun _ => d
  | a::l => fun q =>
    match q with icons b q =>
      if dec (E x a) then b
      else assoc E d q x
    end
  end q
.

Lemma assoc_default A B (l:list A) E d (q:T B l) : forall x, ~(ListSet.mem_list E x l) -> assoc E d q x = d.
Proof.
  intros x.
  induction l as [|a l hl].
  + refine match q with inil => _ end. cbn.
    reflexivity.
  + revert hl.
    refine match q with icons b q' => _ end. cbn [assoc].
    intros hl h.
    destruct dec as [hx|_].
    { cbn in h. contradiction h.
      now eexists (ListSet.head _). }
    apply hl. cbn in h|-*.
    intros [m hm]. apply h.
    now exists (ListSet.tail m).
Qed.

(** Conversely, given a function defined on a domain we can create the
    image of the domain. *)
Fixpoint img {A B} (l:list A) : (ListSet.Mem l -> B) -> T B l :=
  match l with
  | [] => fun _ => inil
  | a::l => fun f =>
    icons (f (ListSet.head a)) (img l (fun m => f (ListSet.tail m)))
  end
.

(** Variant of [img] with decidable equality *)
Program Definition img_dec {A B} (E:A->A->DProp) {_:Reflexive E} (l:list A) (f:forall x:A, Canonize (ListSet.mem_list E x l) -> B) : T B l :=
  img l (fun m => f (ListSet.of_mem m) _).
Next Obligation.
  intros **. apply canonize_spec.
  eexists. reflexivity.
Qed.

Lemma assoc_img₀ A B (E:A->A->DProp) (_:Reflexive E)
      (d:B) l m f :
  (forall u v, E u v -> u=v) ->
  (forall m m':ListSet.Mem l, ListSet.of_mem m = ListSet.of_mem m' -> f m = f m') ->
  assoc E d (img l f) (ListSet.of_mem m) = f m.
Proof.
  intros e_eq f_ext.
  induction l as [ | a l hl ].
  { ListSet.use_no_mem_empty. }
  cbn. destruct dec as [he|he].
  + apply e_eq in he.
    now apply f_ext.
  + revert he f f_ext hl.
    refine match m with ListSet.head a' => _ | ListSet.tail m' => _ end.
    { intros he f _ _. cbn in he. rewrite denies_spec in he.
      now pose proof (reflexivity a') as he'. }
    intros _ f f_ext hl. cbn.
    apply hl.
    eauto.
Qed.

Lemma assoc_img A B (E:A->A->DProp) (_:Reflexive E)
      (d:B) l x (h:Canonize (ListSet.mem_list E x l)) f :
  (forall u v, E u v -> u=v) -> assoc E d (img_dec E l f) x = f x h.
Proof.
  intros e_eq.
  assert (forall y hy z hz, y=z -> f y hy = f z hz) as f_ext.
  { intros y hy z hz <-. f_equal.
    apply irrelevant_canonize. }
  unfold img_dec.
  pose proof h as h'. apply canonize_spec in h'.
  pose proof (ListSet.mem_of_mem_list_spec _ _ _ _ h') as hx.
  apply e_eq in hx. rewrite hx at 1.
  rewrite assoc_img₀;cycle 1.
  { typeclasses eauto. }
  { assumption. }
  { intros **.
    now apply f_ext. }
  now apply f_ext.
Qed.

Module Coercions.

  Coercion to_list : T >-> list.

End Coercions.
