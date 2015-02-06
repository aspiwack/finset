(** There are three kinds of finite functions defined in this file
    - Functions which are constant except on a finite set called the
      support. They are defined in module [CofinitelyConstant].
    - Partial function with decidable finite domain. They are defined
      in module [Partial].
    - Endofunctions which are the identity except on a finite set
      called the support. They are defined in module
      [CofinitelyId]. They are of special interest as non-degenerate
      cases are invertible, hence they have more properties of regular
      functions than the previous two. *)

Require Import FinSet.Lib.DProp.
Require Import FinSet.Quotients.Retract.
Require Import FinSet.Quotients.Countable.
Require Import FinSet.FinSet.
Import FinSet.Notations.

Module CofinitelyConstant.

 (** Decidably distinguished point in a type. *)
 Record Distinguished (A:Type) := {
   pt : A;
   distinguished : forall x, {x=pt}+{x<>pt}
 }.
 Arguments pt {A} _.
 Arguments distinguished {A} _ _.

 Program Definition Distinct_from {A:Type} (x:Distinguished A) (y:A) : DProp := {|
   dec := Sumbool.sumbool_not _ _ (x.(distinguished) y)
 |}.

 Program  Definition T A {_:Countable A} (B:Type) (x:Distinguished B) :=
   { l:list (A*B) | Canonize (
                      eq_countable
                        (List.map fst l) 
                        (listset.(inj) (listset.(proj) (List.map fst l)))
                   && ListSet.dforall
                        (Distinct_from x)
                        (List.map snd l)
   )}.

 Fixpoint assoc {A} {c:Countable A} {B} (d:B) (x:A) (l:list (A*B)) : B :=
   match l with
   | nil => d
   | cons (a,b) q => if dec (eq_countable x a) then b else assoc d x q
   end
 .

 Definition fun_of {A} {_:Countable A} {B x} (f:T A B x) (a:A) : B :=
   assoc x.(pt) a (proj1_sig f).

 Coercion fun_of : T >-> Funclass.

 Lemma ext A (_:Countable A) B x :
   forall f g:T A B x, (forall a, f a = g a) -> f = g.
 Proof.
   assert (forall (l:list (A*B)) (a:A),
     ListSet.dforall (Distinct_from x) (List.map snd l) ->
     Distinct_from x (assoc x.(pt) a l) ->
     ListSet.mem_list eq_countable a (List.map fst l))
   as mem_domain.
   { cbn. intros l.
     induction l as [ | [a₀ b₀] l hl ].
     + cbn. congruence.
     + cbn -[eq_countable]. intros a h₂ hass.
       destruct dec as [ha|ha].
       * exists (ListSet.head _).
         now cbn in ha|-*.
       * apply hl in hass; cycle 1.
         { refine (fun m => h₂ (ListSet.tail m)). }
         destruct hass as [m hm].
         exists (ListSet.tail m). cbn.
         trivial. }
   assert (forall (l:list (A*B)) (m₁:ListSet.Mem (List.map fst l)),
           exists (m₂:ListSet.Mem (List.map snd l)),
             ListSet.of_mem m₂ = assoc x.(pt) (ListSet.of_mem m₁) l)
   as assoc_mem.
   { fix assoc_mem 2. intros l m.
     destruct l as [|[a b] l].
     { cbn in m. ListSet.use_no_mem_empty. }
     cbn  -[eq_countable] in m|-*.
     destruct dec as [ha|ha].
     + now exists (ListSet.head _).
     + revert ha.
       refine (match m in ListSet.Mem l' return l' = cons a (List.map fst l) -> _ with | ListSet.head a' => _ | ListSet.tail m' => _ end eq_refl).
       { cbn. congruence. }
       intros [= _ ->] _.
       specialize (assoc_mem _ m').
       destruct assoc_mem as [m'' hm''].
       now exists (ListSet.tail m'').
     Guarded. }
   assert (forall l₁ l₂:list(A*B),
     ListSet.dforall (Distinct_from x) (List.map snd l₁) ->
     (forall a, assoc x.(pt) a l₁ = assoc x.(pt) a l₂) ->
     ListSet.included_list eq_countable (List.map fst l₁) (List.map fst l₂))
   as incl_domain.
   { intros l₁ l₂ nx₁ h. cbn. intros m₁.
     destruct (dec (Distinct_from x (assoc x.(pt) (ListSet.of_mem m₁) l₁)))
       as [hm|hm]; cycle 1.
     { cbn in hm,nx₁.
       specialize (assoc_mem _ m₁).
       destruct assoc_mem as [m₁' hm₁].
       rewrite <- hm₁ in *.
       congruence. }
     rewrite h in hm. cbn in hm.
     revert hm. generalize (ListSet.of_mem m₁). clear l₁ nx₁ h m₁.
     induction l₂ as [|[a b] l hl].
     { cbn. congruence. }
     cbn -[eq_countable]. intros a' h.
     destruct dec as [->|ha].
     + now exists (ListSet.head _).
     + apply hl in h. destruct h as [m hm].
       now exists (ListSet.tail m). }
   assert (forall (a:A) (l:list (A*B)),
             Denies (ListSet.mem_list eq_countable a (List.map fst l)) ->
             assoc x.(pt) a l = x.(pt))
   as denies_assoc.
   { intros a l. induction l as [|[a' b'] l hl].
     + trivial.
     + cbn -[eq_countable]. intros h.
       destruct dec as [c|_].
       { specialize (h (ListSet.head _)).
         cbn in *. contradiction. }
       apply hl. cbn in *.
       intros m. specialize (h (ListSet.tail m)).
       exact h. }
   assert (forall l₁ l₂:list(A*B),
     ListSet.dforall (Distinct_from x) (List.map snd l₁) ->
     ListSet.dforall (Distinct_from x) (List.map snd l₂) ->
     (forall a, assoc x.(pt) a l₁ = assoc x.(pt) a l₂) ->
     ListSet.eq_set_list eq_countable (List.map fst l₁) (List.map fst l₂))
   as eq_domain.
   { intros **. split.
     all: now apply incl_domain. }
   assert (forall l₁ l₂:list (A*B),
             ListSet.nodup eq_countable (List.map fst l₁) ->
             ListSet.nodup eq_countable (List.map fst l₂) ->
             ListSet.dforall (Distinct_from x) (List.map snd l₁) ->
             ListSet.dforall (Distinct_from x) (List.map snd l₂) ->
             List.map fst l₁ = List.map fst l₂ ->
             (forall a, assoc x.(pt) a l₁ = assoc x.(pt) a l₂) ->
             l₁=l₂)
   as assoc_ext.
   { intros l₁. induction l₁ as [|[a₁ b₁] l₁ hl₁].
     + intros [|[a₂ b₂] l₂];cycle 1.
       { cbn. congruence. }
       trivial.
     + intros [|[a₂ b₂] l₂].
       { cbn. congruence. }
       cbn -[eq_countable]. intros [h₁ h₂] [h₃ h₄] h₅ h₆ [= <- h₇] h₈.
       f_equal.
       { f_equal.
         specialize (h₈ a₁).
         destruct dec as [_|n];cycle 1.
         { cbn in n. congruence. }
         congruence. }
       apply hl₁.
       * assumption.
       * assumption.
       * intros m. specialize (h₅ (ListSet.tail m)).
         trivial.
       * intros m. specialize (h₆ (ListSet.tail m)).
         trivial.
       * assumption.
       * intros a. specialize (h₈ a).
         destruct dec as [<-|_].
         { rewrite !denies_assoc.
           { trivial. }
           all:assumption. }
         trivial. }
   (* /intermediate lemmas *)
   (* rearranging goal *)
   intros [f hf] [g hg] h. cbn in h.
   apply dsigma_ext. cbn. rewrite !canonize_spec in hf,hg.
   cbn -[inj proj] in hf,hg.
   destruct hf as [hf₁ hf₂], hg as [hg₁ hg₂].
   (* /rearranging goal *)
   apply assoc_ext.
   all: try solve[try rewrite hf₁;try rewrite hg₁; auto using set_nodup].
   rewrite hf₁,hg₁. f_equal.
   apply set_ext. unfold mem.
   rewrite <-hf₁, <-hg₁. intros a.
   apply ListSet.mem_eq_set_list.
   { typeclasses eauto. }
   apply eq_domain.
   all:eauto.
 Qed.

 Definition support {A} {_:Countable A} {B x} (f:T A B x) : FinSet.T A :=
   listset.(proj) (List.map fst (proj1_sig f)).

 Lemma mem_support A B x (_:Countable A) : forall f:T A B x,
   forall y, y∈(support f) <-> f y<>x.(pt).
 Proof.
   intros [f hf] y. unfold support. unfold fun_of. cbn [proj1_sig].
   rewrite canonize_spec in hf. destruct hf as [hf₁ hf₂].
   unfold FinSet.mem. rewrite <- hf₁. clear hf₁.
   induction f as [|[a b] l hl].
   + cbn. split.
     * intros [m _]. ListSet.use_no_mem_empty.
     * congruence.
   + cbn -[eq_countable]. destruct dec as [ha|ha].
     * cbn in hf₂. specialize (hf₂ (ListSet.head b)). cbn in hf₂.
       split.
       - trivial.
       - intros _. exists (ListSet.head a).
         trivial.
     * rewrite <- hl; cycle 1.
       { cbn in hf₂|-*. intros m.
         now specialize (hf₂ (ListSet.tail m)). }
       split.
       - intros [m hm]. revert ha hm.
         refine match m with
                | ListSet.head a' => _
                | ListSet.tail m' => _
                end.
         { cbn. congruence. }
         cbn. intros _ h.
         eexists. eauto.
       - intros [m hm].
         now exists (ListSet.tail m).
 Qed.

End CofinitelyConstant.

Module Partial.

 Program Definition dnone {A} : CofinitelyConstant.Distinguished (option A) := {|
   CofinitelyConstant.pt := None;
   CofinitelyConstant.distinguished x := match x return _ with
                      | None => left _
                      | Some a => right _
                      end
 |}.
 Next Obligation. intros ** [=]. Qed.

 Definition T (A:Type) {_:Countable A} (B:Type) :=
   CofinitelyConstant.T A (option B) dnone.

 Definition fun_of {A} {_:Countable A} {B} (f:T A B) (a:A) : option B :=
   CofinitelyConstant.fun_of f a.

 Coercion fun_of : T >-> Funclass.

 Lemma ext A (_:Countable A) B :
   forall f g:T A B, (forall a, f a = g a) -> f = g.
 Proof. apply CofinitelyConstant.ext. Qed.

 Definition domain {A} {_:Countable A} {B} (f:T A B) : FinSet.T A :=
   CofinitelyConstant.support f.

 Lemma mem_domain A B (_:Countable A) : forall f:T A B,
   forall y, y∈(domain f) <-> f y<>None.
 Proof. apply CofinitelyConstant.mem_support. Qed.

End Partial.


Module CofinitelyId.

 Definition T (A:Type) {_:Countable A} :=
   { f:Partial.T A A | Canonize (
     dforall (Partial.domain f)
             (fun x => DNot (eq_countable (Partial.fun_of f x) (Some x)))) }.

 Definition fun_of {A} {_:Countable A} (f:T A) (x:A) : A :=
   match Partial.fun_of (proj1_sig f) x with
   | Some y => y
   | None   => x
   end.

 Coercion fun_of : T >-> Funclass.

 Lemma ext A (_:Countable A) :
   forall f g:T A, (forall a, f a = g a) -> f = g.
 Proof.
   intros [f hf] [g hg] h.
   apply dsigma_ext. cbn. unfold fun_of in *. cbn [proj1_sig] in *.
   rewrite !canonize_spec in *. cbn -[Partial.domain] in hf,hg.
   apply Partial.ext. intros a. specialize (h a).
   specialize (hf a). specialize (hg a). rewrite Partial.mem_domain in hf,hg.
   destruct Partial.fun_of,Partial.fun_of.
   all: try congruence.
   + destruct hf; congruence.
   + destruct hg;congruence.
 Qed.

 Definition support {A} {_:Countable A} (f:T A) : FinSet.T A :=
   Partial.domain (proj1_sig f).

 Lemma mem_support A (_:Countable A) : forall f:T A,
   forall y, y∈(support f) <-> f y<>y.
 Proof.
   intros [f hf] y. unfold support,fun_of. cbn -[Partial.domain].
   rewrite canonize_spec in hf. cbn -[Partial.domain] in hf.
   specialize (hf y).
   split.
   + intros hy. specialize (hf hy). rewrite Partial.mem_domain in hy.
     destruct Partial.fun_of. all:congruence.
   + rewrite Partial.mem_domain.
     destruct Partial.fun_of. all:congruence.
 Qed.

End CofinitelyId.