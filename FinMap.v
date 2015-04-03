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
Require FinSet.Lib.Image.

Module CofinitelyConstant.

 (** The definition of functions as a pair of a [FinSet.T] and a
     dependently typed list of corresponding size has been suggested
     by Cyril Cohen. *)

 Import Image.Coercions.

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

 Record T A {C:Countable A} (B:Type) (x:Distinguished B) := {
   support : FinSet.T A ;
   range   : Image.T B (listset.(inj) support) ;
   reduced : Canonize (ListSet.dforall (Distinct_from x) range)
 }.
 Arguments range {A C B x} _.
 Arguments support {A C B x} _.

 Definition fun_of {A} {_:Countable A} {B x} (f:T A B x) (a:A) : B :=
   Image.assoc eq_countable x.(pt) f.(range) a.

 Coercion fun_of : T >-> Funclass.

 Lemma support_spec A (_:Countable A) B x (f:T A B x) :
   forall a:A, a∈(support f) <-> f a <> x.(pt).
 Proof.
   intros a. destruct f as [s img reduced_img]. cbn. unfold mem.
     rewrite canonize_spec in reduced_img. revert img reduced_img.
     generalize (listset.(inj) s). clear s. intros l img reduced_img.
   induction l as [ | a' l hl ].
   + split.
     * intros. ListSet.use_no_mem_list_empty.
     * refine match img with Image.inil => _ end. cbn.
       congruence.
   + revert reduced_img hl.
     refine match img with Image.icons b img' => _ end. cbn [Image.assoc].
       intros reduced_img hl.
     destruct dec as [ha'|ha']. all:cbn in ha'.
     * subst a. clear hl. cbn in reduced_img |- *.
       split.
       - now specialize (reduced_img (ListSet.head b)).
       - intros _.
         now exists (ListSet.head _).
     * rewrite <- hl; cycle 1.
       { cbn in reduced_img |-*. intros m.
         now specialize (reduced_img (ListSet.tail m)). }
       split.
       - cbn. intros [m hm]. revert ha' hm.
         refine match m with ListSet.head a => _ | ListSet.tail m' => _ end.
         { cbn. congruence. }
         intros _ hm. cbn in hm.
         now exists m'.
       - cbn. intros [m hm].
         now exists (ListSet.tail m).
 Qed.

 Lemma ext A (_:Countable A) B x :
   forall f g:T A B x, (forall a, f a = g a) -> f = g.
 Proof.
   assert (forall f g : T A B x, (forall a, f a = g a) -> support f ⊆ support g)
      as incl_support.
   { unfold subset. intros f g h a ha. cbn.
     rewrite support_spec in *. congruence. }
   assert (forall f g : T A B x, (forall a, f a = g a) -> support f = support g)
      as eq_support.
   { intros **.
     apply double_inclusion.
     all:eauto. }
   assert (forall (l:list A) (f g:Image.T B l),
               ListSet.nodup eq_countable l ->
               ListSet.dforall (Distinct_from x) f ->
               ListSet.dforall (Distinct_from x) g ->
               (forall a, Image.assoc eq_countable x.(pt) f a = Image.assoc eq_countable x.(pt) g a) ->
               f=g) as eq_range.
   { intros * hl hf hg h.
     induction l as [|a l ihl].
     { refine match f with Image.inil => _ end.
       refine match g with Image.inil => _ end.
       reflexivity. }
     revert g hl hf hg h ihl.
     refine match f with Image.icons b q => _ end. clear. intros g.
     revert b q.
     refine match g with Image.icons b' q' => _ end. clear.
     intros b q hl hf hg h ihl.
     rewrite ihl with (f:=q) (g:=q').
     { apply Image.ext. cbn. f_equal.
       specialize (h a). (* spiwack: I think 'a' is a generated name here *)
       unfold Image.assoc in h. destruct dec as [_|c];cycle 1.
       { clear -c. cbn in c. congruence. }
       assumption. }
     + clear -hl. cbn in *. tauto.
     + clear -hf. cbn in *.
       intros m. specialize (hf (ListSet.tail m)). cbn in hf.
       assumption.
     + clear -hg. cbn in *.
       intros m. specialize (hg (ListSet.tail m)). cbn in hg.
       assumption.
     + clear -h hl. intros a'. specialize (h a'). cbn [Image.assoc] in h.
       destruct dec as [<-|h'].
       { cbn in hl. transitivity (x.(pt)).
         all: rewrite Image.assoc_default;[reflexivity|]. all:cbn.
         all: destruct hl as [_ hl]. all:solve[firstorder]. }
       assumption. }
   intros f g h. specialize (eq_support f g h).
   destruct f as [sf rf rdf], g as [sg rg rdg]. cbn -[ListSet.dforall] in *. destruct eq_support.
   apply eq_range in h;cycle 1.
   { apply set_nodup. }
   { now rewrite canonize_spec in *. }
   { now rewrite canonize_spec in *. }
   destruct h.
   f_equal.
   apply irrelevant_canonize.
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

 Lemma domain_spec A B (_:Countable A) : forall f:T A B,
   forall y, y∈(domain f) <-> f y<>None.
 Proof. apply CofinitelyConstant.support_spec. Qed.

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
   specialize (hf a). specialize (hg a). rewrite Partial.domain_spec in hf,hg.
   destruct Partial.fun_of,Partial.fun_of.
   all: try congruence.
   + destruct hf; congruence.
   + destruct hg;congruence.
 Qed.

 Definition support {A} {_:Countable A} (f:T A) : FinSet.T A :=
   Partial.domain (proj1_sig f).

 Lemma support_spec A (_:Countable A) : forall f:T A,
   forall y, y∈(support f) <-> f y<>y.
 Proof.
   intros [f hf] y. unfold support,fun_of. cbn -[Partial.domain].
   rewrite canonize_spec in hf. cbn -[Partial.domain] in hf.
   specialize (hf y).
   split.
   + intros hy. specialize (hf hy). rewrite Partial.domain_spec in hy.
     destruct Partial.fun_of. all:congruence.
   + rewrite Partial.domain_spec.
     destruct Partial.fun_of. all:congruence.
 Qed.

End CofinitelyId.