(** This file defines retractions and basic properties on them. *)

Require Coq.Program.Program.
Require Coq.NArith.NArith.
Require Coq.Lists.List.


(** [Retract A B] is the type of retractions from [B] to [A]. *)
Record Retract A B := {
  inj  : B -> A;
  proj : A -> B;
  retract : forall x, proj (inj x) = x
}.
Arguments inj  {A B} _ _.
Arguments proj {A B} _ _.

Obligation Tactic := try solve [intuition eauto|intros **;cbn;now rewrite !retract].

(** * Categorical combinators *)

Program Definition id {A} : Retract A A := {|
  inj  x := x;
  proj x := x
|}.

Program Definition compose {A B C} 
    (f:Retract A B) (g:Retract B C) : Retract A C := {|
  inj  x := f.(inj)  (g.(inj)  x);
  proj x := g.(proj) (f.(proj) x)
|}.

Program Definition opt_compose {A B C}
     (f:Retract A (option B)) (g:Retract B (option C))
     : Retract A (option C) := {|
  inj  x := f.(inj)  (Some (g.(inj) x));
  proj x := match f.(proj) x return _ with
            | Some y => g.(proj) y
            | None   => None
            end
|}.

Program Definition opt_lift {A B}
     (f:Retract A B) : Retract (option A) (option B) := {|
  inj  x := match x return _ with
            | Some x => Some (f.(inj) x)
            | None   => None
            end;
  proj x := match x return _ with
            | Some x => Some (f.(proj) x)
            | None   => None
            end
|}.
Next Obligation.
  intros A B f [x|].
  all: now rewrite ?retract.
Qed.

(** * Retracts of the natural numbers *)

(** Retracts of the natural numbers are of special importance as they
    are used to define countable types. *)

(** A retraction from [A] into [nat] lifts to a retraction of [A+1]
    into [nat]. *)
Program Definition retract_nat_opt {A}
     (f:Retract nat A) : Retract nat (option A) := {|
  inj  x := match x return _ with
            | Some a => S(f.(inj) a)
            | None   => 0
            end;
  proj x := match x return _ with
            | S n => Some (f.(proj) n)
            | 0 => None
            end
|}.
Next Obligation.
  intros A f [a|].
  + now rewrite !retract.
  + reflexivity.
Qed.

(** A retraction from [A+1] into [nat] restricts to a retraction from
    [A] to [nat] when [A] is inhabited. *)
Program Definition retract_nat_inh {A}
     (f:Retract nat (option A)) (a:A) : Retract nat A := {|
  inj  x := f.(inj) (Some x) ;
  proj x := match f.(proj) x return _ with
            | Some x' => x'
            | None    => a
            end
|}.


(** * Standard retractions *)

Import NArith.

Definition retract_nat_N : Retract nat N := {|
  inj  := N.to_nat ;
  proj := N.of_nat ;
  retract := N2Nat.id
|}.


(** In this module we establish that [list nat] is a retract of
    [N]. We use, to that effect the following Gӧdel numbering:
    encoding [[n₁;...;nₖ]] as [[0...n₁...01...10...nₖ...01]] (least
    significant bit to the left).

    Examples:
    - [[]] is encoded as [0].
    - [[0]] is encoded as [1].
    - [[2]] is encoded as [001] (4).
    - [[3;2]] is encoded as [0001001] (72). *)

Module RetractNListNat.

 Import NArith List List.ListNotations.

 Local Open Scope positive.
 Local Open Scope N.

 (** [encode_nat n p] is [p] preceeded by [n] [0]-s. *)
 Fixpoint encode_nat (n:nat) (p:N) : N :=
   match n with
   | 0%nat => p
   | S n => N.double (encode_nat n p)
   end
 .

 Definition encode : list nat -> N :=
   List.fold_right (fun n p => encode_nat n (N.succ_double p)) 0.

 (** Positive integers decode to non-empty lists. *)
 Fixpoint decode_positive (p:positive) : nat * list nat :=
   match p with
   | 1%positive => (0%nat,[])
   | p~0 => let (n,l) := decode_positive p in (S n, l)
   | p~1 => let (n,l) := decode_positive p in (0%nat,n::l)
   end
 .

 Definition decode (n:N) : list nat :=
   match n with
   | 0 => []
   | Npos p => let (n,l) := decode_positive p in n::l
 end.

 Lemma retract : forall l, decode (encode l) = l.
 Proof.
   assert (forall n, decode (N.succ_double n) = 0%nat::(decode n)) as decode_succ_double.
   { intros [ | p ].
     + reflexivity.
     + cbn.
       now destruct (decode_positive p). }
   intros l.
   induction l as [ | n l hl ].
   + reflexivity.
   + cbn.
     induction n as [ | n hn ].
     * cbn. rewrite decode_succ_double.
       now rewrite hl.
     * cbn.
       unfold decode in hn |- *.
       destruct (encode_nat n (N.succ_double (encode l))); cbn.
       - easy.
       - destruct (decode_positive p).
         congruence.
 Qed.

End RetractNListNat.

Definition retract_N_list_nat : Retract N (list nat) := {|
  inj  := RetractNListNat.encode ;
  proj := RetractNListNat.decode ;
  retract := RetractNListNat.retract
|}.
