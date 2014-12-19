(** This file defines retractions and basic properties on them. *)

Require Coq.Program.Program.

Obligation Tactic := try solve [intuition eauto].


(** [Retract A B] is the type of retractions from [B] to [A]. *)
Record Retract A B := {
  inj  : B -> A;
  proj : A -> B;
  retract : forall x, proj (inj x) = x
}.
Arguments inj  {A B} _ _.
Arguments proj {A B} _ _.

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
Next Obligation. intros **. now rewrite !retract. Qed.

Program Definition opt_compose {A B C}
     (f:Retract A (option B)) (g:Retract B (option C))
     : Retract A (option C) := {|
  inj  x := f.(inj)  (Some (g.(inj) x));
  proj x := match f.(proj) x return _ with
            | Some y => g.(proj) y
            | None   => None
            end
|}.
Next Obligation. intros **. now rewrite !retract. Qed.

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