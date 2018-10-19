Require Import Lia.
Require Import List.
Require Coq.Program.Wf.
Generalizable All Variables.

Class PartialOrder (A : Type) := {
leq : A -> A -> Prop;

reflexive : forall (x : A), leq x x;
anti_symmetric : forall (x y : A), leq x y /\ leq y x -> x = y;
transitive : forall (x y z : A), leq x y /\ leq y z -> leq x z
}.

Class EventStructure `(E : PartialOrder M) := 
{incompatible : M -> M -> Prop;
ideal : M -> list M;

symmetric : forall (x y: M), incompatible x y -> incompatible y x;
irreflexive : forall (x : M), not (incompatible x x);
ideal_finite : forall (x y : M), leq y x <-> In y (ideal x);
incompatible_closed : forall (x y z : M),
(incompatible x y) /\ (leq y z) -> incompatible x z
}.

Definition Position `(E : EventStructure M) := M -> bool.

Definition valid_position `(E: EventStructure M) (f : Position E) :=
forall (x y z: M), 
(f x = true /\ f y = true ->  not (incompatible x y))
 /\ 
(f x = true /\ leq y x -> f y = true).

Definition finite_position `(E : EventStructure M) (f : Position E) :=
valid_position E f /\
exists (l : list M),forall (n : M), f n = true <-> In n l.

Definition EmptyPosition `(E: EventStructure M) : Position E :=
fun _ => false.

Fact empty_is_finite `(E: EventStructure M) : 
finite_position E (EmptyPosition E).
Proof. unfold finite_position. split.
- unfold valid_position. intros. split.
+ intros. compute in H. destruct H. inversion H.
+ intros. destruct H. compute in H. inversion H.
-   pose (witness := nil : list M).
    refine (ex_intro _ witness _).
intros. compute. split.
+ intros. inversion H.
+ intros. contradiction H.
Qed.


(* TODO : Change the nat to int *)
Program Fixpoint valid_walk `(E: EventStructure M) 
(w : list (Position E + (M * nat))) {measure (length w)} :=
match w with
| inl(p1) :: nil => finite_position E p1
| inl(p1) :: inr(m, ep) :: inl(p2) :: xs => 
finite_position E p1 /\ finite_position E p2 /\
(valid_walk E (inl(p2) :: xs)) /\ 
(
(ep = 1 /\ p2 m = false /\ forall (n : M), n <> m -> p1 n = p2 n)
\/
(ep = 0 /\ p1 m = false /\ forall (n : M), n <> m -> p1 n = p2 n)
)
| _ => False
end.
Next Obligation.
simpl. lia. Qed.
Next Obligation.
split.
- intros. discriminate.
- intros. discriminate. Qed.
Next Obligation.
split.
- intros. discriminate.
- intros. discriminate. Qed.
Next Obligation.
split.
- intros. discriminate.
- intros. discriminate. Qed.
Next Obligation.
split.
- intros. discriminate.
- intros. discriminate. Qed.
Next Obligation.
split.
- intros. discriminate.
- intros. discriminate. Qed.

(* TODO : Change nat to int *)
Definition Walk `(E: EventStructure M) := 
list (Position E + (M * nat)) .

Inductive Infinity : Type :=
| plus_infinity : Infinity
| minus_infinity : Infinity.

Definition initial_move `(E: EventStructure M) (m : M) :=
forall (n : M), In n (ideal m) <-> m = n.

Definition second_move `(E: EventStructure M) (m : M) :=
forall (n : M), In n (ideal m) ->  n = m \/ 
initial_move E m.

Class AsynchronousArena `(E : EventStructure M) := {
(* TODO : Change nat to int *)
polarity : M -> nat;
(* TODO : Change nat to int *)
finite_payoff : (Position E + Walk E) -> nat;
(* TODO: Is infinity already represented in coq? *)
infinite_payoff : Position E -> Infinity;

(* TODO : Change nat to int *)
polarity_unit : forall (m : M), polarity m = 0 \/ polarity m = 1;

initial_incompatible :
forall (m n : M), initial_move E m /\ initial_move E n 
-> incompatible m n;

(* TODO : Change nat to int *)
initial_payoff :
forall (f : Position E), 
forall (m : M), f m = false -> finite_payoff (inl f) = 0 \/
finite_payoff (inl f) = 1;

(* TODO : change nat to int, change sign *)
polarity_first :
forall (m : M), initial_move E m -> 
polarity m = finite_payoff (inl(EmptyPosition E));

(* TODO : Change nat to int *)
polarity_second :
forall (m : M), second_move E m -> 
polarity m = finite_payoff (inl(EmptyPosition E));

empty_null :
forall (w : Walk E), 
exists (p : Position E), 
w = inl (p) :: nil -> finite_payoff (inr w) = 0;

nonempty_payoff :
forall (w : Walk E) (p : Position E),
length w > 1 /\ hd_error (rev w) = Some (inl p) /\
In (inl (EmptyPosition E)) w -> 
finite_payoff (inr w) = finite_payoff (inl p)
}.

(* TODO : Change nat to int *)
Definition valid_path `(E : EventStructure M) (p : Walk E) :=
valid_walk E p /\
forall (m : M) (n : nat), In (inr(m,n)) p -> n = 1.

Definition valid_play `(E : EventStructure M) (p : Walk E) :=
valid_path E p /\
hd_error p = Some (inl(EmptyPosition E)).

Definition Play `(E: EventStructure M) := Walk E.

Definition EmptyPlay `(E: EventStructure M) : Play E :=
inl(EmptyPosition E) :: nil.

Fact empty_play_is_valid `(E: EventStructure M) :
valid_play E (EmptyPlay E).
Proof. unfold valid_play. split.
- unfold valid_path. split.
+ split.
++ compute. intros. split.
+++ intros. destruct H. inversion H.
+++ intros. destruct H. inversion H.
++ pose (witness := nil : list M).
    refine (ex_intro _ witness _). intros. compute. split.
+++ intros. inversion H.
+++ intros. contradiction H.
+ intros. compute in H. inversion H.
++ inversion H0.
++ contradiction H0.
- compute. reflexivity.
Qed.


(* TODO : Change the nat to int. Change sign *)
Program Fixpoint valid_alternating_play 
`(E: EventStructure M) (p : Play E) {measure (length p)} := 
valid_play E p /\
match p with
| inl(pos) :: nil => True
| inl(pos1) :: inr(m1, ep1) :: inl(pos2) :: nil => True
| inl(pos1) :: inr(m1, ep1) :: inl(pos2) :: inr(m2, ep2) :: xs => 
(valid_walk E (inl(pos2) :: inr(m2, ep2) :: xs)) /\ ep1 = ep2
| _ => False
end.
Next Obligation.
split.
- intros. discriminate.
- split.
+ intros. discriminate.
+ intros. discriminate. Qed.
Next Obligation.
split.
- intros. discriminate.
- split.
+ intros. discriminate.
+ intros. discriminate. Qed.
Next Obligation.
split.
- intros. discriminate.
- split.
+ intros. discriminate.
+ intros. discriminate. Qed.
Next Obligation.
split.
- intros. discriminate.
- split.
+ intros. discriminate.
+ intros. discriminate. Qed.
Next Obligation.
split.
- intros. discriminate.
- split.
+ intros. discriminate.
+ intros. discriminate. Qed.
Next Obligation.
split.
- intros. discriminate.
- split.
+ intros. discriminate.
+ intros. discriminate. Qed.


Fact empty_is_alternating `(E: EventStructure M) :
valid_alternating_play E (EmptyPlay E).
Proof. compute. split.
- split.
+ split.
++ intros. split.
+++ intros. split.
++++ intros. destruct H. inversion H.
++++ intros. destruct H. inversion H.
+++ pose (witness := nil : list M).
    refine (ex_intro _ witness _).
intros. split.
++++ intros. inversion H.
++++ intros. compute in H. contradiction H.
++ intros. inversion H. inversion H0. contradiction H0.
+ reflexivity.
- auto.
Qed.

(* TODO : Change nat to int. Change sign *)
Definition opponent_move
`(E: EventStructure M) (A : AsynchronousArena E) (m : M):=
polarity m = 0.

(* TODO : Change nat to int. Change sign *)
Definition player_move
`(E: EventStructure M) (A : AsynchronousArena E) (m : M):=
polarity m = 1.

Definition AlternatingPlay `(E: EventStructure M) := Play E.

Definition Strategy `(E: EventStructure M) (A : AsynchronousArena E) :=
AlternatingPlay E -> bool.
