Require Import Lia.
Require Import List.
Require Import Coq.Program.Wf.
Require Import ZArith.
Require Import Init.Nat.

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

Definition move_from `(E: EventStructure M) 
(m : M) (p1 p2 : Position E) :=
forall (n : M), n <> m -> p1 n = p2 n /\ p1 m = false.

Definition Walk `(E: EventStructure M) := 
list (Position E + (M * bool)).

Program Fixpoint valid_walk `(E: EventStructure M) 
(w : Walk E) {measure (length w)} :=
match w with
| inl(p1) :: nil => finite_position E p1
| inl(p1) :: inr(m, ep) :: inl(p2) :: xs => 
finite_position E p1 /\ finite_position E p2 /\
(valid_walk E (inl(p2) :: xs)) /\ 
((ep = true /\ move_from E m p1 p2) \/ (ep = false /\ move_from E m p2 p1))
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

Inductive Infinity : Type :=
| plus_infinity : Infinity
| minus_infinity : Infinity.

Definition initial_move `(E: EventStructure M) (m : M) :=
forall (n : M), In n (ideal m) <-> m = n.

Definition second_move `(E: EventStructure M) (m : M) :=
forall (n : M), In n (ideal m) ->  n = m \/ 
initial_move E m.

Class AsynchronousArena `(E : EventStructure M) := {
polarity : M -> bool;
finite_payoff : (Position E + Walk E) -> Z;

infinite_payoff : Position E -> Infinity;

initial_incompatible :
forall (m n : M), initial_move E m /\ initial_move E n 
-> incompatible m n;

initial_payoff :
let n := finite_payoff (inl (EmptyPosition E)) in
 n = (-1)%Z \/ n = (1)%Z;

polarity_first :
forall (m : M), initial_move E m -> 
(polarity m = true -> finite_payoff (inl(EmptyPosition E)) = (-1)%Z)
/\
(polarity m = false -> finite_payoff (inl(EmptyPosition E)) = (1)%Z);

polarity_second :
forall (m : M), second_move E m -> 
(polarity m = true -> finite_payoff (inl(EmptyPosition E)) = (1)%Z)
/\
(polarity m = false -> finite_payoff (inl(EmptyPosition E)) = (-1)%Z);

empty_null :
forall (w : Walk E), 
exists (p : Position E), 
w = inl (p) :: nil -> finite_payoff (inr w) = 0%Z;

nonempty_payoff :
forall (w : Walk E) (p : Position E),
valid_walk E w /\
length w > 1 /\ 
hd_error (rev w) = Some (inl p) /\
In (inl (EmptyPosition E)) w -> 
finite_payoff (inr w) = finite_payoff (inl p)
}.

Definition Path `(E : EventStructure M) := Walk E.

Definition valid_path `(E : EventStructure M) (p : Walk E) :=
valid_walk E p /\
forall (m : M) (b : bool), In (inr(m, b)) p -> b = true.

Definition Play `(E: EventStructure M) := Walk E.

Definition valid_play `(E : EventStructure M) (p : Walk E) :=
valid_path E p /\
hd_error p = Some (inl(EmptyPosition E)).

Program Fixpoint valid_alternating_play `(E: EventStructure M)
(A : AsynchronousArena E) (p : Path E) {measure (length p)} := 
valid_play E p /\
match p with
| inl(pos) :: nil => True
| inl(pos1) :: inr(m1, ep1) :: inl(pos2) :: nil => True
| inl(pos1) :: inr(m1, ep1) :: inl(pos2) :: inr(m2, ep2) :: xs => 
(valid_walk E (inl(pos2) :: inr(m2, ep2) :: xs)) /\ 
polarity m1 = negb (polarity m2)
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

Fact empty_play_is_alternating `(E: EventStructure M)
(A : AsynchronousArena E) :
valid_alternating_play E A (EmptyPlay E).
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
++ intros. destruct H.
+++ inversion H.
+++ contradiction H.
+ reflexivity.
- auto.
Qed.

Definition player_move
`(E: EventStructure M) (A : AsynchronousArena E) (m : M):=
polarity m = true.

Definition opponent_move
`(E: EventStructure M) (A : AsynchronousArena E) (m : M):=
polarity m = false.

Definition Strategy `(E: EventStructure M) (A : AsynchronousArena E) :=
Play E -> bool.

Definition valid_strategy
`(E: EventStructure M) (A : AsynchronousArena E)
(f : Strategy E A) :=
(forall (s : Play E), 
f s = true -> valid_alternating_play E A s) 
/\
(f (EmptyPlay E) = true)
 /\
(forall (s : Play E),
f s = true /\ length s > 1 -> 
exists (m1 m2 : M) (b1 b2 : bool), 
nth_error s 1 = Some (inr(m1, b1)) /\
nth_error (rev s) 1 = Some (inr(m2, b2)) /\
opponent_move E A m1 /\ player_move E A m2)
/\
(forall (s : Play E) (x y z: Position E) (m n: M),
hd_error s = Some (inl (EmptyPosition E)) /\
hd_error (rev s) = Some (inl x) /\
move_from E m x y /\
opponent_move E A m /\
move_from E n y z /\
player_move E A n ->
f (s ++ ((inr (m,false) :: (inl y) :: 
(inr (n,true)) :: (inl z) :: nil))) = true -> f s = true)
/\
(forall (s : Play E) (x y z1 z2: Position E) (m n1 n2: M),
hd_error s = Some (inl (EmptyPosition E)) /\
hd_error (rev s) = Some (inl x) /\
move_from E m x y /\
opponent_move E A m /\
move_from E n1 y z1 /\
player_move E A n1 /\
move_from E n2 y z2 /\
player_move E A n2 ->
f (s ++ ((inr (m,false) :: (inl y) :: 
(inr (n1,true)) :: (inl z1) :: nil))) = true 
/\
f (s ++ ((inr (m,false) :: (inl y) :: 
(inr (n2,true)) :: (inl z2) :: nil))) = true 
-> n1 = n2)
.

Definition independent `(E: EventStructure M) (m n : M) :=
incompatible m n /\ not (leq m n) /\ not (leq n m).

Definition backward_consistent 
`(E: EventStructure M) (A : AsynchronousArena E)
(s : Strategy E A) :=
valid_strategy E A s
/\
forall (s1 : Play E) (s2 : Path E) (m1 m2 n1 n2 : M)
, 
valid_play E s1 /\ valid_path E s2 /\
(exists (p1 p2 p3: Position E),
s (s1 ++ (inr(m1,true) :: inl(p1) :: 
inr(n1,true) :: inl(p2) :: inr(m2,true) :: 
inl(p3) :: inr(n2, true) :: nil) ++ s2) = true
/\ (independent E n1 m2) /\ (independent E m1 m2)
-> 
(independent E n1 n2) /\ (independent E m1 n2) /\
exists (p1' p2' p3': Position E),
s (s1 ++ (inr(m2,true) :: inl(p1') :: 
inr(n2,true) :: inl(p2') :: inr(m1,true) :: 
inl(p3') :: inr(n1, true) :: nil) ++ s2) = true
)
.

Definition forward_consistent 
`(E: EventStructure M) (A : AsynchronousArena E)
(s : Strategy E A) :=
valid_strategy E A s
/\
forall (s1 : Play E) (m1 m2 n1 n2 : M), 
valid_play E s1 /\
(exists (p1 p2 p3 p4: Position E), 
s (s1 ++ (inr(m1,true) :: inl(p1) :: inr(n1,true) :: inl(p2) :: nil)) = true
/\ 
s (s1 ++ (inr(m2,true) :: inl(p3) :: inr(n2,true) :: inl(p4) :: nil)) = true
/\
(independent E m1 m2) 
/\
(independent E m2 n1)
-> 
(independent E m1 n2) 
/\ (independent E n1 n2) /\
exists (p1' p2' p3' p4': Position E),
s (s1 ++ (inr(m1,true) :: inl(p1') :: 
inr(n1,true) :: inl(p2') :: inr(m2,true) :: 
inl(p3') :: inr(n2, true) :: inl(p4') :: nil)) = true
)
.

Definition innocent `(E: EventStructure M) (A : AsynchronousArena E)
(s : Strategy E A) :=
forward_consistent E A s /\ backward_consistent E A s.

Definition InfinitePlay `(E: EventStructure M) :=
nat -> (Position E + M).

Definition even (n : nat) := exists (m : nat), n = 2*m.

Definition infinite_play_valid `(E: EventStructure M)
(p : InfinitePlay E) := 
p 0 = inl(EmptyPosition E) /\

forall (n : nat), even n -> 
exists (m : M) (x x' : Position E),
p n = inl(x) /\ p (n+1) = inr (m) /\ p (n+2) = inl(x') /\
move_from E m x x'.

Definition total_strategy
 `(E: EventStructure M) (A : AsynchronousArena E) (sigma : Strategy E A) :=
forall (s : Play E) (m : M) (pos : Position E),
(valid_play E (s ++ (inr(m,true) :: inl(pos) :: nil)) /\
sigma s = true /\ opponent_move E A m)
-> exists (n : M) (pos' : Position E),
(sigma (s ++ (inr(m,true) :: inl(pos) :: inr(n,true) :: inl(pos') :: nil)) 
= true /\ player_move E A n).

Definition finite_nonnegative
 `(E: EventStructure M) (A : AsynchronousArena E) (sigma : Strategy E A) :=
forall (x : Position E),
(exists (s : Play E), sigma s = true 
/\ hd_error (rev s) = Some (inl(x)))
-> Z.geb (finite_payoff (inl (x))) (0%Z) = true.

Fixpoint subsequence_helper
`(E: EventStructure M) (s : InfinitePlay E) (m : nat) (temp : Play E) :=
match m with
| 0 => 
(match (s 0) with
  | inl(p) => inl(p) :: temp
  | inr(m) => inr(m,true) :: temp
end)
| S m' => 
(match (s m) with
  | inl(p) => subsequence_helper E s m' (inl(p) :: temp)
  | inr(m) => subsequence_helper E s m' (inr(m, true) :: temp)
end)
end.

Definition subsequence
`(E: EventStructure M) (s : InfinitePlay E) (m : nat):=
subsequence_helper E s m nil.


Definition infinite_nonnegative
`(E: EventStructure M) (A : AsynchronousArena E) (sigma : Strategy E A) :=
forall (x : Position E),
(exists (s : InfinitePlay E), 
infinite_play_valid E s 
/\
forall (k : nat), sigma (subsequence E s (2 * k)) = true
/\
forall (m : M) (a : nat), 
x m = true <-> exists (q : nat) (b : Position E), 
s q = inl(b) /\ (forall (c : M), b c = true -> x c = true)
)
-> infinite_payoff x = plus_infinity.

Definition multiply_bool (b1 b2 : bool) :=
match b1,b2 with
| true, true => true
| true, false => false
| false, true => false
| false, false => true
end.

Program Fixpoint alternating_walk `(E: EventStructure M)
(A : AsynchronousArena E) (w : Walk E) {measure (length w)} := 
valid_walk E w /\
match w with
| inl(pos) :: nil => True
| inl(pos1) :: inr(m1, ep1) :: inl(pos2) :: nil => True
| inl(pos1) :: inr(m1, ep1) :: inl(pos2) :: inr(m2, ep2) :: xs => 
multiply_bool (polarity m1) ep1 = 
negb (multiply_bool (polarity m2) ep2)
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

Definition is_position `(E: EventStructure M)
(A : AsynchronousArena E) (p : Position E) (sigma : Strategy E A) :=
exists (s : Play E),
sigma s = true /\ nth_error (rev s) 1 = Some (inl(p)).

Definition valid_strategy_walk `(E: EventStructure M)
(A : AsynchronousArena E) (w : Walk E) (sigma : Strategy E A) :=
alternating_walk E A w /\
(length w <= 3
\/
(exists (m n : M) (p q : bool),
nth_error w 1 = Some(inr(m, p)) /\
nth_error (rev w) 1 = Some(inr(n, q)) /\
multiply_bool (polarity m) p = false /\
multiply_bool (polarity n) q = true
)
/\
forall (b : Position E) (a : nat), 4 * a < length w /\
nth_error w (4 * a) = Some (inl(b)) -> 
is_position E A b sigma
).

Definition walk_payoff `(E: EventStructure M)
(A : AsynchronousArena E) (sigma : Strategy E A) :=
forall (w : Walk E),
valid_strategy_walk E A w sigma ->
Z.geb (finite_payoff (inr (w))) (0%Z) = true.

Definition winning_strategy
`(E: EventStructure M)
(A : AsynchronousArena E) (sigma : Strategy E A) :=
total_strategy E A sigma /\
finite_nonnegative E A sigma /\
infinite_nonnegative E A sigma /\
walk_payoff E A sigma.
