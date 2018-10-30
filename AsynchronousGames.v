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

Definition Position `(E : EventStructure M) := list M.

Definition valid_position `(E: EventStructure M) (p : Position E) :=
forall (x y: M), 
(In x p /\ In y p ->  not (incompatible x y))
 /\ 
(In x p /\ leq y x -> In y p)
/\
(NoDup p).

Definition move_from `(E: EventStructure M) 
(m : M) (p1 p2 : Position E) :=
(In m p2) /\ (not (In m p1)) 
/\ (forall (n : M), n <> m -> (In n p1 <-> In n p2)).

Definition Walk `(E: EventStructure M) := 
list (Position E + (M * bool)).

Fixpoint valid_walk `(E: EventStructure M) 
(w : Walk E):=
match w with
| inl(p1) :: nil => valid_position E p1
| inl(p1) :: inr(m, ep) :: ((inl(p2) :: xs) as s) => 
(valid_position E p1) /\ (valid_position E p2) /\ (valid_walk E s) /\
((ep = true /\ move_from E m p1 p2) \/ (ep = false /\ move_from E m p2 p1))
| _ => False
end.

Inductive Infinity : Type :=
| plus_infinity : Infinity
| minus_infinity : Infinity.

Definition initial_move `(E: EventStructure M) (m : M) :=
forall (n : M), In n (ideal m) <-> m = n.

Definition second_move `(E: EventStructure M) (m : M) :=
forall (n : M), In n (ideal m) ->  n = m \/ 
initial_move E m.

Definition InfinitePosition `(E : EventStructure M) := nat -> M.

Class AsynchronousArena `(E : EventStructure M) := {
polarity : M -> bool;
finite_payoff : (Position E + Walk E) -> Z;

infinite_payoff : InfinitePosition E -> Infinity;

initial_incompatible :
forall (m n : M), initial_move E m /\ initial_move E n 
-> incompatible m n;

initial_payoff :
let n := finite_payoff (inl (nil : Position E)) in
 n = (-1)%Z \/ n = (1)%Z;

polarity_first :
forall (m : M), initial_move E m -> 
(polarity m = true -> finite_payoff (inl(nil : Position E)) = (-1)%Z)
/\
(polarity m = false -> finite_payoff (inl(nil : Position E)) = (1)%Z);

polarity_second :
forall (m : M), second_move E m -> 
(polarity m = true -> finite_payoff (inl(nil : Position E)) = (1)%Z)
/\
(polarity m = false -> finite_payoff (inl(nil : Position E)) = (-1)%Z);

initial_null :
forall (w : Walk E) (p : Position E), 
(valid_walk E w /\ w = inl (p) :: nil) -> finite_payoff (inr w) = 0%Z;

noninitial_payoff :
forall (w : Walk E) (p : Position E),
valid_walk E w /\
length w > 1 /\ 
hd_error (rev w) = Some (inl p) /\
In (inl (nil : Position E)) w -> 
finite_payoff (inr w) = finite_payoff (inl p)
}.

Definition Path `(E : EventStructure M) := Walk E.

Definition valid_path `(E : EventStructure M) (p : Walk E) :=
valid_walk E p /\
forall (m : M) (b : bool), In (inr(m, b)) p -> b = true.

Definition Play `(E: EventStructure M) := Walk E.

Definition valid_play `(E : EventStructure M) (p : Walk E) :=
valid_path E p /\
hd_error p = Some (inl(nil : Position E)).

Fixpoint valid_alternating_play `(E: EventStructure M)
(A : AsynchronousArena E) (p : Path E) := 
valid_play E p /\
match p with
| inl(pos) :: nil => True
| inl(pos1) :: inr(m1, ep1) :: inl(pos2) :: nil => True
| inl(pos1) :: inr(m1, ep1) :: ((inl(pos2) :: inr(m2, ep2) :: xs) as s) => 
(valid_walk E s) /\ (polarity m1 = negb (polarity m2))
| _ => False
end.

Definition initialPlay `(E: EventStructure M) : Play E :=
inl(nil : Position E) :: nil.

Fact initial_play_is_valid `(E: EventStructure M) :
valid_play E (initialPlay E).
Proof. unfold valid_play. split.
- unfold valid_path. split.
+ split. 
++ intros. simpl in H. destruct H. contradiction H.
++ split.
+++ intros. simpl in H.  destruct H. inversion H.
+++ apply NoDup_nil.
+ intros. simpl in H. destruct H.
++ inversion H.
++ contradiction H.
- simpl. reflexivity.
Qed.

Fact initial_play_is_alternating `(E: EventStructure M)
(A : AsynchronousArena E) :
valid_alternating_play E A (initialPlay E).
Proof. simpl. split.
- apply initial_play_is_valid.
- auto. Qed. 


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
(f (initialPlay E) = true)
 /\
(forall (s : Play E),
f s = true /\ length s > 1 -> 
exists (m1 m2 : M) (b1 b2 : bool), 
nth_error s 1 = Some (inr(m1, b1)) /\
nth_error (rev s) 1 = Some (inr(m2, b2)) /\
opponent_move E A m1 /\ player_move E A m2)
/\
(forall (s : Play E) (x y z: Position E) (m n: M),
hd_error s = Some (inl (nil : Position E)) /\
hd_error (rev s) = Some (inl x) /\
move_from E m x y /\
opponent_move E A m /\
move_from E n y z /\
player_move E A n ->
f (s ++ ((inr (m,false) :: (inl y) :: 
(inr (n,true)) :: (inl z) :: nil))) = true -> f s = true)
/\
(forall (s : Play E) (x y z1 z2: Position E) (m n1 n2: M),
hd_error s = Some (inl (nil : Position E)) /\
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
p 0 = inl(nil : Position E) /\

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

Definition infinite_position_of_strategy
`(E: EventStructure M) (A : AsynchronousArena E) 
(x : InfinitePosition E) (sigma : Strategy E A) :=
exists (s : InfinitePlay E),
infinite_play_valid E s 
/\
forall (k : nat), sigma (subsequence E s (4 * k)) = true
/\
forall (m : M) (a: nat) (p : Position E), 
(x a = m <->  (exists (b : nat), s b = inl(p) /\ In m p)).


Definition infinite_nonnegative
`(E: EventStructure M) (A : AsynchronousArena E) 
(sigma : Strategy E A) :=
forall (x : InfinitePosition E),
infinite_position_of_strategy E A x sigma
-> infinite_payoff x = plus_infinity.

Definition multiply_bool (b1 b2 : bool) :=
match b1,b2 with
| true, true => true
| true, false => false
| false, true => false
| false, false => true
end.

Fixpoint alternating_walk `(E: EventStructure M)
(A : AsynchronousArena E) (w : Walk E) := 
valid_walk E w /\
match w with
| inl(pos) :: nil => True
| inl(pos1) :: inr(m1, ep1) :: inl(pos2) :: nil => True
| inl(pos1) :: inr(m1, ep1) :: ((inl(pos2) :: inr(m2, ep2) :: xs) as s) => 
(alternating_walk E A s) /\
(multiply_bool (polarity m1) ep1 = 
negb (multiply_bool (polarity m2) ep2))
| _ => False
end.

Definition is_position `(E: EventStructure M)
(A : AsynchronousArena E) (p : Position E) (sigma : Strategy E A) :=
exists (s : Play E),
sigma s = true /\ nth_error (rev s) 1 = Some (inl(p)).

Definition walk_on_strategy `(E: EventStructure M)
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
walk_on_strategy E A w sigma ->
Z.geb (finite_payoff (inr (w))) (0%Z) = true.

Definition winning_strategy
`(E: EventStructure M)
(A : AsynchronousArena E) (sigma : Strategy E A) :=
total_strategy E A sigma /\
finite_nonnegative E A sigma /\
infinite_nonnegative E A sigma /\
walk_payoff E A sigma.

Class Group (A : Type) := {
mult : A -> A -> A;
identity : A;

associative : forall (x y z : A),
mult x (mult y z) = mult (mult x y) z;
identity_exists : forall (x : A), 
mult identity x = mult x identity /\ mult x identity = x;
inverses_exist : forall (x : A),
exists (y : A), mult x y = identity /\ mult y x = identity;
}.


Class AsynchronousGame `(E : EventStructure M) 
(A : AsynchronousArena E) `(X : Group G)
`(Y : Group H) := {
action : G -> M -> H -> M;

action_identity : forall (m : M) (g : G) (h : H),
action identity m identity = m;
action_compatible : forall (m : M) (g g' : G) (h h' : H),
action (mult g g') m (mult h h') = 
action g (action g' m h) h';

coherence_1 : forall (m n : M) (g : G) (h : H),
leq m n -> leq (action g m h) (action g n h);
coherence_2 : forall (m : M) (g : G) (h : H),
polarity (action g m h) = polarity m;
coherence_3 : forall (m : M) (g : G),
(polarity m = false /\ forall (n : M), 
leq m n -> n = action g n identity) -> 
m = action g m identity;
coherence_4 : forall (m : M) (h : H),
(polarity m = true /\ forall (n : M), 
leq m n -> n = action identity n h) -> 
m = action identity m h
}.

Fixpoint action_play `(E : EventStructure M) 
(A : AsynchronousArena E) `(X : Group G) `(Y : Group H)
(B : AsynchronousGame E A X Y)
 (p : Play E) (g : G) (h : H) : Play E :=
match p with
| nil => nil
| inl (s) :: xs => inl (s) :: action_play E A X Y B xs g h
| inr (m,b) :: xs =>
inr (action g m h,b) :: action_play E A X Y B xs g h
end.

Definition uniform_strategy `(E : EventStructure M) 
(A : AsynchronousArena E) `(X : Group G) `(Y : Group H)
(B : AsynchronousGame E A X Y) (sigma : Strategy E A) :=
forall (s : Play E) (h : H),
sigma s = true -> exists (g : G),
sigma (action_play E A X Y B s g h) = true.

Fact negation_negates : (forall (b : bool), 
(negb b = false -> b = true) /\ (negb b = true -> b = false)). 
Proof.
intros. split.
+ destruct b.
- compute. auto.
- compute. auto.
+ destruct b.
- compute. auto.
- compute. auto.
Qed.

Fact zero_equals_zero : (forall (z : Z), (0 - z)%Z = 0%Z <-> z = 0%Z).
Proof.
intros. omega. Qed.

Fact one_equals_one : (forall (z : Z), (0 - z)%Z = (-1)%Z <-> z = 1%Z).
Proof.
intros. omega. Qed.

Fact minusone_equals_minusone : 
(forall (z : Z), (0 - z)%Z = (1)%Z <-> z = (-1)%Z).
Proof.
intros. omega. Qed.

Fact x_equals_x : (forall (x y : Z), (0 - x)%Z = (0-y)%Z <-> x = y).
Proof.
intros. unfold iff. split.
+ intros. omega.
+ intros. omega.
Qed.

Instance dual `(E : EventStructure M) 
(A : AsynchronousArena E) : 
AsynchronousArena E := {

polarity m := negb (polarity m);
finite_payoff c := (0 - (finite_payoff c))%Z;
infinite_payoff p :=
match (infinite_payoff p) with
| plus_infinity => minus_infinity
| minus_infinity => plus_infinity
end;

initial_incompatible := initial_incompatible;
}.

Proof.
- assert (H :
 finite_payoff (inl (nil : Position E)) = (-1)%Z \/ 
finite_payoff (inl (nil : Position E)) = (1)%Z). {apply initial_payoff. }
destruct H.
+ rewrite H. compute. right. reflexivity.
+ rewrite H. compute. left. reflexivity.
- intros. 
assert (forall (m : M), initial_move E m -> 
(polarity m = true -> finite_payoff (inl(nil : Position E)) = (-1)%Z)
/\
(polarity m = false -> finite_payoff (inl(nil : Position E)) = (1)%Z)).
{apply polarity_first. } 
assert ((polarity m = true ->
      finite_payoff (inl (nil : Position E)) =
      (-1)%Z) /\
     (polarity m = false ->
      finite_payoff (inl (nil : Position E)) = 1%Z)).
{apply H0 with (m := m). apply H. }
split.
+ intros. apply negation_negates in H2. destruct H1.
apply one_equals_one. apply H3. apply H2.
+ intros.
apply negation_negates in H2.  destruct H1.
apply minusone_equals_minusone. apply H1. apply H2.
- intros. split.
+ intros. apply negation_negates in H0. apply minusone_equals_minusone.
apply polarity_second with (m0:=m).
++ apply H.
++ apply H0.
+ intros. apply negation_negates in H0. apply one_equals_one.
apply polarity_second with (m0:=m).
++ apply H.
++ apply H0.
- intros. apply zero_equals_zero. apply initial_null with (w0:=w) (p0:=p).
apply H.
- intros. apply x_equals_x. apply noninitial_payoff with (w0:=w) (p0:=p).
apply H.
Defined.

Inductive Singleton : Type :=
| new : Singleton.

Instance lift_partial_order `(M : PartialOrder P) :
PartialOrder (sum P Singleton) :=
{ leq m n := match m,n with
| inl(m), inl(n) => leq m n
| inr(m), _ => True
| _, _ => False
end
}.
Proof. 
- intros. destruct x.
+ apply reflexive.
+ auto.
- intros. destruct x.
+ destruct y.
++ apply anti_symmetric in H. rewrite H. reflexivity.
++ destruct H. contradiction H.
+ destruct y.
++ destruct H. contradiction H0.
++ destruct s. destruct s0. reflexivity.
- intros. destruct x.
+ destruct y.
++ destruct z.
+++ apply transitive in H. apply H.
+++ destruct H. contradiction H0.
++ destruct z.
+++ destruct H. contradiction H.
+++ destruct H. contradiction H.
+ destruct y.
++ destruct z.
+++ auto.
+++ auto.
++ auto.
Defined.

Fact leq_is_preserved `(M : PartialOrder P) :
forall (p q : P), 
let _ := lift_partial_order M in
leq (inl(p)) (inl(q)) <-> leq p q.
Proof. intros. subst l. unfold iff. split. 
+  intros. simpl in H. apply H. 
+ intros. simpl. apply H. Qed.


Fixpoint add_inl (A B : Type) (l : list A) :
list (sum A B) :=
match l with
| nil => nil
| x :: xs => inl(x) :: (add_inl A B xs)
end.
 

Fact add_inl_does_nothing (A B : Type) (l : list A) :
forall (a : A), In a l <-> In (inl(a)) (add_inl A B l).
Proof. intros. unfold iff. split.
+  intros. unfold add_inl. induction l.
++ simpl in H. contradiction H.
++ simpl. simpl in H. destruct H.
+++ left. rewrite H. reflexivity.
+++ right. apply IHl. apply H. 
+ intros. induction l.
++ simpl in H. contradiction H.
++ simpl. simpl in H. destruct H.
+++ left. inversion H. reflexivity.
+++ right. apply IHl. apply H. Qed.

Fact in_tl_in_tl : (forall (A : Type) (a b : A) (l : list A),
In a (b :: l) /\ a <> b -> In a l).
Proof. intros. destruct H. destruct H. contradiction H0. rewrite H.
reflexivity. apply H. Qed.

Fact inl_neq_inr : forall (A B: Type) (a b : A + B),
(exists (x : A) (y : B), a = inl x /\ b = inr y) -> a <> b.
Proof. intros. destruct H. destruct H. destruct H. rewrite H. rewrite H0.
unfold not. intros. inversion H1. Qed.

Instance lift_event_structure 
`(M : PartialOrder P)
(N : EventStructure M)
: EventStructure (lift_partial_order M) :=
{
incompatible m n := match m,n with
| inl(m), inl(n) => incompatible m n
| _, _ => False
end;
ideal m := match m with
| inl(m) => inr(new) :: (add_inl P Singleton (ideal m))
| inr(m) => inr(m) :: nil
end
}.
Proof. intros. destruct x.
+ destruct y.
++ apply symmetric. apply H.
++ apply H.
+ destruct y.
++ apply H.
++ apply H.
+ intros. destruct x.
++ apply irreflexive.
++ auto.
+ intros. destruct x.
++ destruct y.
+++ unfold iff. split.
++++ intros. apply in_cons. apply add_inl_does_nothing.
assert (leq p0 p).
{ apply (leq_is_preserved M). apply H. }
apply ideal_finite. apply H0.
++++ intros. 
assert (In (inl p0)(add_inl P Singleton (ideal p))).
{ apply in_tl_in_tl with (b:= inr new). split.
+ apply H.
+ apply inl_neq_inr. pose (witness := p0).
  refine (ex_intro _ witness _). 
pose (witness1 := new).
  refine (ex_intro _ witness1 _).
split.
++ auto.
++ auto.
}
apply leq_is_preserved. apply add_inl_does_nothing in H0. apply ideal_finite.
apply H0.
+++ unfold iff. assert (s = new). { destruct s.  reflexivity. } split.
++++ intros. rewrite H. compute. left. reflexivity.
++++ intros. compute. auto.
++ unfold iff. split.
+++ intros. assert (s = new). { destruct s.  reflexivity. } rewrite H0 in H.
rewrite H0. destruct y.
++++ compute in H. contradiction H.
++++ assert (s0 = new). { destruct s0.  reflexivity. }
rewrite H1. compute. left. reflexivity.
+++ intros. assert (s = new). { destruct s.  reflexivity. } rewrite H0 in H.
destruct y.
++++ compute in H. destruct H.
+++++ inversion H.
+++++ contradiction H.
++++ assert (s0 = new). { destruct s0.  reflexivity. } rewrite H0. rewrite H1.
apply reflexive.
+ intros. destruct x.
++ destruct z.
+++ destruct y.
++++ apply incompatible_closed with (y:= p1). destruct H.
split.
+++++ apply H.
+++++ apply -> (leq_is_preserved M). apply H0.
++++ destruct H. contradiction H.
+++ destruct y.
++++ destruct H. assert (s = new). { destruct s.  reflexivity. }
rewrite H1 in H0. compute in H0. contradiction H0.
++++ destruct H. contradiction H.
++ destruct H. contradiction H.
Defined.


Definition not_contains_initial `(E : EventStructure M) (w : Walk E) :=
In (inl(nil : Position E)) w.

Definition empty_on_initial `(E : EventStructure M) (w : Walk E) :=
match w with
| inl(nil) :: nil => true
| _ => false
end.

Instance lift_asynchronous_arena 
`(M : PartialOrder P)
(eq_dec : forall x y : (P + Singleton), {x = y} + {x <> y})
(E : EventStructure M)
(A : AsynchronousArena E)
(p : nat)
: AsynchronousArena (lift_event_structure M E) :=
{
finite_payoff m := match m with
| inl(nil) => (-1)%Z
| inl(inr(new) :: nil) => Z.of_nat p
| inl(xs) => 
finite_payoff (inl(remove eq_dec (inr(new)) xs))
| _ => 0%Z
end
}.





