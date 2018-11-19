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
(In x p /\ leq y x -> In y p).

Definition move_from `(E: EventStructure M) 
(m : M) (p1 p2 : Position E) :=
(forall (n : M), In n p1 -> In n p2) /\
(forall (n : M), (not (In n p1) /\ In n p2) <-> n = m).

Inductive Walk `(E: EventStructure M) := 
| empty_walk : Position E -> Walk E
| non_empty_walk : Position E -> (M * bool) -> Walk E -> Walk E.

Inductive valid_walk `(E: EventStructure M) (w : Walk E) : Prop :=
| valid_empty_walk : 
forall p, w = (empty_walk E p) ->
valid_position E p -> valid_walk E w
| valid_one_move_walk :
forall p1 m ep p2, 
w = (non_empty_walk E p1 (m, ep) (empty_walk E p2)) ->
(valid_position E p1) /\ (valid_walk E (empty_walk E p2)) /\
((ep = true /\ move_from E m p1 p2) \/ (ep = false /\ move_from E m p2 p1))
-> valid_walk E w
| valid_non_empty_walk :
forall p1 m ep p2 m' w',
w = (non_empty_walk E p1 (m, ep) (non_empty_walk E p2 m' w')) ->
(valid_position E p1) /\ (valid_walk E (non_empty_walk E p2 m' w')) /\
((ep = true /\ move_from E m p1 p2) \/ (ep = false /\ move_from E m p2 p1))
-> valid_walk E w.

Fixpoint length_walk `(E: EventStructure M) (w : Walk E) :=
match w with
| empty_walk _ _ => 1
| non_empty_walk _ _ _ w => 2 + (length_walk E w)
end.


Fact beq_nat_iff_equal : forall m n, (m =? n) = true <-> m = n.
Proof. intros. unfold iff. split.
+ intros. apply beq_nat_true. apply H.
+ intros. rewrite H. induction n.
++ simpl. reflexivity.
++ simpl.
assert (forall n, (n =? n) = true).
{ intros. induction n0. 
+  simpl. reflexivity.
+ simpl. apply IHn0. }
apply H0.
Qed.

Fixpoint source_walk `(E: EventStructure M) (w : Walk E) :=
match w with
| empty_walk _ p => p
| non_empty_walk _ p _ _ => p
end.

Fixpoint target_walk `(E: EventStructure M) (w : Walk E) :=
match w with
| empty_walk _ p => p
| non_empty_walk _ _ _ w => target_walk E w
end.

Fixpoint position_in_walk `(E: EventStructure M) (p : Position E) (w : Walk E) :=
match w with
| empty_walk _ p' => p' = p
| non_empty_walk _ p' _ w => (p' = p) \/ (position_in_walk E p w)
end.

Fact target_in_walk `(E: EventStructure M)
: forall p w, target_walk E w = p -> position_in_walk E p w.
Proof. intros. induction w.
+ simpl. simpl in H. auto.
+ simpl in H. simpl. right. apply IHw. apply H.
Qed.

Fixpoint move_in_walk `(E: EventStructure M) p (w : Walk E) :=
match w with
| empty_walk _ p' => False
| non_empty_walk _ _ p' w => (p' = p) \/ (move_in_walk E p w)
end.

Inductive Infinity : Type :=
| plus_infinity : Infinity
| minus_infinity : Infinity.

Definition initial_move `(E: EventStructure M) (m : M) :=
forall (n : M), In n (ideal m) <-> m = n.

Definition second_move `(E: EventStructure M) (m : M) :=
(forall (n : M), In n (ideal m) -> (n = m \/ initial_move E n))
/\
(exists (n : M), In n (ideal m) /\ n <> m).

Inductive InfinitePosition `(E : EventStructure M) : Type := 
| stream : M -> (unit -> InfinitePosition E)
-> InfinitePosition E.

Class AsynchronousArena `(E : EventStructure M) := {
polarity : M -> bool;
finite_payoff : (Position E + Walk E) -> Z;

infinite_payoff : InfinitePosition E -> Infinity;

initial_incompatible :
forall (m n : M), initial_move E m /\ initial_move E n /\ m <> n
-> incompatible m n;

initial_payoff :
let n := finite_payoff (inl (nil : Position E)) in
 n = (-1)%Z \/ n = (1)%Z;

polarity_first :
forall (m : M), initial_move E m -> 
(polarity m = true <-> finite_payoff (inl(nil : Position E)) = (-1)%Z)
/\
(polarity m = false <-> finite_payoff (inl(nil : Position E)) = (1)%Z);

polarity_second :
forall (m : M), second_move E m -> 
(polarity m = true -> finite_payoff (inl(nil : Position E)) = (1)%Z)
/\
(polarity m = false -> finite_payoff (inl(nil : Position E)) = (-1)%Z);

initial_null :
forall (w : Walk E) (p : Position E), 
(valid_walk E w /\ w = empty_walk E p) -> finite_payoff (inr w) = 0%Z;

noninitial_payoff :
forall (w : Walk E) (p : Position E),
valid_walk E w /\
length_walk E w > 1 /\ 
target_walk E w = p /\
position_in_walk E nil w -> 
finite_payoff (inr w) = finite_payoff (inl p)
}.

Class Group (A : Type) := {
mult : A -> A -> A;
identity : A;
inverse : A -> A;

associative : forall (x y z : A),
mult x (mult y z) = mult (mult x y) z;
identity_exists : forall (x : A), 
mult identity x = x /\ mult x identity = x;
inverses_exist : forall (x : A),
mult x (inverse x) = identity /\ mult (inverse x) x = identity;
}.

Class AsynchronousGame `(E : EventStructure M) 
(A : AsynchronousArena E) `(X : Group G)
`(Y : Group H) := {
action : G -> M -> H -> M;

action_identity : forall (m : M),
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

Fact negation_negates : (forall (b : bool), 
(negb b = false <-> b = true) /\ (negb b = true <-> b = false)). 
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
(polarity m = true <-> finite_payoff (inl(nil : Position E)) = (-1)%Z)
/\
(polarity m = false <-> finite_payoff (inl(nil : Position E)) = (1)%Z)).
{apply polarity_first. } 
assert ((polarity m = true <->
      finite_payoff (inl (nil : Position E)) =
      (-1)%Z) /\
     (polarity m = false <->
      finite_payoff (inl (nil : Position E)) = 1%Z)).
{apply H0 with (m := m). apply H. }
split.
+ intros. unfold iff. split.
++ intros. apply negation_negates in H2. destruct H1.
apply one_equals_one. apply H3. apply H2.
++ intros. apply negation_negates. destruct H1.
apply one_equals_one in H2. apply H3. apply H2.
+ intros. unfold iff. split.
++ intros. apply negation_negates with (b:= polarity m) in H2. destruct H1.
apply minusone_equals_minusone. apply H1. rewrite H2. reflexivity.
++ intros. apply minusone_equals_minusone in H2. apply negation_negates
with (b:= polarity m). destruct H1. apply H1. apply H2.
- intros. split.
+ intros. apply negation_negates in H0. apply minusone_equals_minusone.
apply polarity_second with (m0:=m).
++ apply H.
++ apply H0.
+ intros. apply negation_negates in H0. apply one_equals_one.
apply polarity_second with (m0:=m).
++ apply H.
++ apply negation_negates in H0. apply negation_negates
with (b:=polarity m) in H0. apply H0.
- intros. apply zero_equals_zero. apply initial_null with (w0:=w) (p0:=p).
apply H.
- intros. apply x_equals_x. apply noninitial_payoff with (w0:=w) (p0:=p).
apply H.
Defined.

Fact inverse_is_unique `(G: Group A) : forall (x y z: A),
mult x y = identity /\ mult x z = identity -> y = z.
Proof. intros. destruct H. rewrite <- H in H0.
assert (mult (inverse x) (mult x z) = mult (inverse x) (mult x y) ).
{  rewrite H0. reflexivity. }
rewrite associative in H1. rewrite associative in H1.
assert (mult (inverse x) x = identity).
{ apply inverses_exist. }
rewrite H2 in H1. 
assert (mult identity z = z /\ mult identity y = y).
{ split. 
+ apply identity_exists.
+ apply identity_exists. }
destruct H3. rewrite H3 in H1. rewrite H4 in H1. auto.
Qed.

Fact mult_inverse `(G: Group A) : forall (g g': A),
mult (inverse g') (inverse g) = inverse (mult g g').
Proof. intros. 
assert (mult (mult g g') (mult (inverse g') (inverse g)) = identity /\
mult (mult g g') (inverse (mult g g')) = identity).
{ assert (mult (mult g g') (inverse (mult g g')) = identity).
{ apply inverses_exist. }
assert (mult (mult g g') (mult (inverse g') (inverse g)) = identity).
{ rewrite associative. 
assert (mult (mult g g') (inverse g') = g).
{ rewrite <- associative.
assert (mult g' (inverse g') = identity).
{ apply inverses_exist. }
rewrite H0. apply identity_exists.
  }
rewrite H0. apply inverses_exist.
 }
rewrite H. rewrite H0. auto.
} apply inverse_is_unique with (G0:=G) (x:=mult g g')
(y:=mult (inverse g') (inverse g)) (z:=inverse (mult g g')).
auto.
Qed.

Fact inverse_identity_is_identity `(G: Group A) :
inverse identity = identity.
Proof. apply inverse_is_unique with (G0:=G) (x:=identity) 
(y:= inverse identity) (z:=identity). 
split.
+ apply inverses_exist.
+ apply identity_exists.
Qed.

Instance dual_game `(E : EventStructure M) 
(A : AsynchronousArena E)
`(X : Group G)
`(Y : Group H)
(Game : AsynchronousGame E A X Y): 
AsynchronousGame E (dual E A) Y X:= {
action h m g := action (inverse g) m (inverse h)}.
Proof.
- intros.
assert (((inverse identity) : G) = (identity : G)).
{ apply inverse_identity_is_identity. } rewrite H0. 
assert (((inverse identity) : H) = (identity : H)).
{ apply inverse_identity_is_identity. } rewrite H1.
apply action_identity.
- intros.
assert (inverse (mult h h') = mult (inverse h') (inverse h)).
{ rewrite mult_inverse. reflexivity. }
rewrite H0.
assert (inverse (mult g g') = mult (inverse g') (inverse g)).
{ rewrite mult_inverse. reflexivity. }
rewrite H1. apply action_compatible.
- intros. apply coherence_1. apply H0.
- intros. simpl. assert (forall a b, negb a = negb b <-> a = b).
{ intros. unfold iff. split. 
-  intros. destruct a.
+ simpl in H0. destruct b.
++ reflexivity.
++ simpl in H0. inversion H0.
+ destruct b.
++ simpl in H0. inversion H0.
++ reflexivity.
- intros. rewrite H0. reflexivity. }
rewrite H0. apply coherence_2.
- intros. rewrite inverse_identity_is_identity.
rewrite inverse_identity_is_identity in H0.
apply coherence_4. simpl in H0. 
assert (forall b, negb b = false <-> b = true).
{ intros. unfold iff. split.
+ intros. destruct b.
++ reflexivity.
++ simpl in H1. inversion H1.
+ intros. rewrite H1. simpl. reflexivity.  }
rewrite H1 in H0. auto.

- intros. rewrite inverse_identity_is_identity.
rewrite inverse_identity_is_identity in H0.
apply coherence_3. simpl in H0.
assert (forall b, negb b = true <-> b = false).
{ intros. unfold iff. split.
+ intros. destruct b.
++ simpl in H1. inversion H1.
++ reflexivity.
+ intros. rewrite H1. simpl. reflexivity.  }
rewrite H1 in H0. auto.
Qed.

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

Fixpoint add_inl (A B : Type) (l : list A) : list (sum A B) :=
match l with
| nil => nil
| x :: xs => inl(x) :: (add_inl A B xs)
end.

Fixpoint add_inr (A B : Type) (l : list B) : list (sum A B) :=
match l with
| nil => nil
| x :: xs => inr(x) :: (add_inr A B xs)
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

Fact add_inr_does_nothing (A B : Type) (l : list B) :
forall (b : B), In b l <-> In (inr b) (add_inr A B l).
Proof. intros. unfold iff. split.
+  intros. induction l.
++ simpl in H. contradiction H.
++ simpl. simpl in H. destruct H.
+++ left. rewrite H. reflexivity.
+++ right. apply IHl. apply H. 
+ intros. induction l.
++ simpl in H. contradiction H.
++ simpl. simpl in H. destruct H.
+++ left. inversion H. reflexivity.
+++ right. apply IHl. apply H. Qed.

Fact inr_not_in_add_inl (A B : Type) (l : list A) :
forall (b : B), not (In (inr b) (add_inl A B l)).
Proof.
intros. unfold not. intros. induction l.
+ simpl in H. apply H.
+ simpl in H. destruct H.
++ inversion H.
++ apply IHl. apply H.
Qed.

Fact inl_not_in_add_inr (A B : Type) (l : list B) :
forall (a : A), not (In (inl a) (add_inr A B l)).
Proof.
intros. unfold not. intros. induction l.
+ simpl in H. apply H.
+ simpl in H. destruct H.
++ inversion H.
++ apply IHl. apply H.
Qed.

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

Fixpoint cast_to_left (A B : Type) (l : list (A + B)) : list A := 
match l with
| nil => nil
| inl(x) :: xs => x :: (cast_to_left A B xs)
| inr(x) :: xs => (cast_to_left A B xs)
end.

Fixpoint cast_to_right (A B : Type) (l : list (A + B)) : list B := 
match l with
| nil => nil
| inr(x) :: xs => x :: (cast_to_right A B xs)
| inl(x) :: xs => (cast_to_right A B xs)
end.

Fact cast_to_left_is_boring (A B : Type) (x : A) (l : list (A + B)):
In x (cast_to_left A B l) <-> In (inl(x)) l.
Proof. unfold iff. split.
+ intros. induction l.
++ simpl in H. contradiction H.
++ simpl in H. simpl. destruct a.
+++ destruct H.
++++ left. rewrite H. reflexivity.
++++ right. apply IHl. apply H.
+++ right. apply IHl. apply H.
+ intros. induction l.
++ simpl in H. contradiction H.
++ simpl. destruct a.
+++ simpl. simpl in H. destruct H.
++++ left. inversion H. reflexivity.
++++ right. apply IHl. apply H.
+++ apply IHl. destruct H.
++++ inversion H.
++++ apply H.
Qed.

Fact cast_to_right_is_boring (A B : Type) (x : B) (l : list (A + B)):
In x (cast_to_right A B l) <-> In (inr(x)) l.
Proof. unfold iff. split.
+ intros. induction l.
++ simpl in H. contradiction H.
++ simpl in H. destruct a.
+++ apply in_cons. apply IHl. apply H.
+++ simpl in H. destruct H.
++++ simpl. left. rewrite H. reflexivity.
++++ simpl. right. apply IHl. apply H.
+ intros. induction l.
++ simpl in H. contradiction H.
++ destruct a.
+++ destruct H.
++++ inversion H.
++++ simpl. apply IHl. apply H.
+++ simpl. simpl in H. destruct H.
++++ left. inversion H. reflexivity.
++++ right. apply IHl. apply H.
Qed.

Fixpoint contains_initial `(E : EventStructure M) (w : Walk E) :=
match w with
| empty_walk _ nil => true
| empty_walk _ _ => false
| non_empty_walk _ nil _ w => true
| non_empty_walk _ _ _ w => contains_initial E w
end.

Fact contains_initial_if_nil_position_in_walk `(E : EventStructure M) (w : Walk E)
: position_in_walk E nil w <-> contains_initial E w = true.
Proof. intros. induction w.
+ simpl. split.
++ intros. subst p. reflexivity.
++ destruct p.
+++ auto.
+++ intros. inversion H.
+ split.
++ intros. simpl. simpl in H. destruct H.
+++ subst p. reflexivity.
+++ destruct p.
++++ reflexivity.
++++ apply IHw. apply H.
++ intros. simpl. simpl in H. destruct p.
+++ left. reflexivity.
+++ right. apply IHw. apply H.
Qed.

Fixpoint remove_sum `(M : PartialOrder P)
(E : EventStructure M)
(w : Walk (lift_event_structure M E)) : Walk E :=
match w with
| empty_walk _ p => empty_walk E (cast_to_left P Singleton p)
| non_empty_walk _ p (inl m ,b) w =>
non_empty_walk E (cast_to_left P Singleton p) (m, b) (remove_sum M E w)
| non_empty_walk _ p (inr m ,b) w => remove_sum M E w
end.

Fixpoint lower_infinite_position
`(M : PartialOrder P)
(E : EventStructure M)
(p : InfinitePosition (lift_event_structure M E)) :
InfinitePosition E
:= match p with
| stream _ (inr m) f => lower_infinite_position M E (f tt)
| stream _ (inl m) f => 
stream E m (fun _ => lower_infinite_position M E (f tt))
end.

Instance lift_asynchronous_arena 
`(M : PartialOrder P)
(E : EventStructure M)
(A : AsynchronousArena E)
(p : nat)
(negative : finite_payoff (inl nil) = (1)%Z)
: AsynchronousArena (lift_event_structure M E) :=
{
finite_payoff m := 
let g k :=
(match k with
| nil => (-1)%Z
| inr(new) :: nil => Z.of_nat p
| xs => finite_payoff (inl (cast_to_left P Singleton xs ))
end) in
match m with
| inl(k) => g k
| inr(w) => 
if negb (contains_initial (lift_event_structure M E) w) then 
finite_payoff (inr(remove_sum M E w)) else 
(match w with
| empty_walk _ nil => 0%Z
| _ => g (target_walk (lift_event_structure M E) w)
end)
end;
infinite_payoff p :=
infinite_payoff (lower_infinite_position _ _ p);
polarity m :=
match m with
| inl(p) => polarity p
| _ => true
end
}.
Proof.
assert 
(H : forall n, initial_move (lift_event_structure M E) n <-> n = inr(new)).
{ intros.  destruct n. 
+ unfold iff. split.
++ intros. unfold initial_move in H. 
assert (In (inr(new)) (ideal (inl p0))).
{ simpl. left. reflexivity. }
assert (inl(p0) = inr(new)).
{ apply H. apply H0. }
apply H1.
++ intros. inversion H.
+ unfold iff. split.
++ intros. destruct s. reflexivity.
++ intros. unfold initial_move. intros. simpl. unfold iff. split.
+++ intros. destruct H0. apply H0. contradiction H0.
+++ intros. left. apply H0.
}
- intros. destruct m. 
++ destruct H0.
assert (inl(p0) = inr(new)).
{ apply -> H. apply H0. }
inversion H2.
++ destruct n.
+++ destruct H0. destruct H1.
assert (inl(p0) = inr(new)).
{ apply -> H. apply H1. }
inversion H3.
+++ destruct H0. destruct H1.  contradiction H2. destruct s. destruct s0.
reflexivity.
- simpl. left. reflexivity.
- intros.
assert 
(H' : forall n, initial_move (lift_event_structure M E) n <-> n = inr(new)).
{ intros.  destruct n. 
+ unfold iff. split.
++ intros. unfold initial_move in H0. 
assert (In (inr(new)) (ideal (inl p0))).
{ simpl. left. reflexivity. }
assert (inl(p0) = inr(new)).
{ apply H0. apply H1. }
apply H2.
++ intros. inversion H0.
+ unfold iff. split.
++ intros. destruct s. reflexivity.
++ intros. unfold initial_move. intros. simpl. unfold iff. split.
+++ intros. destruct H1. apply H1. contradiction H1.
+++ intros. left. apply H1.
}
assert (m = inr(new)).
{ apply -> H'. apply H. } 
split.
+ rewrite H0. intros. unfold iff. auto. 
+ rewrite H0. intros. unfold iff. split.
++ intros. inversion H1.
++ intros. omega.
- intros.
destruct m. unfold second_move in H.
assert (initial_move E p0).
{unfold initial_move. intros. unfold iff. split.
+ intros. 
assert
(H' : forall n, initial_move (lift_event_structure M E) n <-> n = inr(new)).
{ intros.  destruct n0. 
+ unfold iff. split.
++ intros. unfold initial_move in H1. 
assert (In (inr(new)) (ideal (inl p1))).
{ simpl. left. reflexivity. }
assert (inl(p1) = inr(new)).
{ apply H1. apply H2. }
apply H3.
++ intros. inversion H1.
+ unfold iff. split.
++ intros. destruct s. reflexivity.
++ intros. unfold initial_move. intros. simpl. unfold iff. split.
+++ intros. destruct H2. apply H2. contradiction H2.
+++ intros. left. apply H2.
}

assert ((inl(n) : P + Singleton) = (inl(p0) : P + Singleton) \/
    initial_move (lift_event_structure M E) (inl(n))).
{ apply H. simpl. right. apply (add_inl_does_nothing P Singleton).
apply H0. }
destruct H1. inversion H1. reflexivity.

assert (inl(n) = inr(new)).
{ apply -> H'. apply H1. }
inversion H2.
+ intros. apply ideal_finite. rewrite H0. apply reflexive.
 }
split.
+ intros.
assert (polarity p0 = false).
{ apply polarity_first. apply H0. apply negative. }
rewrite H1 in H2. inversion H2.
+ intros. reflexivity.
+ unfold second_move in H. destruct H. destruct H0.
destruct x.
++ simpl in H0. destruct H0. destruct H0.
+++ inversion H0.
+++ contradiction H0.
++ destruct H0. destruct s0. destruct s. contradiction H1.
reflexivity.
- intros. 
destruct (negb (contains_initial (lift_event_structure M E) w)) eqn:H'.
+ destruct w.
++ simpl. destruct H. inversion H0. subst p1.
assert (valid_walk E (empty_walk E (cast_to_left P Singleton p0))).
{ apply valid_empty_walk with (p1:=cast_to_left P Singleton p0).
+ reflexivity.
+ inversion H. inversion H1. subst p1.
++ unfold valid_position. unfold valid_position in H2. intros. split.
+++ intros.
assert (~ incompatible (inl x) (inl y)).
{ apply H2. destruct H3. split.
++ apply cast_to_left_is_boring. apply H3.
++ apply cast_to_left_is_boring. apply H4.  }
simpl in H4. apply H4.
+++ intros. destruct H3.
apply cast_to_left_is_boring.
assert (In (inl y) p0).
{ apply H2 with (x:=inl x). split.
+ apply cast_to_left_is_boring. apply H3.
+ simpl. apply H4.
 } apply H5.
++ inversion H1.
++ inversion H1.
}
apply initial_null with
(p1:=(cast_to_left P Singleton p0)). split.
+++ apply H1.
+++ reflexivity.
++ destruct H. inversion H0.
+ simpl. destruct w.
++ destruct H. inversion H0. subst p1.
apply negation_negates with
(b:=(contains_initial (lift_event_structure M E)
          (empty_walk (lift_event_structure M E) p0))) in H'.
simpl in H'. destruct p0.
+++ reflexivity.
+++ inversion H'.
++ destruct H. inversion H0.
- intros. destruct H. destruct H0. destruct H1. destruct w.
+ simpl in H0. lia.
+ apply contains_initial_if_nil_position_in_walk in H2.
apply negation_negates in H2.
destruct
(negb
    (contains_initial (lift_event_structure M E)
       (non_empty_walk (lift_event_structure M E)
          p1 p2 w))) eqn:H'.
++ inversion H2.
++ simpl. simpl in H1. subst p0. reflexivity.
Defined.

Fact reverse_inversion_left A B:
forall (a a' : A), (inl a : A + B) = (inl a' : A + B) <-> a = a'.
Proof.
intros. unfold iff. split.
+ intros. inversion H. reflexivity.
+ intros. rewrite H. reflexivity.
Qed.

Fact reverse_inversion_right A B:
forall (a a' : B), (inr a : A + B) = (inr a' : A + B) <-> a = a'.
Proof.
intros. unfold iff. split.
+ intros. inversion H. reflexivity.
+ intros. rewrite H. reflexivity.
Qed.

Fact reverse_inversion_opposite_left A B:
forall (a a' : A), (inl a : A + B) <> (inl a' : A + B) <-> a <> a'.
Proof.
intros. unfold iff. split.
+ intros. unfold not in H. unfold not. intros. apply H. 
apply reverse_inversion_left. apply H0.
+ intros. unfold not in H. unfold not. intros. apply H.
apply reverse_inversion_left in H0. apply H0.
Qed.

Fact reverse_inversion_opposite_right A B:
forall (a a' : B), (inr a : A + B) <> (inr a' : A + B) <-> a <> a'.
Proof.
intros. unfold iff. split.
+ intros. unfold not in H. unfold not. intros. apply H. 
apply reverse_inversion_right. apply H0.
+ intros. unfold not in H. unfold not. intros. apply H.
apply reverse_inversion_right in H0. apply H0.
Qed.

Instance lift_asynchronous_game 
`(M : PartialOrder P)
(E : EventStructure M)
(A : AsynchronousArena E)
`(X : Group G)
`(Y : Group H)
(Game : AsynchronousGame E A X Y)
(p : nat)
(negative : finite_payoff (inl nil) = (1)%Z)
: AsynchronousGame (lift_event_structure M E)
(lift_asynchronous_arena M E A p negative) X Y := {
action g m h :=
match m with
| inl m => inl (action g m h)
| inr m => inr m
end
}.
Proof.
- intros. destruct m.
+ apply reverse_inversion_left. apply action_identity.
+ reflexivity.
- intros. destruct m.
+ apply reverse_inversion_left. apply action_compatible.
+ reflexivity.
- intros. destruct m.
+ destruct n.
++ simpl. simpl in H0. apply coherence_1. apply H0.
++ simpl in H0. contradiction H0.
+ destruct n.
++ simpl. auto.
++ simpl. auto.
- intros. destruct m.
+ simpl. apply coherence_2.
+ reflexivity.
- intros. destruct m.
+ apply reverse_inversion_left. apply coherence_3.
simpl in H0. destruct H0. split.
++ apply H0.
++ intros. 
assert (n = action g n identity <->
(inl n : P + Singleton) = inl (action g n identity)).
{ rewrite reverse_inversion_left. unfold iff. auto.  }
apply H3. apply H1. apply H2.
+ reflexivity.
- intros. destruct m.
+ apply reverse_inversion_left. apply coherence_4.
simpl in H0. destruct H0. split.
++ apply H0.
++ intros. 
assert (n = action identity n h <->
(inl n : P + Singleton) = inl (action identity n h)).
{ rewrite reverse_inversion_left. unfold iff. auto.  }
apply H3. apply H1. apply H2.
+ reflexivity.
Defined.

Definition empty_type := {b : bool | False}.

Instance zero_partial_order : PartialOrder empty_type := {
leq x y := True
}.
Proof.
- intros. destruct x. contradiction f.
- intros. destruct x. contradiction f.
- intros. destruct x. contradiction f.
Defined.

Instance zero_event_structure : 
EventStructure zero_partial_order := {
incompatible x y := True;
ideal x := nil
}.
Proof. 
- intros. destruct x. contradiction f.
- intros. destruct x. contradiction f.
- intros. destruct x. contradiction f.
- intros. destruct x. contradiction f.
Defined.

Instance zero_asynchronous_arena : 
AsynchronousArena zero_event_structure := {
polarity m := true;
finite_payoff m := 
match m with
| inl _ => (-1)%Z
| inr _ => 0%Z
end;
infinite_payoff m := plus_infinity
}.
Proof. 
- intros. destruct m. contradiction f.
- intros. subst n. left. reflexivity.
- intros. destruct m. contradiction f.
- intros. destruct m. contradiction f.
- intros. reflexivity.
- intros. destruct H. destruct H0. destruct H1.
destruct w.
+ simpl in H0. omega.
+ destruct p.
++ destruct p1. destruct e. contradiction f.
++ destruct p1. destruct e. contradiction f.
Defined.

Instance trivial_group : Group Singleton := {
mult a b := new;
identity := new
}.
Proof.
- auto.
- auto.
- intros. destruct x. auto.
- auto.
Defined.

Instance product_group `(X : Group G) `(Y : Group H) : 
Group (G * H) := {
mult m n := match m, n with
(g, h), (g', h') => (mult g g', mult h h')
end;
identity := (identity, identity);
inverse m := match m with
(g, h) => (inverse g, inverse h)
end
}.
Proof.
- intros. destruct x. destruct y. destruct z.
rewrite associative. rewrite associative. reflexivity.
- intros. destruct x.
assert (mult identity g = g /\ mult g identity = g).
{ apply identity_exists. }
assert (mult identity h = h /\ mult h identity = h).
{ apply identity_exists. }
destruct H0. destruct H1.
rewrite H0. rewrite H1. rewrite H2. rewrite H3. auto.
- intros. destruct x. 
assert (mult g (inverse g) = identity 
/\ mult (inverse g) g = identity).
{ apply inverses_exist. }
assert (mult h (inverse h) = identity 
/\ mult (inverse h) h = identity).
{ apply inverses_exist. }
destruct H0. destruct H1.
rewrite H0. rewrite H1. rewrite H2. rewrite H3. auto.
Defined.

Instance zero_asynchronous_game : 
AsynchronousGame zero_event_structure
zero_asynchronous_arena trivial_group trivial_group := {
action g m h := m
}.
Proof.
- intros. destruct m. contradiction f.
- intros. destruct m. contradiction f.
- intros. destruct m. contradiction f.
- intros. destruct m. contradiction f.
- intros. destruct m. contradiction f.
- intros. destruct m. contradiction f.
Defined.

Definition top := dual_game
zero_event_structure
zero_asynchronous_arena
trivial_group
trivial_group
zero_asynchronous_game.

Fact negative :
let _ := (dual zero_event_structure zero_asynchronous_arena) in
finite_payoff (inl nil) = (1)%Z.
Proof. simpl. reflexivity. Qed. 

Definition one := lift_asynchronous_game
zero_partial_order
zero_event_structure
(dual zero_event_structure zero_asynchronous_arena)
trivial_group
trivial_group
top
0
negative.

Instance partial_order_sum `(P : PartialOrder A) `(Q : PartialOrder B) :
PartialOrder (A + B) := {
leq m n :=
match m, n with
| inl m, inl n => leq m n
| inr m, inr n => leq m n
| _, _ => False
end
}.
Proof.
- intros. destruct x.
+ apply reflexive.
+ apply reflexive.
- intros. destruct x.
+ destruct y.
++ apply reverse_inversion_left. apply anti_symmetric. apply H.
++ destruct H. contradiction H.
+ destruct y.
++ destruct H. contradiction H.
++ apply reverse_inversion_right. apply anti_symmetric. apply H.
- destruct x.
+ destruct y.
++ destruct z.
+++ apply transitive.
+++ intros. destruct H. contradiction H0.
++ destruct z.
+++ intros. destruct H. contradiction H.
+++ intros. destruct H. contradiction H.
+ destruct y.
++ destruct z.
+++ intros. destruct H. contradiction H.
+++ intros. destruct H. contradiction H.
++ destruct z.
+++ intros. destruct H. contradiction H0.
+++ apply transitive.
Defined.

Instance event_structure_sum
`(P : PartialOrder A) `(Q : PartialOrder B)
(E : EventStructure P) (F : EventStructure Q) :
EventStructure (partial_order_sum P Q) :=
{ incompatible m n := 
match m,n with
| inl m, inl n => incompatible m n
| inr m, inr n => incompatible m n
| _, _ => True
end;
ideal m := match m with
| inl m => add_inl A B (ideal m)
| inr m => add_inr A B (ideal m)
end
}.
Proof.
- destruct x.
+ destruct y.
++ apply symmetric.
++ auto.
+ destruct y.
++ auto.
++ apply symmetric.
- intros. destruct x.
+ apply irreflexive.
+ apply irreflexive.
- intros. destruct x.
+ destruct y.
++ intros. unfold iff. split.
+++ intros. simpl in H. apply add_inl_does_nothing.
apply ideal_finite. apply H.
+++ intros. simpl. apply add_inl_does_nothing in H. 
apply ideal_finite. apply H.
++ unfold iff. split.
+++ intros. simpl in H. contradiction H.
+++ intros. 
assert (not (In (inr b) (add_inl A B (ideal a)))).
{ apply inr_not_in_add_inl. }
contradiction H0.
+ unfold iff. split.
++ intros. destruct y.
+++ simpl in H. contradiction H.
+++ apply add_inr_does_nothing. apply ideal_finite.
simpl in H. apply H.
++ destruct y.
+++ intros.
assert (not (In (inl a) (add_inr A B (ideal b)))).
{ apply inl_not_in_add_inr. }
contradiction H0.
+++ intros. apply add_inr_does_nothing in H. simpl. apply ideal_finite.
apply H.
- intros. destruct x.
+ destruct y.
++ destruct z.
+++ simpl in H. apply incompatible_closed with (y:=a0). apply H.
+++ auto.
++ destruct z.
+++ destruct H. simpl in H0. contradiction H0.
+++ auto.
+ destruct y.
++ destruct z.
+++ auto.
+++ simpl in H. destruct H. contradiction H0.
++ destruct z.
+++ auto.
+++ simpl in H. apply incompatible_closed with (y:=b0). apply H.
Defined.

Fixpoint cast_to_left_in_walk 
`(P : PartialOrder X)
`(Q : PartialOrder Y)
(E : EventStructure P)
(F : EventStructure Q)
(w : Walk (event_structure_sum P Q E F)) : Walk E
:= match w with
| empty_walk _ p => empty_walk E (cast_to_left X Y p)
| non_empty_walk _ p (inl m, b) w
=> non_empty_walk _ (cast_to_left X Y p) (m, b) 
(cast_to_left_in_walk P Q E F w)
| non_empty_walk _ p (inr m, b) w
=> cast_to_left_in_walk P Q E F w
end. 

Fixpoint cast_to_right_in_walk 
`(P : PartialOrder X)
`(Q : PartialOrder Y)
(E : EventStructure P)
(F : EventStructure Q)
(w : Walk (event_structure_sum P Q E F)) : Walk F
:= match w with
| empty_walk _ p => empty_walk _ (cast_to_right X Y p)
| non_empty_walk _ p (inr m, b) w
=> non_empty_walk _ (cast_to_right X Y p) (m, b) 
(cast_to_right_in_walk P Q E F w)
| non_empty_walk _ p (inl m, b) w
=> cast_to_right_in_walk P Q E F w
end.

Fact sum_valid_position_is_pure 
`(P : PartialOrder X) `(Q : PartialOrder Y)
(E : EventStructure P) (F : EventStructure Q): forall p x y, 
valid_position (event_structure_sum P Q E F) p ->
~ (In (inl x) p /\ In (inr y) p).
Proof.
intros. unfold not. intros. destruct H0.
 unfold valid_position in H. 
assert (~ incompatible (inl x) (inr y)).
{ apply H.  auto. }
simpl in H2. auto.
Qed.

Fact sum_valid_position_valid_inl
`(P : PartialOrder X) `(Q : PartialOrder Y)
(E : EventStructure P) (F : EventStructure Q): (forall p, 
valid_position (event_structure_sum P Q E F) p 
-> valid_position E (cast_to_left X Y p)).
Proof.
intros. unfold valid_position in H. unfold valid_position.
intros. split.
+ intros. destruct H0.
assert ((In (inl x) p /\ In (inl y) p -> 
~ incompatible (inl x) (inl y))).
{ apply H. }
assert (~ incompatible (inl x) (inl y)).
{ apply H2. split.
+ apply cast_to_left_is_boring. apply H0.
+ apply cast_to_left_is_boring. apply H1. }
simpl in H3. apply H3.
+ intros. destruct H0.
assert (In (inl y) p).
{ apply H with (x:=inl x). split.
+ apply cast_to_left_is_boring. apply H0.
+ simpl. apply H1. }
apply cast_to_left_is_boring. apply H2.
Qed.

Fact sum_valid_position_valid_inr
`(P : PartialOrder X) `(Q : PartialOrder Y)
(E : EventStructure P) (F : EventStructure Q): (forall p, 
valid_position (event_structure_sum P Q E F) p 
-> valid_position F (cast_to_right X Y p)).
Proof.
intros. unfold valid_position in H. unfold valid_position.
intros. split.
+ intros. destruct H0.
assert ((In (inr x) p /\ In (inr y) p -> 
~ incompatible (inr x) (inr y))).
{ apply H. }
assert (~ incompatible (inr x) (inr y)).
{ apply H2. split.
+ apply cast_to_right_is_boring. apply H0.
+ apply cast_to_right_is_boring. apply H1. }
simpl in H3. apply H3.
+ intros. destruct H0.
assert (In (inr y) p).
{ apply H with (x:=inr x). split.
+ apply cast_to_right_is_boring. apply H0.
+ simpl. apply H1. }
apply cast_to_right_is_boring. apply H2.
Qed.

Fact not_inl_equals_inr X Y : forall (m : X + Y),
not (exists y, m = inl y) <-> exists y, m = inr y.
Proof.
intros. unfold iff. split.
+ intros. destruct m.
++ contradiction H. refine (ex_intro _ x _). reflexivity.
++ refine (ex_intro _ y _). reflexivity.
+ intros. unfold not. intros. destruct H. destruct H0.
subst m. inversion H0.
Qed.

Fact not_inr_equals_inl X Y : forall (m : X + Y),
not (exists y, m = inr y) <-> exists y, m = inl y.
Proof.
intros. unfold iff. split.
+ intros. destruct m.
++ refine (ex_intro _ x _). reflexivity.
++ contradiction H. refine (ex_intro _ y _). reflexivity.
+ intros. unfold not. intros. destruct H. destruct H0.
subst m. inversion H0.
Qed.


Fact inl_move_implies_inl 
`(P : PartialOrder X) `(Q : PartialOrder Y)
(E : EventStructure P) (F : EventStructure Q):
forall y p1 p2,
(valid_position (event_structure_sum P Q E F) p1
/\
valid_position (event_structure_sum P Q E F) p2
/\
move_from (event_structure_sum P Q E F) (inl y) p1 p2)
-> (forall m, (In m p1 ->(exists y, m = inl y)) /\
(In m p2 ->(exists y, m = inl y))).
Proof.
intros. destruct H. destruct H0. split.
+ intros. destruct m.
++ refine (ex_intro _ x _). reflexivity.
++ unfold move_from in H1. destruct H1.
assert (In (inr y0) p2).
{ apply H1. apply H2. }
assert (In (inl y) p2).
{apply H3. reflexivity. }
assert (~ (In (inl y) p2 /\ In (inr y0) p2)).
{ apply sum_valid_position_is_pure. apply H0. }
contradiction H6. auto.
+ unfold move_from in H1. intros. 
apply not_inr_equals_inl. unfold not. 
intros. destruct H3. subst m.
assert (In (inl y) p2).
{apply H1. reflexivity. }
assert (~ (In (inl y) p2 /\ In (inr x) p2)).
{ apply sum_valid_position_is_pure. apply H0. }
contradiction H4. auto.
Qed.

Fact inr_move_implies_inr 
`(P : PartialOrder X) `(Q : PartialOrder Y)
(E : EventStructure P) (F : EventStructure Q):
forall y p1 p2,
(valid_position (event_structure_sum P Q E F) p1
/\
valid_position (event_structure_sum P Q E F) p2
/\
move_from (event_structure_sum P Q E F) (inr y) p1 p2)
-> (forall m, (In m p1 ->(exists y, m = inr y)) /\
(In m p2 ->(exists y, m = inr y))).
Proof.
intros. destruct H. destruct H0. split.
+ intros. destruct m.
++ unfold move_from in H1. destruct H1.
assert (In (inl x) p2).
{ apply H1. apply H2. }
assert (In (inr y) p2).
{apply H3. reflexivity. }
assert (~ (In (inl x) p2 /\ In (inr y) p2)).
{ apply sum_valid_position_is_pure. apply H0. }
contradiction H6. auto.
++ refine (ex_intro _ y0 _). reflexivity.
+ unfold move_from in H1. intros. 
apply not_inl_equals_inr. unfold not. 
intros. destruct H3. subst m.
assert (In (inr y) p2).
{apply H1. reflexivity. }
assert (~ (In (inl x) p2 /\ In (inr y) p2)).
{ apply sum_valid_position_is_pure. apply H0. }
contradiction H4. auto.
Qed.

Fact cast_inr_to_inl_nil
`(P : PartialOrder X) `(Q : PartialOrder Y):
forall p,
(forall m : X + Y, In m p -> exists y : Y, m = inr y) ->
cast_to_left X Y p = nil.
Proof.
intros. induction p.
+ simpl. reflexivity.
+ simpl. destruct a.
assert (exists y : Y, inl x = inr y).
{apply H. simpl. left. reflexivity. }
destruct H0. inversion H0. apply IHp.
intros. apply H. simpl. right. apply H0.
Qed.

Fact cast_inl_to_inr_nil
`(P : PartialOrder X) `(Q : PartialOrder Y):
forall p,
(forall m : X + Y, In m p -> exists x : X, m = inl x) ->
cast_to_right X Y p = nil.
Proof.
intros. induction p.
+ simpl. reflexivity.
+ simpl. destruct a.
++ apply IHp. intros. apply H. simpl. right. apply H0.
++
assert (exists x : X, inr y = inl x).
{apply H. simpl. left. reflexivity. }
destruct H0. inversion H0. 
Qed.

Fact cast_to_nil_inr 
`(P : PartialOrder X) `(Q : PartialOrder Y)
(E : EventStructure P) (F : EventStructure Q)
: forall w, (exists p0 y0 b0, 
valid_walk (event_structure_sum P Q E F)
        (non_empty_walk (event_structure_sum P Q E F) p0
           (inr y0, b0) w)) ->
source_walk _ (cast_to_left_in_walk P Q E F w) = nil.
Proof. intros. induction w.
+ simpl. destruct H. destruct H. destruct H. destruct H.
++ inversion H.
++ inversion H. subst p1. subst m. subst ep. subst p2.
destruct H0. destruct H1. destruct H1.
+++ inversion H1. subst p. destruct H2.
assert ((forall m, (In m x ->(exists y, m = inr y)) /\
(In m p0 ->(exists y, m = inr y)))).
{ apply inr_move_implies_inr
with (p1:=x) (p2:=p0) (y:=x0)
(P0:=P) (Q0:=Q) (E0:=E) (F0:=F). split.
+ apply H0.
+ split.
++ apply H3.
++ apply H2.
}
apply cast_inr_to_inl_nil.
++++ apply P.
++++ apply Q.
++++ apply H4.
++++  apply cast_inr_to_inl_nil.
+++++ apply P.
+++++ apply Q.
+++++ assert ((forall m, (In m p0 ->(exists y, m = inr y)) /\
(In m x ->(exists y, m = inr y)))).
{ apply inr_move_implies_inr
with (p1:=p0) (p2:=x) (y:=x0)
(P0:=P) (Q0:=Q) (E0:=E) (F0:=F). split.
+ apply H3.
+ split.
++ apply H0.
++ apply H2.
}
apply H4.
+++ inversion H1.
+++ inversion H1.
++ inversion H.
+ simpl. destruct p0. destruct s.
++ simpl. destruct H. destruct H. destruct H.
destruct H.
+++ inversion H.
+++ inversion H.
+++ inversion H.
subst p1. subst m. subst x2. subst p2. subst m'. subst w'.
destruct H0. destruct H1. destruct H1.
++++ inversion H1.
++++ inversion H1. subst p1. destruct H2.
assert ((forall m, (In m x0 ->(exists y, m = inr y)) /\
(In m p ->(exists y, m = inr y)))).
{ apply inr_move_implies_inr
with (p1:=x0) (p3:=p) (y:=x1)
(P0:=P) (Q0:=Q) (E0:=E) (F0:=F). split.
+ apply H0.
+ split.
++ apply H3.
++ apply H2.
}
apply cast_inr_to_inl_nil.
+++++ apply P.
+++++ apply Q.
+++++ apply H4.
+++++  apply cast_inr_to_inl_nil.
++++++ apply P.
++++++ apply Q.
++++++ assert ((forall m, (In m p ->(exists y, m = inr y)) /\
(In m x0 ->(exists y, m = inr y)))).
{ apply inr_move_implies_inr
with (p1:=p) (p3:=x0) (y:=x1)
(P0:=P) (Q0:=Q) (E0:=E) (F0:=F). split.
+ apply H3.
+ split.
++ apply H0.
++ apply H2.
}
apply H4.
++++ inversion H1. subst p1. destruct H2.
+++++
assert ((forall m, (In m x0 ->(exists y, m = inr y)) /\
(In m p ->(exists y, m = inr y)))).
{ apply inr_move_implies_inr
with (p1:=x0) (p3:=p) (y:=x1)
(P0:=P) (Q0:=Q) (E0:=E) (F0:=F). split.
+ apply H0.
+ split.
++ apply H3.
++ apply H2.
}
apply cast_inr_to_inl_nil.
++++++ apply P.
++++++ apply Q.
++++++ apply H4.
+++++ inversion H1. destruct H2.
++++++
assert ((forall m, (In m p ->(exists y, m = inr y)) /\
(In m x0 ->(exists y, m = inr y)))).
{ apply inr_move_implies_inr
with (p1:=p) (p3:=x0) (y:=x1)
(P0:=P) (Q0:=Q) (E0:=E) (F0:=F). split.
+ apply H3.
+ split.
++ apply H0.
++ apply H4.
}
apply cast_inr_to_inl_nil.
+++++++ apply P.
+++++++ apply Q.
+++++++ apply H11.
++ apply IHw. destruct H. destruct H. destruct H. destruct H.
+++ inversion H.
+++ inversion H.
+++ inversion H. subst p1. subst m. subst x1.
subst p2. subst m'. subst w'. destruct H0.
destruct H1. 
refine (ex_intro _ p _).
refine (ex_intro _ y _).
refine (ex_intro _ b _). auto.
Qed.

Fact cast_to_nil_inl 
`(P : PartialOrder X) `(Q : PartialOrder Y)
(E : EventStructure P) (F : EventStructure Q)
: forall w, (exists p0 y0 b0, 
valid_walk (event_structure_sum P Q E F)
        (non_empty_walk (event_structure_sum P Q E F) p0
           (inl y0, b0) w)) ->
source_walk _ (cast_to_right_in_walk P Q E F w) = nil.
Proof. intros. induction w.
+ simpl. destruct H. destruct H. destruct H. destruct H.
++ inversion H.
++ inversion H. subst p1. subst m. subst ep. subst p2.
destruct H0. destruct H1. destruct H1.
+++ inversion H1. subst p. destruct H2.
assert ((forall m, (In m x ->(exists y, m = inl y)) /\
(In m p0 ->(exists y, m = inl y)))).
{ apply inl_move_implies_inl
with (p1:=x) (p2:=p0) (y:=x0)
(P0:=P) (Q0:=Q) (E0:=E) (F0:=F). split.
+ apply H0.
+ split.
++ apply H3.
++ apply H2.
}
apply cast_inl_to_inr_nil.
++++ apply P.
++++ apply Q.
++++ apply H4.
++++  apply cast_inl_to_inr_nil.
+++++ apply P.
+++++ apply Q.
+++++ assert ((forall m, (In m p0 ->(exists y, m = inl y)) /\
(In m x ->(exists y, m = inl y)))).
{ apply inl_move_implies_inl
with (p1:=p0) (p2:=x) (y:=x0)
(P0:=P) (Q0:=Q) (E0:=E) (F0:=F). split.
+ apply H3.
+ split.
++ apply H0.
++ apply H2.
}
apply H4.
+++ inversion H1.
+++ inversion H1.
++ inversion H.
+ simpl. destruct p0. destruct s.
++ simpl. destruct H. destruct H. destruct H.
destruct H.
+++ inversion H.
+++ inversion H.
+++ inversion H.
subst p1. subst m. subst x2. subst p2. subst m'. subst w'.
destruct H0. destruct H1. apply IHw.
refine (ex_intro _ p _).
refine (ex_intro _ x _).
refine (ex_intro _ b _). auto.
++ simpl. destruct H. destruct H. destruct H.
destruct H.
+++ inversion H.
+++ inversion H.
+++ inversion H. subst p1. subst m. subst ep. subst p2.
destruct H0. destruct H1. destruct H1.
++++ inversion H1.
++++ inversion H1. subst p1. destruct H2.
assert ((forall m, (In m x ->(exists y, m = inl y)) /\
(In m p ->(exists y, m = inl y)))).
{ apply inl_move_implies_inl
with (p1:=x) (p3:=p) (y0:=x0)
(P0:=P) (Q0:=Q) (E0:=E) (F0:=F). split.
+ apply H0.
+ split.
++ apply H3.
++ apply H2.
}
apply cast_inl_to_inr_nil.
+++++ apply P.
+++++ apply Q.
+++++ apply H4.
+++++  apply cast_inl_to_inr_nil.
++++++ apply P.
++++++ apply Q.
++++++ assert ((forall m, (In m p ->(exists y, m = inl y)) /\
(In m x ->(exists y, m = inl y)))).
{ apply inl_move_implies_inl
with (p1:=p) (p3:=x) (y0:=x0)
(P0:=P) (Q0:=Q) (E0:=E) (F0:=F). split.
+ apply H3.
+ split.
++ apply H0.
++ apply H2.
}
apply H4.
++++ inversion H1. subst p1. destruct H2.
assert ((forall m, (In m x ->(exists y, m = inl y)) /\
(In m p ->(exists y, m = inl y)))).
{ apply inl_move_implies_inl
with (p1:=x) (p3:=p) (y0:=x0)
(P0:=P) (Q0:=Q) (E0:=E) (F0:=F). split.
+ apply H0.
+ split.
++ apply H3.
++ apply H2.
}
apply cast_inl_to_inr_nil.
+++++ apply P.
+++++ apply Q.
+++++ apply H4.
+++++  apply cast_inl_to_inr_nil.
++++++ apply P.
++++++ apply Q.
++++++ assert ((forall m, (In m p ->(exists y, m = inl y)) /\
(In m x ->(exists y, m = inl y)))).
{ apply inl_move_implies_inl
with (p1:=p) (p3:=x) (y0:=x0)
(P0:=P) (Q0:=Q) (E0:=E) (F0:=F). split.
+ apply H3.
+ split.
++ apply H0.
++ apply H2.
}
apply H4.
Qed.

Fact cast_to_left_in_walk_monotonic 
`(P : PartialOrder X)
`(Q : PartialOrder Y)
(E : EventStructure P)
(F : EventStructure Q)
: forall (w : Walk (event_structure_sum P Q E F)),
length_walk E (cast_to_left_in_walk P Q E F w) <
length_walk (event_structure_sum P Q E F) w
\/
length_walk E (cast_to_left_in_walk P Q E F w) =
length_walk (event_structure_sum P Q E F) w
.
Proof. intros. induction w.
+ simpl. right. reflexivity.
+ simpl. destruct p0. destruct s.
++ simpl. destruct IHw.
+++ left. lia.
+++ right. lia.
++ destruct IHw. 
+++ left. lia.
+++ left. lia.
Qed.

Fact cast_to_right_in_walk_monotonic 
`(P : PartialOrder X)
`(Q : PartialOrder Y)
(E : EventStructure P)
(F : EventStructure Q)
: forall (w : Walk (event_structure_sum P Q E F)),
length_walk F (cast_to_right_in_walk P Q E F w) <
length_walk (event_structure_sum P Q E F) w
\/
length_walk F (cast_to_right_in_walk P Q E F w) =
length_walk (event_structure_sum P Q E F) w
.
Proof. intros. induction w.
+ simpl. right. reflexivity.
+ simpl. destruct p0. destruct s.
++ destruct IHw. 
+++ left. lia.
+++ left. lia.
++ simpl. destruct IHw.
+++ left. lia.
+++ right. lia.
Qed.

Fact sum_equals_inl_implies_inl
`(P : PartialOrder X) `(Q : PartialOrder Y)
(E : EventStructure P) (F : EventStructure Q)
: forall w,
valid_walk (event_structure_sum P Q E F) w /\
length_walk (event_structure_sum P Q E F) w =
  length_walk E (cast_to_left_in_walk P Q E F w)
-> ((exists p, w = empty_walk (event_structure_sum P Q E F) p)
\/
forall m p, (position_in_walk _ p w /\ In m p) ->
(exists x, m = inl x)).
Proof. intros. induction w.
+ left. refine (ex_intro _ p _). reflexivity.
+ right. destruct H. simpl in H0. destruct p0.
destruct s.
++ simpl in H0.
assert
(length_walk E (cast_to_left_in_walk P Q E F w) =
length_walk (event_structure_sum P Q E F) w).
{lia. }
destruct H.
+++ inversion H.
+++ inversion H. subst p1. subst m. subst b. subst w.
assert ((exists p : Position (event_structure_sum P Q E F),
         empty_walk (event_structure_sum P Q E F) p2 =
         empty_walk (event_structure_sum P Q E F) p) \/
      (forall (m : X + Y) (p : Position (event_structure_sum P Q E F)),
       position_in_walk (event_structure_sum P Q E F) p
         (empty_walk (event_structure_sum P Q E F) p2) /\ 
       In m p -> exists x : X, m = inl x)).
{apply IHw. destruct H2. destruct H3. auto. }
destruct H3. destruct H3. inversion H3. subst x0. simpl.
intros. destruct H4. destruct H4.
++++ subst p0. destruct H2. destruct H4. destruct H6.
+++++ destruct H6. unfold move_from in H7. 
assert ((forall m, (In m p ->(exists y, m = inl y)) /\
(In m p2 ->(exists y, m = inl y)))).
{apply inl_move_implies_inl with (y:=x). destruct H4.
+ inversion H4. subst p2. auto.
+ inversion H4.
+ inversion H4. }
assert (forall m : X + Y,
     (In m p -> exists y : X, m = inl y)).
{apply H8. }
apply H9. apply H5.
+++++ destruct H6. unfold move_from in H7. 
assert ((forall m, (In m p2 ->(exists y, m = inl y)) /\
(In m p ->(exists y, m = inl y)))).
{apply inl_move_implies_inl with (y:=x). destruct H4.
+ inversion H4. subst p2. auto.
+ inversion H4.
+ inversion H4. }
assert (forall m : X + Y,
     (In m p -> exists y : X, m = inl y)).
{apply H8. }
apply H9. apply H5.
++++ subst p2. destruct H2. destruct H4. destruct H6.
destruct H6.
+++++
assert ((forall m, (In m p ->(exists y, m = inl y)) /\
(In m p0 ->(exists y, m = inl y)))).
{apply inl_move_implies_inl with (y:=x). destruct H4.
+ inversion H4. subst p0. auto.
+ inversion H4.
+ inversion H4. }
assert (forall m : X + Y,
     (In m p0 -> exists y : X, m = inl y)).
{apply H8. }
apply H9. apply H5.
+++++ assert ((forall m, (In m p0 ->(exists y, m = inl y)) /\
(In m p ->(exists y, m = inl y)))).
{apply inl_move_implies_inl with (y:=x). destruct H4.
+ inversion H4. subst p0. destruct H6. auto.
+ inversion H4.
+ inversion H4. }
assert (forall m : X + Y,
     (In m p0 -> exists y : X, m = inl y)).
{apply H7. }
apply H8. apply H5.
++++ simpl. intros. destruct H4. destruct H4.
+++++ subst p0. destruct H2. destruct H4. destruct H6.
++++++ destruct H6.
assert ((forall m, (In m p ->(exists y, m = inl y)) /\
(In m p2 ->(exists y, m = inl y)))).
{apply inl_move_implies_inl with (y:=x). destruct H4.
+ inversion H4. subst p0. auto.
+ inversion H4.
+ inversion H4. }
assert (forall m : X + Y,
     (In m p -> exists y : X, m = inl y)).
{apply H8. }
apply H9. apply H5.
++++++ destruct H6.
assert ((forall m, (In m p2 ->(exists y, m = inl y)) /\
(In m p ->(exists y, m = inl y)))).
{apply inl_move_implies_inl with (y:=x). destruct H4.
+ inversion H4. subst p0. auto.
+ inversion H4.
+ inversion H4. }
assert (forall m : X + Y,
     (In m p -> exists y : X, m = inl y)).
{apply H8. }
apply H9. apply H5.
+++++ subst p2. destruct H2. destruct H4. destruct H6.
++++++ destruct H6.
assert ((forall m, (In m p ->(exists y, m = inl y)) /\
(In m p0 ->(exists y, m = inl y)))).
{apply inl_move_implies_inl with (y:=x). destruct H4.
+ inversion H4. subst p0. auto.
+ inversion H4.
+ inversion H4. }
assert (forall m : X + Y,
     (In m p0 -> exists y : X, m = inl y)).
{apply H8. }
apply H9. apply H5.
++++++ destruct H6.
assert ((forall m, (In m p0 ->(exists y, m = inl y)) /\
(In m p ->(exists y, m = inl y)))).
{apply inl_move_implies_inl with (y:=x). destruct H4.
+ inversion H4. subst p0. auto.
+ inversion H4.
+ inversion H4. }
assert (forall m : X + Y,
     (In m p0 -> exists y : X, m = inl y)).
{apply H8. }
apply H9. apply H5.
+++ inversion H. subst p1. subst m. subst ep. subst w.
assert ((exists p : Position (event_structure_sum P Q E F),
         non_empty_walk (event_structure_sum P Q E F) p2 m' w' =
         empty_walk (event_structure_sum P Q E F) p) \/
      (forall (m : X + Y) (p : Position (event_structure_sum P Q E F)),
       position_in_walk (event_structure_sum P Q E F) p
         (non_empty_walk (event_structure_sum P Q E F) p2 m' w') /\ 
       In m p -> exists x : X, m = inl x)).
{apply IHw. destruct H2. destruct H3. auto. } destruct H3.
++++ destruct H3. inversion H3.
++++ intros. simpl in H4. destruct H4. destruct H4.
+++++ subst p0. destruct H2. destruct H4. destruct H6.
++++++ destruct H6. 
assert ((forall m, (In m p ->(exists y, m = inl y)) /\
(In m p2 ->(exists y, m = inl y)))).
{apply inl_move_implies_inl with (y:=x). destruct H4.
+ inversion H4.
+ inversion H4. subst p2. destruct H8. auto.
+ inversion H4. subst p2. destruct H8. auto. }
assert (forall m : X + Y,
     (In m p -> exists y : X, m = inl y)).
{apply H8. }
apply H9. apply H5.
++++++ destruct H6. 
assert ((forall m, (In m p2 ->(exists y, m = inl y)) /\
(In m p ->(exists y, m = inl y)))).
{apply inl_move_implies_inl with (y:=x). destruct H4.
+ inversion H4.
+ inversion H4. subst p2. destruct H8. auto.
+ inversion H4. subst p2. destruct H8. auto. }
assert (forall m : X + Y,
     (In m p -> exists y : X, m = inl y)).
{apply H8. }
apply H9. apply H5.
+++++ destruct H4.
++++++ subst p2. destruct H2. destruct H4.
destruct H6.
+++++++ destruct H6. 
assert ((forall m, (In m p ->(exists y, m = inl y)) /\
(In m p0 ->(exists y, m = inl y)))).
{apply inl_move_implies_inl with (y:=x). destruct H4.
+ inversion H4.
+ inversion H4. subst p1. destruct H8. auto.
+ inversion H4. subst p1. destruct H8. auto. }
assert (forall m : X + Y,
     (In m p0 -> exists y : X, m = inl y)).
{apply H8. }
apply H9. apply H5.
+++++++ destruct H6. 
assert ((forall m, (In m p0 ->(exists y, m = inl y)) /\
(In m p ->(exists y, m = inl y)))).
{apply inl_move_implies_inl with (y:=x). destruct H4.
+ inversion H4.
+ inversion H4. subst p1. destruct H8. auto.
+ inversion H4. subst p1. destruct H8. auto. }
assert (forall m : X + Y,
     (In m p0 -> exists y : X, m = inl y)).
{apply H8. }
apply H9. apply H5.
++++++ apply H3 with (p:=p0). split.
+++++++ simpl. right. auto.
+++++++ auto.
++
assert
(length_walk E (cast_to_left_in_walk P Q E F w) <
length_walk (event_structure_sum P Q E F) w
\/
length_walk E (cast_to_left_in_walk P Q E F w) =
length_walk (event_structure_sum P Q E F) w).
{ apply cast_to_left_in_walk_monotonic. }
lia.
Qed.

Fact sum_equals_inr_implies_inr
`(P : PartialOrder X) `(Q : PartialOrder Y)
(E : EventStructure P) (F : EventStructure Q)
: forall w,
valid_walk (event_structure_sum P Q E F) w /\
length_walk (event_structure_sum P Q E F) w =
  length_walk F (cast_to_right_in_walk P Q E F w)
-> ((exists p, w = empty_walk (event_structure_sum P Q E F) p)
\/
forall m p, (position_in_walk _ p w /\ In m p) ->
(exists x, m = inr x)).
Proof. intros. induction w.
+ left. refine (ex_intro _ p _). reflexivity.
+ right. destruct H. simpl in H0. destruct p0.
destruct s.
++ assert
(length_walk F (cast_to_right_in_walk P Q E F w) <
length_walk (event_structure_sum P Q E F) w
\/
length_walk F (cast_to_right_in_walk P Q E F w) =
length_walk (event_structure_sum P Q E F) w).
{ apply cast_to_right_in_walk_monotonic. }
lia.
++ simpl in H0.
assert
(length_walk F (cast_to_right_in_walk P Q E F w) =
length_walk (event_structure_sum P Q E F) w).
{lia. }
destruct H.
+++ inversion H.
+++ inversion H. subst p1. subst m. subst b. subst w.
assert ((exists p : Position (event_structure_sum P Q E F),
         empty_walk (event_structure_sum P Q E F) p2 =
         empty_walk (event_structure_sum P Q E F) p) \/
      (forall (m : X + Y) (p : Position (event_structure_sum P Q E F)),
       position_in_walk (event_structure_sum P Q E F) p
         (empty_walk (event_structure_sum P Q E F) p2) /\ 
       In m p -> exists x : Y, m = inr x)).
{apply IHw. destruct H2. destruct H3. auto. }
destruct H3. destruct H3. inversion H3. subst x. simpl.
intros. destruct H4. destruct H4.
++++ subst p0. destruct H2. destruct H4. destruct H6.
+++++ destruct H6. unfold move_from in H7. 
assert ((forall m, (In m p ->(exists y, m = inr y)) /\
(In m p2 ->(exists y, m = inr y)))).
{apply inr_move_implies_inr with (y0:=y). destruct H4.
+ inversion H4. subst p2. auto.
+ inversion H4.
+ inversion H4. }
assert (forall m : X + Y,
     (In m p -> exists y : Y, m = inr y)).
{apply H8. }
apply H9. apply H5.
+++++ destruct H6. unfold move_from in H7. 
assert ((forall m, (In m p2 ->(exists y, m = inr y)) /\
(In m p ->(exists y, m = inr y)))).
{apply inr_move_implies_inr with (y0:=y). destruct H4.
+ inversion H4. subst p2. auto.
+ inversion H4.
+ inversion H4. }
assert (forall m : X + Y,
     (In m p -> exists y : Y, m = inr y)).
{apply H8. }
apply H9. apply H5.
++++ subst p2. destruct H2. destruct H4. destruct H6.
destruct H6.
+++++
assert ((forall m, (In m p ->(exists y, m = inr y)) /\
(In m p0 ->(exists y, m = inr y)))).
{apply inr_move_implies_inr with (y0:=y). destruct H4.
+ inversion H4. subst p0. auto.
+ inversion H4.
+ inversion H4. }
assert (forall m : X + Y,
     (In m p0 -> exists y : Y, m = inr y)).
{apply H8. }
apply H9. apply H5.
+++++ assert ((forall m, (In m p0 ->(exists y, m = inr y)) /\
(In m p ->(exists y, m = inr y)))).
{apply inr_move_implies_inr with (y0:=y). destruct H4.
+ inversion H4. subst p0. destruct H6. auto.
+ inversion H4.
+ inversion H4. }
assert (forall m : X + Y,
     (In m p0 -> exists y : Y, m = inr y)).
{apply H7. }
apply H8. apply H5.
++++ simpl. intros. destruct H4. destruct H4.
+++++ subst p0. destruct H2. destruct H4. destruct H6.
++++++ destruct H6.
assert ((forall m, (In m p ->(exists y, m = inr y)) /\
(In m p2 ->(exists y, m = inr y)))).
{apply inr_move_implies_inr with (y0:=y). destruct H4.
+ inversion H4. subst p0. auto.
+ inversion H4.
+ inversion H4. }
assert (forall m : X + Y,
     (In m p -> exists y : Y, m = inr y)).
{apply H8. }
apply H9. apply H5.
++++++ destruct H6.
assert ((forall m, (In m p2 ->(exists y, m = inr y)) /\
(In m p ->(exists y, m = inr y)))).
{apply inr_move_implies_inr with (y0:=y). destruct H4.
+ inversion H4. subst p0. auto.
+ inversion H4.
+ inversion H4. }
assert (forall m : X + Y,
     (In m p -> exists y : Y, m = inr y)).
{apply H8. }
apply H9. apply H5.
+++++ subst p2. destruct H2. destruct H4. destruct H6.
++++++ destruct H6.
assert ((forall m, (In m p ->(exists y, m = inr y)) /\
(In m p0 ->(exists y, m = inr y)))).
{apply inr_move_implies_inr with (y0:=y). destruct H4.
+ inversion H4. subst p0. auto.
+ inversion H4.
+ inversion H4. }
assert (forall m : X + Y,
     (In m p0 -> exists y : Y, m = inr y)).
{apply H8. }
apply H9. apply H5.
++++++ destruct H6.
assert ((forall m, (In m p0 ->(exists y, m = inr y)) /\
(In m p ->(exists y, m = inr y)))).
{apply inr_move_implies_inr with (y0:=y). destruct H4.
+ inversion H4. subst p0. auto.
+ inversion H4.
+ inversion H4. }
assert (forall m : X + Y,
     (In m p0 -> exists y : Y, m = inr y)).
{apply H8. }
apply H9. apply H5.
+++ inversion H. subst p1. subst m. subst ep. subst w.
assert ((exists p : Position (event_structure_sum P Q E F),
         non_empty_walk (event_structure_sum P Q E F) p2 m' w' =
         empty_walk (event_structure_sum P Q E F) p) \/
      (forall (m : X + Y) (p : Position (event_structure_sum P Q E F)),
       position_in_walk (event_structure_sum P Q E F) p
         (non_empty_walk (event_structure_sum P Q E F) p2 m' w') /\ 
       In m p -> exists x : Y, m = inr x)).
{apply IHw. destruct H2. destruct H3. auto. } destruct H3.
++++ destruct H3. inversion H3.
++++ intros. simpl in H4. destruct H4. destruct H4.
+++++ subst p0. destruct H2. destruct H4. destruct H6.
++++++ destruct H6. 
assert ((forall m, (In m p ->(exists y, m = inr y)) /\
(In m p2 ->(exists y, m = inr y)))).
{apply inr_move_implies_inr with (y0:=y). destruct H4.
+ inversion H4.
+ inversion H4. subst p2. destruct H8. auto.
+ inversion H4. subst p2. destruct H8. auto. }
assert (forall m : X + Y,
     (In m p -> exists y : Y, m = inr y)).
{apply H8. }
apply H9. apply H5.
++++++ destruct H6. 
assert ((forall m, (In m p2 ->(exists y, m = inr y)) /\
(In m p ->(exists y, m = inr y)))).
{apply inr_move_implies_inr with (y0:=y). destruct H4.
+ inversion H4.
+ inversion H4. subst p2. destruct H8. auto.
+ inversion H4. subst p2. destruct H8. auto. }
assert (forall m : X + Y,
     (In m p -> exists y : Y, m = inr y)).
{apply H8. }
apply H9. apply H5.
+++++ destruct H4.
++++++ subst p2. destruct H2. destruct H4.
destruct H6.
+++++++ destruct H6. 
assert ((forall m, (In m p ->(exists y, m = inr y)) /\
(In m p0 ->(exists y, m = inr y)))).
{apply inr_move_implies_inr with (y0:=y). destruct H4.
+ inversion H4.
+ inversion H4. subst p1. destruct H8. auto.
+ inversion H4. subst p1. destruct H8. auto. }
assert (forall m : X + Y,
     (In m p0 -> exists y : Y, m = inr y)).
{apply H8. }
apply H9. apply H5.
+++++++ destruct H6. 
assert ((forall m, (In m p0 ->(exists y, m = inr y)) /\
(In m p ->(exists y, m = inr y)))).
{apply inr_move_implies_inr with (y0:=y). destruct H4.
+ inversion H4.
+ inversion H4. subst p1. destruct H8. auto.
+ inversion H4. subst p1. destruct H8. auto. }
assert (forall m : X + Y,
     (In m p0 -> exists y : Y, m = inr y)).
{apply H8. }
apply H9. apply H5.
++++++ apply H3 with (p:=p0). split.
+++++++ simpl. right. auto.
+++++++ auto.
Qed.

Fact valid_walk_is_valid_inl 
`(P : PartialOrder X) `(Q : PartialOrder Y)
(E : EventStructure P) (F : EventStructure Q):
forall w : Walk (event_structure_sum P Q E F),
     valid_walk (event_structure_sum P Q E F) w ->
valid_walk _ (cast_to_left_in_walk P Q E F w).
Proof. intros. induction w.
+ simpl. apply valid_empty_walk with (p0:=(cast_to_left X Y p)).
++ reflexivity.
++ destruct H.
+++ inversion H. apply sum_valid_position_valid_inl. apply H0.
+++ inversion H.
+++ inversion H.
+ destruct H.
++ inversion H.
++ inversion H. subst p0. subst p1. subst w. simpl.
destruct m. apply valid_one_move_walk
with (m:=x) (ep0:=ep) (p1:=(cast_to_left X Y p))
(p3:=(cast_to_left X Y p2)).
+++ reflexivity.
+++ split.
++++ destruct H0. apply sum_valid_position_valid_inl. apply H0.
++++ split.
+++++ destruct H0. destruct H1.
++++++ destruct H1.
+++++++ apply valid_empty_walk with (p1:=(cast_to_left X Y p2)).
++++++++ reflexivity.
++++++++ inversion H1. apply sum_valid_position_valid_inl. apply H3.
+++++++ inversion H1.
+++++++ inversion H1.
+++++ destruct ep.
++++++ left. destruct H0. destruct H1. destruct H2.
+++++++ split.
++++++++ reflexivity.
++++++++ unfold move_from. destruct H2.
unfold move_from in H3.
+++++++++ split.
++++++++++ destruct H3. intros. 
rewrite cast_to_left_is_boring.
rewrite cast_to_left_is_boring in H5. apply H3. apply H5.
++++++++++ intros. split.
+++++++++++ intros. destruct H4.
rewrite cast_to_left_is_boring in H4.
rewrite cast_to_left_is_boring in H5.
assert ((inl n : X + Y) = inl x).
{apply H3. auto. }
inversion H6. reflexivity.
+++++++++++ intros. destruct H3. 
rewrite cast_to_left_is_boring.
rewrite cast_to_left_is_boring.
assert ((inl n : X + Y) = inl x).
{rewrite H4. auto. }
apply H5. apply H6.
+++++++ destruct H2. inversion H2.
++++++ right. destruct H0. destruct H1. destruct H2.
+++++++ destruct H2. inversion H2.
+++++++ split.
++++++++ reflexivity.
++++++++ destruct H2. unfold move_from.
unfold move_from in H3. split.
+++++++++ destruct H3. intros.
rewrite cast_to_left_is_boring.
rewrite cast_to_left_is_boring in H5. apply H3.
apply H5.
+++++++++ split.
++++++++++ destruct H3. intros.
rewrite cast_to_left_is_boring in H5.
rewrite cast_to_left_is_boring in H5.
assert ((inl n : X + Y) = inl x).
{ apply H4. auto. } inversion H6. reflexivity.
++++++++++ destruct H3. intros.
rewrite cast_to_left_is_boring. 
rewrite cast_to_left_is_boring.
apply H4. rewrite H5. auto.
+++ apply valid_empty_walk with (p0:=(cast_to_left X Y p2)).
++++ reflexivity.
++++ destruct H0. destruct H1. destruct H1.
+++++ inversion H1. apply sum_valid_position_valid_inl. apply H3.
+++++ inversion H1.
+++++ inversion H1.
++ inversion H. subst p0. subst p1. subst w.
simpl. destruct m.
+++ destruct m'. simpl in IHw. destruct s. 
++++ apply valid_non_empty_walk
with (p1:=(cast_to_left X Y p)) (m:=x)
(ep0:=ep) (p3:=(cast_to_left X Y p2)) (m':=(x0, b))
(w'0:=(cast_to_left_in_walk P Q E F w')).
+++++ reflexivity.
+++++ split.
++++++ destruct H0. apply sum_valid_position_valid_inl. apply H0.
++++++ split.
+++++++ destruct H0. destruct H1. simpl in IHw.
apply IHw. apply H1.
+++++++ destruct H0. destruct H1. destruct H2.
++++++++ left. split.
+++++++++ destruct H2. apply H2.
+++++++++ destruct H2. unfold move_from. unfold
move_from in H3. split.
++++++++++ destruct H3.
intros. apply cast_to_left_is_boring in H5.
 apply cast_to_left_is_boring. apply H3. apply H5.
++++++++++ split.
+++++++++++ destruct H3. intros.
 rewrite cast_to_left_is_boring in H5. 
 rewrite cast_to_left_is_boring in H5.
assert ((inl n : X + Y) = inl x).
{ apply H4. auto. } inversion H6. reflexivity.
+++++++++++ intros.
 rewrite cast_to_left_is_boring.
 rewrite cast_to_left_is_boring.
apply H3. rewrite H4. reflexivity.
++++++++ destruct H2. right. split.
+++++++++ apply H2.
+++++++++ unfold move_from. unfold move_from in H3. split.
++++++++++ destruct H3. intros.
apply cast_to_left_is_boring in H5. 
apply cast_to_left_is_boring. apply H3. apply H5.
++++++++++ split.
+++++++++++ destruct H3. intros.
rewrite cast_to_left_is_boring in H5.
rewrite cast_to_left_is_boring in H5.
assert ((inl n : X + Y) = inl x).
{ apply H4. auto. } inversion H6. reflexivity.
+++++++++++ intros.
 rewrite cast_to_left_is_boring.
 rewrite cast_to_left_is_boring. apply H3. rewrite H4.
reflexivity.
++++ simpl in IHw.
assert (valid_walk E (cast_to_left_in_walk P Q E F w')).
{ apply IHw. destruct H0. destruct H1. apply H1. }
destruct w'.
+++++ simpl. destruct H0. destruct H2.
destruct H2.
++++++ inversion H2.
++++++ inversion H2. subst p2. subst m. subst b. subst p3.
destruct H4. destruct H5. destruct H6.
+++++++ destruct H3.
++++++++ 
assert (forall m, (In m p ->(exists y, m = inl y)) /\
(In m p1 ->(exists y, m = inl y))).
{ apply inl_move_implies_inl with (y0:=x). destruct H3.
auto. }
assert (forall m, (In m p1 ->(exists y, m = inr y)) /\
(In m p0 ->(exists y, m = inr y))).
{ apply inr_move_implies_inr with (y0:=y). destruct H6.
destruct H5.
+ inversion H5. subst p2. auto.
+ inversion H5.
+ inversion H5.
 }
assert (p1 = nil).
{destruct p1.
+ reflexivity.
+ destruct s.
++ assert (forall m : X + Y,
     (In m (inl x0 :: p1) -> exists y : Y, m = inr y)).
{apply H8. }
assert (exists y : Y, inl x0 = inr y).
{apply H9. simpl. left. reflexivity. }
destruct H10. inversion H10.
++ assert (forall m : X + Y,
(In m (inr y0 :: p1) -> exists y : X, m = inl y)).
{apply H7. }
assert (exists y : X, inr y0 = inl y).
{apply H9.  simpl. left. reflexivity. }
destruct H10. inversion H10.
} subst p1. destruct H3. unfold move_from in H9.
assert (In (inl x : X + Y) nil).
{apply H9. reflexivity. } contradiction H10.
++++++++
assert (forall m, (In m p1 ->(exists y, m = inl y)) /\
(In m p ->(exists y, m = inl y))).
{ apply inl_move_implies_inl with (y0:=x). destruct H3.
auto. }
assert (forall m, (In m p1 ->(exists y, m = inr y)) /\
(In m p0 ->(exists y, m = inr y))).
{ apply inr_move_implies_inr with (y0:=y). destruct H6.
destruct H5.
+ inversion H5. subst p2. auto.
+ inversion H5.
+ inversion H5.
 }
assert (p1 = nil).
{destruct p1.
+ reflexivity.
+ destruct s.
++ assert (forall m : X + Y,
     (In m (inl x0 :: p1) -> exists y : Y, m = inr y)).
{apply H8. }
assert (exists y : Y, inl x0 = inr y).
{apply H9. simpl. left. reflexivity. }
destruct H10. inversion H10.
++ assert (forall m : X + Y,
(In m (inr y0 :: p1) -> exists y : X, m = inl y)).
{apply H7. }
assert (exists y : X, inr y0 = inl y).
{apply H9.  simpl. left. reflexivity. }
destruct H10. inversion H10.
} subst p1. apply valid_one_move_walk with
(p1:=(cast_to_left X Y p)) (m:=x) (ep1:=ep)
(p2:=cast_to_left X Y p0).
+++++++++ reflexivity.
+++++++++ split. 
++++++++++ apply sum_valid_position_valid_inl. auto.
++++++++++ split.
+++++++++++ apply valid_empty_walk with 
(p1:=cast_to_left X Y p0).
++++++++++++ reflexivity.
++++++++++++ apply sum_valid_position_valid_inl.
destruct H5.
+++++++++++++ inversion H5. subst p1. auto.
+++++++++++++ inversion H5.
+++++++++++++ inversion H5.
+++++++++++ right. split.
++++++++++++ apply H3.
++++++++++++
assert (cast_to_left X Y p0 = nil).
{ apply cast_inr_to_inl_nil. 
+ apply P.
+ apply Q.
+ apply H8.
} rewrite H9. unfold move_from. split.
+++++++++++++ intros. contradiction H10.
+++++++++++++ intros. unfold iff. split.
++++++++++++++ intros. destruct H10.
apply cast_to_left_is_boring in H11. destruct H3.
unfold move_from in H12.
assert (inl n = (inl x : X + Y) -> n = x).
{intros.  inversion H13. reflexivity. }
apply H13. apply H12. split.
+++++++++++++++ simpl. auto.
+++++++++++++++ apply H11.
++++++++++++++ intros. split.
+++++++++++++++ simpl. auto.
+++++++++++++++ apply cast_to_left_is_boring.
destruct H3. apply H11. rewrite H10. reflexivity.
+++++++
destruct H3.
++++++++ 
assert (forall m, (In m p ->(exists y, m = inl y)) /\
(In m p1 ->(exists y, m = inl y))).
{ apply inl_move_implies_inl with (y0:=x). destruct H3.
auto. }
assert (forall m, (In m p0 ->(exists y, m = inr y)) /\
(In m p1 ->(exists y, m = inr y))).
{ apply inr_move_implies_inr with (y0:=y). destruct H6.
destruct H5.
+ inversion H5. subst p2. auto.
+ inversion H5.
+ inversion H5.
 }
assert (p1 = nil).
{destruct p1.
+ reflexivity.
+ destruct s.
++ assert (forall m : X + Y,
     (In m (inl x0 :: p1) -> exists y : Y, m = inr y)).
{apply H8. }
assert (exists y : Y, inl x0 = inr y).
{apply H9. simpl. left. reflexivity. }
destruct H10. inversion H10.
++ assert (forall m : X + Y,
(In m (inr y0 :: p1) -> exists y : X, m = inl y)).
{apply H7. }
assert (exists y : X, inr y0 = inl y).
{apply H9.  simpl. left. reflexivity. }
destruct H10. inversion H10.
} subst p1. destruct H3. unfold move_from in H9.
assert (In (inl x : X + Y) nil).
{apply H9. reflexivity. } contradiction H10.
++++++++
assert (forall m, (In m p1 ->(exists y, m = inl y)) /\
(In m p ->(exists y, m = inl y))).
{ apply inl_move_implies_inl with (y0:=x). destruct H3.
auto. }
assert (forall m, (In m p0 ->(exists y, m = inr y)) /\
(In m p1 ->(exists y, m = inr y))).
{ apply inr_move_implies_inr with (y0:=y). destruct H6.
destruct H5.
+ inversion H5. subst p2. auto.
+ inversion H5.
+ inversion H5.
 }
assert (p1 = nil).
{destruct p1.
+ reflexivity.
+ destruct s.
++ assert (forall m : X + Y,
     (In m (inl x0 :: p1) -> exists y : Y, m = inr y)).
{apply H8. }
assert (exists y : Y, inl x0 = inr y).
{apply H9. simpl. left. reflexivity. }
destruct H10. inversion H10.
++ assert (forall m : X + Y,
(In m (inr y0 :: p1) -> exists y : X, m = inl y)).
{apply H7. }
assert (exists y : X, inr y0 = inl y).
{apply H9.  simpl. left. reflexivity. }
destruct H10. inversion H10.
} subst p1. apply valid_one_move_walk with
(p1:=(cast_to_left X Y p)) (m:=x) (ep1:=ep)
(p2:=cast_to_left X Y p0).
+++++++++ reflexivity.
+++++++++ split. 
++++++++++ apply sum_valid_position_valid_inl. auto.
++++++++++ split.
+++++++++++ apply valid_empty_walk with 
(p1:=cast_to_left X Y p0).
++++++++++++ reflexivity.
++++++++++++ apply sum_valid_position_valid_inl.
destruct H5.
+++++++++++++ inversion H5. subst p1. auto.
+++++++++++++ inversion H5.
+++++++++++++ inversion H5.
+++++++++++ right. split.
++++++++++++ apply H3.
++++++++++++
assert (cast_to_left X Y p0 = nil).
{ apply cast_inr_to_inl_nil. 
+ apply P.
+ apply Q.
+ apply H8.
} rewrite H9. unfold move_from. split.
+++++++++++++ intros. contradiction H10.
+++++++++++++ intros. unfold iff. split.
++++++++++++++ intros. destruct H10.
apply cast_to_left_is_boring in H11. destruct H3.
unfold move_from in H12.
assert (inl n = (inl x : X + Y) -> n = x).
{intros.  inversion H13. reflexivity. }
apply H13. apply H12. split.
+++++++++++++++ simpl. auto.
+++++++++++++++ apply H11.
++++++++++++++ intros. split.
+++++++++++++++ simpl. auto.
+++++++++++++++ apply cast_to_left_is_boring.
destruct H3. apply H11. rewrite H10. reflexivity.
++++++ inversion H2.
+++++ simpl. destruct p1. simpl in H1. destruct s.
++++++ apply valid_non_empty_walk
with (p1:=(cast_to_left X Y p)) (m:=x) (ep0:=ep) 
(p3:=(cast_to_left X Y p0))
(m':=(x0,b0)) (w'0:=(cast_to_left_in_walk P Q E F w')).
+++++++ reflexivity.
+++++++ split.
++++++++ destruct H0. apply sum_valid_position_valid_inl.
 apply H0.
++++++++ split.
+++++++++ destruct H0. destruct H2. apply H1.
+++++++++ destruct H0. destruct H2. destruct H3. left.
destruct H3. split.
++++++++++ apply H3.
++++++++++
assert (p2 = nil).
{ destruct p2. 
+ reflexivity. 
+ destruct H2.
++ inversion H2.
++ inversion H2.
++ inversion H2.
subst p1. subst m. subst b. subst p3. subst m'. subst w'0.
destruct s. destruct H5. destruct H6. destruct H7.
+++ destruct H7. unfold move_from in H8.
assert (In (inl x1) p0).
{ destruct H8. apply H8. simpl. left. reflexivity. }
destruct H8.
assert (~ In (inr y) (inl x1 :: p2) /\ In (inr y) p0).
{ apply H10. reflexivity. }
assert (~ (In (inl x1) p0 /\ In (inr y) p0)).
{apply sum_valid_position_is_pure. destruct H6.
+ inversion H6.
+ inversion H6. subst p1. apply H12.
+ inversion H6. subst p1. apply H12.
} contradiction H12. destruct H11. split.
++++ apply H9.
++++ apply H13. 
+++ destruct H7. unfold move_from in H8.
assert (In (inl x1) (inl x1 :: p2)).
{ simpl. left. reflexivity. }
assert (~ (In (inl x1) (inl x1 :: p2) /\ In (inr y) (inl x1 :: p2))).
{apply sum_valid_position_is_pure
with (P0:=P) (Q0:=Q) (E0:=E) (F0:=F). apply H5.
}
assert (In (inl x1) (inl x1 :: p2) /\ In (inr y) (inl x1 :: p2)).
{ split.
+ auto. 
+ apply H8. reflexivity. }
contradiction H10. 
+++ unfold move_from in H4.
assert (~ (In (inl x) (inr y0 :: p2) /\ In (inr y0) (inr y0 :: p2))).
{apply sum_valid_position_is_pure
with (P0:=P) (Q0:=Q) (E0:=E) (F0:=F). apply H5. }
assert ((In (inl x) (inr y0 :: p2) /\ In (inr y0) (inr y0 :: p2))).
{ split.
+ destruct H4. apply H7. auto.
+ simpl. left. reflexivity. }
contradiction H6.
 } subst p2. unfold move_from in H4. destruct H4.
assert (~ In (inl x : X + Y) p /\ In (inl x : X + Y) nil).
{ apply H5.  reflexivity. }
destruct H6. simpl in H7. contradiction H7.
++++++++++
assert (p2 = nil).
{ destruct p2. 
+ reflexivity. 
+ destruct H2.
++ inversion H2.
++ inversion H2.
++ inversion H2.
subst p1. subst m. subst b. subst p3. subst m'. subst w'0.
destruct s. destruct H4. destruct H5. destruct H6.
+++ unfold move_from in H6.
assert (~ In (inr y) (inl x1 :: p2) /\ In (inr y) p0).
{ apply H6.  reflexivity. }
assert (In (inl x1) p0).
{ destruct H6. destruct H8. apply H8. simpl. left. reflexivity. }
assert (~ (In (inl x1) p0 /\ In (inr y) p0)).
{ apply sum_valid_position_is_pure. destruct H5.
+ inversion H5.
+ inversion H5. subst p1. destruct H9. auto.
+ inversion H5. subst p1. destruct H9. auto.
} contradiction H9. destruct H7. auto.
+++ destruct H6. unfold move_from in H7.
assert (~ In (inr y) p0 /\ In (inr y) (inl x1 :: p2)).
{ apply H7.  reflexivity. }
destruct H8.
assert (~ (In (inl x1) (inl x1 :: p2) /\ In (inr y) (inl x1 :: p2))).
{ apply sum_valid_position_is_pure
with (P0:=P) (Q0:=Q) (E0:=E) (F0:=F). auto. } contradiction H10. split.
++++  simpl. left. reflexivity.
++++ auto.
+++ destruct H3. unfold move_from in H5.
assert (In (inr y0) p).
{ destruct H5. apply H5. simpl. left. reflexivity. }
assert (In (inl x) p).
{ apply H5.  reflexivity. }
assert (~ (In (inl x) p /\ In (inr y0) p)).
{ apply sum_valid_position_is_pure
with (P0:=P) (Q0:=Q) (E0:=E) (F0:=F). auto. } contradiction H8. split.
++++ auto.
++++ auto.
} subst p2. right.
destruct H3. split.
+++++++++++ apply H3.
+++++++++++
assert (forall m, In m p0 -> m = inr y).
{intros. destruct H2. 
+ inversion H2. 
+ inversion H2. 
+ inversion H2. subst p1. subst m0. subst b. subst p2.
subst m'. subst w'0.
 destruct H6. destruct H7. destruct H8.
++ destruct H8. unfold move_from in H9.
apply H9.  split.
+++ simpl. auto.
+++ apply H5.
++ destruct H8. unfold move_from in H9.
assert (~ In (inr y) p0 /\ In (inr y : X + Y) nil).
{ apply H9.  reflexivity. }
destruct H10. simpl in H11. contradiction H11.
}
assert (forall m, In m p -> m = inl x).
{ intros. unfold move_from in H4. apply H4. split.
+ simpl. auto.
+ apply H6.
}
assert (forall p0, (forall m : X + Y, In m p0 -> m = inr y) ->
cast_to_left X Y p0 = nil).
{ intros. induction p1. 
+ simpl. reflexivity.
+ destruct a.
++ assert (inl x1 = inr y).
{ apply H7.  simpl. left. reflexivity. }
inversion H8.
++ simpl. apply IHp1. intros. apply H7. simpl. right. apply H8.
 }
assert ( cast_to_left X Y p0 = nil).
{apply H7.  apply H5. } rewrite H8.
assert (forall p2, move_from (event_structure_sum P Q E F)
        (inl x) nil p2 ->
(forall m, In m (cast_to_left X Y p2) -> m = x) ).
{intros. induction p2.
+ simpl in H8. contradiction H10.
+ simpl in H8. destruct a.
++ simpl in H8. destruct H10.
+++ subst x1. unfold move_from in H9.
assert (inl m = (inl x : X + Y)).
{apply H9. split.
+ simpl. auto.
+ simpl. left. reflexivity.
 }
inversion H10. reflexivity.
+++ apply IHp2. destruct p2.
++++ simpl in H10. contradiction H10.
++++ unfold move_from. split.
+++++ intros. contradiction H11.
+++++ intros. unfold iff. split.
++++++ intros. unfold move_from in H9.
apply H9. split.
+++++++ simpl. auto.
+++++++ simpl. simpl in H11. right. apply H11.
++++++ intros. unfold move_from in H9.
subst n.
assert (s = inl x).
{apply H9. split.
+ simpl. auto.
+ simpl. right. left. reflexivity.
} subst s. simpl. auto.
++++ apply H10.
++ apply IHp2. destruct p2.
+++ simpl in H10. contradiction H10.
+++ unfold move_from in H9.
assert (inr y0 = (inl x : X + Y)).
{apply H9. split.
+ simpl. auto.
+ simpl. left. reflexivity.
} inversion H11.
+++ apply H10.
}
assert (forall m : X, In m (cast_to_left X Y p) -> m = x).
{ apply H9. apply H4. }
unfold move_from. split.
++++++++++++ intros. contradiction H11.
++++++++++++ intros. unfold iff. split.
+++++++++++++ intros. apply H10. apply H11.
+++++++++++++ intros. split.
++++++++++++++ simpl. auto.
++++++++++++++ unfold move_from in H4.
assert (In (inl x) p).
{apply H4.  reflexivity. }
apply cast_to_left_is_boring. subst n. apply H12.
++++++ simpl in IHw. destruct H0. destruct H2.
destruct H2.
+++++++ inversion H2.
+++++++ inversion H2.
+++++++ inversion H2.
subst p3. subst m. subst ep0. subst p2. subst m'. subst w'0.
destruct H4. destruct H5.
destruct H3.
++++++++ destruct H6.
+++++++++
assert ((forall m, (In m p1 ->(exists y, m = inr y)) /\
(In m p0 ->(exists y, m = inr y)))).
{ apply inr_move_implies_inr with (y1:=y). 
destruct H5.
+ inversion H5.
+ inversion H5. subst p2. destruct H7. destruct H6. auto.
+ inversion H5. subst p2. destruct H7. destruct H6. auto. }
assert (forall m, (In m p ->(exists y, m = inl y)) /\
(In m p1 ->(exists y, m = inl y))).
{ apply inl_move_implies_inl with (y1:=x). 
destruct H3. auto. }
assert (p1 = nil).
{destruct p1.
+ reflexivity.
+ destruct s.
++ assert (forall m : X + Y,
     (In m (inl x0 :: p1) -> exists y : Y, m = inr y)).
{apply H7. }
assert (exists y : Y, inl x0 = inr y).
{apply H9. simpl. left. reflexivity. }
destruct H10. inversion H10.
++ assert (forall m : X + Y,
     (In m (inr y1 :: p1) -> exists y : X, m = inl y)).
{ apply H8. }
assert (exists x : X, inr y1 = inl x).
{ apply H9. simpl. left. reflexivity. }
destruct H10. inversion H10.
} subst p1. destruct H3. unfold move_from in H9.
assert (~ In (inl x : X + Y) p /\ In (inl x : X + Y) nil).
{apply H9. reflexivity. }
destruct H10. contradiction H11.
+++++++++
assert ((forall m, (In m p0 ->(exists y, m = inr y)) /\
(In m p1 ->(exists y, m = inr y)))).
{ apply inr_move_implies_inr with (y1:=y). 
destruct H5.
+ inversion H5.
+ inversion H5. subst p2. destruct H7. destruct H6. auto.
+ inversion H5. subst p2. destruct H7. destruct H6. auto. }
assert (forall m, (In m p ->(exists y, m = inl y)) /\
(In m p1 ->(exists y, m = inl y))).
{ apply inl_move_implies_inl with (y1:=x). 
destruct H3. auto. }
assert (p1 = nil).
{destruct p1.
+ reflexivity.
+ destruct s.
++ assert (forall m : X + Y,
     (In m (inl x0 :: p1) -> exists y : Y, m = inr y)).
{apply H7. }
assert (exists y : Y, inl x0 = inr y).
{apply H9. simpl. left. reflexivity. }
destruct H10. inversion H10.
++ assert (forall m : X + Y,
     (In m (inr y1 :: p1) -> exists y : X, m = inl y)).
{ apply H8. }
assert (exists x : X, inr y1 = inl x).
{ apply H9. simpl. left. reflexivity. }
destruct H10. inversion H10.
} subst p1. destruct H3. unfold move_from in H9.
assert (~ In (inl x : X + Y) p /\ In (inl x : X + Y) nil).
{apply H9. reflexivity. }
destruct H10. contradiction H11.
++++++++ destruct H6.
+++++++++ assert ((forall m, (In m p1 ->(exists y, m = inr y)) /\
(In m p0 ->(exists y, m = inr y)))).
{ apply inr_move_implies_inr with (y1:=y). 
destruct H5.
+ inversion H5.
+ inversion H5. subst p2. destruct H7. destruct H6. auto.
+ inversion H5. subst p2. destruct H7. destruct H6. auto. }
assert (forall m, (In m p1 ->(exists y, m = inl y)) /\
(In m p ->(exists y, m = inl y))).
{ apply inl_move_implies_inl with (y1:=x). 
destruct H3. auto. }
assert (p1 = nil).
{destruct p1.
+ reflexivity.
+ destruct s.
++ assert (forall m : X + Y,
     (In m (inl x0 :: p1) -> exists y : Y, m = inr y)).
{apply H7. }
assert (exists y : Y, inl x0 = inr y).
{apply H9. simpl. left. reflexivity. }
destruct H10. inversion H10.
++ assert (forall m : X + Y,
     (In m (inr y1 :: p1) -> exists y : X, m = inl y)).
{ apply H8. }
assert (exists x : X, inr y1 = inl x).
{ apply H9. simpl. left. reflexivity. }
destruct H10. inversion H10.
} subst p1.
assert (source_walk _ (cast_to_left_in_walk P Q E F w') = nil).
{ apply cast_to_nil_inr. 
refine (ex_intro _ p0 _).
refine (ex_intro _ y0 _).
refine (ex_intro _ b0 _).
apply H5.
}
destruct (cast_to_left_in_walk P Q E F w') eqn:IND.
++++++++++ simpl in H9. subst p1.
apply valid_one_move_walk with 
(p1:=(cast_to_left X Y p)) (m:=x) (ep0:=ep) (p2:=nil).
+++++++++++ reflexivity.
+++++++++++ split.
++++++++++++ apply sum_valid_position_valid_inl. auto.
++++++++++++ split.
+++++++++++++ apply valid_empty_walk with (p1:=nil).
++++++++++++++ reflexivity.
++++++++++++++ unfold valid_position.
intros. split.
+++++++++++++++ intros. destruct H9. contradiction H10.
+++++++++++++++ intros. destruct H9. contradiction H9.
+++++++++++++ right. split.
++++++++++++++ destruct H3. auto.
++++++++++++++ destruct H3. unfold move_from.
split.
+++++++++++++++ intros. contradiction H10.
+++++++++++++++ unfold iff. intros. split.
++++++++++++++++ intros. destruct H10.
apply cast_to_left_is_boring in H11.
unfold move_from in H9.
assert (inl n = (inl x : X + Y) -> n = x).
{ intros. inversion H12. reflexivity. }
apply H12. apply H9. split.
+++++++++++++++++ simpl. auto.
+++++++++++++++++ apply H11.
++++++++++++++++ intros. split.
+++++++++++++++++ simpl. auto.
+++++++++++++++++
assert (inl n = (inl x : X + Y)).
{ rewrite H10. reflexivity. } apply cast_to_left_is_boring.
apply H9. apply H11.
++++++++++ simpl in H9. subst p1.
apply valid_non_empty_walk with
(p1:=cast_to_left X Y p) (m:=x) (ep0:=ep) (p3:=nil)
(w'0:=w) (m':=p2).
+++++++++++ reflexivity.
+++++++++++ split.
++++++++++++ apply sum_valid_position_valid_inl. auto.
++++++++++++ split.
+++++++++++++ auto.
+++++++++++++ right. split.
++++++++++++++ apply H3.
++++++++++++++ unfold move_from. split.
+++++++++++++++ intros. contradiction H9.
+++++++++++++++ intros. unfold iff. split.
++++++++++++++++ intros. destruct H9.
apply cast_to_left_is_boring in H10.
destruct H3.
unfold move_from in H11.
assert (inl n = (inl x : X + Y) -> n = x).
{ intros. inversion H12. reflexivity. }
apply H12. apply H11. split.
+++++++++++++++++ simpl. auto.
+++++++++++++++++ apply H10.
++++++++++++++++ intros. split.
+++++++++++++++++ simpl. auto.
+++++++++++++++++
assert (inl n = (inl x : X + Y)).
{ rewrite H9. reflexivity. } apply cast_to_left_is_boring.
destruct H3.
unfold move_from in H11. apply H11. apply H10.
+++++++++
assert ((forall m, (In m p0 ->(exists y, m = inr y)) /\
(In m p1 ->(exists y, m = inr y)))).
{ apply inr_move_implies_inr with (y1:=y). 
destruct H5.
+ inversion H5.
+ inversion H5. subst p2. destruct H7. destruct H6. auto.
+ inversion H5. subst p2. destruct H7. destruct H6. auto. }
assert (forall m, (In m p1 ->(exists y, m = inl y)) /\
(In m p ->(exists y, m = inl y))).
{ apply inl_move_implies_inl with (y1:=x). 
destruct H3. auto. }
assert (p1 = nil).
{destruct p1.
+ reflexivity.
+ destruct s.
++ assert (forall m : X + Y,
     (In m (inl x0 :: p1) -> exists y : Y, m = inr y)).
{apply H7. }
assert (exists y : Y, inl x0 = inr y).
{apply H9. simpl. left. reflexivity. }
destruct H10. inversion H10.
++ assert (forall m : X + Y,
     (In m (inr y1 :: p1) -> exists y : X, m = inl y)).
{ apply H8. }
assert (exists x : X, inr y1 = inl x).
{ apply H9. simpl. left. reflexivity. }
destruct H10. inversion H10.
} subst p1.
assert (source_walk _ (cast_to_left_in_walk P Q E F w') = nil).
{ apply cast_to_nil_inr. 
refine (ex_intro _ p0 _).
refine (ex_intro _ y0 _).
refine (ex_intro _ b0 _).
apply H5.
}
destruct (cast_to_left_in_walk P Q E F w') eqn:IND.
++++++++++ simpl in H9. subst p1.
apply valid_one_move_walk with 
(p1:=(cast_to_left X Y p)) (m:=x) (ep0:=ep) (p2:=nil).
+++++++++++ reflexivity.
+++++++++++ split.
++++++++++++ apply sum_valid_position_valid_inl. auto.
++++++++++++ split.
+++++++++++++ apply valid_empty_walk with (p1:=nil).
++++++++++++++ reflexivity.
++++++++++++++ unfold valid_position.
intros. split.
+++++++++++++++ intros. destruct H9. contradiction H10.
+++++++++++++++ intros. destruct H9. contradiction H9.
+++++++++++++ right. split.
++++++++++++++ destruct H3. auto.
++++++++++++++ destruct H3. unfold move_from.
split.
+++++++++++++++ intros. contradiction H10.
+++++++++++++++ unfold iff. intros. split.
++++++++++++++++ intros. destruct H10.
apply cast_to_left_is_boring in H11.
unfold move_from in H9.
assert (inl n = (inl x : X + Y) -> n = x).
{ intros. inversion H12. reflexivity. }
apply H12. apply H9. split.
+++++++++++++++++ simpl. auto.
+++++++++++++++++ apply H11.
++++++++++++++++ intros. split.
+++++++++++++++++ simpl. auto.
+++++++++++++++++
assert (inl n = (inl x : X + Y)).
{ rewrite H10. reflexivity. } apply cast_to_left_is_boring.
apply H9. apply H11.
++++++++++ simpl in H9. subst p1.
apply valid_non_empty_walk with
(p1:=cast_to_left X Y p) (m:=x) (ep0:=ep) (p3:=nil)
(w'0:=w) (m':=p2).
+++++++++++ reflexivity.
+++++++++++ split.
++++++++++++ apply sum_valid_position_valid_inl. auto.
++++++++++++ split.
+++++++++++++ auto.
+++++++++++++ right. split.
++++++++++++++ apply H3.
++++++++++++++ unfold move_from. split.
+++++++++++++++ intros. contradiction H9.
+++++++++++++++ intros. unfold iff. split.
++++++++++++++++ intros. destruct H9.
apply cast_to_left_is_boring in H10.
destruct H3.
unfold move_from in H11.
assert (inl n = (inl x : X + Y) -> n = x).
{ intros. inversion H12. reflexivity. }
apply H12. apply H11. split.
+++++++++++++++++ simpl. auto.
+++++++++++++++++ apply H10.
++++++++++++++++ intros. split.
+++++++++++++++++ simpl. auto.
+++++++++++++++++
assert (inl n = (inl x : X + Y)).
{ rewrite H9. reflexivity. } apply cast_to_left_is_boring.
destruct H3.
unfold move_from in H11. apply H11. apply H10.
+++ destruct m'. destruct s.
++++ simpl in IHw. apply IHw. destruct H0. destruct H1.
apply H1.
++++ simpl in IHw. apply IHw. apply H0.
Qed.
(* RUDI HAPA *)
Fact valid_walk_is_valid_inr
`(P : PartialOrder X) `(Q : PartialOrder Y)
(E : EventStructure P) (F : EventStructure Q):
forall w : Walk (event_structure_sum P Q E F),
     valid_walk (event_structure_sum P Q E F) w ->
valid_walk _ (cast_to_right_in_walk P Q E F w).
Proof. intros. induction w.
+ simpl. apply valid_empty_walk with (p0:=(cast_to_right X Y p)).
++ reflexivity.
++ destruct H.
+++ inversion H. apply sum_valid_position_valid_inr. apply H0.
+++ inversion H.
+++ inversion H.
+ destruct H.
++ inversion H.
++ inversion H. subst p0. subst p1. subst w. simpl. destruct m. 
+++ apply valid_empty_walk with (p0:=(cast_to_right X Y p2)).
++++ reflexivity.
++++ destruct H0. destruct H1. destruct H1.
+++++ inversion H1. apply sum_valid_position_valid_inr. apply H3.
+++++ inversion H1.
+++++ inversion H1.
+++ apply valid_one_move_walk
with (m:=y) (ep0:=ep) (p1:=(cast_to_right X Y p))
(p3:=(cast_to_right X Y p2)).
++++ reflexivity.
++++ split.
+++++ destruct H0. apply sum_valid_position_valid_inr. apply H0.
+++++ split.
++++++ destruct H0. destruct H1.
+++++++ destruct H1.
++++++++ apply valid_empty_walk with (p1:=(cast_to_right X Y p2)).
+++++++++ reflexivity.
+++++++++ inversion H1. apply sum_valid_position_valid_inr. apply H3.
++++++++ inversion H1.
++++++++ inversion H1.
++++++ destruct ep.
+++++++ left. destruct H0. destruct H1. destruct H2.
++++++++ split.
+++++++++ reflexivity.
+++++++++ unfold move_from. destruct H2.
unfold move_from in H3.
++++++++++ split.
+++++++++++ destruct H3. intros. 
rewrite cast_to_right_is_boring.
rewrite cast_to_right_is_boring in H5. apply H3. apply H5.
+++++++++++ intros. split.
++++++++++++ intros. destruct H4.
rewrite cast_to_right_is_boring in H4.
rewrite cast_to_right_is_boring in H5.
assert ((inr n : X + Y) = inr y).
{apply H3. auto. }
inversion H6. reflexivity.
++++++++++++ intros. destruct H3. 
rewrite cast_to_right_is_boring.
rewrite cast_to_right_is_boring.
assert ((inr n : X + Y) = inr y).
{rewrite H4. auto. }
apply H5. apply H6.
++++++++ destruct H2. inversion H2.
+++++++ right. destruct H0. destruct H1. destruct H2.
++++++++ destruct H2. inversion H2.
++++++++ split.
+++++++++ reflexivity.
+++++++++ destruct H2. unfold move_from.
unfold move_from in H3. split.
++++++++++ destruct H3. intros.
rewrite cast_to_right_is_boring.
rewrite cast_to_right_is_boring in H5. apply H3.
apply H5.
++++++++++ split.
+++++++++++ destruct H3. intros.
rewrite cast_to_right_is_boring in H5.
rewrite cast_to_right_is_boring in H5.
assert ((inr n : X + Y) = inr y).
{ apply H4. auto. } inversion H6. reflexivity.
+++++++++++ destruct H3. intros.
rewrite cast_to_right_is_boring. 
rewrite cast_to_right_is_boring.
apply H4. rewrite H5. auto.
++ inversion H. subst p0. subst p1. subst w.
simpl. destruct m.
+++ destruct m'. simpl in IHw. destruct s. 
++++ simpl in IHw. apply IHw. destruct H0. destruct H1.
apply H1.
++++ simpl in IHw. apply IHw. apply H0.
+++ destruct m'. simpl in IHw. destruct s. 
++++ simpl in IHw.
assert (valid_walk F (cast_to_right_in_walk P Q E F w')).
{ apply IHw. destruct H0. destruct H1. apply H1. }
destruct w'.
+++++ simpl. destruct H0. destruct H2.
destruct H2.
++++++ inversion H2.
++++++ inversion H2. subst p2. subst m. subst b. subst p3.
destruct H4. destruct H5. destruct H6.
+++++++ destruct H3.
++++++++ 
assert (forall m, (In m p ->(exists y, m = inr y)) /\
(In m p1 ->(exists y, m = inr y))).
{ apply inr_move_implies_inr with (y0:=y). destruct H3.
auto. }
assert (forall m, (In m p1 ->(exists y, m = inl y)) /\
(In m p0 ->(exists y, m = inl y))).
{ apply inl_move_implies_inl with (y0:=x). destruct H6.
destruct H5.
+ inversion H5. subst p2. auto.
+ inversion H5.
+ inversion H5.
 }
assert (p1 = nil).
{destruct p1.
+ reflexivity.
+ destruct s.
++ assert (forall m : X + Y,
     (In m (inl x0 :: p1) -> exists y : Y, m = inr y)).
{apply H7. }
assert (exists y : Y, inl x0 = inr y).
{apply H9. simpl. left. reflexivity. }
destruct H10. inversion H10.
++ assert (forall m : X + Y,
(In m (inr y0 :: p1) -> exists y : X, m = inl y)).
{apply H8. }
assert (exists y : X, inr y0 = inl y).
{apply H9.  simpl. left. reflexivity. }
destruct H10. inversion H10.
} subst p1. destruct H3. unfold move_from in H9.
assert (In (inr y : X + Y) nil).
{apply H9. reflexivity. } contradiction H10.
++++++++
assert (forall m, (In m p1 ->(exists y, m = inr y)) /\
(In m p ->(exists y, m = inr y))).
{ apply inr_move_implies_inr with (y0:=y). destruct H3.
auto. }
assert (forall m, (In m p1 ->(exists y, m = inl y)) /\
(In m p0 ->(exists y, m = inl y))).
{ apply inl_move_implies_inl with (y0:=x). destruct H6.
destruct H5.
+ inversion H5. subst p2. auto.
+ inversion H5.
+ inversion H5.
 }
assert (p1 = nil).
{destruct p1.
+ reflexivity.
+ destruct s.
++ assert (forall m : X + Y,
     (In m (inl x0 :: p1) -> exists y : Y, m = inr y)).
{apply H7. }
assert (exists y : Y, inl x0 = inr y).
{apply H9. simpl. left. reflexivity. }
destruct H10. inversion H10.
++ assert (forall m : X + Y,
(In m (inr y0 :: p1) -> exists y : X, m = inl y)).
{apply H8. }
assert (exists y : X, inr y0 = inl y).
{apply H9.  simpl. left. reflexivity. }
destruct H10. inversion H10.
} subst p1. apply valid_one_move_walk with
(p1:=(cast_to_right X Y p)) (m:=y) (ep1:=ep)
(p2:=cast_to_right X Y p0).
+++++++++ reflexivity.
+++++++++ split. 
++++++++++ apply sum_valid_position_valid_inr. auto.
++++++++++ split.
+++++++++++ apply valid_empty_walk with 
(p1:=cast_to_right X Y p0).
++++++++++++ reflexivity.
++++++++++++ apply sum_valid_position_valid_inr.
destruct H5.
+++++++++++++ inversion H5. subst p1. auto.
+++++++++++++ inversion H5.
+++++++++++++ inversion H5.
+++++++++++ right. split.
++++++++++++ apply H3.
++++++++++++
assert (cast_to_right X Y p0 = nil).
{ apply cast_inl_to_inr_nil. 
+ apply P.
+ apply Q.
+ apply H8.
} rewrite H9. unfold move_from. split.
+++++++++++++ intros. contradiction H10.
+++++++++++++ intros. unfold iff. split.
++++++++++++++ intros. destruct H10.
apply cast_to_right_is_boring in H11. destruct H3.
unfold move_from in H12.
assert (inr n = (inr y : X + Y) -> n = y).
{intros.  inversion H13. reflexivity. }
apply H13. apply H12. split.
+++++++++++++++ simpl. auto.
+++++++++++++++ apply H11.
++++++++++++++ intros. split.
+++++++++++++++ simpl. auto.
+++++++++++++++ apply cast_to_right_is_boring.
destruct H3. apply H11. rewrite H10. reflexivity.
+++++++ destruct H3.
++++++++ 
assert (forall m, (In m p ->(exists y, m = inr y)) /\
(In m p1 ->(exists y, m = inr y))).
{ apply inr_move_implies_inr with (y0:=y). destruct H3.
auto. }
assert (forall m, (In m p0 ->(exists y, m = inl y)) /\
(In m p1 ->(exists y, m = inl y))).
{ apply inl_move_implies_inl with (y0:=x). destruct H6.
destruct H5.
+ inversion H5. subst p2. auto.
+ inversion H5.
+ inversion H5.
 }
assert (p1 = nil).
{destruct p1.
+ reflexivity.
+ destruct s.
++ assert (forall m : X + Y,
     (In m (inl x0 :: p1) -> exists y : Y, m = inr y)).
{apply H7. }
assert (exists y : Y, inl x0 = inr y).
{apply H9. simpl. left. reflexivity. }
destruct H10. inversion H10.
++ assert (forall m : X + Y,
(In m (inr y0 :: p1) -> exists y : X, m = inl y)).
{apply H8. }
assert (exists y : X, inr y0 = inl y).
{apply H9.  simpl. left. reflexivity. }
destruct H10. inversion H10.
} subst p1. destruct H3. unfold move_from in H9.
assert (In (inr y : X + Y) nil).
{apply H9. reflexivity. } contradiction H10.
++++++++
assert (forall m, (In m p1 ->(exists y, m = inr y)) /\
(In m p ->(exists y, m = inr y))).
{ apply inr_move_implies_inr with (y0:=y). destruct H3.
auto. }
assert (forall m, (In m p0 ->(exists y, m = inl y)) /\
(In m p1 ->(exists y, m = inl y))).
{ apply inl_move_implies_inl with (y0:=x). destruct H6.
destruct H5.
+ inversion H5. subst p2. auto.
+ inversion H5.
+ inversion H5.
 }
assert (p1 = nil).
{destruct p1.
+ reflexivity.
+ destruct s.
++ assert (forall m : X + Y,
     (In m (inl x0 :: p1) -> exists y : Y, m = inr y)).
{apply H7. }
assert (exists y : Y, inl x0 = inr y).
{apply H9. simpl. left. reflexivity. }
destruct H10. inversion H10.
++ assert (forall m : X + Y,
(In m (inr y0 :: p1) -> exists y : X, m = inl y)).
{apply H8. }
assert (exists y : X, inr y0 = inl y).
{apply H9.  simpl. left. reflexivity. }
destruct H10. inversion H10.
} subst p1. apply valid_one_move_walk with
(p1:=(cast_to_right X Y p)) (m:=y) (ep1:=ep)
(p2:=cast_to_right X Y p0).
+++++++++ reflexivity.
+++++++++ split. 
++++++++++ apply sum_valid_position_valid_inr. auto.
++++++++++ split.
+++++++++++ apply valid_empty_walk with 
(p1:=cast_to_right X Y p0).
++++++++++++ reflexivity.
++++++++++++ apply sum_valid_position_valid_inr.
destruct H5.
+++++++++++++ inversion H5. subst p1. auto.
+++++++++++++ inversion H5.
+++++++++++++ inversion H5.
+++++++++++ right. split.
++++++++++++ apply H3.
++++++++++++
assert (cast_to_right X Y p0 = nil).
{ apply cast_inl_to_inr_nil. 
+ apply P.
+ apply Q.
+ apply H8.
} rewrite H9. unfold move_from. split.
+++++++++++++ intros. contradiction H10.
+++++++++++++ intros. unfold iff. split.
++++++++++++++ intros. destruct H10.
apply cast_to_right_is_boring in H11. destruct H3.
unfold move_from in H12.
assert (inr n = (inr y : X + Y) -> n = y).
{intros.  inversion H13. reflexivity. }
apply H13. apply H12. split.
+++++++++++++++ simpl. auto.
+++++++++++++++ apply H11.
++++++++++++++ intros. split.
+++++++++++++++ simpl. auto.
+++++++++++++++ apply cast_to_right_is_boring.
destruct H3. apply H11. rewrite H10. reflexivity.
++++++ inversion H2.
+++++ simpl. destruct p1. simpl in H1. destruct s.
++++++ simpl in IHw. destruct H0. destruct H2.
destruct H2.
+++++++ inversion H2.
+++++++ inversion H2.
+++++++ inversion H2.
subst p3. subst m. subst ep0. subst p2. subst m'. subst w'0.
destruct H4. destruct H5.
destruct H3.
++++++++ destruct H6.
+++++++++
assert ((forall m, (In m p1 ->(exists y, m = inl y)) /\
(In m p0 ->(exists y, m = inl y)))).
{ apply inl_move_implies_inl with (y0:=x). 
destruct H5.
+ inversion H5.
+ inversion H5. subst p2. destruct H7. destruct H6. auto.
+ inversion H5. subst p2. destruct H7. destruct H6. auto. }
assert (forall m, (In m p ->(exists y, m = inr y)) /\
(In m p1 ->(exists y, m = inr y))).
{ apply inr_move_implies_inr with (y0:=y). 
destruct H3. auto. }
assert (p1 = nil).
{destruct p1.
+ reflexivity.
+ destruct s.
++ assert (forall m : X + Y,
     (In m (inl x1 :: p1) -> exists y : Y, m = inr y)).
{apply H8. }
assert (exists y : Y, inl x1 = inr y).
{apply H9. simpl. left. reflexivity. }
destruct H10. inversion H10.
++ assert (forall m : X + Y,
     (In m (inr y0 :: p1) -> exists y : X, m = inl y)).
{ apply H7. }
assert (exists x : X, inr y0 = inl x).
{ apply H9. simpl. left. reflexivity. }
destruct H10. inversion H10.
} subst p1. destruct H3. unfold move_from in H9.
assert (~ In (inr y : X + Y) p /\ In (inr y : X + Y) nil).
{apply H9. reflexivity. }
destruct H10. contradiction H11.
+++++++++
assert ((forall m, (In m p0 ->(exists y, m = inl y)) /\
(In m p1 ->(exists y, m = inl y)))).
{ apply inl_move_implies_inl with (y0:=x). 
destruct H5.
+ inversion H5.
+ inversion H5. subst p2. destruct H7. destruct H6. auto.
+ inversion H5. subst p2. destruct H7. destruct H6. auto. }
assert (forall m, (In m p ->(exists y, m = inr y)) /\
(In m p1 ->(exists y, m = inr y))).
{ apply inr_move_implies_inr with (y0:=y). 
destruct H3. auto. }
assert (p1 = nil).
{destruct p1.
+ reflexivity.
+ destruct s.
++ assert (forall m : X + Y,
     (In m (inl x1 :: p1) -> exists y : Y, m = inr y)).
{apply H8. }
assert (exists y : Y, inl x1 = inr y).
{apply H9. simpl. left. reflexivity. }
destruct H10. inversion H10.
++ assert (forall m : X + Y,
     (In m (inr y0 :: p1) -> exists y : X, m = inl y)).
{ apply H7. }
assert (exists x : X, inr y0 = inl x).
{ apply H9. simpl. left. reflexivity. }
destruct H10. inversion H10.
} subst p1. destruct H3. unfold move_from in H9.
assert (~ In (inr y : X + Y) p /\ In (inr y : X + Y) nil).
{apply H9. reflexivity. }
destruct H10. contradiction H11.
++++++++ destruct H6.
+++++++++ assert ((forall m, (In m p1 ->(exists y, m = inl y)) /\
(In m p0 ->(exists y, m = inl y)))).
{ apply inl_move_implies_inl with (y0:=x). 
destruct H5.
+ inversion H5.
+ inversion H5. subst p2. destruct H7. destruct H6. auto.
+ inversion H5. subst p2. destruct H7. destruct H6. auto. }
assert (forall m, (In m p1 ->(exists y, m = inr y)) /\
(In m p ->(exists y, m = inr y))).
{ apply inr_move_implies_inr with (y0:=y). 
destruct H3. auto. }
assert (p1 = nil).
{destruct p1.
+ reflexivity.
+ destruct s.
++ assert (forall m : X + Y,
     (In m (inl x1 :: p1) -> exists y : Y, m = inr y)).
{apply H8. }
assert (exists y : Y, inl x1 = inr y).
{apply H9. simpl. left. reflexivity. }
destruct H10. inversion H10.
++ assert (forall m : X + Y,
     (In m (inr y0 :: p1) -> exists y : X, m = inl y)).
{ apply H7. }
assert (exists x : X, inr y0 = inl x).
{ apply H9. simpl. left. reflexivity. }
destruct H10. inversion H10. 
} subst p1.
assert (source_walk _ (cast_to_right_in_walk P Q E F w') = nil).
{ apply cast_to_nil_inl. 
refine (ex_intro _ p0 _).
refine (ex_intro _ x0 _).
refine (ex_intro _ b0 _).
apply H5.
}
destruct (cast_to_right_in_walk P Q E F w') eqn:IND.
++++++++++ simpl in H9. subst p1.
apply valid_one_move_walk with 
(p1:=(cast_to_right X Y p)) (m:=y) (ep0:=ep) (p2:=nil).
+++++++++++ reflexivity.
+++++++++++ split.
++++++++++++ apply sum_valid_position_valid_inr. auto.
++++++++++++ split.
+++++++++++++ apply valid_empty_walk with (p1:=nil).
++++++++++++++ reflexivity.
++++++++++++++ unfold valid_position.
intros. split.
+++++++++++++++ intros. destruct H9. contradiction H10.
+++++++++++++++ intros. destruct H9. contradiction H9.
+++++++++++++ right. split.
++++++++++++++ destruct H3. auto.
++++++++++++++ destruct H3. unfold move_from.
split.
+++++++++++++++ intros. contradiction H10.
+++++++++++++++ unfold iff. intros. split.
++++++++++++++++ intros. destruct H10.
apply cast_to_right_is_boring in H11.
unfold move_from in H9.
assert (inr n = (inr y : X + Y) -> n = y).
{ intros. inversion H12. reflexivity. }
apply H12. apply H9. split.
+++++++++++++++++ simpl. auto.
+++++++++++++++++ apply H11.
++++++++++++++++ intros. split.
+++++++++++++++++ simpl. auto.
+++++++++++++++++
assert (inr n = (inr y : X + Y)).
{ rewrite H10. reflexivity. } apply cast_to_right_is_boring.
apply H9. apply H11.
++++++++++ simpl in H9. subst p1.
apply valid_non_empty_walk with
(p1:=cast_to_right X Y p) (m:=y) (ep0:=ep) (p3:=nil)
(w'0:=w) (m':=p2).
+++++++++++ reflexivity.
+++++++++++ split.
++++++++++++ apply sum_valid_position_valid_inr. auto.
++++++++++++ split.
+++++++++++++ auto.
+++++++++++++ right. split.
++++++++++++++ apply H3.
++++++++++++++ unfold move_from. split.
+++++++++++++++ intros. contradiction H9.
+++++++++++++++ intros. unfold iff. split.
++++++++++++++++ intros. destruct H9.
apply cast_to_right_is_boring in H10.
destruct H3.
unfold move_from in H11.
assert (inr n = (inr y : X + Y) -> n = y).
{ intros. inversion H12. reflexivity. }
apply H12. apply H11. split.
+++++++++++++++++ simpl. auto.
+++++++++++++++++ apply H10.
++++++++++++++++ intros. split.
+++++++++++++++++ simpl. auto.
+++++++++++++++++
assert (inr n = (inr y : X + Y)).
{ rewrite H9. reflexivity. } apply cast_to_right_is_boring.
destruct H3.
unfold move_from in H11. apply H11. apply H10.
+++++++++
assert ((forall m, (In m p0 ->(exists y, m = inl y)) /\
(In m p1 ->(exists y, m = inl y)))).
{ apply inl_move_implies_inl with (y0:=x). 
destruct H5.
+ inversion H5.
+ inversion H5. subst p2. destruct H7. destruct H6. auto.
+ inversion H5. subst p2. destruct H7. destruct H6. auto. }
assert (forall m, (In m p1 ->(exists y, m = inr y)) /\
(In m p ->(exists y, m = inr y))).
{ apply inr_move_implies_inr with (y0:=y). 
destruct H3. auto. }
assert (p1 = nil).
{destruct p1.
+ reflexivity.
+ destruct s.
++ assert (forall m : X + Y,
     (In m (inl x1 :: p1) -> exists y : Y, m = inr y)).
{apply H8. }
assert (exists y : Y, inl x1 = inr y).
{apply H9. simpl. left. reflexivity. }
destruct H10. inversion H10.
++ assert (forall m : X + Y,
     (In m (inr y0 :: p1) -> exists y : X, m = inl y)).
{ apply H7. }
assert (exists x : X, inr y0 = inl x).
{ apply H9. simpl. left. reflexivity. }
destruct H10. inversion H10.
} subst p1.
assert (source_walk _ (cast_to_right_in_walk P Q E F w') = nil).
{ apply cast_to_nil_inl. 
refine (ex_intro _ p0 _).
refine (ex_intro _ x0 _).
refine (ex_intro _ b0 _).
apply H5.
}
destruct (cast_to_right_in_walk P Q E F w') eqn:IND.
++++++++++ simpl in H9. subst p1.
apply valid_one_move_walk with 
(p1:=(cast_to_right X Y p)) (m:=y) (ep0:=ep) (p2:=nil).
+++++++++++ reflexivity.
+++++++++++ split.
++++++++++++ apply sum_valid_position_valid_inr. auto.
++++++++++++ split.
+++++++++++++ apply valid_empty_walk with (p1:=nil).
++++++++++++++ reflexivity.
++++++++++++++ unfold valid_position.
intros. split.
+++++++++++++++ intros. destruct H9. contradiction H10.
+++++++++++++++ intros. destruct H9. contradiction H9.
+++++++++++++ right. split.
++++++++++++++ destruct H3. auto.
++++++++++++++ destruct H3. unfold move_from.
split.
+++++++++++++++ intros. contradiction H10.
+++++++++++++++ unfold iff. intros. split.
++++++++++++++++ intros. destruct H10.
apply cast_to_right_is_boring in H11.
unfold move_from in H9.
assert (inr n = (inr y : X + Y) -> n = y).
{ intros. inversion H12. reflexivity. }
apply H12. apply H9. split.
+++++++++++++++++ simpl. auto.
+++++++++++++++++ apply H11.
++++++++++++++++ intros. split.
+++++++++++++++++ simpl. auto.
+++++++++++++++++
assert (inr n = (inr y : X + Y)).
{ rewrite H10. reflexivity. } apply cast_to_right_is_boring.
apply H9. apply H11.
++++++++++ simpl in H9. subst p1.
apply valid_non_empty_walk with
(p1:=cast_to_right X Y p) (m:=y) (ep0:=ep) (p3:=nil)
(w'0:=w) (m':=p2).
+++++++++++ reflexivity.
+++++++++++ split.
++++++++++++ apply sum_valid_position_valid_inr. auto.
++++++++++++ split.
+++++++++++++ auto.
+++++++++++++ right. split.
++++++++++++++ apply H3.
++++++++++++++ unfold move_from. split.
+++++++++++++++ intros. contradiction H9.
+++++++++++++++ intros. unfold iff. split.
++++++++++++++++ intros. destruct H9.
apply cast_to_right_is_boring in H10.
destruct H3.
unfold move_from in H11.
assert (inr n = (inr y: X + Y) -> n = y).
{ intros. inversion H12. reflexivity. }
apply H12. apply H11. split.
+++++++++++++++++ simpl. auto.
+++++++++++++++++ apply H10.
++++++++++++++++ intros. split.
+++++++++++++++++ simpl. auto.
+++++++++++++++++
assert (inr n = (inr y : X + Y)).
{ rewrite H9. reflexivity. } apply cast_to_right_is_boring.
destruct H3.
unfold move_from in H11. apply H11. apply H10.
++++++
apply valid_non_empty_walk
with (p1:=(cast_to_right X Y p)) (m:=y) (ep0:=ep) 
(p3:=(cast_to_right X Y p0))
(m':=(y0,b0)) (w'0:=(cast_to_right_in_walk P Q E F w')).
+++++++ reflexivity.
+++++++ split.
++++++++ destruct H0. apply sum_valid_position_valid_inr.
 apply H0.
++++++++ split.
+++++++++ destruct H0. destruct H2. apply H1.
+++++++++ destruct H0. destruct H2. destruct H3. left.
destruct H3. split.
++++++++++ apply H3.
++++++++++
assert (p2 = nil).
{ destruct p2. 
+ reflexivity. 
+ destruct H2.
++ inversion H2.
++ inversion H2.
++ inversion H2.
subst p1. subst m. subst b. subst p3. subst m'. subst w'0.
destruct s. destruct H5. destruct H6.
+++ destruct H4. unfold move_from in H8.
assert (In (inr y) (inl x0 :: p2)).
{ apply H8. reflexivity. }
assert (~ (In (inl x0) (inl x0 :: p2) /\ In (inr y) (inl x0 :: p2))).
{apply sum_valid_position_is_pure
with (P0:=P) (Q0:=Q) (E0:=E) (F0:=F). apply H5.
}
contradiction H10. split.
+++++ simpl. left. reflexivity.
+++++ apply H9.
+++ destruct H5. destruct H6. destruct H7.
++++ destruct H7. unfold move_from in H8. destruct H8.
assert (In (inr y1) p0).
{apply H8. simpl. left. reflexivity. }
assert ( ~ In (inl x) (inr y1 :: p2) /\ In (inl x) p0).
{apply H9. reflexivity. }
assert (~ (In (inl x) p0 /\ In (inr y1) p0)).
{apply sum_valid_position_is_pure
with (P0:=P) (Q0:=Q) (E0:=E) (F0:=F). destruct H6.
+ inversion H6.
+ inversion H6. subst p1. apply H12.
+ inversion H6. subst p1. apply H12.
} contradiction H12. destruct H11. split.
+++++ apply H13.
+++++ apply H10. 
++++ destruct H7. unfold move_from in H8.
assert (In (inl x) (inr y1 :: p2)).
{apply H8. reflexivity. }
assert (~(In (inl x) (inr y1 :: p2) /\ In (inr y1) (inr y1 :: p2))).
{apply sum_valid_position_is_pure
with (P0:=P) (Q0:=Q) (E0:=E) (F0:=F). apply H5.
}
contradiction H10. split.
+++++ apply H9.
+++++ simpl. left. reflexivity.
}
subst p2. unfold move_from in H4. destruct H4.
assert (~ In (inr y : X + Y) p /\ In (inr y : X + Y) nil).
{ apply H5.  reflexivity. }
destruct H6. simpl in H7. contradiction H7.
++++++++++
assert (p2 = nil).
{ destruct p2. 
+ reflexivity. 
+ destruct H2.
++ inversion H2.
++ inversion H2.
++ inversion H2.
subst p1. subst m. subst b. subst p3. subst m'. subst w'0.
destruct s. destruct H4. destruct H5. destruct H3.
+++ unfold move_from in H7.
assert ( In (inr y) p).
{ apply H7.  reflexivity. }
assert (In (inl x0) p).
{ destruct H7. apply H7. simpl. left. reflexivity. }
assert (~ (In (inl x0) p /\ In (inr y) p)).
{ apply sum_valid_position_is_pure. apply H0. }
contradiction H10. split.
++++ apply H9.
++++ apply H8.
+++ destruct H4. destruct H5. destruct H6.
++++ destruct H6. unfold move_from in H7.
assert (In (inl x) p0).
{apply H7. reflexivity. }
assert (In (inr y1) p0).
{destruct H7. apply H7. simpl. left. reflexivity. }
assert (~(In (inl x) p0 /\ In (inr y1) p0)).
{apply sum_valid_position_is_pure. 
 destruct H5.
+ inversion H5.
+ inversion H5. subst p1. destruct H10. auto.
+ inversion H5. subst p1. destruct H10. auto.
} contradiction H10. destruct H7. auto.
++++ destruct H6. unfold move_from in H7.
assert (In (inl x) (inr y1 :: p2)).
{ apply H7.  reflexivity. }
assert (~ (In (inl x) (inr y1 :: p2) /\ In (inr y1) (inr y1 :: p2))).
{ apply sum_valid_position_is_pure
with (P0:=P) (Q0:=Q) (E0:=E) (F0:=F). auto. } contradiction H9. split.
+++++  apply H8.
+++++ simpl. left. reflexivity.
} subst p2. right.
destruct H3. split.
+++++++++++ apply H3.
+++++++++++
assert (forall m, In m p0 -> m = inl x).
{intros. destruct H2. 
+ inversion H2. 
+ inversion H2. 
+ inversion H2. subst p1. subst m0. subst b. subst p2.
subst m'. subst w'0.
 destruct H6. destruct H7. destruct H8.
++ destruct H8. unfold move_from in H9.
apply H9.  split.
+++ simpl. auto.
+++ apply H5.
++ destruct H8. unfold move_from in H9.
assert (In (inl x: X + Y) nil).
{ apply H9.  reflexivity. } contradiction H10.
}
assert (forall m, In m p -> m = inr y).
{ intros. unfold move_from in H4. apply H4. split.
+ simpl. auto.
+ apply H6.
}
assert (forall p0, (forall m : X + Y, In m p0 -> m = inl x) ->
cast_to_right X Y p0 = nil).
{ intros. induction p1. 
+ simpl. reflexivity.
+ destruct a.
++ simpl. apply IHp1. intros. apply H7. simpl. right. apply H8.
++ assert (inr y1 = inl x).
{ apply H7.  simpl. left. reflexivity. }
inversion H8.
 }
assert ( cast_to_right X Y p0 = nil).
{apply H7.  apply H5. } rewrite H8.
assert (forall p2, move_from (event_structure_sum P Q E F)
        (inr y) nil p2 ->
(forall m, In m (cast_to_right X Y p2) -> m = y) ).
{intros. induction p2.
+ simpl in H8. contradiction H10.
+ simpl in H8. destruct a.
++ apply IHp2. destruct p2.
+++ simpl in H10. contradiction H10.
+++ unfold move_from. split.
++++ intros. contradiction H11.
++++ intros. unfold iff. split.
+++++ intros. unfold move_from in H9.
apply H9. split.
++++++ simpl. auto.
++++++ simpl. simpl in H11. right. apply H11.
+++++ intros. unfold move_from in H9.
subst n.
assert (s = inr y).
{apply H9. split.
+ simpl. auto.
+ simpl. right. left. reflexivity.
} subst s. simpl. auto.
+++ destruct p2.
++++ unfold move_from in H9. simpl in H9.
assert (inl x0 = (inr y : X + Y)).
{apply H9. split.
+ simpl. auto.
+ simpl. left. reflexivity.
} inversion H11.
++++ unfold move_from in H9.
assert (s = inr y).
{apply H9. split.
+ simpl. auto.
+ simpl. right. left. reflexivity.
} subst s. simpl in H10. simpl. apply H10.
++ destruct p2. unfold move_from in H9. simpl in H9.
simpl in H10.
assert (inr y1 = (inr y : X + Y)).
{apply H9. split.
+ simpl. auto.
+ simpl. left. reflexivity.
 } inversion H11. subst y1. destruct H10. rewrite H10.
reflexivity.
+++ contradiction H10.
+++ apply IHp2.
++++ unfold move_from. unfold move_from in H9. split.
+++++ intros. contradiction H11.
+++++ unfold iff. intros. split.
++++++ intros. apply H9. split.
+++++++ simpl. auto.
+++++++ destruct H11. simpl in H12. simpl. right. apply H12.
++++++ intros. split.
+++++++ simpl. auto.
+++++++ subst n.
assert (s = inr y).
{apply H9. split.
+ simpl. auto.
+ simpl. right. left. reflexivity. } subst s.
simpl. left. reflexivity.
++++ unfold move_from in H9.
assert (inr y1 = (inr y : X + Y)).
{apply H9. split.
+ simpl. auto.
+ simpl. left.  reflexivity. } inversion H11. subst y1.
assert (s = (inr y : X + Y)).
{apply H9. split.
+ simpl. auto.
+ simpl. right. left.  reflexivity. } inversion H11. subst s.
simpl in H10. simpl. destruct H10.
+++++ left. apply H10.
+++++ apply H10.
}
assert (forall m : Y, In m (cast_to_right X Y p) -> m = y).
{ apply H9. apply H4. }
unfold move_from. split.
++++++++++++ intros. contradiction H11.
++++++++++++ intros. unfold iff. split.
+++++++++++++ intros. apply H10. apply H11.
+++++++++++++ intros. split.
++++++++++++++ simpl. auto.
++++++++++++++ unfold move_from in H4.
assert (In (inr y) p).
{apply H4.  reflexivity. }
apply cast_to_right_is_boring. subst n. apply H12.
++++ apply valid_non_empty_walk
with (p1:=(cast_to_right X Y p)) (m:=y)
(ep0:=ep) (p3:=(cast_to_right X Y p2)) (m':=(y0, b))
(w'0:=(cast_to_right_in_walk P Q E F w')).
+++++ reflexivity.
+++++ split.
++++++ destruct H0. apply sum_valid_position_valid_inr. apply H0.
++++++ split.
+++++++ destruct H0. destruct H1. simpl in IHw.
apply IHw. apply H1.
+++++++ destruct H0. destruct H1. destruct H2.
++++++++ left. split.
+++++++++ destruct H2. apply H2.
+++++++++ destruct H2. unfold move_from. unfold
move_from in H3. split.
++++++++++ destruct H3.
intros. apply cast_to_right_is_boring in H5.
 apply cast_to_right_is_boring. apply H3. apply H5.
++++++++++ split.
+++++++++++ destruct H3. intros.
 rewrite cast_to_right_is_boring in H5. 
 rewrite cast_to_right_is_boring in H5.
assert ((inr n : X + Y) = inr y).
{ apply H4. auto. } inversion H6. reflexivity.
+++++++++++ intros.
 rewrite cast_to_right_is_boring.
 rewrite cast_to_right_is_boring.
apply H3. rewrite H4. reflexivity.
++++++++ destruct H2. right. split.
+++++++++ apply H2.
+++++++++ unfold move_from. unfold move_from in H3. split.
++++++++++ destruct H3. intros.
apply cast_to_right_is_boring in H5. 
apply cast_to_right_is_boring. apply H3. apply H5.
++++++++++ split.
+++++++++++ destruct H3. intros.
rewrite cast_to_right_is_boring in H5.
rewrite cast_to_right_is_boring in H5.
assert ((inr n : X + Y) = inr y).
{ apply H4. auto. } inversion H6. reflexivity.
+++++++++++ intros.
 rewrite cast_to_right_is_boring.
 rewrite cast_to_right_is_boring. apply H3. rewrite H4.
reflexivity.
Qed.

Fact target_is_cast_inl
`(P : PartialOrder X) `(Q : PartialOrder Y)
(E : EventStructure P) (F : EventStructure Q)
: forall w p,
target_walk (event_structure_sum P Q E F) w = p
->
target_walk E (cast_to_left_in_walk P Q E F w) 
= (cast_to_left X Y p).
Proof. intros. induction w.
+ simpl in H. subst p0. simpl. reflexivity.
+ simpl. destruct p1. destruct s.
++ simpl. apply IHw. simpl in H. apply H.
++ apply IHw. simpl in H. apply H.
Qed.

Fact target_is_cast_inr
`(P : PartialOrder X) `(Q : PartialOrder Y)
(E : EventStructure P) (F : EventStructure Q)
: forall w p,
target_walk (event_structure_sum P Q E F) w = p
->
target_walk F (cast_to_right_in_walk P Q E F w) 
= (cast_to_right X Y p).
Proof. intros. induction w.
+ simpl in H. subst p0. simpl. reflexivity.
+ simpl. destruct p1. destruct s.
++ apply IHw. simpl in H. apply H.
++ simpl. apply IHw. simpl in H. apply H.
Qed.

Fact nil_in_cast_inl
`(P : PartialOrder X) `(Q : PartialOrder Y)
(E : EventStructure P) (F : EventStructure Q)
: forall w, valid_walk _ w ->
position_in_walk (event_structure_sum P Q E F) nil w
->
position_in_walk E nil (cast_to_left_in_walk P Q E F w).
Proof. intros. induction w.
+ simpl in H0. simpl. subst p. simpl. reflexivity.
+ simpl. destruct p0. destruct s.
++ simpl. simpl in H0. destruct H0.
+++ left. subst p. simpl. reflexivity.
+++ right. apply IHw. destruct H. 
++++ inversion H.
++++ inversion H. subst p1. subst m. subst ep. subst w.
apply H1.
++++ inversion H. subst p1. subst m. subst ep. subst w.
apply H1.
++++ apply H0.
++
assert (source_walk _ (cast_to_left_in_walk P Q E F w) = nil).
{apply cast_to_nil_inr. 
refine (ex_intro _ p _).
refine (ex_intro _ y _).
refine (ex_intro _ b _).
auto.
}
destruct (cast_to_left_in_walk P Q E F w).
+++ simpl in H1. subst p0. simpl. reflexivity.
+++ simpl in H1. subst p0. simpl. left. reflexivity.
Qed.

Fact nil_in_cast_inr
`(P : PartialOrder X) `(Q : PartialOrder Y)
(E : EventStructure P) (F : EventStructure Q)
: forall w, valid_walk _ w ->
position_in_walk (event_structure_sum P Q E F) nil w
->
position_in_walk F nil (cast_to_right_in_walk P Q E F w).
Proof. intros. induction w.
+ simpl in H0. simpl. subst p. simpl. reflexivity.
+ simpl. destruct p0. destruct s.
++
assert (source_walk _ (cast_to_right_in_walk P Q E F w) = nil).
{apply cast_to_nil_inl. 
refine (ex_intro _ p _).
refine (ex_intro _ x _).
refine (ex_intro _ b _).
auto.
}
destruct (cast_to_right_in_walk P Q E F w).
+++ simpl in H1. subst p0. simpl. reflexivity.
+++ simpl in H1. subst p0. simpl. left. reflexivity.
++ simpl. simpl in H0. destruct H0.
+++ left. subst p. simpl. reflexivity.
+++ right. apply IHw. destruct H. 
++++ inversion H.
++++ inversion H. subst p1. subst m. subst ep. subst w.
apply H1.
++++ inversion H. subst p1. subst m. subst ep. subst w.
apply H1.
++++ apply H0.
Qed.

Fixpoint cast_infinite_position_to_inl
`(P : PartialOrder X) `(Q : PartialOrder Y)
(E : EventStructure P) (F : EventStructure Q)
(p : InfinitePosition (event_structure_sum P Q E F)) :
InfinitePosition E :=
match p with
| stream _ (inr m) f => 
cast_infinite_position_to_inl _ _ _ _ (f tt)
| stream _ (inl m) f => 
stream E m (fun _ => 
cast_infinite_position_to_inl _ _ _ _ (f tt))
end. 

Fixpoint cast_infinite_position_to_inr
`(P : PartialOrder X) `(Q : PartialOrder Y)
(E : EventStructure P) (F : EventStructure Q)
(p : InfinitePosition (event_structure_sum P Q E F)) :
InfinitePosition F :=
match p with
| stream _ (inl _) f => 
cast_infinite_position_to_inr _ _ _ _ (f tt)
| stream _ (inr m) f => stream _ m 
(fun _ => cast_infinite_position_to_inr _ _ _ _ (f tt))
end. 

Instance asynchronous_arena_sum
`(P : PartialOrder X) `(Q : PartialOrder Y)
(E : EventStructure P) (F : EventStructure Q)
(A : AsynchronousArena E) (B : AsynchronousArena F)
(positive1 : finite_payoff (inl (nil : Position E)) = (-1)%Z)
(positive2 : finite_payoff (inl (nil : Position F)) = (-1)%Z)
: AsynchronousArena (event_structure_sum P Q E F) :=
{ polarity m := match m with
| inl m => polarity m
| inr m => polarity m
end;

finite_payoff m := match m with
| inl nil => (-1)%Z 
| inl (((inl _) :: _) as l) => 
finite_payoff (inl (cast_to_left X Y l))
| inl (((inr _) :: _) as l) => 
finite_payoff (inl (cast_to_right X Y l))
| inr (w) =>
if beq_nat (length_walk _ w) 
(length_walk _ (cast_to_left_in_walk P Q E F w)) then
finite_payoff (inr (cast_to_left_in_walk P Q E F w)) else
if beq_nat (length_walk _ w) 
(length_walk _ (cast_to_right_in_walk P Q E F w)) then
finite_payoff (inr (cast_to_right_in_walk P Q E F w)) else
(match (target_walk _ w) with
| nil => (-1)%Z
| ((inl _ :: _) as pos) => 
 finite_payoff (inl (cast_to_left X Y pos))
| ((inr _ :: _) as pos) => 
 finite_payoff (inl (cast_to_right X Y pos))
end)
end;
infinite_payoff p :=
match p with
| stream _ (inl _) _ => 
infinite_payoff (cast_infinite_position_to_inl _ _ _ _ p)
| stream _ (inr _) _ => 
infinite_payoff (cast_infinite_position_to_inr _ _ _ _ p)
end
}.
Proof.
- intros. destruct H. destruct H0.
destruct m.
+ destruct n.
++ simpl.
unfold initial_move in H. simpl in H.
assert (initial_move E x).
{ unfold initial_move. intros. unfold iff.  split. 
- intros. apply reverse_inversion_left with (A:=X) (B:=Y).
apply H. apply add_inl_does_nothing. apply H2.
- intros. apply add_inl_does_nothing with (A:=X) (B:=Y).
apply H. apply reverse_inversion_left with (A:=X) (B:=Y). apply H2.
}
unfold initial_move in H0. simpl in H0.
assert (initial_move E x0).
{ unfold initial_move. intros. unfold iff.  split. 
- intros. apply reverse_inversion_left with (A:=X) (B:=Y).
apply H0. apply add_inl_does_nothing. apply H3.
- intros. apply add_inl_does_nothing with (A:=X) (B:=Y).
apply H0. apply reverse_inversion_left with (A:=X) (B:=Y). apply H3.
} apply initial_incompatible. split.
+++ apply H2.
+++ split.
++++ apply H3.
++++ apply reverse_inversion_opposite_left in H1. apply H1.
++ simpl. auto.
+ destruct n.
++ simpl. auto.
++ unfold initial_move in H. simpl in H.
assert (initial_move F y).
{ unfold initial_move. intros. unfold iff.  split. 
- intros. apply reverse_inversion_right with (A:=X) (B:=Y).
apply H. apply add_inr_does_nothing. apply H2.
- intros. apply add_inr_does_nothing with (A:=X) (B:=Y).
apply H. apply reverse_inversion_right with (A:=X) (B:=Y). apply H2.
}
unfold initial_move in H0. simpl in H0.
assert (initial_move F y0).
{ unfold initial_move. intros. unfold iff.  split. 
- intros. apply reverse_inversion_right with (A:=X) (B:=Y).
apply H0. apply add_inr_does_nothing. apply H3.
- intros. apply add_inr_does_nothing with (A:=X) (B:=Y).
apply H0. apply reverse_inversion_right with (A:=X) (B:=Y). apply H3.
} simpl. apply initial_incompatible. split.
+++ apply H2.
+++ split.
++++ apply H3.
++++ apply reverse_inversion_opposite_right in H1. apply H1.
- left. reflexivity.
- intros. destruct m.
+ assert (initial_move E x).
{ unfold initial_move. intros. unfold iff.  split. 
- intros. apply reverse_inversion_left with (A:=X) (B:=Y).
apply H. apply add_inl_does_nothing. apply H0.
- intros. apply add_inl_does_nothing with (A:=X) (B:=Y).
apply H. apply reverse_inversion_left with (A:=X) (B:=Y). apply H0.
} 

assert
((polarity x = true <-> finite_payoff (inl(nil : Position E)) = (-1)%Z)
/\
(polarity x = false <-> finite_payoff (inl(nil : Position E)) = (1)%Z)).
{ apply polarity_first. apply H0. }
split.
++ unfold iff. split.
+++ intros. reflexivity.
+++ intros. apply H1. apply positive1.
++ unfold iff. split.
+++ intros.
assert (polarity x = true).
{ apply H1. apply positive1. }
rewrite H2 in H3. inversion H3.
+++ intros. omega.
+ unfold initial_move in H. 
assert (initial_move F y).
{ unfold initial_move. intros. unfold iff.  split. 
- intros. apply reverse_inversion_right with (A:=X) (B:=Y).
apply H. apply add_inr_does_nothing. apply H0.
- intros. apply add_inr_does_nothing with (A:=X) (B:=Y).
apply H. apply reverse_inversion_right with (A:=X) (B:=Y). apply H0.
}
split.
++ unfold iff. split.
+++ intros. reflexivity.
+++ intros. 
assert
((polarity y = true <-> finite_payoff (inl(nil : Position F)) = (-1)%Z)
/\
(polarity y = false <-> finite_payoff (inl(nil : Position F)) = (1)%Z)).
{ apply polarity_first. apply H0. }
apply H2. apply positive2.
++ unfold iff. split.
+++ intros.
assert
((polarity y = true <-> finite_payoff (inl(nil : Position F)) = (-1)%Z)
/\
(polarity y = false <-> finite_payoff (inl(nil : Position F)) = (1)%Z)).
{ apply polarity_first. apply H0. }
assert (polarity y = true).
{ apply H2.  apply positive2. }
rewrite H1 in H3. inversion H3.
+++ intros. omega.
- intros. destruct m.
+ split. 
++ intros.
assert (second_move E x).
{ unfold second_move. unfold second_move in H. split. 
+  intros.
assert ((inl n : X + Y) = inl x \/
     initial_move (event_structure_sum P Q E F)
       (inl n)).
{ apply H. simpl. apply add_inl_does_nothing. apply H1. }
destruct H2.
++ inversion H2. left. reflexivity.
++ right.
unfold initial_move. intros. unfold iff.  split. 
+++ intros. apply reverse_inversion_left with (A:=X) (B:=Y).
apply H2. apply add_inl_does_nothing. apply H3.
+++ intros. apply add_inl_does_nothing with (A:=X) (B:=Y).
apply H2. apply reverse_inversion_left with (A:=X) (B:=Y). apply H3.
+ destruct H. destruct H1. destruct x0.
++ refine (ex_intro _ x0 _). destruct H1. split.
+++  simpl in H1. apply add_inl_does_nothing in H1. apply H1.
+++ apply reverse_inversion_opposite_left with (A:= X) (B:=Y) in H2.
apply H2.
++ destruct H1.  simpl in H1. apply inr_not_in_add_inl in H1.
contradiction H1.
 }
assert 
(polarity x = true -> finite_payoff (inl(nil : Position E)) = (1)%Z).
{ apply polarity_second. apply H1. }
assert (finite_payoff (inl(nil : Position E)) = (1)%Z).
{ apply H2. apply H0. }
rewrite positive1 in H3. apply H3.
++ intros. auto.
+ split.
++ intros.
assert (second_move F y).
{ unfold second_move. unfold second_move in H. split. 
+  intros.
assert ((inr n : X + Y) = inr y \/
     initial_move (event_structure_sum P Q E F)
       (inr n)).
{ apply H. simpl. apply add_inr_does_nothing. apply H1. }
destruct H2.
++ inversion H2. left. reflexivity.
++ right.
unfold initial_move. intros. unfold iff.  split. 
+++ intros. apply reverse_inversion_right with (A:=X) (B:=Y).
apply H2. apply add_inr_does_nothing. apply H3.
+++ intros. apply add_inr_does_nothing with (A:=X) (B:=Y).
apply H2. apply reverse_inversion_right with (A:=X) (B:=Y). apply H3.
+ destruct H. destruct H1. destruct x.
++ destruct H1.  simpl in H1. apply inl_not_in_add_inr in H1.
contradiction H1.
++ refine (ex_intro _ y0 _). destruct H1. split.
+++  simpl in H1. apply add_inr_does_nothing in H1. apply H1.
+++ apply reverse_inversion_opposite_right with (A:= X) (B:=Y) in H2.
apply H2.
 }
assert 
(polarity y = true -> finite_payoff (inl(nil : Position F)) = (1)%Z).
{ apply polarity_second. apply H1. }
assert (finite_payoff (inl(nil : Position F)) = (1)%Z).
{ apply H2. apply H0. }
rewrite positive2 in H3. apply H3.
++ intros. auto.
- intros. destruct H. subst w. simpl in H. simpl.
assert (valid_position E (cast_to_left X Y p)).
{ unfold valid_position in H. unfold valid_position.
intros. split.
+ intros. destruct H0.
assert ((In (inl x) p /\ In (inl y) p -> 
~ incompatible (inl x) (inl y))).
{ inversion H. 
+ inversion H2.
subst p.  unfold valid_position in H3. apply H3.
+ inversion H2.
+ inversion H2.
 }
assert (~ incompatible (inl x) (inl y)).
{ apply H2. split.
+ apply cast_to_left_is_boring. apply H0.
+ apply cast_to_left_is_boring. apply H1. }
simpl in H3. apply H3.
+ intros. destruct H0.
assert (In (inl y) p).
{ inversion H.
+ unfold valid_position in H3.
inversion H2. subst p. apply H3 with (x:=inl x). split.
++ apply cast_to_left_is_boring. apply H0.
++ simpl. apply H1.
+ inversion H2.
+ inversion H2.
 }
apply cast_to_left_is_boring. apply H2.
}
apply initial_null with (p0:=(cast_to_left X Y p)).
inversion H. split.
+ apply valid_empty_walk with (p1:=(cast_to_left X Y p)). 
reflexivity. inversion H1. subst p. apply H0.
+ reflexivity.
+ inversion H1.
+ inversion H1.
- 
intros. destruct H. destruct H0. destruct H1.


destruct (length_walk (event_structure_sum P Q E F) w =?
  length_walk E (cast_to_left_in_walk P Q E F w)) eqn:H'.
+ apply beq_nat_true in H'.
rewrite H' in H0.
assert (position_in_walk E nil (cast_to_left_in_walk P Q E F w)).
{apply nil_in_cast_inl. apply H. apply H2. }
assert (target_walk E (cast_to_left_in_walk P Q E F w) 
= (cast_to_left X Y p)).
{apply target_is_cast_inl. apply H1. }
assert (valid_walk E (cast_to_left_in_walk P Q E F w)).
{apply valid_walk_is_valid_inl. apply H. }
assert (finite_payoff (inr (cast_to_left_in_walk P Q E F w)) 
= finite_payoff (inl (cast_to_left X Y p))).
{apply noninitial_payoff. auto. }
rewrite H6. destruct p.
++ simpl. apply positive1.
++ destruct s.
+++ reflexivity.
+++ 
assert ((exists p, w = empty_walk (event_structure_sum P Q E F) p)
\/
forall m p, (position_in_walk _ p w /\ In m p) ->
(exists x, m = inl x)).
{apply sum_equals_inl_implies_inl. auto. }
destruct H7.
++++ destruct H7. subst w. simpl in H0. lia.
++++
assert (exists x : X, inr y = inl x).
{apply H7 with (p:= inr y :: p). split.
 apply target_in_walk. auto. simpl. left. reflexivity. }
destruct H8. inversion H8.
+ destruct (length_walk (event_structure_sum P Q E F) w =?
  length_walk F (cast_to_right_in_walk P Q E F w)) eqn:H''.
apply beq_nat_true in H''.
rewrite H'' in H0.
assert (position_in_walk F nil (cast_to_right_in_walk P Q E F w)).
{apply nil_in_cast_inr. apply H. apply H2. }
assert (target_walk F (cast_to_right_in_walk P Q E F w) 
= (cast_to_right X Y p)).
{apply target_is_cast_inr. apply H1. }
assert (valid_walk F (cast_to_right_in_walk P Q E F w)).
{apply valid_walk_is_valid_inr. apply H. }
assert (finite_payoff (inr (cast_to_right_in_walk P Q E F w)) 
= finite_payoff (inl (cast_to_right X Y p))).
{apply noninitial_payoff. auto. }
rewrite H6. destruct p.
++ simpl. apply positive2.
++ destruct s.
+++ 
assert ((exists p, w = empty_walk (event_structure_sum P Q E F) p)
\/
forall m p, (position_in_walk _ p w /\ In m p) ->
(exists x, m = inr x)).
{apply sum_equals_inr_implies_inr. auto. }
destruct H7.
++++ destruct H7. subst w. simpl in H0. lia.
++++
assert (exists y : Y, inl x = inr y).
{apply H7 with (p:= inl x :: p). split.
 apply target_in_walk. auto. simpl. left. reflexivity. }
destruct H8. inversion H8.
+++ reflexivity.
++ rewrite H1. destruct p.
+++ reflexivity.
+++ destruct s.
++++ reflexivity.
++++ reflexivity.
Defined. 

Instance sum_positive_game
`(P : PartialOrder X) `(Q : PartialOrder Y)
(E : EventStructure P) (F : EventStructure Q)
(A : AsynchronousArena E) (B : AsynchronousArena F)
(positive1 : finite_payoff (inl (nil : Position E)) = (-1)%Z)
(positive2 : finite_payoff (inl (nil : Position F)) = (-1)%Z)
`(X : Group G)
`(Y : Group H)
`(X' : Group G')
`(Y' : Group H')
(Game : AsynchronousGame E A X Y)
(Game' : AsynchronousGame F B X' Y')
: AsynchronousGame (event_structure_sum P Q E F)
(asynchronous_arena_sum P Q E F A B positive1 positive2)
 (product_group X X') (product_group Y Y') :=
{ action g m h :=
match g, m, h with
| (g, g'), inl m, (h, h') => inl (action g m h)
| (g, g'), inr m, (h, h') => inr (action g' m h')
end
}.
Proof.
- intros. destruct m.
+ simpl. rewrite action_identity. reflexivity.
+ simpl. rewrite action_identity. reflexivity.
- intros. destruct g. destruct g'.
destruct h. destruct h'. simpl. destruct m.
+ rewrite action_compatible. reflexivity.
+ rewrite action_compatible. reflexivity.
- intros. destruct g. destruct h. simpl. destruct m.
+ destruct n.
++ apply coherence_1. simpl in H0. auto.
++ simpl in H0. contradiction H0.
+ destruct n.
++ simpl in H0. contradiction H0.
++ apply coherence_1. simpl in H0. auto.
- intros. destruct g. destruct h. destruct m.
+ simpl. apply coherence_2.
+ simpl. apply coherence_2.
- intros. destruct g. destruct m.
+ simpl. simpl in H0. apply H0. apply reflexive.
+ simpl. simpl in H0. apply H0. apply reflexive.
- intros. destruct h. destruct m.
+ simpl. simpl in H0. apply H0. apply reflexive.
+ simpl. simpl in H0. apply H0. apply reflexive.
Defined.
