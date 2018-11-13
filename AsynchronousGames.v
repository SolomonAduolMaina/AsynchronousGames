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

(*TODO: We need to redefine this *)
Definition InfinitePosition `(E : EventStructure M) := (M -> bool).

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

Fact cast_to_left_monotonic (A B : Type) (l : list (A + B)):
length (cast_to_left A B l) < length l \/ 
length (cast_to_left A B l) = length l.
Proof.
intros.  induction l.
+ simpl. lia.
+ simpl. destruct a.
++ simpl. lia.
++ lia.
Qed.

Fact cast_to_left_iso (A B : Type) (l : list (A + B)):
(length (cast_to_left A B l) = length l ->
forall x, In x l -> (exists y, x = inl y))
/\
(length (cast_to_left A B l) < length l ->
exists x, In (inr x) l).
Proof. induction l.
+ split.
++ simpl. intros. contradiction H0.
++ simpl. intros. lia.
+ destruct IHl. split.
++ intros. destruct a.
+++ simpl in H1. 
assert (length (cast_to_left A B l) = length l).
{ lia. }
destruct H2. 
++++ refine (ex_intro _ a _). auto.
++++ apply H. apply H3. apply H2.
+++ simpl in H1.
assert (length (cast_to_left A B l) < length l \/ 
length (cast_to_left A B l) = length l).
{ apply cast_to_left_monotonic. }
lia.
++ intros. destruct a.
+++ simpl in H1.
assert (length (cast_to_left A B l) < length l).
{ lia. } 
simpl. 
assert (exists x : B, In (inr x) l).
{ apply H0. apply H2. }
destruct H3. refine (ex_intro _ x _). auto.
+++ refine (ex_intro _ b _). simpl. left. auto.
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
infinite_payoff f :=
let g m := f (inl m) in infinite_payoff g;
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

Fixpoint cast_to_right_position_in_walk 
`(P : PartialOrder X)
`(Q : PartialOrder Y)
(E : EventStructure P)
(F : EventStructure Q)
(w : Walk (event_structure_sum P Q E F)) : Walk F
:= match w with
| empty_walk _ p => empty_walk _ (cast_to_right X Y p)
| non_empty_walk _ p (inr m, b) w
=> non_empty_walk _ (cast_to_right X Y p) (m, b) 
(cast_to_right_position_in_walk P Q E F w)
| non_empty_walk _ p (inl m, b) w
=> cast_to_right_position_in_walk P Q E F w
end.

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

Fact cast_to_left_in_walk_iso
`(P : PartialOrder X)
`(Q : PartialOrder Y)
(E : EventStructure P)
(F : EventStructure Q)
: forall (w : Walk (event_structure_sum P Q E F)),
(length_walk E (cast_to_left_in_walk P Q E F w) =
length_walk (event_structure_sum P Q E F) w
->
(forall m ep, move_in_walk _ (m,ep) w -> exists y, m = inl y))
/\
(length_walk E (cast_to_left_in_walk P Q E F w) <
length_walk (event_structure_sum P Q E F) w
->
(exists y ep, move_in_walk _ (inr y,ep) w)).
Proof.
intros. induction w. split.
+ intros. simpl in H0. contradiction H0.
+ intros. simpl in H. lia.
+ destruct IHw. simpl. destruct p0. split.
++ intros. destruct s.
+++ simpl in H1. 
assert (length_walk E (cast_to_left_in_walk P Q E F w)
=
length_walk (event_structure_sum P Q E F) w).
{ lia. }
assert (forall (m : X + Y) (ep : bool),
    move_in_walk (event_structure_sum P Q E F) (m, ep) w ->
    exists y : X, m = inl y).
{ apply H. apply H3. }
destruct H2.
++++ inversion H2. refine (ex_intro _ x _).
reflexivity.
++++ apply H4 with (ep:=ep). apply H2.
+++
assert (length_walk E (cast_to_left_in_walk P Q E F w) <
length_walk (event_structure_sum P Q E F) w
\/
length_walk E (cast_to_left_in_walk P Q E F w) =
length_walk (event_structure_sum P Q E F) w).
{ apply cast_to_left_in_walk_monotonic. }
lia.
++ destruct s.
+++ intros. simpl in H1.
assert 
(length_walk E (cast_to_left_in_walk P Q E F w) <
     length_walk (event_structure_sum P Q E F) w).
{ lia. }
assert (exists (y : Y) (ep : bool),
       move_in_walk (event_structure_sum P Q E F) 
         (inr y, ep) w).
{apply H0.  apply H2. }
destruct H3. destruct H3.
refine (ex_intro _ x0 _).
refine (ex_intro _ x1 _).
right. apply H3.
+++ intros.
refine (ex_intro _ y _).
refine (ex_intro _ b _).
left. reflexivity.
Qed.

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
(length_walk _ (cast_to_right_position_in_walk P Q E F w)) then
finite_payoff (inr (cast_to_right_position_in_walk P Q E F w)) else
(match (target_walk _ w) with
| nil => (-1)%Z
| ((inl _ :: _) as pos) => 
 finite_payoff (inl (cast_to_left X Y pos))
| ((inr _ :: _) as pos) => 
 finite_payoff (inl (cast_to_right X Y pos))
end)
end;
infinite_payoff f :=
let g m := f (inl m) in
let h m := f (inr m) in
match infinite_payoff g, infinite_payoff h with
| plus_infinity, plus_infinity => plus_infinity
| minus_infinity, minus_infinity => minus_infinity
| _, _ => plus_infinity
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
assert (Incomp : forall p x y, 
valid_position (event_structure_sum P Q E F) p ->
~ (In (inl x) p /\ In (inr y) p)).
{ intros. unfold not. intros. destruct H0.
 unfold valid_position in H. 
assert (~ incompatible (inl x) (inr y)).
{ apply H.  auto. }
simpl in H2. auto.
}

assert (forall p, 
valid_position (event_structure_sum P Q E F)p 
-> valid_position E (cast_to_left X Y p)).
{ intros. unfold valid_position in H. unfold valid_position.
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
}

intros. destruct H0. destruct H1. destruct H2.

assert (forall w,
valid_walk (event_structure_sum P Q E F) w /\
length_walk (event_structure_sum P Q E F) w =?
  length_walk E (cast_to_left_in_walk P Q E F w) = true
-> (forall m ep, move_in_walk _ (m, ep) w -> exists n, m = inl n
)).
{ intros. destruct H4. generalize dependent m. induction w0.
+ intros. simpl in H5. contradiction H5.
+ simpl. intros. destruct p1. destruct H5.
++ destruct s.
+++ refine (ex_intro _ x _). inversion H5. reflexivity.
+++ inversion H5.
++++
assert ((length_walk E
        (cast_to_left_in_walk P Q E F
           (non_empty_walk (event_structure_sum P Q E F) p0
              (inr y, b) w0))
=? length_walk E (cast_to_left_in_walk P Q E F w0)) = true
).
{ simpl.  apply beq_nat_iff_equal. reflexivity. }
subst m. subst b. apply beq_nat_iff_equal in H6.
apply beq_nat_iff_equal in H7. rewrite H7 in H6.
apply IHw0.
+++++ destruct H4.
++++++ inversion H4.
++++++ inversion H4. subst p0. subst m. subst ep.
destruct H8. destruct H9. apply H9.
++++++ simpl in H7. simpl in H6.
assert (length_walk E (cast_to_left_in_walk P Q E F w0) <
length_walk (event_structure_sum P Q E F) w0
\/
length_walk E (cast_to_left_in_walk P Q E F w0) =
length_walk (event_structure_sum P Q E F) w0).
{ apply cast_to_left_in_walk_monotonic. }
destruct H9.
+++++++ lia.
+++++++ lia.
+++++ apply beq_nat_iff_equal. simpl in H6.
assert (length_walk E (cast_to_left_in_walk P Q E F w0) <
length_walk (event_structure_sum P Q E F) w0
\/
length_walk E (cast_to_left_in_walk P Q E F w0) =
length_walk (event_structure_sum P Q E F) w0).
{ apply cast_to_left_in_walk_monotonic. }
destruct H8.
+++++++ lia.
+++++++ lia.
+++++ simpl in H6.
assert (length_walk E (cast_to_left_in_walk P Q E F w0) <
length_walk (event_structure_sum P Q E F) w0
\/
length_walk E (cast_to_left_in_walk P Q E F w0) =
length_walk (event_structure_sum P Q E F) w0).
{ apply cast_to_left_in_walk_monotonic. }
destruct H8.
+++++++ lia.
+++++++ lia.
++ apply beq_nat_iff_equal in H6. simpl in H6.
destruct s.
+++ simpl in H6.
assert (length_walk (event_structure_sum P Q E F) w0 =
    length_walk E (cast_to_left_in_walk P Q E F w0)).
{ lia. }
inversion H4.
++++ inversion H8.
++++ inversion H8. subst p1. subst m0. subst b.
subst w0. apply IHw0. apply valid_empty_walk
with (p1:=p2).
+++++ reflexivity.
+++++ destruct H9. destruct H10.
inversion H10.
++++++ inversion H12. subst p2. apply H13.
++++++ inversion H12.
++++++ inversion H12.
+++++ apply beq_nat_iff_equal. simpl. reflexivity.
+++++ simpl. simpl in H5. contradiction H5.
++++ inversion H8. subst p0. subst m0. subst b. subst w0.
apply IHw0.
+++++ destruct H9. destruct H10. apply H10.
+++++ apply beq_nat_iff_equal. apply H7.
+++++ apply H5.
+++
assert (length_walk E (cast_to_left_in_walk P Q E F w0) <
length_walk (event_structure_sum P Q E F) w0
\/
length_walk E (cast_to_left_in_walk P Q E F w0) =
length_walk (event_structure_sum P Q E F) w0).
{ apply cast_to_left_in_walk_monotonic. }
destruct H7.
++++ lia.
++++ lia.
}
assert
(forall w : Walk (event_structure_sum P Q E F),
     valid_walk (event_structure_sum P Q E F) w ->
valid_walk _ (cast_to_left_in_walk P Q E F w)).
{ intros. induction w0.
+ simpl. apply valid_empty_walk with (p1:=(cast_to_left X Y p0)).
++ reflexivity.
++ destruct H5.
+++ inversion H5. apply H. apply H6.
+++ inversion H5.
+++ inversion H5.
+ destruct H5.
++ inversion H5.
++ inversion H5. subst p0. subst p1. subst w0. simpl.
destruct m. apply valid_one_move_walk
with (m:=x) (ep0:=ep) (p1:=(cast_to_left X Y p2))
(p4:=(cast_to_left X Y p3)).
+++ reflexivity.
+++ split.
++++ destruct H6. apply H. apply H6.
++++ split.
+++++ destruct H6. destruct H7.
++++++ destruct H7.
+++++++ apply valid_empty_walk with (p1:=(cast_to_left X Y p3)).
++++++++ reflexivity.
++++++++ inversion H7. apply H. apply H9.
+++++++ inversion H7.
+++++++ inversion H7.
+++++ destruct ep.
++++++ left. destruct H6. destruct H7. destruct H8.
+++++++ split.
++++++++ reflexivity.
++++++++ unfold move_from. destruct H8.
unfold move_from in H9.
+++++++++ split.
++++++++++ destruct H9. intros. 
rewrite cast_to_left_is_boring.
rewrite cast_to_left_is_boring in H11. apply H9. apply H11.
++++++++++ split.
+++++++++++ destruct H9. 
intros. destruct H11. 
rewrite cast_to_left_is_boring in H11.
rewrite cast_to_left_is_boring in H12.
assert ((inl n : X + Y) = inl x).
{apply H10. auto. }
inversion H13. reflexivity.
+++++++++++ intros. destruct H9. 
rewrite cast_to_left_is_boring.
rewrite cast_to_left_is_boring.
assert ((inl n : X + Y) = inl x).
{rewrite H10. auto. }
apply H11. apply H12.
+++++++ destruct H8. inversion H8.
++++++ right. destruct H6. destruct H7. destruct H8.
+++++++ destruct H8. inversion H8.
+++++++ split.
++++++++ reflexivity.
++++++++ destruct H8. unfold move_from.
unfold move_from in H9. split.
+++++++++ destruct H9. intros.
rewrite cast_to_left_is_boring.
rewrite cast_to_left_is_boring in H11. apply H9.
apply H11.
+++++++++ split.
++++++++++ destruct H9. intros.
rewrite cast_to_left_is_boring in H11.
rewrite cast_to_left_is_boring in H11.
assert ((inl n : X + Y) = inl x).
{ apply H10. auto. } inversion H12. reflexivity.
++++++++++ destruct H9. intros.
rewrite cast_to_left_is_boring. 
rewrite cast_to_left_is_boring.
apply H10. rewrite H11. auto.
+++ apply valid_empty_walk with (p0:=(cast_to_left X Y p3)).
++++ reflexivity.
++++ destruct H6. destruct H7. destruct H7.
+++++ inversion H7. apply H. apply H9.
+++++ inversion H7.
+++++ inversion H7.
++ inversion H5. subst p0. subst p1. subst w0.
simpl. destruct m.
+++ destruct m'. simpl in IHw0. destruct s. 
++++ apply valid_non_empty_walk
with (p1:=(cast_to_left X Y p2)) (m:=x)
(ep0:=ep) (p4:=(cast_to_left X Y p3)) (m':=(x0, b))
(w'0:=(cast_to_left_in_walk P Q E F w')).
+++++ reflexivity.
+++++ split.
++++++ destruct H6. apply H. apply H6.
++++++ split.
+++++++ destruct H6. destruct H7. simpl in IHw0.
apply IHw0. apply H7.
+++++++ destruct H6. destruct H7. destruct H8.
++++++++ left. split.
+++++++++ destruct H8. apply H8.
+++++++++ destruct H8. unfold move_from. unfold
move_from in H9. split.
++++++++++ destruct H9.
intros. apply cast_to_left_is_boring in H11.
 apply cast_to_left_is_boring. apply H9. apply H11.
++++++++++ split.
+++++++++++ destruct H9. intros.
 rewrite cast_to_left_is_boring in H11. 
 rewrite cast_to_left_is_boring in H11.
assert ((inl n : X + Y) = inl x).
{ apply H10. auto. } inversion H12. reflexivity.
+++++++++++ intros.
 rewrite cast_to_left_is_boring.
 rewrite cast_to_left_is_boring.
apply H9. rewrite H10. reflexivity.
++++++++ destruct H8. right. split.
+++++++++ apply H8.
+++++++++ unfold move_from. unfold move_from in H9. split.
++++++++++ destruct H9. intros.
apply cast_to_left_is_boring in H11. 
apply cast_to_left_is_boring. apply H9. apply H11.
++++++++++ split.
+++++++++++ destruct H9. intros.
rewrite cast_to_left_is_boring in H11.
rewrite cast_to_left_is_boring in H11.
assert ((inl n : X + Y) = inl x).
{ apply H10. auto. } inversion H12. reflexivity.
+++++++++++ intros.
 rewrite cast_to_left_is_boring.
 rewrite cast_to_left_is_boring. apply H9. rewrite H10.
reflexivity.
++++ simpl in IHw0.
assert (valid_walk E (cast_to_left_in_walk P Q E F w')).
{ apply IHw0. destruct H6. destruct H7. apply H7. }
destruct w'.
+++++ simpl. destruct H6. destruct H8.
destruct H8.
++++++ inversion H8.
++++++ inversion H8. subst p3. subst m. subst b. subst p4.
admit. (* Hopefully Not hard *)
++++++ inversion H8.
+++++ simpl. destruct p1. simpl in H7. destruct s.
++++++ apply valid_non_empty_walk
with (p1:=(cast_to_left X Y p2)) (m:=x) (ep0:=ep) (p4:=(cast_to_left X Y p0))
(m':=(x0,b0)) (w'0:=(cast_to_left_in_walk P Q E F w')).
+++++++ reflexivity.
+++++++ split.
++++++++ destruct H6. apply H. apply H6.
++++++++ split.
+++++++++ destruct H6. destruct H8. apply H7.
+++++++++ destruct H6. destruct H8. destruct H9. left.
destruct H9. split.
++++++++++ apply H9.
++++++++++
assert (p3 = nil).
{ destruct p3. 
+ reflexivity. 
+ destruct H8.
++ inversion H8.
++ inversion H8.
++ inversion H8.
subst p1. subst m. subst b. subst p4. subst m'. subst w'0.
destruct s. destruct H11. destruct H12. destruct H13.
+++ destruct H13. unfold move_from in H14.
assert (In (inl x1) p0).
{ destruct H14. apply H14. simpl. left. reflexivity. }
destruct H14.
assert (~ In (inr y) (inl x1 :: p3) /\ In (inr y) p0).
{ apply H16. reflexivity. }
assert (~ (In (inl x1) p0 /\ In (inr y) p0)).
{apply Incomp. destruct H12.
+ inversion H12.
+ inversion H12. subst p1. apply H18.
+ inversion H12. subst p1. apply H18.
} contradiction H18. destruct H17. split.
++++ apply H15.
++++ apply H19. 
+++ destruct H13. unfold move_from in H14.
assert (In (inl x1) (inl x1 :: p3)).
{ simpl. left. reflexivity. }
assert (~ (In (inl x1) (inl x1 :: p3) /\ In (inr y) (inl x1 :: p3))).
{apply Incomp. apply H11.
}
assert (In (inl x1) (inl x1 :: p3) /\ In (inr y) (inl x1 :: p3)).
{ split.
+ auto. 
+ apply H14. reflexivity. }
contradiction H16. 
+++ unfold move_from in H10.
assert (~ (In (inl x) (inr y0 :: p3) /\ In (inr y0) (inr y0 :: p3))).
{apply Incomp. apply H11. }
assert ((In (inl x) (inr y0 :: p3) /\ In (inr y0) (inr y0 :: p3))).
{ split.
+ destruct H10. apply H13. auto.
+ simpl. left. reflexivity. }
contradiction H12.
 } subst p3. unfold move_from in H10. destruct H10.
assert (~ In (inl x : X + Y) p2 /\ In (inl x : X + Y) nil).
{ apply H11.  reflexivity. }
destruct H12. simpl in H13. contradiction H13.
++++++++++
assert (p3 = nil).
{ destruct p3. 
+ reflexivity. 
+ destruct H8.
++ inversion H8.
++ inversion H8.
++ inversion H8.
subst p1. subst m. subst b. subst p4. subst m'. subst w'0.
destruct s. destruct H10. destruct H11. destruct H12.
+++ destruct H12. unfold move_from in H13.
assert (~ In (inr y) (inl x1 :: p3) /\ In (inr y) p0).
{ apply H13.  reflexivity. }
assert (In (inl x1) p0).
{ destruct H13. apply H13. simpl. left. reflexivity. }
destruct H14.
assert (~ (In (inl x1) p0 /\ In (inr y) p0)).
{ apply Incomp. destruct H11.
+ inversion H11.
+ inversion H11. subst p1. destruct H17. auto.
+ inversion H11. subst p1. destruct H17. auto.
} contradiction H17. auto.
+++ destruct H12. unfold move_from in H13.
assert (~ In (inr y) p0 /\ In (inr y) (inl x1 :: p3)).
{ apply H13.  reflexivity. }
destruct H14.
assert (~ (In (inl x1) (inl x1 :: p3) /\ In (inr y) (inl x1 :: p3))).
{ apply Incomp. auto. } contradiction H16. split.
++++  simpl. left. reflexivity.
++++ auto.
+++ destruct H9. unfold move_from in H11.
assert (In (inr y0) p2).
{ destruct H11. apply H11. simpl. left. reflexivity. }
assert (In (inl x) p2).
{ apply H11.  reflexivity. }
assert (~ (In (inl x) p2 /\ In (inr y0) p2)).
{ apply Incomp. auto. } contradiction H14. split.
++++ auto.
++++ auto.
} subst p3. right.
destruct H9. split.
+++++++++++ apply H9.
+++++++++++
assert (forall m, In m p0 -> m = inr y).
{intros. destruct H8. 
+ inversion H8. 
+ inversion H8. 
+ inversion H8. subst p1. subst m0. subst b. subst p3. subst m'.
subst w'0. destruct H12. destruct H13. destruct H14.
++ destruct H14. unfold move_from in H15.
apply H15.  split.
+++ simpl. auto.
+++ apply H11.
++ destruct H14. unfold move_from in H15.
assert (~ In (inr y) p0 /\ In (inr y : X + Y) nil).
{ apply H15.  reflexivity. }
destruct H16. simpl in H17. contradiction H17.
}
assert (forall m, In m p2 -> m = inl x).
{ intros. unfold move_from in H10. apply H10. split.
+ simpl. auto.
+ apply H12.
}
assert (forall p0, (forall m : X + Y, In m p0 -> m = inr y) ->
cast_to_left X Y p0 = nil).
{ intros. induction p1. 
+ simpl. reflexivity.
+ destruct a.
++ assert (inl x1 = inr y).
{ apply H13.  simpl. left. reflexivity. }
inversion H14.
++ simpl. apply IHp1. intros. apply H13. simpl. right. apply H14.
 }
assert ( cast_to_left X Y p0 = nil).
{apply H13.  apply H11. } rewrite H14.
assert (forall p2, move_from (event_structure_sum P Q E F)
        (inl x) nil p2 ->
(forall m, In m (cast_to_left X Y p2) -> m = x) ).
{intros. induction p1.
+ simpl in H16. contradiction H16.
+ simpl in H16. destruct a.
++ simpl in H16. destruct H16.
+++ subst x1. unfold move_from in H15.
assert (inl m = (inl x : X + Y)).
{apply H15. split.
+ simpl. auto.
+ simpl. left. reflexivity.
 }
inversion H16. reflexivity.
+++ apply IHp1. destruct p1.
++++ simpl in H16. contradiction H16.
++++ unfold move_from. split.
+++++ intros. contradiction H17.
+++++ intros. unfold iff. split.
++++++ intros. unfold move_from in H15.
apply H15. split.
+++++++ simpl. auto.
+++++++ simpl. simpl in H17. right. apply H17.
++++++ intros. unfold move_from in H15.
subst n.
assert (s = inl x).
{apply H15. split.
+ simpl. auto.
+ simpl. right. left. reflexivity.
} subst s. simpl. auto.
++++ apply H16.
++ apply IHp1. destruct p1.
+++ simpl in H16. contradiction H16.
+++ unfold move_from in H15.
assert (inr y0 = (inl x : X + Y)).
{apply H15. split.
+ simpl. auto.
+ simpl. left. reflexivity.
} inversion H17.
+++ apply H16.
}
assert (forall m : X, In m (cast_to_left X Y p2) -> m = x).
{ apply H15. apply H10. }
unfold move_from. split.
++++++++++++ intros. contradiction H17.
++++++++++++ intros. unfold iff. split.
+++++++++++++ intros. apply H16. apply H17.
+++++++++++++ intros. split.
++++++++++++++ simpl. auto.
++++++++++++++ unfold move_from in H10.
assert (In (inl x) p2).
{apply H10.  reflexivity. }
apply cast_to_left_is_boring. subst n. apply H18.
++++++ simpl in IHw0.

destruct (length_walk (event_structure_sum P Q E F) w =?
  length_walk E (cast_to_left_in_walk P Q E F w)) eqn:H'.




