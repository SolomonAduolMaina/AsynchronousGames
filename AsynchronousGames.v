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

Fixpoint in_order `(E: EventStructure M) (p : Position E) :=
match p with
| nil => True
| x :: nil => True
| x :: ((y :: xs) as s) => leq x y /\ in_order E s
end.

Definition valid_position `(E: EventStructure M) (p : Position E) :=
forall (x y: M), 
(In x p /\ In y p ->  not (incompatible x y))
 /\ 
(In x p /\ leq y x -> In y p)
(*/\
(NoDup p)
/\
(in_order E p)*).

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
(forall (n : M), In n (ideal m) -> (n = m \/ initial_move E n))
/\
(exists (n : M), In n (ideal m) /\ n <> m).

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
(valid_walk E w /\ w = inl (p) :: nil) -> finite_payoff (inr w) = 0%Z;

noninitial_payoff :
forall (w : Walk E) (p : Position E),
valid_walk E w /\
length w > 1 /\ 
hd_error (rev w) = Some (inl p) /\
In (inl (nil : Position E)) w -> 
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

Fixpoint contains_initial `(E : EventStructure M) (w : Walk E) :=
match w with
| nil => false
| inl(nil) :: _ => true
| inl(_ :: _) :: xs => contains_initial E xs
| inr(_) :: xs =>  contains_initial E xs
end.

Fact contains_initial_makes_sense `(E : EventStructure M) (w : Walk E)
: contains_initial E w = true <-> In (inl(nil)) w.
Proof. 
intros. unfold iff. split.
- intros. induction w.
+ simpl in H. inversion H.
+ simpl in H. simpl. destruct a.
++ destruct p.
+++ left. reflexivity.
+++ right. apply IHw. apply H.
++ right. apply IHw. apply H.
- intros. induction w.
+ simpl in H. contradiction H.
+ simpl. destruct a.
++ destruct p.
+++ reflexivity.
+++ apply IHw. simpl in H. destruct H.
++++ inversion H.
++++ apply H.
++ apply IHw. simpl in H. destruct H.
+++ inversion H.
+++ apply H.
Qed.


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

Fixpoint remove_sum `(M : PartialOrder P)
(E : EventStructure M)
(w : Walk (lift_event_structure M E)) : Walk E :=
match w with
| nil => nil
| inl(p) :: xs => (inl(cast_to_left P Singleton p)) :: (remove_sum M E xs)
| inr(inl(p),b) :: xs => (inr (p,b)):: (remove_sum M E xs)
| _ => nil
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
| inr(xs) => 
if negb (contains_initial (lift_event_structure M E) xs) then 
finite_payoff (inr(remove_sum M E xs)) else 
(match xs with
| inl(nil) :: nil => 0%Z
| xs =>
(match hd_error (rev xs) with
| Some (inl(l)) => g l
| _ => 0%Z
end)
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
- intros. destruct H. rewrite H0. simpl. destruct p0.
+ simpl. reflexivity.
+ simpl. destruct s.
++ apply initial_null with
(w0:=inl (p1 :: cast_to_left P Singleton p0) :: nil)
(p2:=p1 :: cast_to_left P Singleton p0)
. split.
+++ subst w. simpl in H. simpl. unfold valid_position.
unfold valid_position in H. intros. split.
++++ intros. destruct H0. 
assert (In (inl(x)) (inl p1 :: p0)).
{ apply -> cast_to_left_is_boring. simpl. simpl in H0. 
apply H0.
}
assert (In (inl(y)) (inl p1 :: p0)).
{ apply -> cast_to_left_is_boring. simpl. simpl in H1. 
apply H1.
}
assert (not (incompatible (inl x) (inl y))).
{ apply H. split.
+ apply H2.
+ apply H3. }
simpl in H4. apply H4.
++++ intros. (* HAPA *)destruct H0. simpl in H0.
 rewrite cast_to_left_is_boring in H0.
simpl. rewrite cast_to_left_is_boring.
assert (forall x y,
(inl x : P + Singleton) = (inl y : P + Singleton) <-> x = y).
{ intros. unfold iff. split.
+  intros. inversion H2. reflexivity.
+ intros. rewrite H2. reflexivity. }
rewrite <- H2. rewrite <- H2 in H0. 
assert (forall A (x y : A) (l : list A), 
(x = y \/ In y l) <-> In y (x::l)).
{ intros. unfold iff. split.
+ intros. simpl. apply H3.
+ intros. simpl in H3. apply H3. }
rewrite H3. rewrite H3 in H0. apply H with (x:=inl(x)) (y:=inl(y)).
split.
+++++ apply H0.
+++++ simpl. apply H1.
+++ reflexivity.
++ apply initial_null with 
(w0:=inl (cast_to_left P Singleton p0) :: nil)
(p1:=cast_to_left P Singleton p0)
. split.
+++ simpl. subst w. simpl in H. unfold valid_position.
unfold valid_position in H. intros.
split.
++++ intros. destruct H0.
assert (In (inl x) p0 /\ In (inl y) p0).
{ split.
+ apply cast_to_left_is_boring. apply H0. 
+ apply cast_to_left_is_boring. apply H1. }
destruct H2.
assert (In (inl x) (inr s :: p0) /\ In (inl y) (inr s :: p0)).
{ split.
+ simpl. right. apply H2.
+ simpl. right. apply H3.
}
assert (not (incompatible (inl x) (inl y))).
{ apply H. apply H4. }
simpl in H5. apply H5.
++++ intros. destruct H0. apply cast_to_left_is_boring.
apply cast_to_left_is_boring in H0.
assert (In (inl x) (inr s :: p0)).
{ simpl. right. apply H0. }
assert (leq (inl y) (inl x)).
{ simpl. apply H1. }
assert (In (inl y) (inr s :: p0) -> In (inl y) p0).
{ intros. destruct H4. 
+ inversion H4.
+ apply H4. }
apply H4. apply H with (x:=inl x) (y:= inl y).
auto.
+++ reflexivity.
- intros. destruct H. destruct H0. destruct H1.
destruct (contains_initial (lift_event_structure M E) w) eqn:H'.
+ simpl. destruct w.
++ simpl in H0. omega.
++ destruct s.
+++ simpl. destruct p1.
++++ destruct w.
+++++ simpl in H0. omega. 
+++++ simpl in H0. destruct s.
++++++ destruct H.
++++++ simpl in H1. simpl.
rewrite H1. reflexivity.
++++ simpl. simpl in H1. rewrite H1. reflexivity.
+++ simpl. simpl in H1. rewrite H1. reflexivity.
+ simpl. destruct p0.
++
assert (forall A (l : list A) (a : A), hd_error l = Some a -> In a l).
{ intros. destruct l.
+ simpl in H3.  inversion H3. 
+ simpl in H3. inversion H3. simpl. left. reflexivity.  }
assert (In  (inl nil) (rev w)).
{apply H3. apply H1. }
assert (In (inl nil) w).
{ apply in_rev. apply H4. } 
assert (contains_initial (lift_event_structure M E) w = true).
{ apply contains_initial_makes_sense. apply H5. }
rewrite H' in H6. inversion H6.
++ assert (contains_initial (lift_event_structure M E) w = true).
{ apply contains_initial_makes_sense. apply H2. }
rewrite H' in H3. inversion H3.
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
+ destruct w.
++ destruct s.
+++ simpl in H0. omega.
+++ destruct p0. destruct e. contradiction f.
++ destruct s. 
+++ destruct s0.
++++ simpl in H. contradiction H.
++++ destruct p1. destruct e. contradiction f.
+++ destruct p0. destruct e. contradiction f.
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
| (inl p) :: xs => 
(inl (cast_to_left X Y p)) :: (cast_to_left_in_walk P Q E F xs)
| (inr (inl x, b)) :: xs => 
(inr (x, b)) :: (cast_to_left_in_walk P Q E F xs)
| _ => nil
end. 

Fixpoint cast_to_right_in_walk 
`(P : PartialOrder X)
`(Q : PartialOrder Y)
(E : EventStructure P)
(F : EventStructure Q)
(w : Walk (event_structure_sum P Q E F)) : Walk F
:= match w with
| (inl p) :: xs => 
(inl (cast_to_right X Y p)) :: (cast_to_right_in_walk P Q E F xs)
| (inr (inr x, b)) :: xs => 
(inr (x, b)) :: (cast_to_right_in_walk P Q E F xs)
| _ => nil
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
(match w with 
| inl ((inl _) :: _) :: xs => 
finite_payoff (inr (cast_to_left_in_walk P Q E F w))
| inl ((inr _) :: _) :: xs => 
finite_payoff (inr (cast_to_right_in_walk P Q E F w))
| _ => 0%Z
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
- intros. destruct H. subst w. simpl in H. destruct p eqn:H'.
+ reflexivity.
+ unfold valid_position in H. destruct s.
++ simpl.
assert (valid_position E (x :: cast_to_left X Y p0)).
{ unfold valid_position. intros. split.
+ intros.
assert ((In (inl x0) (inl x :: p0) /\ In (inl y) (inl x :: p0) ->
     ~ incompatible (inl x0) (inl y)) /\
    (In (inl x0) (inl x :: p0) /\ leq (inl y) (inl x0) 
-> In (inl y) (inl x :: p0))).
{ apply H. }
destruct H1. simpl incompatible in H1. apply H1. split.
++ apply cast_to_left_is_boring. simpl cast_to_left. destruct H0.
+++ apply H0.
++ destruct H0. apply cast_to_left_is_boring. simpl cast_to_left.
apply H3.
+ intros. 
assert 
((In (inl x0) (inl x :: p0) /\ In (inl y) (inl x :: p0) ->
     ~ incompatible (inl x0) (inl y))
 /\ (In (inl x0) (inl x :: p0) /\ 
leq (inl y) (inl x0) -> In (inl y) (inl x :: p0))).
{ apply H. }
destruct H1. simpl leq in H2.
assert (x :: cast_to_left X Y p0 = cast_to_left X Y (inl x :: p0)).
{ simpl. reflexivity. }
rewrite H3. apply cast_to_left_is_boring. 
apply H2. destruct H0.
rewrite H3 in H0. apply cast_to_left_is_boring in H0. auto.
 }
apply initial_null with (p1:=x :: cast_to_left X Y p0).
simpl. auto.






