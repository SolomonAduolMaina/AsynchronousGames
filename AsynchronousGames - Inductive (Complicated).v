Require Import Lia.
Require Import List.
Require Import Coq.Program.Wf.
Require Import ZArith.
Require Import Init.Nat.
Require Import Logic.Eqdep.

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
w = (non_empty_walk E p2 (m, ep) (empty_walk E p1)) ->
(valid_position E p2) /\ (valid_position E p1) /\
((ep = true /\ move_from E m p1 p2) \/ (ep = false /\ move_from E m p2 p1))
-> valid_walk E w
| valid_non_empty_walk :
forall p1 m ep p2 m' w',
w = (non_empty_walk E p2 (m, ep) (non_empty_walk E p1 m' w')) ->
(valid_position E p2) /\ (valid_walk E (non_empty_walk E p1 m' w')) /\
((ep = true /\ move_from E m p1 p2) \/ (ep = false /\ move_from E m p2 p1))
-> valid_walk E w.

Fixpoint length_walk `(E: EventStructure M) (w : Walk E) :=
match w with
| empty_walk _ _ => 1
| non_empty_walk _ _ _ w => 2 + (length_walk E w)
end.

Fixpoint target_walk `(E: EventStructure M) (w : Walk E) :=
match w with
| empty_walk _ p => p
| non_empty_walk _ p _ _ => p
end.

Fixpoint source_walk `(E: EventStructure M) (w : Walk E) :=
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
Proof. intros. destruct w.
+ simpl. simpl in H. auto.
+ simpl in H. simpl. left. auto.
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

Inductive Singleton : Type :=
| new : Singleton.

Instance lift_partial_order `(M : PartialOrder P) :
PartialOrder (sum Singleton P) :=
{ leq m n := match m,n with
| inr(m), inr(n) => leq m n
| inl(m), _ => True
| _, _ => False
end
}.
Proof. 
- intros. destruct x.
+ auto.
+ apply reflexive.
- intros. destruct x.
+ destruct y.
++ destruct s. destruct s0. reflexivity.
++ destruct H. contradiction H0.
+ destruct y.
++ destruct H. contradiction H.
++ apply anti_symmetric in H. rewrite H. reflexivity.
- intros. destruct x.
+ destruct y.
++ destruct z.
+++ auto.
+++ auto.
++ auto.
+ destruct y.
++ destruct z.
+++ destruct H. contradiction H.
+++ destruct H. contradiction H.
++ destruct z.
+++ destruct H. contradiction H0.
+++ apply transitive in H. apply H.
Defined.

Inductive leq_sum `(A : PartialOrder P)
`(E : EventStructure M)
: sigT (fun (m : M) => sig 
(fun (x : {m : M | initial_move E m} ) => let (x, y) := x in leq m x))
 -> sigT (fun (m : M) => sig 
(fun (x : {m : M | initial_move E m} ) => let (x, y) := x in leq m x))
 -> Prop :=
| leq_sum_proof : forall i a b x y, leq (proj1_sig a) (proj1_sig b) ->
leq_sum _ _ (existT _ i (exist _ a x)) (existT _ i (exist _ b y)).

Instance canonical_form `(A : PartialOrder P)
`(E : EventStructure M)
: PartialOrder
(sigT (fun (m : M) => sig 
(fun (x : {m : M | initial_move E m} ) => let (x, y) := x in leq m x)))
:= {leq x y := leq_sum A E x y}.
Proof.
- intros. destruct x. destruct s. apply leq_sum_proof. apply reflexive.
- intros. destruct x. destruct y. destruct s. destruct s0. destruct H.
inversion H. subst. destruct x1. destruct x2.
inversion H0. subst. simpl in *.
assert (x1 = x).
{apply anti_symmetric. auto. }
subst. Admitted.


Class CanonicalRepresentation 
(Index : Type)
(f : Index -> Type)
(g : Index -> Type)
(h : Index -> Type)
(payoffs : Index -> nat) :=
{
posets : forall (i : Index), PartialOrder (sum Singleton (f i));
structures : forall (i : Index), EventStructure (posets i);
arenas : forall (i : Index), AsynchronousArena (structures i);
left_groups : forall (i : Index), Group (g i);
right_groups : forall (i : Index), Group (h i);
games : forall (i : Index), 
AsynchronousGame 
(structures i) (arenas i) (left_groups i) (right_groups i);

}.

Instance partial_order_tensor
`(P : PartialOrder (sum Singleton X)) 
`(Q : PartialOrder (sum Singleton Y)) :
PartialOrder (Singleton + (X + Y)) := {
leq m n :=
match m, n with
| inl _, _ => True
| inr (inl m), inr (inl n) => leq (inr m) (inr n)
| inr (inr m), inr (inr n) => leq (inr m) (inr n)
| _, _ => False
end
}.
Proof.
- intros. destruct x.
+ auto.
+ destruct s.
++ apply reflexive.
++ apply reflexive.
- intros. destruct x.
+ destruct y.
++ destruct s. destruct s0. reflexivity.
++ destruct s0.
+++ destruct H. contradiction H0.
+++ destruct H. contradiction H0.
+ destruct s.
++ destruct y.
+++ destruct H. contradiction H.
+++ destruct s.
++++ apply anti_symmetric in H. inversion H. reflexivity.
++++ destruct H. contradiction H.
++ destruct y.
+++ destruct H. contradiction H.
+++ destruct s.
++++ destruct H. contradiction H.
++++ apply anti_symmetric in H. inversion H. reflexivity.
- intros. destruct x.
+ auto.
+ destruct s.
++ destruct y.
+++ destruct H. contradiction H.
+++ destruct z.
++++ destruct s.
+++++ destruct H. contradiction H0.
+++++ destruct H. contradiction H.
++++ destruct s.
+++++ destruct s0.
++++++ apply transitive in H. auto.
++++++ destruct H. contradiction H0.
+++++ destruct s0.
++++++ destruct H. contradiction H.
++++++ destruct H. contradiction H.
++ destruct z.
+++ destruct y.
++++ destruct H. contradiction H.
++++ destruct s0.
+++++ destruct H. contradiction H.
+++++ destruct H. contradiction H0.
+++ destruct s.
++++ destruct y.
+++++ destruct H. contradiction H.
+++++ destruct s.
++++++ destruct H. contradiction H.
++++++ destruct H. contradiction H0.
++++ destruct y.
+++++ destruct H. contradiction H.
+++++ destruct s.
++++++ destruct H. contradiction H.
++++++ apply transitive in H. auto.
Defined.

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

Instance event_structure_tensor
`(P : PartialOrder (sum Singleton X))
`(Q : PartialOrder (sum Singleton Y))
(E : EventStructure P) (F : EventStructure Q) :
EventStructure (partial_order_tensor P Q) := 
{ incompatible m n := 
match m,n with
| inr (inl m), inr (inl n) => incompatible (inr m) (inr n)
| inr (inr m), inr (inr n) => incompatible (inr m) (inr n)
| _, _ => False
end;
ideal m := match m with
| inl m => (inl m) :: nil
| inr (inl m) => (inl new) ::
(add_inr Singleton (X + Y)
(add_inl X Y (cast_to_right Singleton X (ideal (inr m)))))
| inr (inr m) => (inl new) ::
(add_inr Singleton (X + Y)
(add_inr X Y (cast_to_right Singleton Y (ideal (inr m)))))
end
}.
Proof.
- intros. destruct x.
+ destruct y.
++ contradiction H.
++ contradiction H.
+ destruct y.
++ destruct s.
+++ contradiction H.
+++ contradiction H.
++ destruct s0.
+++ destruct s.
++++ apply symmetric. apply H.
++++ contradiction H.
+++ destruct s.
++++ contradiction H.
++++ apply symmetric. apply H.
- intros. unfold not. intros.
+ destruct x.
++ contradiction H.
++ destruct s.
+++ apply irreflexive in H. contradiction H.
+++ apply irreflexive in H. contradiction H.
- intros. unfold iff. split.
+ intros. destruct x.
++ destruct y.
+++ destruct s. destruct s0. left. reflexivity.
+++ simpl in H. destruct s0. 
++++ contradiction H.
++++ contradiction H.
++ destruct y.
+++ destruct s0. destruct s.
++++ left. reflexivity.
++++ left. reflexivity.
+++ destruct s.
++++ destruct s0.
+++++ simpl in H. apply in_cons. apply add_inr_does_nothing.
apply add_inl_does_nothing. apply cast_to_right_is_boring.
apply ideal_finite. auto.
+++++ simpl in H. contradiction H.
++++ destruct s0.
+++++ simpl in H. contradiction H.
+++++ simpl in H. apply in_cons. apply add_inr_does_nothing.
apply add_inr_does_nothing. apply cast_to_right_is_boring.
apply ideal_finite. auto.
+ intros. destruct x.
++ destruct y.
+++ destruct s. destruct s0. simpl. auto.
+++ destruct H.
++++ inversion H.
++++ contradiction H.
++ destruct s.
+++ destruct y.
++++ destruct s. simpl. auto.
++++ destruct s.
+++++ simpl. apply ideal_finite. destruct H.
++++++ inversion H.
++++++ apply add_inr_does_nothing in H.
apply add_inl_does_nothing in H.
apply cast_to_right_is_boring in H. apply H.
+++++ destruct H.
++++++ inversion H.
++++++ apply add_inr_does_nothing in H.
apply inr_not_in_add_inl in H. contradiction H.
+++ destruct y.
++++ simpl. auto.
++++ destruct s.
+++++ destruct H.
++++++ inversion H.
++++++ apply add_inr_does_nothing in H.
apply inl_not_in_add_inr in H. contradiction H.
+++++ simpl. destruct H.
++++++ inversion H.
++++++ apply add_inr_does_nothing in H.
apply add_inr_does_nothing in H.
apply cast_to_right_is_boring in H. apply ideal_finite. auto.
- intros. destruct x.
+ destruct H. contradiction H.
+ destruct s. 
++ destruct z.
+++ destruct y.
++++ destruct H. contradiction H.
++++ destruct s0.
+++++ destruct H. simpl in H0. contradiction H0.
+++++ destruct H. contradiction H.
+++ destruct s.
++++ destruct y.
+++++ destruct H. contradiction H.
+++++ destruct s.
++++++ simpl in H. apply incompatible_closed with (y:=inr x1).
auto.
++++++ destruct H. contradiction H.
++++ destruct y.
+++++ destruct H. contradiction H.
+++++ destruct s.
++++++ simpl in H. destruct H. contradiction H0.
++++++ destruct H. contradiction H.
++ destruct z.
+++ destruct y.
++++ destruct H. contradiction H.
++++ destruct s0.
+++++ destruct H. contradiction H.
+++++ simpl in H. destruct H. contradiction H0.
+++ destruct s.
++++ destruct y.
+++++ destruct H. contradiction H.
+++++ destruct s.
++++++ destruct H. contradiction H.
++++++ simpl in H. destruct H. contradiction H0.
++++ destruct y.
+++++ destruct H. contradiction H.
+++++ destruct s.
++++++ destruct H. contradiction H.
++++++ simpl in H. apply incompatible_closed with (y2:=inr y).
auto.
Defined.

Fixpoint cast_to_left_in_walk_tensor
`(P : PartialOrder (sum Singleton X))
`(Q : PartialOrder (sum Singleton Y))
(E : EventStructure P) (F : EventStructure Q)
(w : Walk (event_structure_tensor P Q E F)) : Walk E
:= match w with
| empty_walk _ nil => empty_walk _ nil
| empty_walk _ p => 
empty_walk _ (inl new :: (add_inr Singleton X
(cast_to_left X Y (cast_to_right Singleton (X+Y) p ))))
| non_empty_walk _ p (inr (inl m), b) w =>
non_empty_walk _ (inl new :: (add_inr Singleton X
(cast_to_left X Y (cast_to_right Singleton (X+Y) p ))))
(inr m, b) (cast_to_left_in_walk_tensor P Q E F w)
| non_empty_walk _ p _ w
=> cast_to_left_in_walk_tensor P Q E F w
end. 

Fixpoint cast_to_right_in_walk_tensor
`(P : PartialOrder (sum Singleton X))
`(Q : PartialOrder (sum Singleton Y))
(E : EventStructure P) (F : EventStructure Q)
(w : Walk (event_structure_tensor P Q E F)) : Walk F
:= match w with
| empty_walk _ nil => empty_walk _ nil
| empty_walk _ p => 
empty_walk _ (inl new :: (add_inr Singleton Y
(cast_to_right X Y (cast_to_right Singleton (X+Y) p ))))
| non_empty_walk _ p (inr (inr m), b) w =>
non_empty_walk _ (inl new :: (add_inr Singleton Y
(cast_to_right X Y (cast_to_right Singleton (X+Y) p ))))
(inr m, b) (cast_to_right_in_walk_tensor P Q E F w)
| non_empty_walk _ p _ w
=> cast_to_right_in_walk_tensor P Q E F w
end. 

Fixpoint cast_infinite_position_to_inl_tensor
`(P : PartialOrder (sum Singleton X))
`(Q : PartialOrder (sum Singleton Y))
(E : EventStructure P) (F : EventStructure Q)
(p : InfinitePosition (event_structure_tensor P Q E F)) :
InfinitePosition E :=
match p with
| stream _ (inl m) f =>
stream _ (inl m) (fun _ => 
cast_infinite_position_to_inl_tensor _ _ _ _ (f tt))
| stream _ (inr (inl m)) f => 
stream _ (inr m) (fun _ =>
cast_infinite_position_to_inl_tensor _ _ _ _ (f tt))
| stream _ (inr (inr m)) f => 
cast_infinite_position_to_inl_tensor _ _ _ _ (f tt)
end. 

Fixpoint cast_infinite_position_to_inr_tensor
`(P : PartialOrder (sum Singleton X))
`(Q : PartialOrder (sum Singleton Y))
(E : EventStructure P) (F : EventStructure Q)
(p : InfinitePosition (event_structure_tensor P Q E F)) :
InfinitePosition F :=
match p with
| stream _ (inl m) f =>
stream _ (inl m) (fun _ => 
cast_infinite_position_to_inr_tensor _ _ _ _ (f tt))
| stream _ (inr (inr m)) f => 
stream _ (inr m) (fun _ =>
cast_infinite_position_to_inr_tensor _ _ _ _ (f tt))
| stream _ (inr (inl m)) f => 
cast_infinite_position_to_inr_tensor _ _ _ _ (f tt)
end.

Definition tensor (p q : Z) :=
if Z.ltb p 0 then 
(if Z.ltb q 0 then Z.add p q else p)
else
(if Z.ltb q 0 then q else Z.add p q).

Fact initial_move_is_new_lift
`(P : PartialOrder X)
(Q : PartialOrder (sum Singleton X))
(urgh : Q = lift_partial_order P)
(E : EventStructure Q):
forall m, initial_move E m
<-> m = inl new.
Proof. subst. intros. unfold iff. split.
- intros. unfold initial_move in H.
apply H. apply ideal_finite. simpl. auto.
- intros. subst. unfold initial_move. intros.
rewrite <- ideal_finite. simpl. destruct n.
+ destruct s. unfold iff. auto.
+ unfold iff. split.
++ intros. contradiction H.
++ intros. inversion H.
Qed.

Fact initial_move_is_new_tensor
`(P : PartialOrder (sum Singleton X))
`(Q : PartialOrder (sum Singleton Y))
(E : EventStructure P) (F : EventStructure Q)
: forall m, initial_move (event_structure_tensor P Q E F) m
<-> m = inl new.
Proof. intros. unfold iff. split.
+ intros. unfold initial_move in H. apply H.
apply ideal_finite. simpl. auto.
+ intros. subst. unfold initial_move.
intros. unfold iff. rewrite <- ideal_finite. simpl.
destruct n.
++ destruct s. auto.
++ destruct s.
+++ split.
++++ intros. contradiction H.
++++ intros. inversion H.
+++ split.
++++ intros. contradiction H.
++++ intros. inversion H. Qed.

Fact second_move_is_second
`(P1 : PartialOrder X)
`(P2 : PartialOrder Y)
(P : PartialOrder (sum Singleton X))
(Q : PartialOrder (sum Singleton Y))
(urgh : P = lift_partial_order P1 /\ Q = lift_partial_order P2)
(E : EventStructure P) (F : EventStructure Q)
: forall m, second_move (event_structure_tensor P Q E F) m
-> (exists n, m = inr (inl n) /\ second_move E (inr n)) \/ 
(exists n, m = inr (inr n) /\ second_move F (inr n)).
Proof. destruct urgh. subst. intros. unfold second_move in H.
destruct H. destruct H0. destruct H0. destruct m.
- simpl in H0. destruct H0.
+ subst. contradiction H1. reflexivity.
+ contradiction H0.
- destruct x.
+ apply H in H0. destruct s.
++ left. refine (ex_intro _ x _). split.
+++ reflexivity.
+++ unfold second_move. split.
++++ intros. destruct n.
+++++ right. destruct s. rewrite initial_move_is_new_lift.
reflexivity. auto.
+++++ 
assert (In (inr (inl x0)) (ideal (inr (inl x)))).
{ simpl. right. apply add_inr_does_nothing. 
apply add_inl_does_nothing. apply cast_to_right_is_boring. 
apply H2. }
apply H in H3. destruct H3.
++++++ inversion H3. left. reflexivity.
++++++ right. unfold initial_move in H3. unfold initial_move.
intros. Admitted.

Instance asynchronous_arena_tensor
`(P1 : PartialOrder X)
`(P2 : PartialOrder Y)
(P : PartialOrder (sum Singleton X))
(Q : PartialOrder (sum Singleton Y))
(urgh : P = lift_partial_order P1 /\ Q = lift_partial_order P2)
(E : EventStructure P) (F : EventStructure Q)
(A : AsynchronousArena E) (B : AsynchronousArena F)
(positive1 : finite_payoff (inl (nil : Position E)) = (-1)%Z)
(positive1 : finite_payoff (inl (nil : Position F)) = (-1)%Z)
: AsynchronousArena (event_structure_tensor P Q E F) :=
{ polarity m := match m with
| inl new => true
| inr (inl m) => polarity (inr m)
| inr (inr m) => polarity (inr m)
end;
finite_payoff m := match m with
| inl nil => (-1)%Z
| inl p => 
let left := (inl new :: (add_inr Singleton X
(cast_to_left X Y (cast_to_right Singleton (X+Y) p )))) in
let right := (inl new :: (add_inr Singleton Y
(cast_to_right X Y (cast_to_right Singleton (X+Y) p )))) in
tensor (finite_payoff (inl left)) (finite_payoff (inl right))
| inr (w) =>
let p := finite_payoff (inr (cast_to_left_in_walk_tensor P Q E F w)) in
let q := finite_payoff (inr (cast_to_right_in_walk_tensor P Q E F w)) in
tensor p q
end;
infinite_payoff pos :=
let p := infinite_payoff (cast_infinite_position_to_inl_tensor _ _ _ _ pos) in
let q := infinite_payoff (cast_infinite_position_to_inr_tensor _ _ _ _ pos) in
match p, q with
| plus_infinity, plus_infinity => plus_infinity
| _, _ => minus_infinity
end
}.
Proof.


