Require Import Lia.
Require Import List.
Require Import Coq.Program.Wf.
Require Import ZArith.
Require Import Init.Nat.
Require Import Logic.Eqdep.
Require Import Coq.Arith.PeanoNat.

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
p2 = m :: p1 /\ (not (In m p1)).

Inductive Walk `(E: EventStructure M) := 
| empty_walk : Position E -> Walk E
| non_empty_walk : Position E -> (M * bool) -> Walk E -> Walk E.

Inductive valid_walk `(E: EventStructure M) (w : Walk E) : Prop :=
| valid_empty_walk : forall p, 
w = empty_walk E p -> valid_position E p -> valid_walk E w
| valid_one_move_walk :
forall p1 m ep p2, 
w = non_empty_walk E p2 (m, ep) (empty_walk E p1) ->
(valid_position E p2) /\ (valid_position E p1) /\
((ep = true /\ move_from E m p1 p2) \/ (ep = false /\ move_from E m p2 p1))
-> valid_walk E w
| valid_non_empty_walk :
forall p1 m ep p2 m' w',
w = non_empty_walk E p2 (m, ep) (non_empty_walk E p1 m' w') ->
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

Definition initial_move 
`(P : PartialOrder M) (m : M) :=
forall (n : M), leq n m -> m = n.

Definition second_move 
`(P : PartialOrder M) (m : M) :=
(exists (n : M), n <> m /\ leq n m /\
(forall (n : M), leq n m -> (n = m \/ initial_move P n) ) ).

Inductive InfinitePosition `(E : EventStructure M) : Type := 
| stream : M -> (unit -> InfinitePosition E)
-> InfinitePosition E.

Class AsynchronousArena 
`(P : PartialOrder M)
(E : EventStructure P) := {
polarity : M -> bool;
finite_payoff : (Position E + Walk E) -> Z;

infinite_payoff : InfinitePosition E -> Infinity;

initial_payoff :
let n := finite_payoff (inl (nil : Position E)) in
 n = (-1)%Z \/ n = (1)%Z;

polarity_first :
forall (m : M), initial_move P m -> 
(polarity m = true -> finite_payoff (inl(nil : Position E)) = (-1)%Z)
/\
(polarity m = false -> finite_payoff (inl(nil : Position E)) = (1)%Z);

polarity_second :
forall (m : M), second_move P m -> 
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

Class AsynchronousGame 
`(P : PartialOrder M)
(E : EventStructure P) 
(A : AsynchronousArena P E) `(X : Group G)
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

Class CanonicalRepresentation 
(Index : Type)
(f : Index -> Type)
(g : Index -> Type)
(h : Index -> Type)
(payoffs : Index -> Z)
:=
{
posets :> forall (i : Index), PartialOrder (f i);
structures : forall (i : Index), EventStructure (posets i);
arenas :> forall (i : Index), 
AsynchronousArena (posets i)(structures i);
left_groups : forall (i : Index), Group (g i);
right_groups : forall (i : Index), Group (h i);
games : forall (i : Index), 
AsynchronousGame (posets i)
(structures i) (arenas i) (left_groups i) (right_groups i);

positive_or_negative:
(forall (i : Index), finite_payoff
(inl (nil : Position (structures i))) = (1)%Z)
\/
(forall (i : Index), finite_payoff
(inl (nil : Position (structures i))) = (-1)%Z)
}.

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
++ apply anti_symmetric in H. subst. reflexivity.
++ destruct H. contradiction H.
+ destruct y.
++ destruct H. contradiction H.
++ apply anti_symmetric in H. subst. reflexivity.
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

Instance event_structure_tensor
`(P : PartialOrder A) `(Q : PartialOrder B)
(E : EventStructure P) (F : EventStructure Q) :
EventStructure (partial_order_sum P Q) :=
{ incompatible m n := 
match m,n with
| inl m, inl n => incompatible m n
| inr m, inr n => incompatible m n
| _, _ => False
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
+++ simpl in H. destruct H. contradiction H0.
++ destruct z.
+++ destruct H. simpl in H0. contradiction H0.
+++ destruct H. contradiction H.
+ destruct y.
++ destruct z.
+++ destruct H. contradiction H.
+++ destruct H. contradiction H.
++ destruct z.
+++ simpl in H. destruct H. contradiction H0.
+++ simpl in H. apply incompatible_closed with (y:=b0). apply H.
Defined.

Definition tensor (p q : Z) :=
if Z.ltb p 0 then 
(if Z.ltb q 0 then Z.add p q else p)
else
(if Z.ltb q 0 then q else Z.add p q).

Fixpoint cast_to_left_in_walk_tensor
`(P : PartialOrder X)
`(Q : PartialOrder Y)
(E : EventStructure P)
(F : EventStructure Q)
(w : Walk (event_structure_tensor P Q E F)) : Walk E
:= match w with
| empty_walk _ p => empty_walk E (cast_to_left X Y p)
| non_empty_walk _ p (inl m, b) w
=> non_empty_walk _ (cast_to_left X Y p) (m, b) 
(cast_to_left_in_walk_tensor P Q E F w)
| non_empty_walk _ p (inr m, b) w
=> cast_to_left_in_walk_tensor P Q E F w
end. 

Fixpoint cast_to_right_in_walk_tensor
`(P : PartialOrder X)
`(Q : PartialOrder Y)
(E : EventStructure P)
(F : EventStructure Q)
(w : Walk (event_structure_tensor P Q E F)) : Walk F
:= match w with
| empty_walk _ p => empty_walk _ (cast_to_right X Y p)
| non_empty_walk _ p (inr m, b) w
=> non_empty_walk _ (cast_to_right X Y p) (m, b) 
(cast_to_right_in_walk_tensor P Q E F w)
| non_empty_walk _ p (inl m, b) w
=> cast_to_right_in_walk_tensor P Q E F w
end.

Fixpoint cast_infinite_position_to_inl_tensor
`(P : PartialOrder X) `(Q : PartialOrder Y)
(E : EventStructure P) (F : EventStructure Q)
(p : InfinitePosition (event_structure_tensor P Q E F)) :
InfinitePosition E :=
match p with
| stream _ (inr m) f => 
cast_infinite_position_to_inl_tensor _ _ _ _ (f tt)
| stream _ (inl m) f => 
stream E m (fun _ => 
cast_infinite_position_to_inl_tensor _ _ _ _ (f tt))
end. 

Fixpoint cast_infinite_position_to_inr_tensor
`(P : PartialOrder X) `(Q : PartialOrder Y)
(E : EventStructure P) (F : EventStructure Q)
(p : InfinitePosition (event_structure_tensor P Q E F)) :
InfinitePosition F :=
match p with
| stream _ (inl _) f => 
cast_infinite_position_to_inr_tensor _ _ _ _ (f tt)
| stream _ (inr m) f => stream _ m 
(fun _ => cast_infinite_position_to_inr_tensor _ _ _ _ (f tt))
end. 

Fact initial_in_sum_is_initial
`(P : PartialOrder X) `(Q : PartialOrder Y)
: forall m, initial_move (partial_order_sum P Q) m
<-> ((exists n, m = inl n /\ initial_move P n)
\/ (exists n, m = inr n /\ initial_move Q n)).
Proof.
- intros. unfold iff. split.
+ intros. unfold initial_move in H. destruct m.
++ left. refine (ex_intro _ x _). split.
+++ reflexivity.
+++ unfold initial_move. intros.
assert (leq (inl n) (inl x)).
{ simpl. auto. }
apply H in H1. inversion H1. reflexivity.
++ right. refine (ex_intro _ y _). split.
+++ reflexivity.
+++ unfold initial_move. intros. 
assert (leq (inr n) (inr y)).
{ simpl. apply H0. }
assert (inr y = ((inr n) : X + Y)).
{apply H. apply H1. }
 inversion H2. reflexivity.
+ intros. unfold initial_move. intros. destruct H.
++ destruct H. destruct H. subst. unfold initial_move in H1.
destruct n.
+++ simpl in H0. apply H1 in H0. subst. reflexivity.
+++ simpl in H0. contradiction H0.
++ destruct H. destruct H. subst. unfold initial_move in H1.
destruct n.
+++ simpl in H0. contradiction H0.
+++ simpl in H0. apply H1 in H0. subst. reflexivity.
Qed.

Fact second_in_sum_is_second
`(P : PartialOrder X) `(Q : PartialOrder Y)
: forall m, second_move (partial_order_sum P Q) m
<-> ((exists n, m = inl n /\ second_move P n)
\/ (exists n, m = inr n /\ second_move Q n)).
Proof. intros. unfold iff. split.
+ intros. unfold second_move in H. destruct H.
destruct H. destruct H0. destruct m.
++ left. refine (ex_intro _ x0 _). split.
+++ reflexivity.
+++ unfold second_move. destruct x.
++++ refine (ex_intro _ x _). split.
+++++ unfold not. intros. subst. contradiction H. reflexivity.
+++++ split.
++++++ simpl in H0. auto.
++++++ intros.
assert (leq (inl n) (inl x0)).
{ simpl. auto. }
apply H1 in H3. destruct H3.
+++++++ inversion H3. left. reflexivity.
+++++++ right. apply initial_in_sum_is_initial in H3.
destruct H3.
++++++++ destruct H3. destruct H3. inversion H3. auto.
++++++++ destruct H3. destruct H3. inversion H3.
++++ simpl in H0. contradiction H0.
++ right. refine (ex_intro _ y _).
split.
+++ reflexivity.
+++ unfold second_move. destruct x.
++++ simpl in H0. contradiction H0.
++++ refine (ex_intro _ y0 _). split.
+++++ unfold not. intros. subst. contradiction H. reflexivity.
+++++ split.
++++++ simpl in H0. auto.
++++++ intros.
assert (leq (inr n) (inr y)).
{simpl. auto. }
assert 
(((inr n) : X + Y) = inr y \/ initial_move (partial_order_sum P Q) (inr n)).
{apply H1. auto. }
destruct H4.
+++++++ inversion H4. left. reflexivity.
+++++++ right. apply initial_in_sum_is_initial in H4. destruct H4.
++++++++ destruct H4. destruct H4. inversion H4.
++++++++ destruct H4. destruct H4. inversion H4. subst. auto.
+ intros. destruct H.
++ destruct H. destruct H. subst. unfold second_move in H0.
unfold second_move. destruct H0. destruct H. destruct H0.
refine (ex_intro _ (inl x0) _). split.
+++ unfold not. intros. inversion H2. subst. contradiction H.
reflexivity.
+++ split.
++++ simpl. auto.
++++ intros. destruct n.
+++++ simpl in H2. apply H1 in H2. destruct H2.
++++++ subst. left. reflexivity.
++++++ right. unfold initial_move in H2. unfold initial_move.
intros. simpl in H3. destruct n.
+++++++ apply H2 in H3. subst. reflexivity.
+++++++ contradiction H3.
+++++ simpl in H2. contradiction H2.
++ destruct H. destruct H. subst. unfold second_move in H0.
unfold second_move. destruct H0. destruct H. destruct H0.
refine (ex_intro _ (inr x0) _). split.
+++ unfold not. intros. inversion H2. subst. contradiction H.
reflexivity.
+++ split.
++++ simpl. auto.
++++ intros. destruct n.
+++++ simpl in H2. contradiction H2.
+++++ simpl in H2. apply H1 in H2. destruct H2.
++++++ subst. left. reflexivity.
++++++ right. unfold initial_move in H2. unfold initial_move.
intros. destruct n.
+++++++ simpl in H3. contradiction H3.
+++++++ simpl in H3. apply H2 in H3. subst. reflexivity.
Qed.

Fact valid_position_in_tensor_is_valid_inl
`(P : PartialOrder X) `(Q : PartialOrder Y)
(E : EventStructure P) (F : EventStructure Q) :
forall p, 
valid_position (event_structure_tensor P Q E F) p -> 
valid_position E (cast_to_left X Y p).
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

Fact valid_position_in_tensor_is_valid_inr
`(P : PartialOrder X) `(Q : PartialOrder Y)
(E : EventStructure P) (F : EventStructure Q) :
forall p, 
valid_position (event_structure_tensor P Q E F) p -> 
valid_position F (cast_to_right X Y p).
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


Fact move_in_tensor_is_move_inl_and_inr
`(P : PartialOrder X) `(Q : PartialOrder Y)
(E : EventStructure P) (F : EventStructure Q):
forall p1 p2,
(forall x, move_from (event_structure_tensor P Q E F) (inl x) p1 p2
->
move_from E x (cast_to_left X Y p1) (cast_to_left X Y p2))
/\
(forall y, move_from (event_structure_tensor P Q E F) (inr y) p1 p2
->
move_from F y (cast_to_right X Y p1) (cast_to_right X Y p2)).
Proof.
intros. split.
+ intros. unfold move_from in H. unfold move_from.
intros. simpl. destruct H.  subst. simpl. split.
++ reflexivity.
++ rewrite cast_to_left_is_boring. auto.
+ intros. unfold move_from in H. unfold move_from.
intros. simpl. destruct H.  subst. simpl. split.
++ reflexivity.
++ rewrite cast_to_right_is_boring. auto.
Qed.

Fact move_in_tensor_implies_equiv_opp
`(P : PartialOrder X) `(Q : PartialOrder Y)
(E : EventStructure P) (F : EventStructure Q):
forall p1 p2,
(forall x, move_from (event_structure_tensor P Q E F) (inr x) p1 p2
-> cast_to_left X Y p1 = cast_to_left X Y p2)
/\
(forall x, move_from (event_structure_tensor P Q E F) (inl x) p1 p2
-> cast_to_right X Y p1 = cast_to_right X Y p2).
Proof.
intros. split.
+ intros. unfold move_from in H. destruct H. subst. simpl. reflexivity.
+ intros. unfold move_from in H. destruct H. subst. simpl. reflexivity.
Qed.

Fact skip_inr_in_tensor_preserves_inl
`(P : PartialOrder X) `(Q : PartialOrder Y)
(E : EventStructure P) (F : EventStructure Q):
forall p1 y b w', 
valid_walk _ (non_empty_walk 
(event_structure_tensor P Q E F) p1 (inr y, b) w') ->
target_walk _ (cast_to_left_in_walk_tensor P Q E F 
(non_empty_walk 
(event_structure_tensor P Q E F) p1 (inr y, b) w') )
 = cast_to_left X Y p1.
Proof. intros. generalize dependent y.
generalize dependent b.
generalize dependent p1.
induction w'.
+ simpl. intros. inversion H.
++ inversion H0.
++ inversion H0. subst. destruct H1. destruct H2. destruct H3.
+++ apply move_in_tensor_implies_equiv_opp with (x:=y).
apply H3.
+++ symmetry. apply move_in_tensor_implies_equiv_opp with (x:=y).
apply H3.
++ inversion H0.
+ intros. simpl in IHw'. simpl. destruct p0. destruct s.
++ simpl. inversion H.
+++ inversion H0.
+++ inversion H0. 
+++ inversion H0. subst. destruct H1. destruct H2. destruct H3.
++++ apply move_in_tensor_implies_equiv_opp with (x0:=y).
apply H3.
++++ symmetry. apply move_in_tensor_implies_equiv_opp with (x0:=y).
apply H3.
++ 
assert (cast_to_left X Y p1 = cast_to_left X Y p).
{inversion H.
+ inversion H0.
+ inversion H0.
+ inversion H0. subst. destruct H1. destruct H2. destruct H3.
++ symmetry. apply move_in_tensor_implies_equiv_opp with (x:=y).
apply H3.
++ apply move_in_tensor_implies_equiv_opp with (x:=y).
apply H3. }
rewrite H0. apply IHw' with (y:=y0) (b:=b0).
inversion H.
+++ inversion H1.
+++ inversion H1.
+++ inversion H1. subst. destruct H2. destruct H3. apply H3.
Qed.

Fact skip_inl_in_tensor_preserves_inr
`(P : PartialOrder X) `(Q : PartialOrder Y)
(E : EventStructure P) (F : EventStructure Q):
forall p1 y b w', 
valid_walk _ (non_empty_walk 
(event_structure_tensor P Q E F) p1 (inl y, b) w') ->
target_walk _ (cast_to_right_in_walk_tensor P Q E F 
(non_empty_walk 
(event_structure_tensor P Q E F) p1 (inl y, b) w') )
 = cast_to_right X Y p1.
Proof. intros. generalize dependent y.
generalize dependent b.
generalize dependent p1.
induction w'.
+ simpl. intros. inversion H.
++ inversion H0.
++ inversion H0. subst. destruct H1. destruct H2. destruct H3.
+++ apply move_in_tensor_implies_equiv_opp with (x:=y).
apply H3.
+++ symmetry. apply move_in_tensor_implies_equiv_opp with (x:=y).
apply H3.
++ inversion H0.
+ intros. simpl in IHw'. simpl. destruct p0. destruct s.
++ 
assert (cast_to_right X Y p1 = cast_to_right X Y p).
{inversion H.
+ inversion H0.
+ inversion H0.
+ inversion H0. subst. destruct H1. destruct H2. destruct H3.
++ symmetry. apply move_in_tensor_implies_equiv_opp with (x0:=y).
apply H3.
++ apply move_in_tensor_implies_equiv_opp with (x0:=y).
apply H3. }
rewrite H0. apply IHw' with (y:=x) (b:=b0).
inversion H.
+++ inversion H1.
+++ inversion H1.
+++ inversion H1. subst. destruct H2. destruct H3. apply H3.
++ simpl. inversion H.
+++ inversion H0.
+++ inversion H0. 
+++ inversion H0. subst. destruct H1. destruct H2. destruct H3.
++++ apply move_in_tensor_implies_equiv_opp with (x:=y).
apply H3.
++++ symmetry. apply move_in_tensor_implies_equiv_opp with (x:=y).
apply H3.
Qed.


Fact valid_walk_in_tensor_is_valid_inl 
`(P : PartialOrder X) `(Q : PartialOrder Y)
(E : EventStructure P) (F : EventStructure Q):
forall w : Walk (event_structure_tensor P Q E F),
     valid_walk (event_structure_tensor P Q E F) w ->
valid_walk _ (cast_to_left_in_walk_tensor P Q E F w).
Proof. intros. induction w.
simpl. inversion H.
+ inversion H0. subst.
 apply valid_empty_walk with (p:=(cast_to_left X Y p0)).
++ reflexivity.
++ apply valid_position_in_tensor_is_valid_inl. auto.
+ inversion H0.
+ inversion H0.
+ inversion H.
++ inversion H0.
++ inversion H0. subst. simpl. destruct m. 
apply valid_one_move_walk
with (m:=x) (ep0:=ep) (p4:=(cast_to_left X Y p2))
(p3:=(cast_to_left X Y p1)).
+++ reflexivity.
+++ split.
++++ destruct H1. apply valid_position_in_tensor_is_valid_inl. auto.
++++ split.
+++++ destruct H1. destruct H2.
apply valid_position_in_tensor_is_valid_inl. auto.
+++++ destruct H1. destruct H2. destruct H3.
++++++ left. split.
+++++++ apply H3.
+++++++ apply move_in_tensor_is_move_inl_and_inr. apply H3.
++++++ right. split.
+++++++ apply H3.
+++++++ apply move_in_tensor_is_move_inl_and_inr. apply H3.
+++ apply valid_empty_walk with (p:=(cast_to_left X Y p1)).
++++ reflexivity.
++++ destruct H1. destruct H2.
apply valid_position_in_tensor_is_valid_inl. apply H2.
++ destruct H1. destruct H2. inversion H0. subst.
destruct m.
+++ simpl. destruct m'. destruct s.
++++ apply valid_non_empty_walk
with (p3:=(cast_to_left X Y p1)) (m:=x) (ep0:=ep)
(p4:=(cast_to_left X Y p2)) (m':=(x0, b))
(w'0:=(cast_to_left_in_walk_tensor P Q E F w')).
+++++ reflexivity.
+++++ split.
++++++ apply valid_position_in_tensor_is_valid_inl. auto.
++++++ split.
+++++++ destruct H.
++++++++ inversion H.
++++++++ inversion H.
++++++++ inversion H. subst. destruct H4. destruct H5.
apply IHw in H5. simpl in H5. apply H5.
+++++++ destruct H3.
++++++++ left. split.
+++++++++ apply H3.
+++++++++ apply move_in_tensor_is_move_inl_and_inr. apply H3.
++++++++ right. split.
+++++++++ apply H3.
+++++++++ apply move_in_tensor_is_move_inl_and_inr. apply H3.
++++ simpl in IHw. 
destruct (cast_to_left_in_walk_tensor P Q E F w') eqn:cast.
assert (valid_walk E (empty_walk E p)).
{apply IHw. auto. }
apply valid_one_move_walk with
(p3:=p) (m:=x) (ep0:=ep) (p4:=cast_to_left X Y p2).
++++++ reflexivity.
++++++ split.
+++++++ apply valid_position_in_tensor_is_valid_inl. auto.
+++++++ split.
inversion H4.
+++++++++ inversion H5. subst. auto.
+++++++++ inversion H5.
+++++++++ inversion H5.
+++++++++
assert (target_walk _ (cast_to_left_in_walk_tensor P Q E F 
(non_empty_walk 
(event_structure_tensor P Q E F) p1 (inr y, b) w') )
 = cast_to_left X Y p1).
{intros. apply skip_inr_in_tensor_preserves_inl. apply H2. }
simpl in H5. rewrite cast in H5. simpl in H5.
destruct H3.
+++++++++++ left. split.
++++++++++++ apply H3.
++++++++++++ destruct H3.
apply move_in_tensor_is_move_inl_and_inr in H6.
unfold move_from. unfold move_from in H6.
intros. rewrite H5. apply H6.
+++++++++++ right. destruct H3. split.
++++++++++++ apply H3.
++++++++++++ unfold move_from. intros.
apply move_in_tensor_is_move_inl_and_inr in H6.
unfold move_from in H6. rewrite H5. apply H6.
++++++ apply valid_non_empty_walk with
(p4:=cast_to_left X Y p2) (m:=x) (ep0:=ep)
(p3:=p) (m':=p0) (w'0:=w).
+++++++ reflexivity.
+++++++ split.
++++++++ apply valid_position_in_tensor_is_valid_inl. auto.
++++++++ split.
+++++++++ apply IHw. auto.
+++++++++  destruct H3.
++++++++++ left. split.
+++++++++++ apply H3.
+++++++++++
assert (target_walk _ (cast_to_left_in_walk_tensor P Q E F 
(non_empty_walk 
(event_structure_tensor P Q E F) p1 (inr y, b) w') ) = 
cast_to_left X Y p1).
{intros. apply skip_inr_in_tensor_preserves_inl. auto. }
simpl in H4. rewrite cast in H4. simpl in H4.
destruct H3. apply move_in_tensor_is_move_inl_and_inr in H5.
unfold move_from in H5. unfold move_from. intros. rewrite H4.
apply H5.
++++++++++ destruct H3. right. split.
+++++++++++ auto.
+++++++++++ assert (
target_walk _ (cast_to_left_in_walk_tensor P Q E F 
(non_empty_walk 
(event_structure_tensor P Q E F) p1 (inr y, b) w') ) = 
cast_to_left X Y p1).
{intros. apply skip_inr_in_tensor_preserves_inl. auto. }
simpl in H5. rewrite cast in H5. simpl in H5.
apply move_in_tensor_is_move_inl_and_inr in H4.
unfold move_from in H4. unfold move_from. intros. rewrite H5.
apply H4.
+++ simpl. destruct m'. destruct s.
++++ simpl in IHw. apply IHw. auto.
++++ simpl in IHw. apply IHw. auto.
Qed.

Fact valid_walk_in_tensor_is_valid_inr 
`(P : PartialOrder X) `(Q : PartialOrder Y)
(E : EventStructure P) (F : EventStructure Q):
forall w : Walk (event_structure_tensor P Q E F),
     valid_walk (event_structure_tensor P Q E F) w ->
valid_walk _ (cast_to_right_in_walk_tensor P Q E F w).
Proof. intros. induction w.
simpl. inversion H.
+ inversion H0. subst.
 apply valid_empty_walk with (p:=(cast_to_right X Y p0)).
++ reflexivity.
++ apply valid_position_in_tensor_is_valid_inr. auto.
+ inversion H0.
+ inversion H0.
+ inversion H.
++ inversion H0.
++ inversion H0. subst. simpl. destruct m.
+++ apply valid_empty_walk with (p:=(cast_to_right X Y p1)).
++++ reflexivity.
++++ destruct H1. destruct H2.
apply valid_position_in_tensor_is_valid_inr. apply H2.
+++ simpl. apply valid_one_move_walk with
(p3:=(cast_to_right X Y p1)) (m:=y) (ep0:=ep)
(p4:=cast_to_right X Y p2).
++++ reflexivity.
++++ split.
+++++ apply valid_position_in_tensor_is_valid_inr. apply H1.
+++++ split.
++++++ apply valid_position_in_tensor_is_valid_inr. destruct H1.
apply H2.
++++++ destruct H1. destruct H2. destruct H3.
+++++++ left. split.
++++++++ apply H3.
++++++++ apply move_in_tensor_is_move_inl_and_inr. apply H3.
+++++++ right. split.
++++++++ apply H3.
++++++++ apply move_in_tensor_is_move_inl_and_inr. apply H3.
++ inversion H0. subst. destruct m.
+++ simpl. destruct m'. destruct s.
++++ simpl in IHw. apply IHw. destruct H1. apply H2.
++++ simpl in IHw. apply IHw. destruct H1. apply H2.
+++ simpl. destruct m'. destruct s.
++++ simpl in IHw.
destruct (cast_to_right_in_walk_tensor P Q E F w') eqn:cast.
+++++ apply valid_one_move_walk
with (p3:=p) (m:=y) (ep0:=ep) (p4:=cast_to_right X Y p2).
++++++ reflexivity.
++++++ split.
+++++++ apply valid_position_in_tensor_is_valid_inr. apply H1.
+++++++ assert (valid_walk F (empty_walk F p)).
{apply IHw. destruct H1. apply H2. }
inversion H2.
++++++++ inversion H3. subst. split.
+++++++++ apply H4.
+++++++++ destruct H1. destruct H5. destruct H6.
++++++++++ left. split.
+++++++++++ apply H6.
+++++++++++
assert (target_walk _ (cast_to_right_in_walk_tensor P Q E F 
(non_empty_walk 
(event_structure_tensor P Q E F) p1 (inl x, b) w') ) = 
cast_to_right X Y p1).
{intros. apply skip_inl_in_tensor_preserves_inr. auto. }
simpl in H7. rewrite cast in H7. simpl in H7.
destruct H6. apply move_in_tensor_is_move_inl_and_inr in H8.
unfold move_from in H8. unfold move_from. intros. rewrite H7.
apply H8.
++++++++++ destruct H6. right. split.
+++++++++++ auto.
+++++++++++ assert (
target_walk _ (cast_to_right_in_walk_tensor P Q E F 
(non_empty_walk 
(event_structure_tensor P Q E F) p1 (inl x, b) w') )
 = cast_to_right X Y p1).
{intros. apply skip_inl_in_tensor_preserves_inr. auto. }
simpl in H8. rewrite cast in H8. simpl in H8.
apply move_in_tensor_is_move_inl_and_inr in H7.
unfold move_from in H7. unfold move_from. intros. rewrite H8.
apply H7.
++++++++ inversion H3.
++++++++ inversion H3.
+++++ apply valid_non_empty_walk with
(p3:=p) (m:=y) (ep0:=ep) (p4:=cast_to_right X Y p2)
(m':=p0) (w'0:=w).
++++++ reflexivity.
++++++ split.
+++++++ apply valid_position_in_tensor_is_valid_inr.
apply H1.
+++++++ split.
++++++++ apply IHw. apply H1.
++++++++ destruct H1. destruct H2. destruct H3.
+++++++++ left. split.
++++++++++ apply H3.
++++++++++ destruct H3.
assert (
target_walk _ (cast_to_right_in_walk_tensor P Q E F 
(non_empty_walk 
(event_structure_tensor P Q E F) p1 (inl x, b) w') )
 = cast_to_right X Y p1).
{intros. apply skip_inl_in_tensor_preserves_inr. auto. }
simpl in H5. rewrite cast in H5. simpl in H5.
apply move_in_tensor_is_move_inl_and_inr in H4.
unfold move_from in H4. unfold move_from. intros. rewrite H5.
apply H4.
+++++++++ destruct H3. right. split.
++++++++++ auto.
++++++++++
assert (
target_walk _ (cast_to_right_in_walk_tensor P Q E F 
(non_empty_walk 
(event_structure_tensor P Q E F) p1 (inl x, b) w') ) 
= cast_to_right X Y p1).
{intros. apply skip_inl_in_tensor_preserves_inr. auto. }
simpl in H5. rewrite cast in H5. simpl in H5.
apply move_in_tensor_is_move_inl_and_inr in H4.
unfold move_from in H4. unfold move_from. intros. rewrite H5.
apply H4.
++++ apply valid_non_empty_walk with
(p3:=cast_to_right X Y p1) (m:=y) (ep0:=ep) 
(p4:=cast_to_right X Y p2)
(m':=(y0,b)) (w'0:=cast_to_right_in_walk_tensor P Q E F w').
+++++ reflexivity.
+++++ split.
++++++ apply valid_position_in_tensor_is_valid_inr. apply H1.
++++++ split.
+++++++ simpl in IHw. apply IHw. apply H1.
+++++++ destruct H1. destruct H2. destruct H3.
++++++++ left. split.
+++++++++ apply H3.
+++++++++ destruct H3. apply move_in_tensor_is_move_inl_and_inr in H4.
auto.
++++++++ destruct H3. right. split.
+++++++++ auto.
+++++++++ apply move_in_tensor_is_move_inl_and_inr in H4.
auto.
Qed.

Fact target_in_proj_is_cast
`(P : PartialOrder X) `(Q : PartialOrder Y)
(E : EventStructure P) (F : EventStructure Q):
forall w : Walk (event_structure_tensor P Q E F),
     valid_walk (event_structure_tensor P Q E F) w ->
(target_walk _ (cast_to_left_in_walk_tensor P Q E F w) =
cast_to_left X Y (target_walk _ w)
/\
(target_walk _ (cast_to_right_in_walk_tensor P Q E F w) = 
cast_to_right X Y (target_walk _ w))).
Proof.
intros. split.
+ destruct w.
++ simpl. reflexivity.
++ simpl. destruct p0. destruct s.
+++ simpl. reflexivity.
+++ assert
(target_walk _ (cast_to_left_in_walk_tensor P Q E F 
(non_empty_walk 
(event_structure_tensor P Q E F) p (inr y, b) w) )
 = cast_to_left X Y p).
{apply skip_inr_in_tensor_preserves_inl. auto. }
rewrite <- H0. simpl. reflexivity.
+ destruct w.
++ simpl. reflexivity.
++ simpl. destruct p0. destruct s.
+++ assert
(target_walk _ (cast_to_right_in_walk_tensor P Q E F 
(non_empty_walk 
(event_structure_tensor P Q E F) p (inl x, b) w) )
 = cast_to_right X Y p).
{apply skip_inl_in_tensor_preserves_inr. auto. }
rewrite <- H0. simpl. reflexivity.
+++ simpl. reflexivity.
Qed.

Fact cast_of_pos_in_tensor_in_cast
`(P : PartialOrder X) `(Q : PartialOrder Y)
(E : EventStructure P) (F : EventStructure Q):
forall (w : Walk (event_structure_tensor P Q E F)),
     valid_walk (event_structure_tensor P Q E F) w ->
position_in_walk _ nil w -> 
(position_in_walk E nil (cast_to_left_in_walk_tensor P Q E F w)
/\
position_in_walk F nil (cast_to_right_in_walk_tensor P Q E F w)).
Proof. intros. split.
+ induction w.
++ simpl. simpl in H0. subst. reflexivity.
++ destruct H0.
+++ subst. simpl. destruct p0. destruct s.
++++ simpl. left. reflexivity.
++++ assert
(target_walk _ (cast_to_left_in_walk_tensor P Q E F 
(non_empty_walk 
(event_structure_tensor P Q E F) nil (inr y, b) w) )
 = cast_to_left X Y nil).
{apply skip_inr_in_tensor_preserves_inl. auto. }
simpl in H0. destruct
(cast_to_left_in_walk_tensor P Q E F w).
+++++ simpl in H0. subst. simpl. reflexivity.
+++++ simpl in H0. subst. simpl. left. reflexivity.
+++ simpl. destruct p0. destruct s.
++++ simpl. right. apply IHw. destruct H.
+++++ inversion H.
+++++ inversion H. subst. apply valid_empty_walk with (p:=p1).
++++++ reflexivity.
++++++ apply H1.
+++++ inversion H. subst. apply H1.
+++++ auto.
++++ apply IHw. destruct H.
+++++ inversion H.
+++++ inversion H. subst. apply valid_empty_walk with (p:=p1).
++++++ reflexivity.
++++++ apply H1.
+++++ inversion H. subst. apply H1.
+++++ auto.
+ induction w.
++ simpl. simpl in H0. subst. reflexivity.
++ destruct H0.
+++ subst. simpl. destruct p0. destruct s.
++++ assert
(target_walk _ (cast_to_right_in_walk_tensor P Q E F 
(non_empty_walk 
(event_structure_tensor P Q E F) nil (inl x, b) w) )
 = cast_to_right X Y nil).
{apply skip_inl_in_tensor_preserves_inr. auto. }
simpl in H0. destruct
(cast_to_right_in_walk_tensor P Q E F w).
+++++ simpl in H0. subst. simpl. reflexivity.
+++++ simpl in H0. subst. simpl. left. reflexivity.
++++ simpl. left. reflexivity.
+++ simpl. destruct p0. destruct s.
++++ apply IHw. destruct H.
+++++ inversion H.
+++++ inversion H. subst. apply valid_empty_walk with (p:=p1).
++++++ reflexivity.
++++++ apply H1.
+++++ inversion H. subst. apply H1.
+++++ auto.
++++ simpl. right. apply IHw. destruct H.
+++++ inversion H.
+++++ inversion H. subst. apply valid_empty_walk with (p:=p1).
++++++ reflexivity.
++++++ apply H1.
+++++ inversion H. subst. apply H1.
+++++ auto.
Qed.


Instance asynchronous_arena_tensor
`(P : PartialOrder X) `(Q : PartialOrder Y)
(E : EventStructure P) (F : EventStructure Q)
(A : AsynchronousArena P E) (B : AsynchronousArena Q F)
(negative1 : finite_payoff (inl (nil : Position E)) = (1)%Z)
(negative2 : finite_payoff (inl (nil : Position F)) = (1)%Z)
: AsynchronousArena (partial_order_sum P Q)
(event_structure_tensor P Q E F) :=
{ polarity m := match m with
| inl m => polarity m
| inr m => polarity m
end;
finite_payoff m := match m with
| inr w => 
let left := finite_payoff (inr (cast_to_left_in_walk_tensor P Q E F w)) in
let right := finite_payoff (inr (cast_to_right_in_walk_tensor P Q E F w)) in
tensor left right
| inl nil => (1)%Z
| inl pos => 
let left := finite_payoff (inl (cast_to_left X Y pos)) in
let right := finite_payoff (inl (cast_to_right X Y pos)) in
tensor left right
end;
infinite_payoff p :=
match p with
| stream _ (inl _) _ => 
infinite_payoff (cast_infinite_position_to_inl_tensor _ _ _ _ p)
| stream _ (inr _) _ => 
infinite_payoff (cast_infinite_position_to_inr_tensor _ _ _ _ p)
end
}.
Proof.
- simpl. right. reflexivity.
- intros. apply initial_in_sum_is_initial in H.
destruct H.
+ destruct H. destruct H. subst. split.
++ intros.
assert (polarity x = true -> finite_payoff (inl(nil : Position E)) = (-1)%Z).
{apply polarity_first. auto. }
apply H1 in H. rewrite H in negative1. lia.
++ unfold iff. split.
+ destruct H. destruct H. subst. split.
++ intros.
assert (polarity x = true -> finite_payoff (inl(nil : Position F)) = (-1)%Z).
{apply polarity_first. auto. }
apply H1 in H. rewrite H in negative2. lia.
++ auto.
- intros. apply second_in_sum_is_second in H. destruct H.
+ destruct H. destruct H. subst. split.
++ auto.
++ assert (polarity x = false -> finite_payoff (inl(nil : Position E)) = (-1)%Z).
{apply polarity_second. auto. }
intros. apply H in H1. rewrite H1 in negative1. lia.
+ destruct H. destruct H. subst. split.
++ auto.
++ assert (polarity x = false -> finite_payoff (inl(nil : Position F)) = (-1)%Z).
{apply polarity_second. auto. }
intros. apply H in H1. rewrite H1 in negative2. lia.
- intros. destruct H. subst. simpl. inversion H.
+ inversion H0. subst.
assert (valid_walk _ (empty_walk E (cast_to_left X Y p0))).
{ apply valid_empty_walk with (p:=(cast_to_left X Y p0)).
+ reflexivity.
+ apply valid_position_in_tensor_is_valid_inl. auto. }
assert ((finite_payoff (inr (empty_walk E (cast_to_left X Y p0))))
 = 0%Z).
{apply initial_null with (p:=(cast_to_left X Y p0)). auto. }
assert (valid_walk _ (empty_walk _ (cast_to_right X Y p0))).
{ apply valid_empty_walk with (p:=(cast_to_right X Y p0)).
+ reflexivity.
+ apply valid_position_in_tensor_is_valid_inr. auto. }
assert ((finite_payoff (inr (empty_walk _ (cast_to_right X Y p0))))
 = 0%Z).
{apply initial_null with (p:=(cast_to_right X Y p0)). auto. }
rewrite H3. rewrite H5. unfold tensor. simpl. reflexivity.
+ inversion H0.
+ inversion H0.
- intros. destruct H. destruct H0. destruct H1.
assert ((forall (w : Walk E), length_walk E w > 0)
 /\ 
(forall (w' : Walk F), length_walk F w' > 0)).
{split.
+ intros. destruct w0.
++ simpl. lia.
++ simpl. lia.
+ intros. destruct w'.
++ simpl. lia.
++ simpl. lia. }
destruct (Nat.ltb 1 (length_walk _ (cast_to_left_in_walk_tensor P Q E F w))) eqn:LEFT.
+ rewrite Nat.ltb_lt in LEFT.
assert 
(finite_payoff (inr (cast_to_left_in_walk_tensor P Q E F w))
= finite_payoff (inl (cast_to_left X Y p))).
{apply noninitial_payoff. split.
+ apply valid_walk_in_tensor_is_valid_inl. auto.
+ split.
++ lia. 
++ split.
+++ rewrite <- H1. apply target_in_proj_is_cast. auto.
+++ apply cast_of_pos_in_tensor_in_cast. 
++++ auto.
++++ auto. }
rewrite H4.
destruct (Nat.ltb 1 (length_walk _ (cast_to_right_in_walk_tensor P Q E F w))) eqn:RIGHT.
++ rewrite Nat.ltb_lt in RIGHT.
assert 
(finite_payoff (inr (cast_to_right_in_walk_tensor P Q E F w))
= finite_payoff (inl (cast_to_right X Y p))).
{apply noninitial_payoff. split.
+ apply valid_walk_in_tensor_is_valid_inr. auto.
+ split.
++ lia. 
++ split.
+++ rewrite <- H1. apply target_in_proj_is_cast. auto.
+++ apply cast_of_pos_in_tensor_in_cast. 
++++ auto.
++++ auto. }
rewrite H5. admit.
++ rewrite Nat.ltb_nlt in RIGHT. 
assert (length_walk F (cast_to_right_in_walk_tensor P Q E F w) = 0
\/
length_walk F (cast_to_right_in_walk_tensor P Q E F w) = 1).
{lia. } clear RIGHT.
destruct H5.
+++ assert 
(length_walk F (cast_to_right_in_walk_tensor P Q E F w) > 0).
{apply H3. }
lia.
+++ destruct (cast_to_right_in_walk_tensor P Q E F w) eqn:RIGHT.
++++ assert (finite_payoff (inr (empty_walk F p0)) = 0%Z).
{apply initial_null with (p1:=p0). rewrite <- RIGHT.
+ split.
++ apply valid_walk_in_tensor_is_valid_inr. auto. 
++ reflexivity. }
rewrite H6. simpl.
assert ((target_walk _ (cast_to_right_in_walk_tensor P Q E F w) = 
cast_to_right X Y (target_walk _ w))).
{apply target_in_proj_is_cast. auto. }
rewrite RIGHT in H7. simpl in H7. rewrite H1 in H7. admit.
++++ simpl in H5. lia.
+ rewrite Nat.ltb_nlt in LEFT.
assert (length_walk E (cast_to_left_in_walk_tensor P Q E F w) = 0
\/
length_walk E (cast_to_left_in_walk_tensor P Q E F w) = 1).
{lia. } clear LEFT.
destruct H4.
+++ assert 
(length_walk E (cast_to_left_in_walk_tensor P Q E F w) > 0).
{apply H3. }
lia.
+++ destruct (cast_to_left_in_walk_tensor P Q E F w) eqn:LEFT.
++++
assert (finite_payoff (inr (empty_walk E p0)) = 0%Z).
{apply initial_null with (p1:=p0). split.
+ rewrite <- LEFT. apply valid_walk_in_tensor_is_valid_inl.  auto.
+ reflexivity. }
rewrite H5. simpl. 
destruct (Nat.ltb 1 (length_walk _ (cast_to_right_in_walk_tensor P Q E F w))) eqn:RIGHT.
++ rewrite Nat.ltb_lt in RIGHT.
assert 
(finite_payoff (inr (cast_to_right_in_walk_tensor P Q E F w))
= finite_payoff (inl (cast_to_right X Y p))).
{apply noninitial_payoff. split.
+ apply valid_walk_in_tensor_is_valid_inr. auto.
+ split.
++ lia. 
++ split.
+++ rewrite <- H1. apply target_in_proj_is_cast. auto.
+++ apply cast_of_pos_in_tensor_in_cast. 
++++ auto.
++++ auto. }
rewrite H6. admit.
++ apply Nat.ltb_nlt in RIGHT. 
assert (length_walk F (cast_to_right_in_walk_tensor P Q E F w) = 0
\/
length_walk F (cast_to_right_in_walk_tensor P Q E F w) = 1).
{lia. } clear RIGHT.
destruct H6.
+++++ assert 
(length_walk F (cast_to_right_in_walk_tensor P Q E F w) > 0).
{apply H3. }
lia.
+++++ admit. (*left and right can't both be empty. *) 
++++ simpl in H4. lia.
Admitted.

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

Instance game_tensor
`(P : PartialOrder X) `(Q : PartialOrder Y)
(E : EventStructure P) (F : EventStructure Q)
(A : AsynchronousArena P E) (B : AsynchronousArena Q F)
(negative1 : finite_payoff (inl (nil : Position E)) = (1)%Z)
(negative2 : finite_payoff (inl (nil : Position F)) = (1)%Z)
`(X : Group G)
`(Y : Group H)
`(X' : Group G')
`(Y' : Group H')
(Game : AsynchronousGame P E A X Y)
(Game' : AsynchronousGame Q F B X' Y')
: AsynchronousGame 
(partial_order_sum P Q)
(event_structure_tensor P Q E F)
(asynchronous_arena_tensor P Q E F A B negative1 negative2)
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
+ simpl. admit. (* apply coherence_2. *)
+ simpl. admit. (* apply coherence_2. *)
- intros. destruct g. destruct m.
+ simpl. simpl in H0. apply H0. apply reflexive.
+ simpl. simpl in H0. apply H0. apply reflexive.
- intros. destruct h. destruct m.
+ simpl. simpl in H0. apply H0. apply reflexive.
+ simpl. simpl in H0. apply H0. apply reflexive.
Admitted.

Instance canonical_tensor
`(C1 : CanonicalRepresentation Index f g h payoffs)
`(C2 : CanonicalRepresentation Index' f' g' h' payoffs')
(negative1 : forall (i : Index), finite_payoff
(inl (nil : Position (structures i))) = (1)%Z)
(negative2 : forall (i : Index'), finite_payoff
(inl (nil : Position (structures i))) = (1)%Z)
:
CanonicalRepresentation (Index * Index')
(fun i => sum (f (fst i)) (f' (snd i) ) )
(fun i => prod (g (fst i)) (g' (snd i)))
(fun i => prod (h (fst i)) (h' (snd i)))
(fun i => tensor (payoffs (fst i)) (payoffs' (snd i)))
:= {
posets i := partial_order_sum 
(posets (fst i)) (posets (snd i)) ;
structures i := event_structure_tensor
(posets (fst i)) (posets (snd i))
(structures (fst i)) (structures (snd i)) ;
arenas i := asynchronous_arena_tensor
(posets (fst i)) (posets (snd i))
(structures (fst i)) (structures (snd i)) 
(arenas (fst i)) (arenas (snd i))
(negative1 (fst i)) (negative2 (snd i));
left_groups i := product_group 
(left_groups (fst i)) (left_groups (snd i));
right_groups i := product_group 
(right_groups (fst i)) (right_groups (snd i));
games i := game_tensor
(posets (fst i)) (posets (snd i))
(structures (fst i)) (structures (snd i)) 
(arenas (fst i)) (arenas (snd i))
(negative1 (fst i)) (negative2 (snd i))
(left_groups (fst i)) (right_groups (fst i))
(left_groups (snd i)) (right_groups (snd i))
(games (fst i)) (games (snd i))
}.
Proof. left. intros. simpl. Admitted.

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

Fixpoint cast_to_left_in_walk_sum 
`(P : PartialOrder X)
`(Q : PartialOrder Y)
(E : EventStructure P)
(F : EventStructure Q)
(w : Walk (event_structure_sum P Q E F)) : Walk E
:= match w with
| empty_walk _ p => empty_walk E (cast_to_left X Y p)
| non_empty_walk _ p (inl m, b) w
=> non_empty_walk _ (cast_to_left X Y p) (m, b) 
(cast_to_left_in_walk_sum P Q E F w)
| non_empty_walk _ p (inr m, b) w
=> cast_to_left_in_walk_sum P Q E F w
end. 

Fixpoint cast_to_right_in_walk_sum 
`(P : PartialOrder X)
`(Q : PartialOrder Y)
(E : EventStructure P)
(F : EventStructure Q)
(w : Walk (event_structure_sum P Q E F)) : Walk F
:= match w with
| empty_walk _ p => empty_walk _ (cast_to_right X Y p)
| non_empty_walk _ p (inr m, b) w
=> non_empty_walk _ (cast_to_right X Y p) (m, b) 
(cast_to_right_in_walk_sum P Q E F w)
| non_empty_walk _ p (inl m, b) w
=> cast_to_right_in_walk_sum P Q E F w
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
(move_from (event_structure_sum P Q E F) (inl y) p1 p2
\/
move_from (event_structure_sum P Q E F) (inl y) p2 p1)
)
-> (forall m, (In m p1 ->(exists y, m = inl y)) /\
(In m p2 ->(exists y, m = inl y))).
Proof.
intros. destruct H. destruct H0. destruct H1.
unfold move_from in H1. destruct H1. subst. split.
+ intros. destruct m.
++ refine (ex_intro _ x _). reflexivity.
++ apply sum_valid_position_is_pure with (x:=y) (y1:=y0)
in H0. contradiction H0. split.
+++ left. reflexivity.
+++ right. auto.
+ intros. destruct m.
++ refine (ex_intro _ x _). reflexivity.
++ apply sum_valid_position_is_pure with (x:=y) (y1:=y0)
in H0. contradiction H0. split.
+++ left. reflexivity.
+++ right. destruct H1.
++++ inversion H1.
++++ auto.
+ unfold move_from in H1. destruct H1. subst. split.
++ intros. destruct m.
+++ refine (ex_intro _ x _). reflexivity.
+++ apply sum_valid_position_is_pure with (x:=y) (y1:=y0)
in H. contradiction H. split.
++++ left. reflexivity.
++++ right. destruct H1.
+++++ inversion H1.
+++++ auto.
++ intros. destruct m.
+++ refine (ex_intro _ x _). reflexivity.
+++ apply sum_valid_position_is_pure with (x:=y) (y1:=y0)
in H. contradiction H. split.
++++ left. reflexivity.
++++ right. auto.
Qed.

Fact inr_move_implies_inr 
`(P : PartialOrder X) `(Q : PartialOrder Y)
(E : EventStructure P) (F : EventStructure Q):
forall y p1 p2,
(valid_position (event_structure_sum P Q E F) p1
/\
valid_position (event_structure_sum P Q E F) p2
/\
(move_from (event_structure_sum P Q E F) (inr y) p1 p2
\/
move_from (event_structure_sum P Q E F) (inr y) p2 p1))
-> (forall m, (In m p1 ->(exists y, m = inr y)) /\
(In m p2 ->(exists y, m = inr y))).
Proof.
intros. destruct H. destruct H0. destruct H1.
++ unfold move_from in H1. destruct H1. subst. split.
+++ intros. destruct m.
++++ apply sum_valid_position_is_pure with (x0:=x) (y0:=y) in H0.
contradiction H0. split.
+++++ right. auto.
+++++ left. auto.
++++ refine (ex_intro _ y0 _). auto.
+++ intros. destruct m.
apply sum_valid_position_is_pure with (x0:=x) (y0:=y) in H0.
contradiction H0. split.
+++++ destruct H1.
++++++ inversion H1.
++++++ right. auto.
+++++ left. auto.
+++++ refine (ex_intro _ y0 _). auto.
++ unfold move_from in H1. destruct H1. subst. split.
+++ intros. destruct m.
++++ apply sum_valid_position_is_pure with (x0:=x) (y0:=y) in H.
contradiction H. split.
+++++ destruct H1.
++++++ inversion H1.
++++++ right. auto.
+++++ left. auto.
++++ refine (ex_intro _ y0 _). auto.
+++ intros. destruct m.
apply sum_valid_position_is_pure with (x0:=x) (y0:=y) in H.
contradiction H. split.
+++++ right. auto.
+++++ left. auto.
+++++  refine (ex_intro _ y0 _). auto.
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
target_walk _ (cast_to_left_in_walk_sum P Q E F w) = nil.
Proof. intros. induction w.
+ simpl. destruct H. destruct H. destruct H. destruct H.
++ inversion H.
++ inversion H. subst. destruct H0. destruct H1.
assert ((forall m, (In m p1 ->(exists y, m = inr y)) /\
(In m p2 ->(exists y, m = inr y)))).
{ apply inr_move_implies_inr
with (p3:=p1) (p4:=p2) (y:=x0)
(P0:=P) (Q0:=Q) (E0:=E) (F0:=F). split.
+ auto.
+ split.
++ auto.
++ destruct H2.
+++ left. apply H2.
+++ right. apply H2.
}
apply cast_inr_to_inl_nil.
++++ apply P.
++++ apply Q.
++++ apply H3.
++  inversion H.
+ simpl. destruct p0. destruct s.
++ simpl. destruct H. destruct H. destruct H.
destruct H.
+++ inversion H.
+++ inversion H.
+++ inversion H.
subst. destruct H0. destruct H1. destruct H1.
++++ inversion H1.
++++ inversion H1. subst. 
assert ((forall m, (In m p3 ->(exists y, m = inr y)) /\
(In m p2 ->(exists y, m = inr y)))).
{ apply inr_move_implies_inr
with (p1:=p3) (p4:=p2) (y:=x1)
(P0:=P) (Q0:=Q) (E0:=E) (F0:=F). split.
+ apply H3.
+ split.
++ auto.
++ destruct H2.
+++ left. apply H2.
+++ right. apply H2.
}
apply cast_inr_to_inl_nil.
+++++ apply P.
+++++ apply Q.
+++++ apply H4.
++++ inversion H1. subst. apply cast_inr_to_inl_nil.
++++++ apply P.
++++++ apply Q.
++++++ assert ((forall m, (In m p3 ->(exists y, m = inr y)) /\
(In m p2 ->(exists y, m = inr y)))).
{ apply inr_move_implies_inr
with (p1:=p3) (p4:=p2) (y:=x1)
(P0:=P) (Q0:=Q) (E0:=E) (F0:=F). split.
+ apply H3.
+ split.
++ auto.
++ destruct H2.
+++ left. apply H2.
+++ right. apply H2.
}
apply H4.
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
target_walk _ (cast_to_right_in_walk_sum P Q E F w) = nil.
Proof. intros. induction w.
+ simpl. destruct H. destruct H. destruct H. destruct H.
++ inversion H.
++ inversion H. subst. destruct H0. destruct H1. 
assert ((forall m, (In m p1 ->(exists y, m = inl y)) /\
(In m p2 ->(exists y, m = inl y)))).
{ apply inl_move_implies_inl
with (p3:=p1) (p4:=p2) (y:=x0)
(P0:=P) (Q0:=Q) (E0:=E) (F0:=F). split.
+ auto.
+ split.
++ auto.
++ destruct H2.
+++ left. apply H2.
+++ right. apply H2.
}
apply cast_inl_to_inr_nil.
++++ apply P.
++++ apply Q.
++++ apply H3.
++ inversion H.
+ simpl. destruct p0. destruct s.
++ simpl. destruct H. destruct H. destruct H.
destruct H.
+++ inversion H.
+++ inversion H.
+++ inversion H.
subst. destruct H0. destruct H1. apply IHw.
refine (ex_intro _ p1 _).
refine (ex_intro _ x _).
refine (ex_intro _ b _). auto.
++ simpl. destruct H. destruct H. destruct H.
destruct H.
+++ inversion H.
+++ inversion H.
+++ inversion H. subst. destruct H0. destruct H1. destruct H1.
++++ inversion H1.
++++ inversion H1. subst.
assert ((forall m, (In m p3 ->(exists y, m = inl y)) /\
(In m p2 ->(exists y, m = inl y)))).
{ apply inl_move_implies_inl
with (p1:=p3) (p4:=p2) (y0:=x0)
(P0:=P) (Q0:=Q) (E0:=E) (F0:=F). split.
+ apply H3.
+ split.
++ auto.
++ destruct H2.
+++ left. apply H2.
+++ right. apply H2.
}
apply cast_inl_to_inr_nil.
+++++ apply P.
+++++ apply Q.
+++++ apply H4.
++++ inversion H1. subst.
assert ((forall m, (In m p3 ->(exists y, m = inl y)) /\
(In m p2 ->(exists y, m = inl y)))).
{ apply inl_move_implies_inl
with (p1:=p3) (p4:=p2) (y0:=x0)
(P0:=P) (Q0:=Q) (E0:=E) (F0:=F). split.
+ apply H3.
+ split.
++ auto.
++ destruct H2.
+++ left. apply H2.
+++ right. apply H2.
}
apply cast_inl_to_inr_nil.
+++++ apply P.
+++++ apply Q.
+++++ apply H4.
Qed.

Fact cast_to_left_in_walk_sum_monotonic 
`(P : PartialOrder X)
`(Q : PartialOrder Y)
(E : EventStructure P)
(F : EventStructure Q)
: forall (w : Walk (event_structure_sum P Q E F)),
length_walk E (cast_to_left_in_walk_sum P Q E F w) <
length_walk (event_structure_sum P Q E F) w
\/
length_walk E (cast_to_left_in_walk_sum P Q E F w) =
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

Fact cast_to_right_in_walk_sum_monotonic 
`(P : PartialOrder X)
`(Q : PartialOrder Y)
(E : EventStructure P)
(F : EventStructure Q)
: forall (w : Walk (event_structure_sum P Q E F)),
length_walk F (cast_to_right_in_walk_sum P Q E F w) <
length_walk (event_structure_sum P Q E F) w
\/
length_walk F (cast_to_right_in_walk_sum P Q E F w) =
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
  length_walk E (cast_to_left_in_walk_sum P Q E F w)
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
(length_walk E (cast_to_left_in_walk_sum P Q E F w) =
length_walk (event_structure_sum P Q E F) w).
{lia. }
destruct H.
+++ inversion H.
+++ inversion H. subst. intros. destruct H3. destruct H3.
++++ subst. destruct H2. destruct H3.
assert ((forall m, (In m p ->(exists y, m = inl y)) /\
(In m p1 ->(exists y, m = inl y)))).
{apply inl_move_implies_inl with (y:=x). split.
+ auto.
+ split.
++ auto.
++ destruct H5.
+++ right. apply H5.
+++ left. apply H5. }
destruct H6 with (m:=m). apply H7. auto.
++++ simpl in H3. subst. destruct H2. destruct H3.
assert ((forall m, (In m p ->(exists y, m = inl y)) /\
(In m p2 ->(exists y, m = inl y)))).
{apply inl_move_implies_inl with (y:=x). split.
+ auto.
+ split.
++ auto.
++ destruct H5.
+++ left. apply H5.
+++ right. apply H5. }
destruct H6 with (m:=m). apply H7. auto.
+++ inversion H. subst.
assert ((exists p : Position (event_structure_sum P Q E F),
         non_empty_walk (event_structure_sum P Q E F) p1 m' w' =
         empty_walk (event_structure_sum P Q E F) p) \/
      (forall (m : X + Y) (p : Position (event_structure_sum P Q E F)),
       position_in_walk (event_structure_sum P Q E F) p
         (non_empty_walk (event_structure_sum P Q E F) p1 m' w') /\ 
       In m p -> exists x : X, m = inl x)).
{apply IHw. destruct H2. destruct H3. auto. } destruct H3.
++++ destruct H3. inversion H3.
++++ intros. simpl in H4. destruct H4. destruct H4.
+++++ subst. destruct H2. destruct H4. 
assert ((forall m, (In m p1 ->(exists y, m = inl y)) /\
(In m p ->(exists y, m = inl y)))).
{apply inl_move_implies_inl with (y:=x). split.
+ destruct H4.
++ inversion H4.
++ inversion H4. subst. apply H7.
++ inversion H4. subst. apply H7. 
+ split.
++ auto.
++ destruct H6.
+++ left. apply H6.
+++ right. apply H6. }
apply H7. auto.
+++++ apply H3 with (p:=p). split.
++++++ simpl. auto.
++++++ auto.
++
assert
(length_walk E (cast_to_left_in_walk_sum P Q E F w) <
length_walk (event_structure_sum P Q E F) w
\/
length_walk E (cast_to_left_in_walk_sum P Q E F w) =
length_walk (event_structure_sum P Q E F) w).
{ apply cast_to_left_in_walk_sum_monotonic. }
lia.
Qed.

Fact sum_equals_inr_implies_inr
`(P : PartialOrder X) `(Q : PartialOrder Y)
(E : EventStructure P) (F : EventStructure Q)
: forall w,
valid_walk (event_structure_sum P Q E F) w /\
length_walk (event_structure_sum P Q E F) w =
  length_walk F (cast_to_right_in_walk_sum P Q E F w)
-> ((exists p, w = empty_walk (event_structure_sum P Q E F) p)
\/
forall m p, (position_in_walk _ p w /\ In m p) ->
(exists x, m = inr x)).
Proof. intros. induction w.
+ left. refine (ex_intro _ p _). reflexivity.
+ right. destruct H. simpl in H0. destruct p0.
destruct s.
++ assert
(length_walk F (cast_to_right_in_walk_sum P Q E F w) <
length_walk (event_structure_sum P Q E F) w
\/
length_walk F (cast_to_right_in_walk_sum P Q E F w) =
length_walk (event_structure_sum P Q E F) w).
{ apply cast_to_right_in_walk_sum_monotonic. }
lia.
++ simpl in H0.
assert
(length_walk F (cast_to_right_in_walk_sum P Q E F w) =
length_walk (event_structure_sum P Q E F) w).
{lia. }
destruct H.
+++ inversion H.
+++ inversion H. subst. intros. destruct H3. simpl in H3.
destruct H3.
++++ subst. destruct H2. destruct H3.
assert ((forall m, (In m p ->(exists y, m = inr y)) /\
(In m p1 ->(exists y, m = inr y)))).
{apply inr_move_implies_inr with (y0:=y). split.
+ auto.
+ split.
++ auto.
++ destruct H5.
+++ right. apply H5.
+++ left. apply H5. }
apply H6 in H4. auto.
++++ subst. destruct H2. destruct H3. 
assert ((forall m, (In m p ->(exists y, m = inr y)) /\
(In m p2 ->(exists y, m = inr y)))).
{apply inr_move_implies_inr with (y0:=y). split.
+ auto.
+ split.
++ auto. 
++ destruct H5.
+++ left. apply H5.
+++ right. apply H5. }
apply H6 in H4. auto.
+++ inversion H. subst.
assert ((exists p : Position (event_structure_sum P Q E F),
         non_empty_walk (event_structure_sum P Q E F) p1 m' w' =
         empty_walk (event_structure_sum P Q E F) p) \/
      (forall (m : X + Y) (p : Position (event_structure_sum P Q E F)),
       position_in_walk (event_structure_sum P Q E F) p
         (non_empty_walk (event_structure_sum P Q E F) p1 m' w') /\
       In m p -> exists x : Y, m = inr x)).
{apply IHw. destruct H2. destruct H3. auto. } destruct H3.
++++ destruct H3. inversion H3.
++++ intros. simpl in H4. destruct H4. destruct H4.
+++++ subst. destruct H2. destruct H4. 
assert ((forall m, (In m p1 ->(exists y, m = inr y)) /\
(In m p ->(exists y, m = inr y)))).
{apply inr_move_implies_inr with (y0:=y). split.
+ destruct H4.
++ inversion H4.
++ inversion H4. subst. apply H7.
++ inversion H4. subst. apply H7.
+ split.
++ auto.
++ destruct H6.
+++ left. apply H6.
+++ right. apply H6.  }
apply H7 in H5. auto.
+++++ apply H3 with (p:=p). split.
++++++ simpl. auto.
++++++ auto.
Qed.

Fact valid_walk_is_valid_inl 
`(P : PartialOrder X) `(Q : PartialOrder Y)
(E : EventStructure P) (F : EventStructure Q):
forall w : Walk (event_structure_sum P Q E F),
     valid_walk (event_structure_sum P Q E F) w ->
valid_walk _ (cast_to_left_in_walk_sum P Q E F w).
Proof. intros. induction w.
+ simpl. apply valid_empty_walk with (p0:=(cast_to_left X Y p)).
++ reflexivity.
++ destruct H.
+++ inversion H. apply sum_valid_position_valid_inl. apply H0.
+++ inversion H.
+++ inversion H.
+ destruct H.
++ inversion H.
++ inversion H. subst. simpl.
destruct m. apply valid_one_move_walk
with (m:=x) (ep0:=ep) (p3:=(cast_to_left X Y p1))
(p4:=(cast_to_left X Y p2)).
+++ reflexivity.
+++ split.
++++ destruct H0. apply sum_valid_position_valid_inl. apply H0.
++++ split.
+++++ destruct H0. destruct H1.
++++++ apply sum_valid_position_valid_inl. auto.
+++++ destruct ep.
++++++ left. destruct H0. destruct H1. destruct H2.
+++++++ split.
++++++++ reflexivity.
++++++++ unfold move_from. destruct H2.
unfold move_from in H3.
+++++++++ split.
++++++++++ destruct H3. intros. subst. simpl. auto. 
++++++++++ intros. destruct H3. subst.
rewrite cast_to_left_is_boring. auto.
+++++++ destruct H2. inversion H2.
++++++ right. destruct H0. destruct H1. destruct H2.
+++++++ destruct H2. inversion H2.
+++++++ split.
++++++++ reflexivity.
++++++++ destruct H2. unfold move_from.
unfold move_from in H3. split.
+++++++++ destruct H3. intros. subst. simpl. auto.
+++++++++ destruct H3. rewrite cast_to_left_is_boring.
auto.
+++ apply valid_empty_walk with (p:=(cast_to_left X Y p1)).
++++ reflexivity.
++++ destruct H0. destruct H1. 
apply sum_valid_position_valid_inl. auto.
++ inversion H. subst. simpl. destruct m.
+++ destruct m'. simpl in IHw. destruct s. 
++++ apply valid_non_empty_walk
with (p3:=(cast_to_left X Y p1)) (m:=x)
(ep0:=ep) (p4:=(cast_to_left X Y p2)) (m':=(x0, b))
(w'0:=(cast_to_left_in_walk_sum P Q E F w')).
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
intros. subst. simpl. auto.
++++++++++ destruct H3. rewrite cast_to_left_is_boring.
auto.
++++++++ destruct H2. right. split.
+++++++++ apply H2.
+++++++++ unfold move_from. unfold move_from in H3. split.
++++++++++ destruct H3. intros. subst. simpl. auto.
++++++++++ destruct H3. rewrite cast_to_left_is_boring.
auto.
++++ simpl in IHw.
assert (valid_walk E (cast_to_left_in_walk_sum P Q E F w')).
{ apply IHw. destruct H0. destruct H1. apply H1. }
assert 
(target_walk _ (cast_to_left_in_walk_sum P Q E F w') = nil).
{apply cast_to_nil_inr. refine (ex_intro _ p1 _).
refine (ex_intro _ y _).
refine (ex_intro _ b _). apply H0. }
destruct (cast_to_left_in_walk_sum P Q E F w').
+++++ simpl in H2. subst p. destruct H0. destruct H2.
destruct H2.
++++++ inversion H2.
++++++ inversion H2. subst.
assert (forall m, (In m p3 ->(exists y, m = inl y)) /\
(In m p2 ->(exists y, m = inl y))).
{ apply inl_move_implies_inl with (y0:=x).
split.
+ apply H4.
+ split.
++ auto.
++ destruct H3.
+++ left. apply H3.
+++ right. apply H3. }
assert (forall m, (In m p0 ->(exists y, m = inr y)) /\
(In m p3 ->(exists y, m = inr y))).
{ apply inr_move_implies_inr with (y0:=y). split.
+ apply H4.
+ split.
++ apply H4.
++ destruct H4. destruct H6. destruct H7.
+++ left. apply H7.
+++ right. apply H7.
}
assert (p3 = nil).
{destruct p3.
+ reflexivity.
+ destruct s.
assert (exists y : Y, inl x0 = inr y).
{apply H6. simpl. left. reflexivity. }
destruct H7. inversion H7.
++ assert (forall m : X + Y,
     (In m (inr y0 :: p3) -> exists y : X, m = inl y)).
{apply H5. }
assert (exists y : X, inr y0 = inl y).
{apply H7.  simpl. left. reflexivity. }
destruct H8. inversion H8.
}
subst.
assert (p2 = (inl x) :: nil).
{ destruct H3. 
+ unfold move_from in H3. apply H3.
+ unfold move_from in H3. destruct H3. destruct H7.
inversion H7.
} subst. apply valid_one_move_walk
with (m:=x) (ep1:=ep) (p2:=cast_to_left X Y (inl x :: nil))
(p1:=nil).
+++++++ auto.
+++++++ split.
++++++++ apply sum_valid_position_valid_inl
with (Q0:=Q) (F0:=F). auto.
++++++++ split.
+++++++++ unfold valid_position. intros. split.
++++++++++ intros. simpl in H7. destruct H7. contradiction H7.
++++++++++ intros. simpl in H7. destruct H7. contradiction H7.
+++++++++ destruct H3.
++++++++++ left. split.
+++++++++++ apply H3.
+++++++++++ simpl. unfold move_from. auto.
++++++++++ right. split.
+++++++++++ apply H3.
+++++++++++ destruct H3. unfold move_from in H7.
simpl in H7. destruct H7. inversion H7.
++++++ inversion H2. subst.
assert (forall m, (In m p0 ->(exists y, m = inr y)) /\
(In m p3 ->(exists y, m = inr y))).
{ apply inr_move_implies_inr with (y0:=y). split.
+ destruct H4. destruct H5. destruct H5.
++ inversion H5.
++ inversion H5. subst. apply H7.
++ inversion H5. subst. apply H7.
+ split.
++ apply H4.
++ destruct H4. destruct H5. destruct H6.
+++ left. apply H6.
+++ right. apply H6.
}
assert (forall m, (In m p3 ->(exists y, m = inl y)) /\
(In m p2 ->(exists y, m = inl y))).
{ apply inl_move_implies_inl with (y0:=x). split.
+ apply H4.
+ split.
++ auto.
++ destruct H3.
+++ left. apply H3.
+++ right. apply H3.
}
assert (p3 = nil).
{destruct p3.
+ reflexivity.
+ destruct s.
++ assert (exists y : Y, inl x0 = inr y).
{apply H5. simpl. left. reflexivity. }
destruct H7. inversion H7.
++ assert 
(forall m : X + Y,
     (In m (inr y0 :: p3) -> exists y : X, m = inl y)).
{apply H6. }
assert (exists y : X, inr y0 = inl y).
{apply H7.  simpl. left. reflexivity. }
destruct H8. inversion H8.
}
subst.
assert (p2 = (inl x) :: nil).
{ destruct H3. 
+ unfold move_from in H3. apply H3.
+ unfold move_from in H3. destruct H3. destruct H7.
inversion H7.
} subst. simpl.
apply valid_one_move_walk with
(p2:=x :: nil) (m:=x) (ep1:=ep)
(p1:=nil).
+++++++ auto.
+++++++ split.
++++++++ 
assert (cast_to_left X Y (inl x :: nil) = x :: nil).
{simpl. auto. } rewrite <- H7.
apply sum_valid_position_valid_inl with
(Q0:=Q) (F0:=F). auto.
++++++++ split.
+++++++++ unfold valid_position. intros. split.
++++++++++ intros. simpl in H7. destruct H7.
contradiction H7.
++++++++++ intros. simpl in H7. destruct H7.
contradiction H7.
+++++++++ destruct H3.
++++++++++ left. split.
+++++++++++ apply H3.
+++++++++++ unfold move_from. auto.
++++++++++ right. split.
+++++++++++ apply H3.
+++++++++++ destruct H3.
unfold move_from in H7. destruct H7. inversion H7.
+++++ simpl in H2. subst. destruct H0. destruct H2.
destruct H2.
++++++ inversion H2.
++++++ inversion H2. subst.
assert (forall m, (In m p3 ->(exists y, m = inr y)) /\
(In m p4 ->(exists y, m = inr y))).
{ apply inr_move_implies_inr with (y0:=y). split.
+ apply H4.
+ split.
++ apply H4.
++ destruct H4. destruct H5. destruct H6.
+++ left. apply H6.
+++ right. apply H6.
}
assert (forall m, (In m p4 ->(exists y, m = inl y)) /\
(In m p2 ->(exists y, m = inl y))).
{ apply inl_move_implies_inl with (y0:=x). split.
+ apply H4.
+ split.
++ auto.
++ destruct H3.
+++ left. apply H3.
+++ right. apply H3.
}
assert (p4 = nil).
{destruct p4.
+ reflexivity.
+ destruct s.
++ assert (exists y : Y, inl x0 = inr y).
{apply H5. simpl. left. reflexivity. }
destruct H7. inversion H7.
++ assert 
(forall m : X + Y,
     (In m (inr y0 :: p4) -> exists y : X, m = inl y)).
{apply H6. }
assert (exists y : X, inr y0 = inl y).
{apply H7.  simpl. left. reflexivity. }
destruct H8. inversion H8.
}
subst.
assert (p2 = (inl x) :: nil).
{ destruct H3. 
+ unfold move_from in H3. apply H3.
+ unfold move_from in H3. destruct H3. destruct H7.
inversion H7.
} subst. simpl.
apply valid_non_empty_walk with
(p2:=x :: nil) (m:=x) (m':=p0) (ep1:=ep)
(w':=w) (p1:=nil).
+++++++ auto.
+++++++ split.
++++++++ 
assert (cast_to_left X Y (inl x :: nil) = x :: nil).
{simpl. auto. } rewrite <- H7.
apply sum_valid_position_valid_inl with
(Q0:=Q) (F0:=F). auto.
++++++++ split.
+++++++++ unfold valid_position. intros. auto. 
+++++++++ destruct H3.
++++++++++ left. split.
+++++++++++ apply H3.
+++++++++++ unfold move_from. auto.
++++++++++ right. split.
+++++++++++ apply H3.
+++++++++++ destruct H3.
unfold move_from in H7. destruct H7. inversion H7.
++++++ inversion H2. subst.
assert (forall m, (In m p3 ->(exists y, m = inr y)) /\
(In m p4 ->(exists y, m = inr y))).
{ apply inr_move_implies_inr with (y0:=y). split.
+ destruct H4. destruct H5. destruct H5.
++ inversion H5.
++ inversion H5. subst. apply H7.
++ inversion H5. subst. apply H7.
+ split.
++ apply H4.
++ destruct H4. destruct H5. destruct H6.
+++ left. apply H6.
+++ right. apply H6.
}
assert (forall m, (In m p4 ->(exists y, m = inl y)) /\
(In m p2 ->(exists y, m = inl y))).
{ apply inl_move_implies_inl with (y0:=x). split.
+ apply H4.
+ split.
++ auto.
++ destruct H3.
+++ left. apply H3.
+++ right. apply H3.
}
assert (p4 = nil).
{destruct p4.
+ reflexivity.
+ destruct s.
++ assert (exists y : Y, inl x0 = inr y).
{apply H5. simpl. left. reflexivity. }
destruct H7. inversion H7.
++ assert 
(forall m : X + Y,
     (In m (inr y0 :: p4) -> exists y : X, m = inl y)).
{apply H6. }
assert (exists y : X, inr y0 = inl y).
{apply H7.  simpl. left. reflexivity. }
destruct H8. inversion H8.
}
subst.
assert (p2 = (inl x) :: nil).
{ destruct H3. 
+ unfold move_from in H3. apply H3.
+ unfold move_from in H3. destruct H3. destruct H7.
inversion H7.
} subst. simpl.
apply valid_non_empty_walk with
(p2:=x :: nil) (m:=x) (m'0:=p0) (ep1:=ep)
(w':=w) (p1:=nil).
+++++++ auto.
+++++++ split.
++++++++ 
assert (cast_to_left X Y (inl x :: nil) = x :: nil).
{simpl. auto. } rewrite <- H7.
apply sum_valid_position_valid_inl with
(Q0:=Q) (F0:=F). auto.
++++++++ split.
+++++++++ unfold valid_position. intros. auto. 
+++++++++ destruct H3.
++++++++++ left. split.
+++++++++++ apply H3.
+++++++++++ unfold move_from. auto.
++++++++++ right. split.
+++++++++++ apply H3.
+++++++++++ destruct H3.
unfold move_from in H7. destruct H7. inversion H7.
+++ destruct m'. destruct s.
++++ simpl in IHw. apply IHw. apply H0.
++++ simpl in IHw. apply IHw. apply H0.
Qed.

Fact valid_walk_is_valid_inr
`(P : PartialOrder X) `(Q : PartialOrder Y)
(E : EventStructure P) (F : EventStructure Q):
forall w : Walk (event_structure_sum P Q E F),
     valid_walk (event_structure_sum P Q E F) w ->
valid_walk _ (cast_to_right_in_walk_sum P Q E F w).
Proof. intros. induction w.
+ simpl. apply valid_empty_walk with (p0:=(cast_to_right X Y p)).
++ reflexivity.
++ destruct H.
+++ inversion H. apply sum_valid_position_valid_inr. apply H0.
+++ inversion H.
+++ inversion H.
+ destruct H.
++ inversion H.
++ inversion H. subst. simpl. destruct m. 
+++ apply valid_empty_walk with (p:=(cast_to_right X Y p1)).
++++ reflexivity.
++++ apply sum_valid_position_valid_inr. apply H0.
+++ apply valid_one_move_walk
with (m:=y) (ep0:=ep) (p4:=(cast_to_right X Y p2))
(p3:=(cast_to_right X Y p1)).
++++ reflexivity.
++++ split.
+++++ apply sum_valid_position_valid_inr. apply H0.
+++++ split.
++++++ apply sum_valid_position_valid_inr. apply H0.
++++++ destruct H0. destruct H1. destruct H2.
++++++++ left. split.
+++++++++ apply H2.
+++++++++ unfold move_from. split.
++++++++++ destruct H2. unfold move_from in H3.
destruct H3. subst. simpl. auto.
++++++++++ destruct H2. unfold move_from in H3.
destruct H3. subst. rewrite cast_to_right_is_boring. auto.
++++++++ right. split.
+++++++++ apply H2.
+++++++++ unfold move_from. split.
++++++++++ destruct H2. unfold move_from in H3.
destruct H3. subst. simpl. auto.
++++++++++ destruct H2. unfold move_from in H3.
destruct H3. subst. rewrite cast_to_right_is_boring. auto.
++ inversion H. subst. simpl. destruct m.
+++ destruct m'. destruct s.
++++ simpl in IHw. apply IHw. apply H0.
++++ simpl in IHw. apply IHw. apply H0.
+++ destruct m'. destruct s.
++++ simpl in IHw.
assert 
(target_walk _ (cast_to_right_in_walk_sum P Q E F w') = nil).
{apply cast_to_nil_inl. refine (ex_intro _ p1 _).
refine (ex_intro _ x _).
refine (ex_intro _ b _). apply H0. }
destruct (cast_to_right_in_walk_sum P Q E F w').
+++++ simpl in H1. subst. destruct H0. destruct H1.
destruct H1.
++++++ inversion H1.
++++++ inversion H1. subst.
assert (forall m, (In m p3 ->(exists y, m = inr y)) /\
(In m p2 ->(exists y, m = inr y))).
{ apply inr_move_implies_inr with (y0:=y). split.
+ apply H3.
+ split.
++ auto.
++ destruct H2.
+++ left. apply H2.
+++ right. apply H2.
}
assert (forall m, (In m p0 ->(exists y, m = inl y)) /\
(In m p3 ->(exists y, m = inl y))).
{ apply inl_move_implies_inl with (y0:=x). split.
+ apply H3.
+ split.
++ apply H3.
++ destruct H3. destruct H5. destruct H6.
+++ left. apply H6.
+++ right. apply H6.
}
assert (p3 = nil).
{destruct p3.
+ reflexivity.
+ destruct s.
++ assert (forall m : X + Y,
     (In m (inl x0 :: p3) -> exists y : Y, m = inr y)).
{apply H4. }
assert (exists y : Y, inl x0 = inr y).
{apply H6. simpl. left. reflexivity. }
destruct H7. inversion H7.
++ assert (exists y : X, inr y0 = inl y).
{apply H5. simpl. left. reflexivity. }
destruct H6. inversion H6.
}
subst.
assert (p2 = inr y :: nil).
{destruct H2.
+ destruct H2. unfold move_from in H6. apply H6.
+ destruct H2. unfold move_from in H6. destruct H6.
inversion H6. }
subst. simpl. apply valid_one_move_walk with
(p2:=y :: nil) (m:=y) (ep1:=ep)
(p1:=nil).
+++++++ auto.
+++++++ split.
assert (cast_to_right X Y (inr y :: nil) = y :: nil).
{simpl. auto. } rewrite <- H6.
apply sum_valid_position_valid_inr with
(P0:=P) (E0:=E). auto.
++++++++ split.
+++++++++ unfold valid_position. intros. split.
++++++++++ intros. simpl in H6. destruct H6. contradiction H6.
++++++++++ intros. simpl in H6. destruct H6. contradiction H6.
+++++++++ destruct H2.
++++++++++ left. split.
+++++++++++ apply H2.
+++++++++++ unfold move_from. auto.
++++++++++ right. split.
+++++++++++ apply H2.
+++++++++++ destruct H2. unfold move_from in H6.
destruct H6. inversion H6.
++++++ inversion H1. subst.
assert (forall m, (In m p3 ->(exists y, m = inr y)) /\
(In m p2 ->(exists y, m = inr y))).
{ apply inr_move_implies_inr with (y0:=y). split.
+ apply H3.
+ split.
++ auto.
++ destruct H2.
+++ left. apply H2.
+++ right. apply H2.
}
assert (forall m, (In m p0 ->(exists y, m = inl y)) /\
(In m p3 ->(exists y, m = inl y))).
{ apply inl_move_implies_inl with (y0:=x). split.
+ destruct H3. destruct H5. destruct H5.
++ inversion H5.
++ inversion H5. subst. apply H7.
++ inversion H5. subst. apply H7.
+ split.
++ apply H3.
++ destruct H3. destruct H5. destruct H6.
+++ left. apply H6.
+++ right. apply H6.
}
assert (p3 = nil).
{destruct p3.
+ reflexivity.
+ destruct s.
++ assert (forall m : X + Y,
     (In m (inl x0 :: p3) -> exists y : Y, m = inr y)).
{apply H4. }
assert (exists y : Y, inl x0 = inr y).
{apply H6. simpl. left. reflexivity. }
destruct H7. inversion H7.
++ assert (exists y : X, inr y0 = inl y).
{apply H5. simpl. left. reflexivity. }
destruct H6. inversion H6.
}
subst.
assert (p2 = inr y :: nil).
{destruct H2.
+ destruct H2. unfold move_from in H6. apply H6.
+ destruct H2. unfold move_from in H6. destruct H6.
inversion H6. }
subst. simpl. apply valid_one_move_walk with
(p2:=y :: nil) (m:=y) (ep1:=ep)
(p1:=nil).
+++++++ auto.
+++++++ split.
assert (cast_to_right X Y (inr y :: nil) = y :: nil).
{simpl. auto. } rewrite <- H6.
apply sum_valid_position_valid_inr with
(P0:=P) (E0:=E). auto.
++++++++ split.
+++++++++ unfold valid_position. intros. split.
++++++++++ intros. simpl in H6. destruct H6. contradiction H6.
++++++++++ intros. simpl in H6. destruct H6. contradiction H6.
+++++++++ destruct H2.
++++++++++ left. split.
+++++++++++ apply H2.
+++++++++++ unfold move_from. auto.
++++++++++ right. split.
+++++++++++ apply H2.
+++++++++++ destruct H2. unfold move_from in H6.
destruct H6. inversion H6.
+++++ simpl in H1. subst. destruct H0. destruct H1.
destruct H1.
++++++ inversion H1.
++++++ inversion H1. subst.
assert (forall m, (In m p4 ->(exists y, m = inr y)) /\
(In m p2 ->(exists y, m = inr y))).
{ apply inr_move_implies_inr with (y0:=y). split.
+ apply H3.
+ split.
++ auto.
++ destruct H2.
+++ left. apply H2.
+++ right. apply H2.
}
assert (forall m, (In m p3 ->(exists y, m = inl y)) /\
(In m p4 ->(exists y, m = inl y))).
{ apply inl_move_implies_inl with (y0:=x). split.
+ apply H3.
+ split.
++ apply H3.
++ destruct H3. destruct H5. destruct H6.
+++ left. apply H6.
+++ right. apply H6.
}
assert (p4 = nil).
{destruct p4.
+ reflexivity.
+ destruct s.
++ assert (forall m : X + Y,
     (In m (inl x0 :: p4) -> exists y : Y, m = inr y)).
{apply H4. }
assert (exists y : Y, inl x0 = inr y).
{apply H6. simpl. left. reflexivity. }
destruct H7. inversion H7.
++ assert (exists y : X, inr y0 = inl y).
{apply H5. simpl. left. reflexivity. }
destruct H6. inversion H6.
}
subst.
assert (p2 = inr y :: nil).
{destruct H2.
+ destruct H2. unfold move_from in H6. apply H6.
+ destruct H2. unfold move_from in H6. destruct H6.
inversion H6. }
subst. simpl.
apply valid_non_empty_walk with
(p2:=y :: nil) (m:=y) (m':=p0) (ep1:=ep)
(w':=w) (p1:=nil).
+++++++ auto.
+++++++ split.
++++++++ 
assert (cast_to_right X Y (inr y :: nil) = y :: nil).
{simpl. auto. } rewrite <- H6.
apply sum_valid_position_valid_inr with
(P0:=P) (E0:=E). auto.
++++++++ split.
+++++++++ apply IHw.
apply valid_one_move_walk with
(p1:=p3) (m:=inl x) (ep1:=ep0) (p2:=nil).
++++++++++ auto.
++++++++++ apply H3.
+++++++++ destruct H2.
++++++++++ left. split.
+++++++++++ apply H2.
+++++++++++ unfold move_from. auto.
++++++++++ right. split.
+++++++++++ apply H2.
+++++++++++ destruct H2. unfold move_from in H6.
destruct H6. inversion H6.
++++++ inversion H1. subst.
assert (forall m, (In m p4 ->(exists y, m = inr y)) /\
(In m p2 ->(exists y, m = inr y))).
{ apply inr_move_implies_inr with (y0:=y). split.
+ apply H3.
+ split.
++ auto.
++ destruct H2.
+++ left. apply H2.
+++ right. apply H2.
}
assert (forall m, (In m p3 ->(exists y, m = inl y)) /\
(In m p4 ->(exists y, m = inl y))).
{ apply inl_move_implies_inl with (y0:=x). split.
+ destruct H3. destruct H5. destruct H5.
++ inversion H5.
++ inversion H5. subst. apply H7.
++ inversion H5. subst. apply H7.
+ split.
++ apply H3.
++ destruct H3. destruct H5. destruct H6.
+++ left. apply H6.
+++ right. apply H6.
}
assert (p4 = nil).
{destruct p4.
+ reflexivity.
+ destruct s.
++ assert (forall m : X + Y,
     (In m (inl x0 :: p4) -> exists y : Y, m = inr y)).
{apply H4. }
assert (exists y : Y, inl x0 = inr y).
{apply H6. simpl. left. reflexivity. }
destruct H7. inversion H7.
++ assert (exists y : X, inr y0 = inl y).
{apply H5. simpl. left. reflexivity. }
destruct H6. inversion H6.
}
subst.
assert (p2 = inr y :: nil).
{destruct H2.
+ destruct H2. unfold move_from in H6. apply H6.
+ destruct H2. unfold move_from in H6. destruct H6.
inversion H6. }
subst. simpl.
apply valid_non_empty_walk with
(p2:=y :: nil) (m:=y) (m'0:=p0) (ep1:=ep)
(w':=w) (p1:=nil).
+++++++ auto.
+++++++ split.
++++++++ 
assert (cast_to_right X Y (inr y :: nil) = y :: nil).
{simpl. auto. } rewrite <- H6.
apply sum_valid_position_valid_inr with
(P0:=P) (E0:=E). auto.
++++++++ split.
+++++++++ apply IHw.
apply valid_non_empty_walk with
(p2:=nil) (m:=inl x) (m'0:=m') (ep1:=ep0)
(w':=w'0) (p1:=p3).
++++++++++ auto.
++++++++++ apply H3.
+++++++++ destruct H2.
++++++++++ left. split.
+++++++++++ apply H2.
+++++++++++ unfold move_from. auto.
++++++++++ right. split.
+++++++++++ apply H2.
+++++++++++ destruct H2. unfold move_from in H6.
destruct H6. inversion H6.
++++ simpl in IHw.
apply valid_non_empty_walk with
(p4:=cast_to_right X Y p2) (m:=y) (m':=(y0,b)) (ep0:=ep)
(w'0:=cast_to_right_in_walk_sum P Q E F w')
(p3:=cast_to_right X Y p1).
+++++ auto.
+++++ split.
++++++ apply sum_valid_position_valid_inr. apply H0.
++++++ split.
+++++++ apply IHw. apply H0.
+++++++ destruct H0. destruct H1. destruct H2.
++++++++ left. split.
+++++++++ apply H2.
+++++++++ unfold move_from. unfold move_from in H2. destruct H2.
destruct H3. subst. split.
++++++++++ auto.
++++++++++ rewrite cast_to_right_is_boring. auto.
++++++++ right. split.
+++++++++ apply H2.
+++++++++ unfold move_from. unfold move_from in H2. destruct H2.
destruct H3. subst. split.
++++++++++ auto.
++++++++++ rewrite cast_to_right_is_boring. auto.
Qed.

Fact target_is_cast_inl
`(P : PartialOrder X) `(Q : PartialOrder Y)
(E : EventStructure P) (F : EventStructure Q)
: forall w p,
valid_walk _ w ->
target_walk (event_structure_sum P Q E F) w = p
->
target_walk E (cast_to_left_in_walk_sum P Q E F w) 
= (cast_to_left X Y p).
Proof. intros. destruct w.
+ simpl in H0. subst p0. simpl. reflexivity.
+ simpl. destruct p1. destruct s.
++ simpl in H0. subst. auto.
++ assert
(target_walk _ (cast_to_left_in_walk_sum P Q E F w) = nil).
{apply cast_to_nil_inr.
refine (ex_intro _ p0 _).
refine (ex_intro _ y _).
refine (ex_intro _ b _). apply H. } destruct H.
+++ inversion H.
+++ inversion H. subst. simpl.
assert (forall m, (In m p1 ->(exists y, m = inr y)) /\
(In m p2 ->(exists y, m = inr y))).
{ apply inr_move_implies_inr with (y0:=y). split.
+ apply H2.
+ split.
++ apply H2.
++ destruct H2. destruct H2. destruct H3.
+++ left. apply H3.
+++ right. apply H3.
}
assert (forall p1,
(forall (m : X + Y), In m p1 -> exists y : Y, m = inr y) ->
cast_to_left X Y p1 = nil).
{intros. induction p0.
+ auto.
+ destruct a.
++ simpl.
assert (exists y : Y, inl x = inr y).
{apply H3. simpl. left. reflexivity. }
destruct H4. inversion H4.
++ simpl. apply IHp0. intros. apply H3. right. auto.
 }
assert (cast_to_left X Y p1 = nil /\ cast_to_left X Y p2 = nil).
{split.
+ apply H3. apply H0. 
+ apply H3. apply H0. }
destruct H4. rewrite H4. rewrite H5. auto.
+++ inversion H. subst. simpl. simpl in H1. destruct m'.
destruct s.
++++ simpl.
assert (forall m, (In m p1 ->(exists y, m = inr y)) /\
(In m p2 ->(exists y, m = inr y))).
{ apply inr_move_implies_inr with (y0:=y). split.
+ destruct H2. destruct H2. destruct H2.
++ inversion H2.
++ inversion H2. subst. apply H4.
++ inversion H2. subst. apply H4.
+ split.
++ apply H2.
++ destruct H2. destruct H2. destruct H3.
+++ left. apply H3.
+++ right. apply H3.
}
assert (forall p1,
(forall (m : X + Y), In m p1 -> exists y : Y, m = inr y) ->
cast_to_left X Y p1 = nil).
{intros. induction p0.
+ auto.
+ destruct a.
++ simpl.
assert (exists y : Y, inl x0 = inr y).
{apply H3. simpl. left. reflexivity. }
destruct H4. inversion H4.
++ simpl. apply IHp0. intros. apply H3. right. auto.
 }
assert (cast_to_left X Y p1 = nil /\ cast_to_left X Y p2 = nil).
{split.
+ apply H3. apply H0. 
+ apply H3. apply H0. }
destruct H4. rewrite H4. rewrite H5. auto.
++++ rewrite H1.
assert (forall m, (In m p1 ->(exists y, m = inr y)) /\
(In m p2 ->(exists y, m = inr y))).
{ apply inr_move_implies_inr with (y1:=y). split.
+ destruct H2. destruct H2. destruct H2.
++ inversion H2.
++ inversion H2. subst. apply H4.
++ inversion H2. subst. apply H4.
+ split.
++ apply H2.
++ destruct H2. destruct H2. destruct H3.
+++ left. apply H3.
+++ right. apply H3.
}
assert (forall p1,
(forall (m : X + Y), In m p1 -> exists y : Y, m = inr y) ->
cast_to_left X Y p1 = nil).
{intros. induction p0.
+ auto.
+ destruct a.
++ simpl.
assert (exists y : Y, inl x = inr y).
{apply H3. simpl. left. reflexivity. }
destruct H4. inversion H4.
++ simpl. apply IHp0. intros. apply H3. right. auto.
 }
assert (cast_to_left X Y p1 = nil /\ cast_to_left X Y p2 = nil).
{split.
+ apply H3. apply H0. 
+ apply H3. apply H0. }
destruct H4. rewrite H5. auto.
Qed.

Fact target_is_cast_inr
`(P : PartialOrder X) `(Q : PartialOrder Y)
(E : EventStructure P) (F : EventStructure Q)
: forall w p,
valid_walk _ w ->
target_walk (event_structure_sum P Q E F) w = p
->
target_walk F (cast_to_right_in_walk_sum P Q E F w) 
= (cast_to_right X Y p).
Proof. intros. destruct w.
+ simpl. simpl in H0. subst. auto.
+ simpl in H0. simpl. subst. destruct p1. destruct s.
++ assert
(target_walk _ (cast_to_right_in_walk_sum P Q E F w) = nil).
{apply cast_to_nil_inl. 
refine (ex_intro _ p _).
refine (ex_intro _ x _).
refine (ex_intro _ b _). auto. }
rewrite H0. destruct H.
+++ inversion H.
+++ inversion H. subst.
assert (forall m, (In m p1 ->(exists y, m = inl y)) /\
(In m p2 ->(exists y, m = inl y))).
{ apply inl_move_implies_inl with (y:=x). split.
+ apply H1.
+ split.
++ apply H1.
++ destruct H1. destruct H2. destruct H3.
+++ left. apply H3.
+++ right. apply H3.
}
assert (forall p1,
(forall (m : X + Y), In m p1 -> exists y : X, m = inl y) ->
cast_to_right X Y p1 = nil).
{intros. induction p0.
+ auto.
+ destruct a.
++ simpl. apply IHp0. intros. apply H3. right. auto.
++ assert (exists x : X, inr y = inl x).
{apply H3. simpl. left. reflexivity. }
destruct H4. inversion H4.
 }
assert (cast_to_right X Y p1 = nil /\ cast_to_right X Y p2 = nil).
{split.
+ apply H3. apply H2. 
+ apply H3. apply H2. }
destruct H4. rewrite H5. auto.
+++ inversion H. subst.
assert (forall m, (In m p1 ->(exists y, m = inl y)) /\
(In m p2 ->(exists y, m = inl y))).
{ apply inl_move_implies_inl with (y:=x). split.
+ destruct H1. destruct H2. destruct H2.
++ inversion H2.
++ inversion H2. subst. apply H4.
++ inversion H2. subst. apply H4.
+ split.
++ apply H1.
++ destruct H1. destruct H2. destruct H3.
+++ left. apply H3.
+++ right. apply H3.
}
assert (forall p1,
(forall (m : X + Y), In m p1 -> exists y : X, m = inl y) ->
cast_to_right X Y p1 = nil).
{intros. induction p0.
+ auto.
+ destruct a.
++ simpl. apply IHp0. intros. apply H3. right. auto.
++ assert (exists x : X, inr y = inl x).
{apply H3. simpl. left. reflexivity. }
destruct H4. inversion H4.
 }
assert (cast_to_right X Y p1 = nil /\ cast_to_right X Y p2 = nil).
{split.
+ apply H3. apply H2. 
+ apply H3. apply H2. }
destruct H4. rewrite H5. auto.
++ simpl. auto.
Qed.

Fact nil_in_cast_inl
`(P : PartialOrder X) `(Q : PartialOrder Y)
(E : EventStructure P) (F : EventStructure Q)
: forall w, valid_walk _ w ->
position_in_walk (event_structure_sum P Q E F) nil w
->
position_in_walk E nil (cast_to_left_in_walk_sum P Q E F w).
Proof. intros. induction w.
+ simpl in H0. simpl. subst p. simpl. reflexivity.
+ simpl. destruct p0. destruct s.
++ simpl. simpl in H0. destruct H0.
+++ left. subst p. simpl. reflexivity.
+++ right. apply IHw. destruct H. 
++++ inversion H.
++++ inversion H. subst. apply 
valid_empty_walk with (p:=p1).
+++++ auto.
+++++ apply H1.
++++ inversion H. subst. apply H1.
++++ apply H0.
++
assert (target_walk _ (cast_to_left_in_walk_sum P Q E F w) = nil).
{apply cast_to_nil_inr. 
refine (ex_intro _ p _).
refine (ex_intro _ y _).
refine (ex_intro _ b _).
auto.
}
destruct (cast_to_left_in_walk_sum P Q E F w).
+++ simpl in H1. subst p0. simpl. reflexivity.
+++ simpl in H1. subst p0. simpl. left. reflexivity.
Qed.

Fact nil_in_cast_inr
`(P : PartialOrder X) `(Q : PartialOrder Y)
(E : EventStructure P) (F : EventStructure Q)
: forall w, valid_walk _ w ->
position_in_walk (event_structure_sum P Q E F) nil w
->
position_in_walk F nil (cast_to_right_in_walk_sum P Q E F w).
Proof. intros. induction w.
+ simpl in H0. simpl. subst p. simpl. reflexivity.
+ simpl. destruct p0. destruct s.
++
assert (target_walk _ (cast_to_right_in_walk_sum P Q E F w) = nil).
{apply cast_to_nil_inl. 
refine (ex_intro _ p _).
refine (ex_intro _ x _).
refine (ex_intro _ b _).
auto.
}
destruct (cast_to_right_in_walk_sum P Q E F w).
+++ simpl in H1. subst p0. simpl. reflexivity.
+++ simpl in H1. subst p0. simpl. left. reflexivity.
++ simpl. simpl in H0. destruct H0.
+++ left. subst p. simpl. reflexivity.
+++ right. apply IHw. destruct H. 
++++ inversion H.
++++ inversion H. subst.
apply valid_empty_walk with (p:=p1).
+++++ auto.
+++++ apply H1.
++++ inversion H. subst. apply H1.
++++ apply H0.
Qed.

Fixpoint cast_infinite_position_to_inl_sum
`(P : PartialOrder X) `(Q : PartialOrder Y)
(E : EventStructure P) (F : EventStructure Q)
(p : InfinitePosition (event_structure_sum P Q E F)) :
InfinitePosition E :=
match p with
| stream _ (inr m) f => 
cast_infinite_position_to_inl_sum _ _ _ _ (f tt)
| stream _ (inl m) f => 
stream E m (fun _ => 
cast_infinite_position_to_inl_sum _ _ _ _ (f tt))
end. 

Fixpoint cast_infinite_position_to_inr_sum
`(P : PartialOrder X) `(Q : PartialOrder Y)
(E : EventStructure P) (F : EventStructure Q)
(p : InfinitePosition (event_structure_sum P Q E F)) :
InfinitePosition F :=
match p with
| stream _ (inl _) f => 
cast_infinite_position_to_inr_sum _ _ _ _ (f tt)
| stream _ (inr m) f => stream _ m 
(fun _ => cast_infinite_position_to_inr_sum _ _ _ _ (f tt))
end. 

Instance asynchronous_arena_sum
`(P : PartialOrder X) `(Q : PartialOrder Y)
(E : EventStructure P) (F : EventStructure Q)
(A : AsynchronousArena P E) (B : AsynchronousArena Q F)
(positive1 : finite_payoff (inl (nil : Position E)) = (-1)%Z)
(positive2 : finite_payoff (inl (nil : Position F)) = (-1)%Z)
: AsynchronousArena (partial_order_sum P Q)
(event_structure_sum P Q E F) :=
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
(length_walk _ (cast_to_left_in_walk_sum P Q E F w)) then
finite_payoff (inr (cast_to_left_in_walk_sum P Q E F w)) else
if beq_nat (length_walk _ w) 
(length_walk _ (cast_to_right_in_walk_sum P Q E F w)) then
finite_payoff (inr (cast_to_right_in_walk_sum P Q E F w)) else
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
infinite_payoff (cast_infinite_position_to_inl_sum _ _ _ _ p)
| stream _ (inr _) _ => 
infinite_payoff (cast_infinite_position_to_inr_sum _ _ _ _ p)
end
}.
Proof.
- simpl. left. reflexivity.
- intros. apply initial_in_sum_is_initial in H.
destruct H.
+ destruct H. destruct H. subst. 
assert (polarity x = true).
{destruct (polarity x) eqn:POL.
+ auto.
+ apply polarity_first in H0. apply H0 in POL. 
rewrite positive1 in POL. lia. }
rewrite H. split.
++ intros. auto.
++ intros. inversion H1.
+ destruct H. destruct H. subst.
assert (polarity x = true).
{destruct (polarity x) eqn:POL.
+ auto.
+ apply polarity_first in H0. apply H0 in POL. 
rewrite positive2 in POL. lia. }
rewrite H. split.
++ intros. auto.
++ intros. inversion H1.
- intros. apply second_in_sum_is_second in H. destruct H.
+ destruct H. destruct H. subst.
assert (polarity x = false).
{destruct (polarity x) eqn:POL.
+ apply polarity_second in H0. apply H0 in POL. 
rewrite positive1 in POL. lia.
+ auto. }
rewrite H. split.
++ intros. inversion H1.
++ intros. auto.
+ destruct H. destruct H. subst.
assert (polarity x = false).
{destruct (polarity x) eqn:POL.
+ apply polarity_second in H0. apply H0 in POL. 
rewrite positive2 in POL. lia.
+ auto. }
rewrite H. split.
++ intros. inversion H1.
++ intros. auto.
- intros. destruct H. subst. simpl. apply initial_null
with (p0:=cast_to_left X Y p).
+ split.
++ destruct H.
+++ inversion H. subst. apply valid_empty_walk
with (p:=cast_to_left X Y p0).
++++ auto.
++++ apply sum_valid_position_valid_inl. auto.
+++ inversion H.
+++ inversion H.
++ auto.
- intros. destruct H. destruct H0. destruct H1.


destruct (length_walk (event_structure_sum P Q E F) w =?
  length_walk E (cast_to_left_in_walk_sum P Q E F w)) eqn:H'.
+ apply beq_nat_true in H'. rewrite H' in H0.
assert (position_in_walk E nil (cast_to_left_in_walk_sum P Q E F w)).
{ apply nil_in_cast_inl. apply H. apply H2. }
assert (target_walk E (cast_to_left_in_walk_sum P Q E F w) 
= (cast_to_left X Y p)).
{apply target_is_cast_inl. apply H. apply H1. }
assert (valid_walk E (cast_to_left_in_walk_sum P Q E F w)).
{apply valid_walk_is_valid_inl. apply H. }
assert (finite_payoff (inr (cast_to_left_in_walk_sum P Q E F w)) 
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
  length_walk F (cast_to_right_in_walk_sum P Q E F w)) eqn:H''.
apply beq_nat_true in H''.
rewrite H'' in H0.
assert (position_in_walk F nil (cast_to_right_in_walk_sum P Q E F w)).
{apply nil_in_cast_inr. apply H. apply H2. }
assert (target_walk F (cast_to_right_in_walk_sum P Q E F w) 
= (cast_to_right X Y p)).
{apply target_is_cast_inr. apply H. apply H1. }
assert (valid_walk F (cast_to_right_in_walk_sum P Q E F w)).
{apply valid_walk_is_valid_inr. apply H. }
assert (finite_payoff (inr (cast_to_right_in_walk_sum P Q E F w)) 
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
(A : AsynchronousArena P E) (B : AsynchronousArena Q F)
(positive1 : finite_payoff (inl (nil : Position E)) = (-1)%Z)
(positive2 : finite_payoff (inl (nil : Position F)) = (-1)%Z)
`(X : Group G)
`(Y : Group H)
`(X' : Group G')
`(Y' : Group H')
(Game : AsynchronousGame P E A X Y)
(Game' : AsynchronousGame Q F B X' Y')
: AsynchronousGame 
(partial_order_sum P Q)
(event_structure_sum P Q E F)
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

Instance canonical_sum
`(C1 : CanonicalRepresentation Index f g h payoffs)
`(C2 : CanonicalRepresentation Index' f' g' h' payoffs')
(negative1 : forall (i : Index), finite_payoff
(inl (nil : Position (structures i))) = (1)%Z)
(negative2 : forall (i : Index'), finite_payoff
(inl (nil : Position (structures i))) = (1)%Z)
:
CanonicalRepresentation (Index + Index')
(fun i => match i with
| inl x => f x
| inr x => f' x
end)
(fun i => match i with
| inl x => g x
| inr x => g' x
end)
(fun i => match i with
| inl x => h x
| inr x => h' x
end)
(fun i => match i with
| inl x => payoffs x
| inr x => payoffs' x
end)
:= {
 posets i := match i with
| inl x => posets x
| inr x => posets x
end ;
structures i := match i with
| inl x => structures x
| inr x => structures x
end ;
arenas i := match i with
| inl x => arenas x
| inr x => arenas x
end ;
left_groups i := match i with
| inl x => left_groups x
| inr x => left_groups x
end ;
right_groups i := match i with
| inl x => right_groups x
| inr x => right_groups x
end ;
games i := match i with
| inl x => games x
| inr x => games x
end ;
}.