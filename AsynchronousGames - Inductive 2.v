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

Inductive leq_sum 
`(P : PartialOrder (sigT (f : Index -> Type)) ) 
`(Q : PartialOrder (sigT (f' : Index' -> Type)))
: (sigT ( 
fun x => match x with
| inl m => f m
| inr m => f' m
end)  ) -> 
(sigT ( 
fun x => match x with
| inl m => f m
| inr m => f' m
end) ) -> Prop :=
| leq_sum_left : forall (i j : Index) (p : f i) (q : f j) x y, 
leq (existT _ i p) (existT _ j q) -> 
x = (existT _  (inl i) p) ->
y = (existT _  (inl j) q) ->
leq_sum _ _ x y
| leq_sum_right : forall (i j : Index') (p : f' i) (q : f' j) x y, 
leq (existT _ i p) (existT _ j q) -> 
x = (existT _  (inr i) p) ->
y = (existT _  (inr j) q) ->
leq_sum _ _ x y.

Instance partial_order_sum 
`(P : PartialOrder (sigT (f : Index -> Type)) ) 
`(Q : PartialOrder (sigT (f' : Index' -> Type))) :
PartialOrder (sigT (
fun x => match x with
| inl m => f m
| inr m => f' m
end)) := { leq x y := leq_sum P Q x y }.
Proof.
- intros. destruct x. destruct x.
+ apply leq_sum_left with 
(i0:=i) (j:=i) (p:=y) (q:=y).
++ apply reflexive.
++ reflexivity.
++ reflexivity.
+ apply leq_sum_right with 
(i0:=i) (j:=i) (p:=y) (q:=y).
++ apply reflexive.
++ reflexivity.
++ reflexivity.
- intros. destruct x. destruct y. destruct H.
inversion H. 
+ subst. inversion H2. subst. apply
inj_pair2 in H2. subst. inversion H3. subst. apply
inj_pair2 in H3. subst. clear H5. clear H6. clear H.
inversion H0.
++ subst. inversion H2. subst. apply
inj_pair2 in H2. subst. inversion H3. subst. apply
inj_pair2 in H3. subst. clear H0.
assert ((existT f j0 q0) = (existT f i0 p0)).
{apply anti_symmetric. auto. }
inversion H0. reflexivity.
++ subst. inversion H2. 
+ subst. inversion H2. subst. apply
inj_pair2 in H2. subst. inversion H3. subst. apply
inj_pair2 in H3. subst. clear H5. clear H6. clear H.
inversion H0.
++ subst. inversion H2. 
++ subst. inversion H2. subst. apply
inj_pair2 in H2. subst. inversion H3. subst. apply
inj_pair2 in H3. subst. clear H0.
assert ((existT f' j0 q0) = (existT f' i0 p0)).
{apply anti_symmetric. auto. }
inversion H0. reflexivity.
- intros. destruct x. destruct y. destruct z.
destruct H. inversion H.
+ subst. inversion H2. subst. apply
inj_pair2 in H2. subst. inversion H3. subst. apply
inj_pair2 in H3. subst. clear H5. clear H6. clear H.
inversion H0.
++ subst. inversion H2. subst. apply
inj_pair2 in H2. subst. inversion H3. subst. apply
inj_pair2 in H3. subst. clear H0.
assert (leq (existT f i p) (existT f j0 q0)).
{apply transitive with (y:= (existT f i0 p0)). auto. }
apply leq_sum_left with 
(i1:=i) (j:=j0) (p1:=p) (q:=q0).
+++ auto.
+++ auto.
+++ auto.
++ subst. inversion H2. 
+ subst. inversion H2. subst. apply
inj_pair2 in H2. subst. inversion H3. subst. apply
inj_pair2 in H3. subst. clear H5. clear H6. clear H.
inversion H0.
++ subst. inversion H2. 
++ subst. inversion H2. subst. apply
inj_pair2 in H2. subst. inversion H3. subst. apply
inj_pair2 in H3. subst. clear H0.
assert (leq (existT f' i p) (existT f' j0 q0)).
{apply transitive with (y:= (existT f' i0 p0)). auto. }
apply leq_sum_right with 
(i1:=i) (j:=j0) (p1:=p) (q:=q0).
+++ auto.
+++ auto.
+++ auto.
Defined.

Instance event_structure_tensor
`(P : PartialOrder (sigT (f : Index -> Type))) 
`(Q : PartialOrder (sigT (f' : Index' -> Type)))
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

Instance canonical_tensor
`(C1 : CanonicalRepresentation Index f g h payoffs p)
`(C2 : CanonicalRepresentation Index' f' g' h' payoffs' p')
(positive1 : p = true)
(positive2 : p = true) :
CanonicalRepresentation (Index * Index')
(fun i => sum (f (fst i)) (f' (snd i) ) )
(fun i => prod (g (fst i)) (g' (snd i)))
(fun i => prod (h (fst i)) (h' (snd i)))
(fun i => tensor (payoffs (fst i)) (payoffs' (snd i)))
true
:= {
posets i := partial_order_sum 
(_ : (PartialOrder (f (fst i)))) 
(_ : (PartialOrder (f'(snd i)))) ;
structures i := event_structure_tensor
(_ : (PartialOrder (f (fst i))))
(_ : (PartialOrder (f' (snd i))))
(_ : (EventStructure (posets (fst i))))
(_ : (EventStructure (posets (snd i)))) ;
}.


