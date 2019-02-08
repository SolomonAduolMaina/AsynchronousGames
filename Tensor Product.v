Require Import Lia.
Require Import List.
Require Import ZArith.
Require Import Init.Nat.
Require Import Logic.Eqdep.
Require Import Logic.Eqdep_dec.
Require Import Arith.PeanoNat.
Require Import Bool.Bool.

Record PartialOrder :=
  {
    I : Type; 
    N : I -> Type;
    M := {i : I & (sum unit (N i))};
    (* the set of moves is given by a choice of component, and either
       the initial move in that component (unit) or a non-initial move
       in that component. *)

    leq : M -> M -> Prop;
    (*eq_bool : M -> M -> bool;*)

    reflexive : forall (x : M), leq x x;
    anti_symmetric : forall (x y : M), leq x y /\ leq y x -> x = y;
    transitive : forall (x y z : M), leq x y /\ leq y z -> leq x z;

    (*eq_bool_is_eq : forall (x y : M), eq_bool x y = true <-> x = y;*)
  }.

Inductive leq_tensor (P Q : PartialOrder) :
{i : ((I P) * (I Q)) & (sum unit (sum (N P (fst i)) (N Q (snd i)))) } ->
{i : ((I P) * (I Q)) & (sum unit (sum (N P (fst i)) (N Q (snd i)))) } ->
Prop :=
| leq_tensor_least : forall i j m, 
leq_tensor P Q (existT _ (i, j) (inl tt)) (existT _ (i, j) m)
| leq_tensor_left : forall i j m m' a b,
leq P (existT _ i (inr m)) (existT _ i (inr m')) ->
a = (existT _ (i, j) (inr (inl m))) ->
b = (existT _ (i, j) (inr (inl m'))) ->
leq_tensor P Q a b
| leq_tensor_right : forall i j m m' a b, 
leq Q (existT _ j (inr m)) (existT _ j (inr m')) -> 
a = (existT _ (i, j) (inr (inr m))) ->
b = (existT _ (i, j) (inr (inr m'))) ->
leq_tensor P Q a b.

Definition partial_order_tensor (P Q : PartialOrder) : PartialOrder.
  refine({| 
            I := (I P) * (I Q);
            N x := sum (N P (fst x)) (N Q (snd x));
            leq := leq_tensor P Q
         |}).
Proof. 
- intros.
+ destruct x. destruct x. destruct s.
++ destruct u. apply leq_tensor_least.
++ destruct s.
+++ apply leq_tensor_left with (i:=i) (j:=i0) (m:=n) (m':=n).
++++ apply reflexive.
++++ auto.
++++ auto.
+++ apply leq_tensor_right with (i:=i) (j:=i0) (m:=n) (m':=n).
++++ apply reflexive.
++++ auto.
++++ auto.
- intros. destruct x. destruct y. destruct H. inversion H.
+ subst. inversion H0.
++ subst. apply inj_pairT2 in H3. subst. apply inj_pairT2 in H6.
subst. apply inj_pairT2 in H5. subst. auto.
++ subst. apply inj_pairT2 in H5. subst. inversion H2.
subst. apply inj_pairT2 in H2. inversion H2. subst.
apply inj_pairT2 in H3. subst. apply inj_pairT2 in H4. inversion H4.
++ subst. apply inj_pairT2 in H5. subst. inversion H2. subst.
apply inj_pairT2 in H2. subst. apply inj_pairT2 in H3. subst.
apply inj_pairT2 in H4. inversion H4.
+ subst. inversion H3. subst. inversion H2. subst.
apply inj_pairT2 in H2. subst. apply inj_pairT2 in H6. subst.
auto. inversion H0.
++ subst. inversion H5. subst. apply inj_pairT2 in H5.
inversion H5. subst. apply inj_pairT2 in H4. inversion H4. subst.
assert 
((existT (fun i : I P => (unit + N P i)%type) i0 (inr m0)) =
       (existT (fun i : I P => (unit + N P i)%type) i0 (inr m'0))).
{apply anti_symmetric. auto. }
apply inj_pairT2 in H6. inversion H6. auto.
++ subst. inversion H5. 
+ subst. inversion H3. subst. inversion H2. subst.
apply inj_pairT2 in H7. subst. apply inj_pairT2 in H3. subst.
inversion H0.
++ subst. inversion H5. 
++ subst. inversion H5. subst. apply inj_pairT2 in H5. inversion H5.
subst. apply inj_pairT2 in H4. inversion H4. subst.
assert (
(existT (fun i : I Q => (unit + N Q i)%type) j0 (inr m0)) = 
(existT (fun i : I Q => (unit + N Q i)%type) j0 (inr m'0)) ).
{ apply anti_symmetric. auto. }
apply inj_pairT2 in H7. inversion H7. auto.
- intros. destruct H. inversion H.
+ subst. inversion H0.
++ subst. apply leq_tensor_least.
++ subst. inversion H2. subst. apply leq_tensor_least.
++ subst. inversion H2. subst. apply leq_tensor_least.
+ subst. inversion H0.
++ subst. inversion H3. subst. apply inj_pairT2 in H3.
inversion H3. subst.
assert (leq P
       (existT (fun i : I P => (unit + N P i)%type) i0 (inr m))
       (existT (fun i : I P => (unit + N P i)%type) i0 (inr m'0))).
{apply transitive with (y:=
(existT (fun i : I P => (unit + N P i)%type) i0 (inr m0))). auto. }
apply leq_tensor_left with (i:=i0) (j:=j0) (m:=m) (m':=m'0). auto.
auto. auto.
++ subst. inversion H3.
+ subst. inversion H0.
++ subst. inversion H3.
++ subst. inversion H3. subst. apply inj_pairT2 in H3. inversion H3.
subst.
assert (leq Q
       (existT (fun i : I Q => (unit + N Q i)%type) j0 (inr m))
       (existT (fun i : I Q => (unit + N Q i)%type) j0 (inr m'0))).
{apply transitive with (y:=
(existT (fun i : I Q => (unit + N Q i)%type) j0 (inr m0))). auto. }
apply leq_tensor_right with (i:=i0) (j:=j0) (m:=m) (m':=m'0). auto.
auto. auto.
Defined.

Record EventStructure := 
  {
    P : PartialOrder;
    incompatible : (M P) -> (M P) -> Prop;

    ideal : (M P)  -> list (M P);

    symmetric : forall x y, incompatible x y -> incompatible y x;
    irreflexive : forall x, not (incompatible x x);
    ideal_finite : forall x y, leq P y x <-> In y (ideal x);
    incompatible_closed : forall x y z,
        (incompatible x y) /\ (leq P y z) -> incompatible x z
  }.

Inductive incompatible_tensor (E F : EventStructure) :
(M (partial_order_tensor (P E) (P F))) ->
(M (partial_order_tensor (P E) (P F))) ->
Prop :=
| incomp_tensor_least : forall i j i' j' m m',
((i <> i') \/ (j <> j')) ->
incompatible_tensor E F (existT _ (i, j) m) (existT _ (i', j') m')
| incomp_tensor_left : forall index m m' a b,
incompatible E (existT _ (fst index) (inr m)) 
(existT _ (fst index) (inr m')) ->
a = (existT _ index (inr (inl m))) ->
b = (existT _ index (inr (inl m'))) ->
incompatible_tensor E F a b
| incomp_tensor_right : forall index m m' a b, 
incompatible F (existT _ (snd index) (inr m)) 
(existT _ (snd index) (inr m')) ->
a = (existT _ index (inr (inr m))) ->
b = (existT _ index (inr (inr m'))) ->
incompatible_tensor E F a b.

Definition event_structure_tensor (E F : EventStructure) : EventStructure.
  refine({| 
P := partial_order_tensor (P E) (P F);
incompatible := incompatible_tensor E F;
ideal m := match m with
| existT _ (i, j) (inl tt) => (existT _ (i, j) (inl tt)) :: nil
| existT _ (i, j) (inr (inl m)) =>
map (fun x => match x with
| existT _ i (inl tt) => existT _ (i, j) (inl tt)
| existT _ i (inr m) => existT _ (i, j) (inr (inl m))
end) (ideal E (existT _ i (inr m)))
| existT _ (i, j) (inr (inr m)) =>
map (fun x => match x with
| existT _ j (inl tt) => existT _ (i, j) (inl tt)
| existT _ j (inr m) => existT _ (i, j) (inr (inr m))
end) (ideal F (existT _ j (inr m)))
end;
         |}).
Proof.
- intros. inversion H.
+ subst. apply incomp_tensor_least. intuition.
+ subst. inversion H.
++ subst. inversion H4. subst. intuition.
++ subst. inversion H3. subst. apply inj_pairT2 in H6. subst.
apply inj_pairT2 in H2. inversion H2. subst.
apply incomp_tensor_left with (m:=m'0) (m':=m0).
+++ apply symmetric. auto.
+++ auto.
+++ auto.
++ subst. inversion H3.
+ subst. apply incomp_tensor_right with (m:=m') (m':=m).
++ apply symmetric. auto.
++ auto.
++ auto.
- unfold not. intros. inversion H.
+ subst. intuition.
+ subst. apply inj_pairT2 in H2. inversion H2. subst.
assert (~ incompatible E
       (existT (fun i : I (P E) => (unit + N (P E) i)%type)
          (fst index) (inr m'))
       (existT (fun i : I (P E) => (unit + N (P E) i)%type)
          (fst index) (inr m'))).
{apply irreflexive. } contradiction H1.
+ subst. apply inj_pairT2 in H2. inversion H2. subst.
assert (~ incompatible F
       (existT (fun i : I (P F) => (unit + N (P F) i)%type)
          (snd index) (inr m'))
       (existT (fun i : I (P F) => (unit + N (P F) i)%type)
          (snd index) (inr m'))).
{apply irreflexive. } contradiction H1.
- intros. simpl. destruct x.
+ destruct x. destruct y.
++ destruct x. destruct s.
+++ simpl. destruct u.
++++

Definition Position (E : EventStructure) := list (M (P E)).

Definition valid_position (E : EventStructure) (p : Position E) :=
forall m n, (In n p -> leq (P E) m n -> In m p)
/\
(In m p /\ In n p ->  not (incompatible E m n)).

Definition move_from (E : EventStructure) (p q: Position E) 
(m : (M (P E))) :=
(In m q) /\ (~ In m p) /\ (forall n, In n p -> In n q).

Definition Path (E: EventStructure) := prod (Position E) (list (M (P E))).


Definition valid_path (E: EventStructure) (i : (I (P E))) (p : Path E i) :=
forall n, 0 <= n <= length (snd p) ->
(valid_position E i ((fst p) ++ (firstn n (snd p))) /\
(n > 0 -> move_from E i (nth (n-1) (snd p) (inl i))
((fst p) ++ (firstn (n-1) (snd p))) 
((fst p) ++ (firstn n (snd p))))).

Definition Walk (E: EventStructure) (i j : (I (P E))) :=
prod (Path E i) (Path E j).

Definition valid_walk (E: EventStructure) (i j : (I (P E))) (w : Walk E i j) := 
valid_path E i (fst w) /\ valid_path E j (snd w) /\
(forall (EQ:j = i), 
forall (x: I (P E) + N (P E) i), 
In x (fst (fst w)) <-> In x (eq_rect j (Position E) (fst (snd w)) _ EQ)) 
/\
(~ i = j -> (fst (fst w)) = nil /\ (fst (snd w)) = nil).

Definition second_move (P : PartialOrder) (i : I P) (m : N P i) :=
forall n, leq P i n m -> n = m.

Fact sum_injective A B :
(forall a1 a2, a1 = a2 <-> (inl a1 : A + B) = inl a2)
/\
(forall b1 b2, b1 = b2 <-> (inr b1 : A + B) = inr b2).
Proof. intros. split.
+ unfold iff. split.
++ intros. subst. auto.
++ intros. inversion H. auto.
+ unfold iff. split.
++ intros. subst. auto.
++ intros. inversion H. auto.
Qed.

Fact second_in_tensor_is_second (E F : EventStructure)
(i : I (P (event_structure_tensor E F)))
(m : N (P (event_structure_tensor E F)) i) :
second_move (P (event_structure_tensor E F)) i m ->
(exists a, m = inl a /\ second_move (P E) (fst i) a)
\/
(exists a, m = inr a /\ second_move (P F) (snd i) a).
Proof. intros. unfold second_move in H. destruct m.
+ left. refine (ex_intro _ n _). split.
++ auto.
++ unfold second_move. intros.
apply sum_injective with (A := N (P E) (fst i))
(B := N (P F) (snd i)). apply H. simpl. auto.
+ right. refine (ex_intro _ n _). split.
++ auto.
++ unfold second_move. intros.
apply sum_injective with (A := N (P E) (fst i))
(B := N (P F) (snd i)). apply H. simpl. auto.
Qed.

Inductive Infinity : Type :=
| plus_infinity : Infinity
| minus_infinity : Infinity.

Inductive InfinitePosition (E : EventStructure) (i : I (P E)): Type := 
| stream : (I (P E) + N (P E) i) -> (unit -> InfinitePosition E i)
-> InfinitePosition E i.

Record AsynchronousArena := {
E : EventStructure;
polarity : forall i, (I (P E) + N (P E) i) -> bool;
finite_payoff_position : forall i, Position E i -> Z;
finite_payoff_walk : forall i j, Walk E i j -> Z;
infinite_payoff : forall i, InfinitePosition E i -> Infinity;

initial_payoff : forall i,
finite_payoff_position i nil = (-1)%Z \/ finite_payoff_position i nil = (1)%Z;

polarity_first : forall i,
(polarity i (inl i) = true -> finite_payoff_position i nil = (-1)%Z)
/\
(polarity i (inl i) = false -> finite_payoff_position i nil = (1)%Z);

polarity_second :
forall i m, second_move (P E) i m -> 
(polarity i (inr m) = true -> finite_payoff_position i nil = (-1)%Z)
/\
(polarity i (inr m) = false -> finite_payoff_position i nil = (1)%Z);

initial_null :
forall i j (w : Walk E i j),
((*valid_walk E i j w /\*) snd (fst w) = nil /\ snd (snd w) = nil) -> 
finite_payoff_walk i j w = 0%Z;

(*noninitial_payoff :
forall i j (w : Walk E i j) (p : Position E i),
(valid_walk E i j w /\
((length (snd (fst w)) > 0) \/  (length (snd (fst w)) > 0)) /\ 
(fst (fst w)) = nil) -> 
finite_payoff_walk i j w = 
finite_payoff_position j ((fst (snd w)) ++ (snd (snd w)))
*)
}.

Fixpoint cast_tensor_to_left (E F : EventStructure)
(i : I (P E)) (j : I (P F))
(p : Position (event_structure_tensor E F) (i,j)) :
Position E i := 
match p with
| nil => nil
| inl (k, l) :: xs => 
(match eqsum_index _ i k, eqsum_index _ j l with
| left _, left _ => inl i :: (cast_tensor_to_left E F i j xs)
| _, _ => cast_tensor_to_left E F i j xs
end)
| inr (inl m) :: xs => inr m :: (cast_tensor_to_left E F i j xs)
| _ :: xs => cast_tensor_to_left E F i j xs
end.

Fixpoint cast_tensor_to_right (E F : EventStructure)
(i : I (P E)) (j : I (P F))
(p : Position (event_structure_tensor E F) (i,j)) :
Position F j := 
match p with
| nil => nil
| inl (k, l) :: xs => 
(match eqsum_index _ i k, eqsum_index _ j l with
| left _, left _ => inl j :: (cast_tensor_to_right E F i j xs)
| _, _ => cast_tensor_to_right E F i j xs
end)
| inr (inr m) :: xs => inr m :: (cast_tensor_to_right E F i j xs)
| _ :: xs => cast_tensor_to_right E F i j xs
end.

Fact cast_tensor_inl_is_boring E F : forall i j p,
(forall k, In (inl k) (cast_tensor_to_left E F i j p) <->
(k = i) /\ In (inl (i,j)) p)
/\
(forall m, In (inr (inl m)) p <-> In (inr m) (cast_tensor_to_left E F i j p)).
Proof. intros. split.
+ unfold iff.
++ split. 
+++ intros. induction p.
++++ contradiction H.
++++ destruct a.
+++++ simpl cast_tensor_to_left in H. destruct i0. 
destruct (eqsum_index (P E) i i0).
++++++ destruct (eqsum_index (P F) j i1).
+++++++ subst. destruct H.
++++++++ inversion H. subst. split.
+++++++++ auto.
+++++++++ left. auto.
++++++++ apply IHp in H. split.
+++++++++ apply H.
+++++++++ left. auto.
+++++++ apply IHp in H. split.
++++++++ apply H.
++++++++ right. apply H.
++++++ apply IHp in H. split.
+++++++ apply H.
+++++++ right. apply H.
+++++ simpl cast_tensor_to_left in H. destruct n.
++++++ destruct H.
+++++++ inversion H.
+++++++ apply IHp in H. split.
++++++++ apply H.
++++++++ right. apply H.
++++++ apply IHp in H. split.
+++++++ apply H.
+++++++ right. apply H.
+++ intros. destruct H. subst. induction p.
++++ contradiction H0.
++++ destruct H0.
+++++ subst. simpl cast_tensor_to_left.
destruct (eqsum_index (P E) i i).
++++++ destruct (eqsum_index (P F) j j).
+++++++ left. auto.
+++++++ contradiction n. auto.
++++++ contradiction n. auto.
+++++ apply IHp in H. destruct a.
++++++ simpl. destruct i0. destruct (eqsum_index (P E) i i0).
+++++++ destruct (eqsum_index (P F) j i1).
++++++++ subst. right. auto.
++++++++ auto.
+++++++ auto.
++++++ simpl. destruct n.
+++++++ right. auto.
+++++++ auto.
+ intros. unfold iff. split.
++ intros. induction p.
+++ contradiction H.
+++ destruct a.
++++ destruct H.
+++++ inversion H.
+++++ apply IHp in H. simpl. destruct i0.
destruct (eqsum_index (P E) i i0).
++++++ destruct (eqsum_index (P F) j i1).
+++++++ subst. right. auto.
+++++++ auto.
++++++ auto.
++++ destruct H.
+++++ inversion H. subst. simpl. left. auto.
+++++ simpl. destruct n.
++++++ right. apply IHp in H. auto.
++++++ apply IHp in H. auto.
++ intros. induction p.
+++ contradiction H.
+++ destruct a.
++++ simpl in H. destruct i0. destruct (eqsum_index (P E) i i0).
+++++ destruct (eqsum_index (P F) j i1).
++++++ subst. destruct H.
+++++++ inversion H.
+++++++ right. apply IHp in H. auto.
++++++ right. apply IHp in H. auto.
+++++ right. apply IHp in H. auto.
++++ simpl in H. destruct n. destruct H.
+++++ inversion H. left. auto.
+++++ right. apply IHp in H. auto.
+++++ right. apply IHp in H. auto.
Qed.

Fact cast_tensor_inr_is_boring E F : forall i j p,
(forall k, In (inl k) (cast_tensor_to_right E F i j p) <->
(k = j) /\ In (inl (i,j)) p)
/\
(forall m, In (inr (inr m)) p <-> In (inr m) (cast_tensor_to_right E F i j p)).
Proof. intros. split.
+ intros. unfold iff. split.
++ intros. induction p.
+++ contradiction H.
+++ destruct a.
++++ simpl cast_tensor_to_right in H. destruct i0. 
destruct (eqsum_index (P E) i i0).
+++++ destruct (eqsum_index (P F) j i1).
++++++ subst. destruct H.
+++++++ inversion H. subst. split.
++++++++ auto.
++++++++ left. auto.
+++++++ apply IHp in H. split.
++++++++ apply H.
++++++++ right. apply H.
++++++ subst. apply IHp in H. split.
+++++++ apply H.
+++++++ right. apply H.
+++++ apply IHp in H. split.
++++++ apply H.
++++++ right. apply H.
++++ simpl cast_tensor_to_right in H. destruct n.
+++++ apply IHp in H. split.
++++++ apply H.
++++++ right. apply H.
+++++ destruct H.
++++++ inversion H.
++++++ apply IHp in H. split.
+++++++ apply H.
+++++++ right. apply H.
++ intros. destruct H. subst. induction p.
+++ contradiction H0.
+++ simpl cast_tensor_to_right. destruct a.
++++ destruct i0. destruct (eqsum_index (P E) i i0).
+++++ destruct (eqsum_index (P F) j i1).
++++++ subst. left. auto.
++++++ subst. destruct H0.
+++++++ inversion H. subst. contradiction n. auto.
+++++++ apply IHp in H. auto.
+++++ destruct H0.
++++++ inversion H. subst. contradiction n. auto.
++++++ apply IHp in H. auto.
++++ destruct n.
+++++ destruct H0.
++++++ inversion H.
++++++ apply IHp in H. auto.
+++++ destruct H0.
++++++ inversion H.
++++++ apply IHp in H. right. auto.
+ intros. unfold iff. split.
++ intros. induction p.
+++ contradiction H.
+++ destruct a.
++++ destruct H.
+++++ inversion H.
+++++ simpl cast_tensor_to_right. destruct i0.
destruct (eqsum_index (P E) i i0).
++++++ destruct (eqsum_index (P F) j i1).
+++++++ subst. apply IHp in H. right. auto.
+++++++ apply IHp in H. auto.
++++++ apply IHp in H. auto.
++++ simpl cast_tensor_to_right. destruct n.
+++++ destruct H.
++++++ inversion H.
++++++ apply IHp in H. auto.
+++++ destruct H.
++++++ inversion H. left. auto.
++++++ apply IHp in H. right. auto.
++ intros. induction p.
+++ contradiction H.
+++ destruct a.
++++ simpl cast_tensor_to_right in H. destruct i0.
destruct (eqsum_index (P E) i i0).
+++++ destruct (eqsum_index (P F) j i1).
++++++ subst. destruct H.
+++++++ inversion H.
+++++++ apply IHp in H. right. auto.
++++++ subst. apply IHp in H. right. auto.
+++++ apply IHp in H. right. auto.
++++ simpl cast_tensor_to_right in H. destruct n.
+++++ apply IHp in H. right. auto.
+++++ destruct H.
++++++ inversion H. left. auto.
++++++ apply IHp in H. right. auto.
Qed.


Fact cast_not_nil_implies_not_nil E F : forall i j p,
(~ (cast_tensor_to_left E F i j p) = nil \/ 
~ (cast_tensor_to_right E F i j p) = nil)
-> ~ p = nil.
Proof. intros. destruct H; unfold not in H; unfold not; intros;
apply H; subst; simpl in H; simpl; auto.
Qed.

(*Fact cast_monotonic E F : forall i j p,
length (cast_tensor_to_left E F i j p) <= length p /\ 
length (cast_tensor_to_right E F i j p) <= length p.
Proof. intros. induction p.
+ auto.
+ destruct a.
++ destruct i0. simpl. destruct (eqsum_index (P E) i i0).
+++ destruct (eqsum_index (P F) j i1).
++++ subst. simpl. destruct IHp. split.
+++++ assert (forall a b, a <= b -> S a <= S b).
{intros. lia. } apply H1. auto.
+++++ assert (forall a b, a <= b -> S a <= S b).
{intros. lia. } apply H1. auto.
++++ subst. destruct IHp. split.
+++++ assert (forall a b, a <= b -> a <= S b).
{intros. lia. } apply H1. auto.
+++++ assert (forall a b, a <= b -> a <= S b).
{intros. lia. } apply H1. auto.
+++ destruct IHp. split.
++++ assert (forall a b, a <= b -> a <= S b).
{intros. lia. } apply H1. auto.
++++ assert (forall a b, a <= b -> a <= S b).
{intros. lia. } apply H1. auto.
++ simpl. destruct n.
+++ simpl. split.
++++ destruct IHp. 
assert (forall a b, a <= b -> S a <= S b).
{intros. lia. } apply H1. auto.
++++ destruct IHp.
assert (forall a b, a <= b -> a <= S b).
{intros. lia. } apply H1. auto.
+++ destruct IHp. simpl. split.
++++ assert (forall a b, a <= b -> a <= S b).
{intros. lia. } apply H1. auto.
++++ assert (forall a b, a <= b -> S a <= S b).
{intros. lia. } apply H1. auto.
Qed.
*)

Fact valid_pos_in_tensor_is_valid_inl (E F : EventStructure) :
forall i p,  valid_position (event_structure_tensor E F) i p ->
valid_position E (fst i) (cast_tensor_to_left E F (fst i) (snd i) p).
Proof. intros. unfold valid_position. intros. split.
+ unfold not in H0.
destruct (cast_tensor_to_left E F (fst i) (snd i) p) eqn:EQ.
++ contradiction H0. auto.
++ assert (~ p = nil).
{apply cast_not_nil_implies_not_nil. left. destruct i. unfold not.
intros. simpl fst in EQ. simpl snd in EQ. rewrite EQ in H1. 
inversion H1. }
unfold valid_position in H. apply H in H1. rewrite <- EQ.
apply cast_tensor_inl_is_boring. destruct i. simpl fst. simpl snd.
split.
+++ auto.
+++ apply H1.
+ intros. split.
++ intros. assert (H3 := H1). apply cast_tensor_inl_is_boring in H1.
apply cast_tensor_inl_is_boring.
assert (~ p = nil).
{apply cast_not_nil_implies_not_nil. left. destruct i. 
simpl fst in H3. simpl snd in H3. 
assert (forall A (a : A) l, In a l -> l <> nil).
{ intros. unfold not. intros. destruct l.
+ contradiction H4.
+ inversion H5. }
apply H4 with (a:=inr x). auto. }
unfold valid_position in H. apply H in H4. destruct H4.
assert ( (In (inr (inl x)) p ->
      leq (P (event_structure_tensor E F)) i (inl y) (inl x) ->
      In (inr (inl y)) p)).
{ apply H5. }
apply H6. auto. simpl. auto.
++ intros. destruct H1. apply cast_tensor_inl_is_boring in H1.
apply cast_tensor_inl_is_boring in H2. unfold valid_position in H.
assert (~ p = nil).
{apply cast_not_nil_implies_not_nil. left. destruct i. 
simpl fst in H0. simpl snd in H0. auto. }
assert (In (inr (inl x)) p /\ In (inr (inl y)) p ->
      ~ incompatible (event_structure_tensor E F) i (inl x) (inl y)).
{apply H. auto. }
simpl incompatible in H4. apply H4. auto.
Qed.

Fact cast_path_inl_is_projection :
forall E F i j p n,
exists m, 0 <= m <= length p /\
firstn n (cast_tensor_to_left E F i j p) = 
cast_tensor_to_left E F i j (firstn m p).
Proof. intros. simpl. generalize dependent n. induction p.
+ intros. simpl. refine (ex_intro _ 0 _). split.
++ auto.
++ destruct n; auto.
+ intros. destruct a.
++ destruct i0. destruct (eqsum_index (P E0) i i0).
+++ destruct (eqsum_index (P F) j i1).
++++ subst. destruct (eqsum_index (P E0) i0 i0) eqn:eqn1.
+++++ destruct (eqsum_index (P F) i1 i1) eqn:eqn2.
++++++ simpl. rewrite eqn1. rewrite eqn2. destruct n.
+++++++ simpl. refine (ex_intro _ 0 _). split.
++++++++ lia.
++++++++ simpl. auto.
+++++++ simpl.
assert (exists m : nat,
        0 <= m <= length p /\
        firstn n (cast_tensor_to_left E0 F i0 i1 p) =
        cast_tensor_to_left E0 F i0 i1 (firstn m p)).
{apply IHp. } destruct H. destruct H. rewrite H0.
refine (ex_intro _ (S x) _). split.
++++++++ split.
+++++++++ lia.
+++++++++ destruct H. 
assert (forall a b, a <= b -> S a <= S b).
{intros. lia. } apply H2. auto.
++++++++ simpl. rewrite eqn1. rewrite eqn2. auto.
++++++ contradiction n0. auto.
+++++ contradiction n0. auto.
++++ subst. simpl. destruct (eqsum_index (P E0) i0 i0) eqn:eqn1.
+++++ destruct (eqsum_index (P F) j i1) eqn:eqn2.
++++++ subst. contradiction n0. auto.
++++++ assert (exists m : nat,
 0 <= m <= length p /\
        firstn n (cast_tensor_to_left E0 F i0 j p) =
        cast_tensor_to_left E0 F i0 j (firstn m p)).
{apply IHp. } destruct H.  refine (ex_intro _ (S x) _).
simpl. rewrite eqn1. rewrite eqn2. destruct H. split.
+++++++ split.
++++++++ lia.
++++++++ destruct H.
assert (forall a b, a <= b -> S a <= S b).
{intros. lia. } apply H2. auto.
+++++++ auto.
+++++ assert (exists m : nat,
0 <= m <= length p /\
        firstn n (cast_tensor_to_left E0 F i0 j p) =
        cast_tensor_to_left E0 F i0 j (firstn m p)).
{apply IHp. } destruct H. destruct H. refine (ex_intro _ (S x) _).
split.
++++++ split.
+++++++ lia.
+++++++ destruct H. 
assert (forall a b, a <= b -> S a <= S b).
{intros. lia. } apply H2. auto. 
++++++ simpl. rewrite eqn1. auto.
+++ destruct (eqsum_index (P E0) i i0) eqn:eqn1.
++++ subst. contradiction n0. auto.
++++ simpl. rewrite eqn1. 
assert (exists m : nat,
0 <= m <= length p /\
        firstn n (cast_tensor_to_left E0 F i j p) =
        cast_tensor_to_left E0 F i j (firstn m p)).
{apply IHp. } destruct H. refine (ex_intro _ (S x) _). split.
+++++ split.
++++++ lia.
++++++ assert (forall a b, a <= b -> S a <= S b).
{intros. lia. } apply H0. destruct H. destruct H. auto. 
+++++ simpl. rewrite eqn1. destruct H. auto.
++ destruct n0. 
+++ simpl. destruct n.
++++ simpl. refine (ex_intro _ 0 _). split.
+++++ lia.
+++++ simpl. auto.
++++
assert (exists m : nat,
0 <= m <= length p /\
        firstn n (cast_tensor_to_left E0 F i j p) =
        cast_tensor_to_left E0 F i j (firstn m p)).
{apply IHp. } destruct H. destruct H. simpl. rewrite H0.
refine (ex_intro _ (S x) _). simpl. split.
+++++ split.
++++++ lia.
++++++ assert (forall a b, a <= b -> S a <= S b).
{intros. lia. } apply H1. destruct H. auto.
+++++ auto.
+++ simpl.
assert (exists m : nat,
0 <= m <= length p /\
        firstn n (cast_tensor_to_left E0 F i j p) =
        cast_tensor_to_left E0 F i j (firstn m p)).
{apply IHp. } destruct H. destruct H. rewrite H0.
refine (ex_intro _ (S x) _). simpl. split.
++++ split.
+++++ lia.
+++++ assert (forall a b, a <= b -> S a <= S b).
{intros. lia. } apply H1. destruct H. auto.
++++ auto.
Qed.

Fact valid_app_inl (E F : EventStructure) :
forall i p p', valid_position (event_structure_tensor E F) i (p ++ p') ->
valid_position E (fst i) 
(cast_tensor_to_left E F (fst i) (snd i) p ++ 
cast_tensor_to_left E F (fst i) (snd i) p').
Proof. intros. unfold valid_position in H. unfold valid_position. intros.
assert (In (inl i) (p ++ p') /\
    (forall x y : N (P (event_structure_tensor E F)) i,
     (In (inr x) (p ++ p') ->
      leq (P (event_structure_tensor E F)) i y x ->
      In (inr y) (p ++ p')) /\
     (In (inr x) (p ++ p') /\ In (inr y) (p ++ p') ->
      ~ incompatible (event_structure_tensor E F) i x y))).
{apply H. unfold not. intros. apply app_eq_nil in H1. destruct H1. subst. simpl in H0.
contradiction H0. auto. } destruct H1. split.
++ apply in_or_app. apply in_app_or in H1. destruct H1.
++++ left. apply cast_tensor_inl_is_boring. destruct i. auto.
++++ right. apply cast_tensor_inl_is_boring. destruct i. auto.
++ intros. split.
+++ intros. apply in_app_or in H3. destruct H3.
++++ apply cast_tensor_inl_is_boring in H3. 
assert ( In (inr (inl x)) (p ++ p')).
{apply in_or_app. auto. }
assert ((In (inr (inl x)) (p ++ p') ->
      leq (P (event_structure_tensor E F)) i (inl y) (inl x) ->
      In (inr (inl y)) (p ++ p')) /\
     (In (inr (inl x)) (p ++ p') /\ In (inr (inl y)) (p ++ p') ->
      ~ incompatible (event_structure_tensor E F) i (inl x) (inl y))).
{apply H2. } destruct H6. apply H6 in H5. apply in_app_or in H5.
apply in_or_app. destruct H5.
+++++ left. apply cast_tensor_inl_is_boring. auto.
+++++ right. apply cast_tensor_inl_is_boring. auto.
+++++ auto.
++++ apply cast_tensor_inl_is_boring in H3.
assert (In (inr (inl x)) (p ++ p')).
{apply in_or_app. right. auto. }
assert ((In (inr (inl x)) (p ++ p') ->
      leq (P (event_structure_tensor E F)) i (inl y) (inl x) ->
      In (inr (inl y)) (p ++ p')) /\
     (In (inr (inl x)) (p ++ p') /\ In (inr (inl y)) (p ++ p') ->
      ~ incompatible (event_structure_tensor E F) i (inl x) (inl y))).
{apply H2. } destruct H6. apply H6 in H5. apply in_or_app.
apply in_app_or in H5. destruct H5.
+++++ left. apply cast_tensor_inl_is_boring. auto.
+++++ right. apply cast_tensor_inl_is_boring. auto.
+++++ auto.
+++ intros. destruct H3.
assert ((In (inr (inl x)) (p ++ p') /\ In (inr (inl y)) (p ++ p') ->
      ~ incompatible (event_structure_tensor E F) i (inl x) (inl y))).
{apply H2. } apply in_app_or in H3. apply in_app_or in H4.
destruct H3.
++++ destruct H4.
+++++ apply cast_tensor_inl_is_boring in H3. 
apply cast_tensor_inl_is_boring in H4.
assert (In (inr (inl x)) (p ++ p') /\ In (inr (inl y)) (p ++ p')).
{split; apply in_or_app; left; auto. }
apply H5 in H6. simpl in H6. auto.
+++++ apply cast_tensor_inl_is_boring in H3. 
apply cast_tensor_inl_is_boring in H4.
assert (In (inr (inl x)) (p ++ p') /\ In (inr (inl y)) (p ++ p')).
{split.
+ apply in_or_app. left. auto.
+ apply in_or_app. right. auto. }
apply H5 in H6. simpl in H6. auto.
++++ destruct H4.
+++++ apply cast_tensor_inl_is_boring in H3. 
apply cast_tensor_inl_is_boring in H4.
assert (In (inr (inl x)) (p ++ p') /\ In (inr (inl y)) (p ++ p')).
{split.
+ apply in_or_app. right. auto.
+ apply in_or_app. left. auto. }
apply H5 in H6. simpl in H6. auto.
+++++ apply cast_tensor_inl_is_boring in H3. 
apply cast_tensor_inl_is_boring in H4.
assert (In (inr (inl x)) (p ++ p') /\ In (inr (inl y)) (p ++ p')).
{split; apply in_or_app; right; auto. }
apply H5 in H6. simpl in H6. auto.
Qed.

Fact nth_in_firstn :
forall A (a : A) k n l, 0 <= k < n /\ n <= length l ->
nth k (firstn n l) a = nth k l a.
Proof. intros. generalize dependent k. 
generalize dependent l. induction n.
+ intros. lia.
+ intros. destruct l.
++ easy.
++ simpl firstn. destruct k.
+++ easy.
+++ simpl. simpl in H. destruct n.
++++ lia.
++++ destruct H. apply IHn. split; lia.
Qed.

Fact cast_firstn_monotonic :
forall E F i j p m m', m <= m' ->
length (cast_tensor_to_left E F i j (firstn m p)) <=
length (cast_tensor_to_left E F i j (firstn m' p)).
Proof. intros. generalize dependent m.
generalize dependent m'. induction p.
+ intros. destruct m; destruct m'; simpl; lia.
+ intros. destruct m.
++ simpl. lia.
++ destruct m'.
+++ lia.
+++ simpl firstn. destruct a.
++++ destruct i0. destruct (eqsum_index (P E0) i i0).
+++++ destruct (eqsum_index (P F) j i1).
++++++ subst. simpl. destruct (eqsum_index (P E0) i0 i0).
+++++++ destruct (eqsum_index (P F) i1 i1).
++++++++ simpl. 
assert (forall a b, a <= b -> S a <= S b).
{intros. lia. }
apply H0. apply IHp. lia.
++++++++ contradiction n. auto.
+++++++ contradiction n. auto.
++++++ subst. simpl. destruct (eqsum_index (P E0) i0 i0).
+++++++ destruct (eqsum_index (P F) j i1).
++++++++ simpl.
assert (forall a b, a <= b -> S a <= S b).
{intros. lia. }
apply H0. apply IHp. lia.
++++++++ apply IHp. lia.
+++++++ apply IHp. lia.
+++++ simpl. destruct (eqsum_index (P E0) i i0).
++++++ contradiction n.
++++++ apply IHp. lia.
++++ destruct n.
+++++ assert (forall a b, a <= b -> S a <= S b).
{intros. lia. } simpl. apply H0. apply IHp. lia.
+++++ simpl. apply IHp. lia.
Qed.

Fact moves_not_in_start_if_valid : forall E i p l,
valid_path E i (p, l) ->
(forall m, In m l -> (~ In m p)).
Proof. intros. unfold valid_path in H.
simpl fst in *. simpl snd in *. unfold move_from in H.
assert (orig := H0). apply In_nth with (d:= inl i) in H0. 
destruct H0. destruct H0. assert (0 <= S x <= length l). {lia. }
apply H in H2. destruct H2. assert (S x - 1 = x). {lia. }
rewrite H4 in H3. rewrite H1 in H3. unfold not. intros.
assert (~ In m (p ++ firstn x l)).
{apply H3. lia. } contradiction H6. apply in_or_app. left. auto.
Qed.

Fact firstn_monotonic : forall A (a : A) l m n,
m <= n -> In a (firstn m l) -> In a (firstn n l).
Proof. intros. generalize dependent m.
generalize dependent n. induction l.
+ intros. destruct m; contradiction H0.
+ intros. destruct m.
++ contradiction H0.
++ assert (exists k, S k = n).
{destruct n.
+ lia.
+ refine (ex_intro _ n _). auto. } destruct H1. subst.
simpl in H0. destruct H0.
+++ left. auto.
+++ right. apply IHl with (m:=m). lia. auto.
Qed.

Fact moves_not_in_prev_if_valid : forall E i p l,
valid_path E i (p, l) ->
(forall m n, 0 <= m <= n /\ n < length l -> 
~ (In (nth n l (inl i)) (p ++ (firstn m l) ))).
Proof. intros. unfold valid_path in H. unfold not. intros.
simpl fst in *. simpl snd in *.
assert 
(move_from E0 i (nth (S n - 1) l (inl i)) (p ++ firstn (S n - 1) l)
       (p ++ firstn (S n) l)).
{apply H. lia. lia. }
assert (S n - 1 = n). {lia. } rewrite H3 in H2.
apply in_app_or in H1. destruct H1.
+ assert (In (nth n l (inl i)) l).
{apply nth_In. lia. }
assert (forall m, In m l -> (~ In m p)).
{apply moves_not_in_start_if_valid. auto. }
assert (~ In (nth n l (inl i)) p).
{apply H5. auto. } contradiction H6.
+ assert (In (nth n l (inl i)) (firstn n l)).
{apply firstn_monotonic with (m:=m). lia. auto. }
assert (In (nth n l (inl i)) (p ++ firstn n l)).
{apply in_or_app. right. auto. }
unfold move_from in H2. destruct H2. destruct H6.
contradiction H6.
Qed.

Fact many_occ_implies_two : forall A p l (a : A),
((count_occ p l a >= 1) <->
(exists n, n < length l /\ nth n l a = a)) /\
((count_occ p l a >= 2) <->
(exists m n, 0 <= m < n /\ n < length l /\
nth m l a = nth n l a /\ nth m l a = a)).
Proof. intros. induction l.
+ split.
++ unfold iff. split.
+++ intros. simpl in H. lia.
+++ intros. destruct H. simpl in H. lia.
++ unfold iff. split.
+++ intros. simpl in H. lia.
+++ intros. destruct H. destruct H. simpl in H. lia.
+ destruct IHl. split. simpl count_occ. destruct (p a0 a).
++ subst. unfold iff. split.
+++ intros. refine (ex_intro _ 0 _). simpl. split.
++++ lia.
++++ auto.
+++ intros. destruct H1. destruct x.
++++ simpl in H1. lia.
++++ simpl in H1. assert (forall a, a >= 0 -> S a >= 1).
{intros. lia. }
apply H2. lia.
++ unfold iff. split.
+++ intros. apply H in H1. destruct H1.
refine (ex_intro _ (S x) _). simpl. split.
++++ lia.
++++ apply H1.
+++ intros. destruct H1. destruct x.
++++ simpl in H1. contradiction n. apply H1.
++++ simpl in H1. apply H. refine (ex_intro _ x _).
split.
+++++ lia.
+++++ apply H1.
++ unfold iff. split.
+++ intros. simpl count_occ in H1. destruct (p a0 a).
++++ subst. refine (ex_intro _ 0 _).
assert ((count_occ p l a) >= 1). {lia. } apply H in H2.
destruct H2. refine (ex_intro _ (S x) _). simpl. split.
+++++ lia.
+++++ split.
++++++ lia.
++++++ easy.
++++ apply H0 in H1. destruct H1. destruct H1.
refine (ex_intro _ (S x) _). refine (ex_intro _ (S x0) _).
simpl. split.
+++++ lia.
+++++ split.
++++++ lia.
++++++ easy.
+++ intros. destruct H1. destruct H1. simpl. destruct (p a0 a).
++++ subst. assert (forall a, a >= 1 -> S a >= 2).
{intros. lia. } apply H2. apply H. destruct x0.
+++++ lia.
+++++ refine (ex_intro _ x0 _). split.
++++++ destruct H1. destruct H3. simpl in H3. lia.
++++++ destruct H1. destruct H3. simpl in H3. 
simpl (nth (S x0) (a :: l) a) in H4. destruct H4.
rewrite H4 in H5. auto.
++++ apply H0. destruct x.
+++++ simpl (nth 0 (a0 :: l) a) in H1. contradiction n. apply H1.
+++++ destruct x0.
++++++ lia.
++++++ refine (ex_intro _ x _). refine (ex_intro _ x0 _).
simpl in H1. split.
+++++++ lia.
+++++++ split.
++++++++ lia.
++++++++ apply H1.
Qed.

Fact occurences_in_valid : forall E i p l,
valid_path E i (p,l) ->
(forall a, count_occ (eqsum (P E) i) l a <= 1).
Proof. intros. 
destruct (le_gt_dec (count_occ (eqsum (P E0) i) l a) 1).
+ auto.
+ assert (count_occ (eqsum (P E0) i) l a >= 2). {lia. }
assert ((count_occ (eqsum (P E0) i) l a >= 2) ->
(exists m n, 0 <= m < n /\ n < length l /\
nth m l a = nth n l a /\ nth m l a = a)).
{apply many_occ_implies_two. }
apply H1 in H0. destruct H0. destruct H0. destruct H0.
destruct H2. destruct H3.
assert (In (nth x l a) (p ++ (firstn (S x) l) )).
{ apply in_or_app. right. rewrite <- nth_in_firstn
with (n:=S x). apply firstn_monotonic with (m:=S x). lia. 
apply nth_In. assert (length (firstn (S x) l) = S x). 
{apply firstn_length_le. lia. }  lia.
lia. } rewrite H3 in H5.
assert (nth x0 l a = nth x0 l (inl i)).
{apply nth_indep . lia. } rewrite H6 in H5.
assert (~ In (nth x0 l (inl i)) (p ++ firstn (S x) l)).
{apply moves_not_in_prev_if_valid. auto. split.
+ lia.
+ lia. } contradiction H7.
Qed.

Fact in_tail_implies_num_occ: forall A (a : A) p l x y,
0 <= y <= x /\ S x <= length l ->
In (nth x (firstn (S x) l) a) (firstn y l) ->
(count_occ p l (nth x (firstn (S x) l) a) >= 2).
Proof. intros.
assert (exists n, n < (length (firstn y l)) /\ 
nth n (firstn y l) a = nth x (firstn (S x) l) a).
{apply In_nth. auto. } destruct H1.
assert (length (firstn y l) = y).
{apply firstn_length_le. lia. } rewrite H2 in H1.
apply many_occ_implies_two.
refine (ex_intro _ x0 _). refine (ex_intro _ x _). split.
+ lia.
+ split.
++ lia.
++ rewrite nth_in_firstn. rewrite nth_in_firstn in H1.
rewrite nth_in_firstn in H1.
+++ assert (nth x0 l (nth x l a) = nth x0 l a).
{apply nth_indep. lia. }
rewrite H3.
assert (nth x l (nth x l a) = nth x l a).
{apply nth_indep. lia. }
rewrite H4. easy.
+++ lia.
+++ lia.
+++ lia.
Qed.

Fact sumbool_case_left : forall A B C (a : {A} + {B})
(b c d : C), (b = d) ->
((exists p, a = left p) -> (if a then b else c) = d).
Proof. intros. destruct a eqn:eqn1.
++ auto.
++ intros. destruct H0. inversion H0.
Qed.

Fact sumbool_case_right : forall A B C (a : {A} + {B})
(b c d : C), (b = d) ->
((exists p, a = right p) -> (if a then c else b) = d).
Proof. intros. destruct a eqn:eqn1.
++ intros. destruct H0. inversion H0.
++ auto.
Qed.

Fact sumbool_case2_right : forall A B C D E
(a : {A} + {B}) (d : {C} + {D})
(b c e f : E), (c = f) ->
((exists p, a = right p) -> 
(exists p, d = right p) -> 
(if a then b else c) = (if d then e else f)).
Proof. intros. destruct a eqn:eqn1.
+ destruct H0. inversion H0.
+ destruct d eqn:eqn2.
++ destruct H1. inversion H1. 
++ auto.
Qed.

Fact sumbool_case2_left : forall A B C D E
(a : {A} + {B}) (d : {C} + {D})
(b c e f : E), (c = f) ->
((exists p, a = left p) -> 
(exists p, d = left p) -> 
(if a then c else b) = (if d then f else e)).
Proof. intros. destruct a eqn:eqn1.
+ destruct d eqn:eqn2.
++ auto.
++ destruct H1. inversion H1.
+ destruct H0. inversion H0.
Qed.

Fact equality_is_reflexive : forall A (x y : A)
(p : {x = y} + {x <> y}),
x = y -> (exists p', p = left p').
Proof. intros. destruct p.
+ refine (ex_intro _ e _). auto.
+ contradiction n. 
Qed.

Fact cast_inl_preserves_count : forall E F i j l,
count_occ (eqsum (P E) i) (cast_tensor_to_left E F i j l) (inl i) = 
count_occ (eqsum (P (event_structure_tensor E F)) (i, j)) l (inl (i, j)) /\
(forall m,
count_occ (eqsum (P E) i) (cast_tensor_to_left E F i j l) (inr m) = 
count_occ (eqsum (P (event_structure_tensor E F)) (i, j)) l (inr (inl m))).
Proof. split. induction l.
+ auto.
+ simpl. destruct a.
++ destruct i0. destruct (eqsum_index (P E0) i i0).
+++ destruct (eqsum_index (P F) j i1).
++++ subst. simpl. destruct (eqsum (P E0) i0 (inl i0) (inl i0)).
+++++ symmetry. apply sumbool_case_left. auto. apply equality_is_reflexive. 
auto.
+++++ contradiction n. auto.
++++ subst.
assert (exists p, eqsum (partial_order_tensor (P E0) (P F))
    (i0, j) (inl (i0, i1)) (inl (i0, j)) = right p).
{destruct (eqsum (partial_order_tensor (P E0) (P F))
    (i0, j) (inl (i0, i1)) (inl (i0, j))).
+ inversion e. contradiction n. auto.
+ refine (ex_intro _ n0 _). auto. }
symmetry. apply sumbool_case_right. auto. auto.
+++ destruct (eqsum_index (P F) j i1).
++++ subst.
 assert (exists p, eqsum (partial_order_tensor (P E0) (P F))
    (i, i1) (inl (i0, i1)) (inl (i, i1)) = right p).
{destruct (eqsum (partial_order_tensor (P E0) (P F))
    (i, i1) (inl (i0, i1)) (inl (i, i1))).
+ inversion e. contradiction n. auto.
+ refine (ex_intro _ n0 _). auto. }
symmetry. apply sumbool_case_right. auto. auto.
++++ assert (exists p, eqsum (partial_order_tensor (P E0) (P F)) 
    (i, j) (inl (i0, i1)) (inl (i, j)) = right p).
{destruct (eqsum (partial_order_tensor (P E0) (P F)) 
    (i, j) (inl (i0, i1)) (inl (i, j))).
+ inversion e. contradiction n. auto.
+ refine (ex_intro _ n1 _). auto. }
symmetry. apply sumbool_case_right. auto. auto.
++ destruct n.
+++ simpl. apply sumbool_case2_right. auto.
destruct (eqsum (P E0) i (inr n) (inl i)) eqn:eqn1.
++++ inversion e.
++++ refine (ex_intro _ n0 _). auto.
++++ destruct (eqsum (partial_order_tensor (P E0) (P F)) (i, j) 
    (inr (inl n)) (inl (i, j))) eqn:eqn1.
+++++ inversion e.
+++++ refine (ex_intro _ n0 _). auto.
+++ symmetry. apply sumbool_case_right. auto.
destruct (eqsum (partial_order_tensor (P E0) (P F)) (i, j) 
    (inr (inr n)) (inl (i, j))) eqn:eqn1.
++++ inversion e.
++++ refine (ex_intro _ n0 _). auto.
+ intros. induction l.
++ simpl. auto.
++ destruct a.
+++ simpl. destruct i0. destruct (eqsum_index (P E0) i i0).
++++ destruct (eqsum_index (P F) j i1).
+++++ subst. symmetry. apply sumbool_case_right. 
++++++ simpl. symmetry. apply sumbool_case_right.
+++++++ auto.
+++++++ destruct (eqsum (P E0) i0 (inl i0) (inr m)) eqn:eqn1.
++++++++ inversion e.
++++++++ refine (ex_intro _ n _). auto.
++++++ destruct (eqsum (partial_order_tensor (P E0) (P F)) 
    (i0, i1) (inl (i0, i1)) (inr (inl m))) eqn:eqn1.
+++++++ inversion e.
+++++++ refine (ex_intro _ n _). auto.
+++++ subst. symmetry. apply sumbool_case_right.
++++++ auto.
++++++ destruct (eqsum (partial_order_tensor (P E0) (P F)) 
    (i0, j) (inl (i0, i1)) (inr (inl m))) eqn:eqn1.
+++++++ inversion e.
+++++++ refine (ex_intro _ n0 _). auto.
++++ symmetry. apply sumbool_case_right.
+++++ auto.
+++++ destruct (eqsum (partial_order_tensor (P E0) (P F)) 
    (i, j) (inl (i0, i1)) (inr (inl m))) eqn:eqn1.
++++++ inversion e.
++++++ refine (ex_intro _ n0 _). auto.
+++ destruct n.
++++ simpl. destruct (eqsum (P E0) i (inr n) (inr m)).
+++++ inversion e. subst. apply sumbool_case2_left. 
++++++ rewrite IHl. auto. 
++++++ destruct (eqsum (P E0) i (inr m) (inr m)).
+++++++ refine (ex_intro _ e0 _). auto.
+++++++ contradiction n.
++++++ destruct (eqsum (partial_order_tensor (P E0) (P F)) (i, j) 
    (inr (inl m)) (inr (inl m))) eqn:eqn1.
+++++++ refine (ex_intro _ e0 _). auto.
+++++++ contradiction n. auto.
+++++ apply sumbool_case2_right.
++++++ auto.
++++++ destruct (eqsum (P E0) i (inr n) (inr m)) eqn:eqn1.
+++++++ contradiction n0.
+++++++ refine (ex_intro _ n1 _). auto.
++++++ destruct (eqsum (partial_order_tensor (P E0) (P F)) (i, j) 
    (inr (inl n)) (inr (inl m))) eqn:eqn1.
+++++++ inversion e. subst. contradiction n0. auto.
+++++++ refine (ex_intro _ n1 _). auto.
++++ simpl. symmetry. apply sumbool_case_right.
+++++ auto.
+++++ destruct (eqsum (partial_order_tensor (P E0) (P F)) 
    (i, j) (inr (inr n)) (inr (inl m))) eqn:eqn1.
++++++ inversion e.
++++++ refine (ex_intro _ n0 _). auto.
Qed.

Fact in_firstn_implies_in_list : forall A (a : A) l n,
In a (firstn n l) -> In a l.
Proof. intros. generalize dependent n. induction l.
+ intros. destruct n in H; contradiction H.
+ intros. destruct n.
++ contradiction H.
++ simpl in H. destruct H.
+++ subst. left. auto.
+++ right. apply IHl with (n:=n). auto.
Qed.

Fact valid_path_in_tensor_is_valid_inl (E F : EventStructure) :
forall i p, valid_path (event_structure_tensor E F) i p ->
valid_path E (fst i) (cast_tensor_to_left E F (fst i) (snd i) (fst p), 
cast_tensor_to_left E F (fst i) (snd i) (snd p)).
Proof. intros. destruct i. destruct p.
unfold valid_path. simpl fst. simpl snd. intros. split.
+ assert (exists m, 0 <= m <= length l /\
firstn n (cast_tensor_to_left E F i i0 l) = 
cast_tensor_to_left E F i i0 (firstn m l)).
{apply cast_path_inl_is_projection. } destruct H1. destruct H1.
rewrite H2. simpl fst in *. simpl snd in *.
assert (valid_position E (fst (i, i0))
  (cast_tensor_to_left E F (fst (i, i0)) (snd (i, i0)) p ++
   cast_tensor_to_left E F (fst (i, i0)) (snd (i, i0)) (firstn x l))).
{apply valid_app_inl. unfold valid_path in H. simpl fst in H. simpl snd in H.
apply H. auto. } simpl fst in H3. simpl snd in H3. auto.
+ intros. unfold move_from. split.
++ assert (exists k, n = S k).
{ destruct n.
+ lia.
+ refine (ex_intro _ n _). auto. } destruct H2. subst.
assert (S x - 1 = x). {lia. } rewrite H2.
assert (nth x (cast_tensor_to_left E F i i0 l) (inl i) = 
nth x (firstn (S x) (cast_tensor_to_left E F i i0 l)) (inl i)).
{symmetry. apply nth_in_firstn. lia. }
rewrite H3. apply in_or_app. right. apply nth_In.
assert (length (firstn (S x) (cast_tensor_to_left E F i i0 l)) = S x).
{apply firstn_length_le. lia. } rewrite H4. lia.
++ split.
+++ unfold not. intros. 
assert (exists k, n = S k).
{ destruct n.
+ lia.
+ refine (ex_intro _ n _). auto. } destruct H3. subst.
assert (S x - 1 = x). {lia. } rewrite H3 in H2.
assert (nth x (cast_tensor_to_left E F i i0 l) (inl i) = 
nth x (firstn (S x) (cast_tensor_to_left E F i i0 l)) (inl i)).
{symmetry. apply nth_in_firstn. lia. }
assert (exists m, 0 <= m <= length l /\
firstn x (cast_tensor_to_left E F i i0 l) = 
cast_tensor_to_left E F i i0 (firstn m l)).
{apply cast_path_inl_is_projection. } destruct H5.
destruct H5. apply in_app_or in H2. destruct H2.
++++ assert (In (nth x (cast_tensor_to_left E F i i0 l) (inl i))
(cast_tensor_to_left E F i i0 l)). 
{apply nth_In. lia. }
destruct (nth x (cast_tensor_to_left E F i i0 l) (inl i)) eqn:eqn1.
+++++ apply cast_tensor_inl_is_boring in H2.
apply cast_tensor_inl_is_boring in H7.
assert (forall m, In m l -> (~ In m p)).
{apply moves_not_in_start_if_valid. auto. }
assert (~ In (inl (i, i0)) p). {apply H8. easy. }
contradiction H9. easy.
+++++ apply cast_tensor_inl_is_boring in H2.
apply cast_tensor_inl_is_boring in H7.
assert (forall m, In m l -> (~ In m p)).
{apply moves_not_in_start_if_valid. auto. }
assert (~ In (inr (inl n)) p). {apply H8. easy. }
contradiction H9.
++++ rewrite H4 in H2.
assert (count_occ 
(eqsum (P E) i) 
(cast_tensor_to_left E F i i0 l)
(nth x (firstn (S x) (cast_tensor_to_left E F i i0 l)) (inl i)) >= 2).
{apply in_tail_implies_num_occ with (y:=x).
+ lia.
+ auto. } apply in_firstn_implies_in_list in H2.
destruct (nth x (firstn (S x) (cast_tensor_to_left E F i i0 l))).
+++++ apply cast_tensor_inl_is_boring in H2. destruct H2. subst.
assert (
count_occ (eqsum (P E) i) (cast_tensor_to_left E F i i0 l) (inl i) = 
count_occ (eqsum (P (event_structure_tensor E F)) (i, i0)) l (inl (i, i0))).
{apply cast_inl_preserves_count. }
rewrite H2 in H7.
assert (count_occ (eqsum (P (event_structure_tensor E F)) (i, i0)) l
       (inl (i, i0)) <= 1).
{apply occurences_in_valid with (p:=p). auto. } lia.
+++++ apply cast_tensor_inl_is_boring in H2. 
assert (
count_occ (eqsum (P E) i) (cast_tensor_to_left E F i i0 l) (inr n) = 
count_occ (eqsum (P (event_structure_tensor E F)) (i, i0)) l (inr (inl n))).
{apply cast_inl_preserves_count. }
rewrite H8 in H7.
assert (count_occ (eqsum (P (event_structure_tensor E F)) (i, i0)) l
       (inr (inl n)) <= 1).
{apply occurences_in_valid with (p:=p). auto. } lia.
+++ intros. apply in_app_or in H2. destruct H2.
++++ apply in_or_app. left. auto.
++++ apply in_or_app. right. apply firstn_monotonic
with (m:=n-1). lia. auto.
Qed.

Fact valid_walk_in_tensor_is_valid_inl (E F : EventStructure) :
forall i1 j1 i2 j2 p1 p2 w1 w2,
valid_walk (event_structure_tensor E F)
      (i1,j1) (i2,j2) ((p1, w1), (p2, w2)) ->
valid_walk E i1 i2
((cast_tensor_to_left E F i1 j1 p1, cast_tensor_to_left E F i1 j1 w1),
(cast_tensor_to_left E F i2 j2 p2, cast_tensor_to_left E F i2 j2 w2)).  
Proof. intros. unfold valid_walk in H. simpl fst in *. simpl snd in *. 
unfold valid_walk. destruct H. destruct H0. simpl fst. simpl snd.
split.
+ apply valid_path_in_tensor_is_valid_inl in H. simpl in H. auto.
+ split.
++ apply valid_path_in_tensor_is_valid_inl in H0. simpl in H0. auto.
++ split.
+++ intros. subst. 
assert (cast_tensor_to_left E F i1 j2 p2 = 
eq_rect i1 (Position E)
     (cast_tensor_to_left E F i1 j2 p2) i1 eq_refl).
{apply eq_rect_eq_dec. apply eqsum_index. }
rewrite <- H2. destruct x.
++++ assert
(forall k, In (inl k) (cast_tensor_to_left E F i1 j1 p1) <->
(k = i1) /\ In (inl (i1,j1)) p1).
{apply cast_tensor_inl_is_boring. }
rewrite H3. 
assert
(forall k, In (inl k) (cast_tensor_to_left E F i1 j2 p2) <->
(k = i1) /\ In (inl (i1,j2)) p2).
{apply cast_tensor_inl_is_boring. }
rewrite H4. destruct (eqsum_index _ j1 j2).
++++++ subst.
assert (p2 = eq_rect (i1, j2)
          (Position (event_structure_tensor E F)) p2
          (i1, j2) eq_refl).
{apply eq_rect_eq_dec. apply 
(eqsum_index (P (event_structure_tensor E F))). }
assert
(forall x, In x p1 <->
     In x
       (eq_rect (i1, j2)
          (Position (event_structure_tensor E F)) p2
          (i1, j2) eq_refl)).
{ apply H1. } rewrite <- H5 in H6. unfold iff. split.
+++++++ intros. split.
++++++++ apply H7.
++++++++ apply H6. apply H7.
+++++++ intros. split.
++++++++ apply H7.
++++++++ apply H6. apply H7.
++++++ assert ((i1, j1) <> (i1, j2)).
{unfold not. intros. inversion H5. subst. contradiction n.
auto. } destruct H1. apply H6 in H5. destruct H5. subst.
simpl. easy. 
++++ destruct (eqsum_index _ j1 j2).
+++++ subst.
assert (p2 = eq_rect (i1, j2)
          (Position (event_structure_tensor E F)) p2
          (i1, j2) eq_refl).
{apply eq_rect_eq_dec. apply 
(eqsum_index (P (event_structure_tensor E F))). }
assert
(forall x, In x p1 <->
     In x
       (eq_rect (i1, j2)
          (Position (event_structure_tensor E F)) p2
          (i1, j2) eq_refl)).
{ apply H1. } rewrite <- H3 in H4.
assert (forall m, In (inr (inl m)) p1 <-> 
In (inr m) (cast_tensor_to_left E F i1 j2 p1)).
{apply cast_tensor_inl_is_boring. }
assert (forall m, In (inr (inl m)) p2 <-> 
In (inr m) (cast_tensor_to_left E F i1 j2 p2)).
{apply cast_tensor_inl_is_boring. }
rewrite <- H5. rewrite <- H6.
apply H4.
+++++ assert ((i1, j1) <> (i1, j2)).
{unfold not. intros. inversion H3. subst. contradiction n0.
auto. }
destruct H1. apply H4 in H3. destruct H3. subst. easy.
+++ intros. assert ((i1, j1) <> (i2, j2)).
{unfold not. intros. inversion H3. subst. contradiction H2.
auto. } destruct H1. apply H4 in H3. destruct H3. subst.
easy.
Qed.


Fixpoint cast_infinite_tensor_left (E F : EventStructure)
(i : I (P E) * I (P F))
(p : InfinitePosition (event_structure_tensor E F) i)
: InfinitePosition E  (fst i) := 
match p with
| stream _ _ (inl _) f => 
stream _ _ (inl (fst i)) (fun _ => cast_infinite_tensor_left E F i (f tt))
| stream _ _ (inr (inl m)) f =>
stream _ _ (inr m) (fun _ => cast_infinite_tensor_left E F i (f tt))
| stream _ _ _ f => cast_infinite_tensor_left E F i (f tt)
end.

Fixpoint cast_infinite_tensor_right (E F : EventStructure)
(i : I (P E) * I (P F))
(p : InfinitePosition (event_structure_tensor E F) i)
: InfinitePosition F (snd i) := 
match p with
| stream _ _ (inl _) f => 
stream _ _ (inl (snd i)) (fun _ => cast_infinite_tensor_right E F i (f tt))
| stream _ _ (inr (inr m)) f =>
stream _ _ (inr m) (fun _ => cast_infinite_tensor_right E F i (f tt))
| stream _ _ _ f => cast_infinite_tensor_right E F i (f tt)
end.

Definition tensor (p q : Z) :=
if Z.ltb p 0 then 
(if Z.ltb q 0 then Z.add p q else p)
else
(if Z.ltb q 0 then q else Z.add p q).

Definition tensor_infinity (p q : Infinity) :=
match p,q with
| plus_infinity, plus_infinity => plus_infinity
| _, _ => minus_infinity
end.

Definition asynchronous_arena_tensor (A B : AsynchronousArena)
(positive1 : forall i, finite_payoff_position A i nil = (-1)%Z)
(positive2 : forall i, finite_payoff_position B i nil = (-1)%Z)
: AsynchronousArena.
  refine({| E := event_structure_tensor (E A) (E B);
polarity i m := 
match m with
| inl _ => true
| inr m => 
( match m with
| inl m => polarity A (fst i) (inr m)
| inr m => polarity B (snd i) (inr m)
end)
end;
finite_payoff_position i p := 
match p with
| nil => (-1)%Z
| _ => tensor
(finite_payoff_position A (fst i)
(cast_tensor_to_left (E A) (E B) (fst i) (snd i) p))
(finite_payoff_position B (snd i)
(cast_tensor_to_right (E A) (E B) (fst i) (snd i) p))
end;
finite_payoff_walk i j w :=
let (a, b) := w in
let (p1, w1) := a in
let (p2, w2) := b in
let p1' := (cast_tensor_to_left (E A) (E B) (fst i) (snd i) p1) in
let w1' := (cast_tensor_to_left (E A) (E B) (fst i) (snd i) w1) in
let p2' := (cast_tensor_to_left (E A) (E B) (fst j) (snd j) p2) in
let w2' := (cast_tensor_to_left (E A) (E B) (fst j) (snd j) w2) in
let x := finite_payoff_walk A (fst i) (fst j) ((p1',w1'),(p2',w2')) in
let p1' := (cast_tensor_to_right (E A) (E B) (fst i) (snd i) p1) in
let w1' := (cast_tensor_to_right (E A) (E B) (fst i) (snd i) w1) in
let p2' := (cast_tensor_to_right (E A) (E B) (fst j) (snd j) p2) in
let w2' := (cast_tensor_to_right (E A) (E B) (fst j) (snd j) w2) in
let y := finite_payoff_walk B (snd i) (snd j) ((p1',w1'),(p2',w2')) in
tensor x y;
infinite_payoff i p :=
let x := infinite_payoff A (fst i) (cast_infinite_tensor_left (E A) (E B) i p) in
let y := infinite_payoff B (snd i) (cast_infinite_tensor_right (E A) (E B) i p)
in tensor_infinity x y ;
         |}).
- intros. simpl. left. auto.
- intros. split.
+ intros. auto.
+ intros. inversion H.
- intros. apply second_in_tensor_is_second in H. destruct H.
+ destruct H. destruct H. subst. split.
++ intros. auto.
++ intros. apply polarity_second in H0. destruct H0.
apply H1 in H. rewrite positive1 in H. auto.
+ destruct H. destruct H. subst. split.
++ intros. auto.
++ intros. apply polarity_second in H0. destruct H0.
apply H1 in H. rewrite positive2 in H. auto.
- intros. simpl. destruct w. destruct p. destruct p0.
simpl in H. destruct H. subst. destruct i. destruct j. simpl.
assert ( finite_payoff_walk A i i1
     (cast_tensor_to_left (E A) (E B) i i0 p, nil,
     (cast_tensor_to_left (E A) (E B) i1 i2 p0, nil)) = 0%Z).
{apply initial_null. split; auto. }
assert ((finite_payoff_walk B i0 i2
     (cast_tensor_to_right (E A) (E B) i i0 p, nil,
     (cast_tensor_to_right (E A) (E B) i1 i2 p0, nil))) = 0%Z).
{apply initial_null. split; auto. }
assert (forall n m f, n = 0%Z /\ m = 0%Z /\ 
f 0%Z 0%Z = 0%Z -> f n m = 0%Z).
{intros. destruct H1. destruct H2. rewrite H1. rewrite H2. auto. }
apply H1. auto.
Defined.

Record Group := {
G : Type;
mult : G -> G -> G;
identity : G;
inverse : G -> G;

associative : forall (x y z : G),
mult x (mult y z) = mult (mult x y) z;
identity_exists : forall (x : G), 
mult identity x = x /\ mult x identity = x;
inverses_exist : forall (x : G),
mult x (inverse x) = identity /\ mult (inverse x) x = identity;
}.

Record AsynchronousGame 
(A : AsynchronousArena) (X : Group) (Y : Group) := {
A : AsynchronousArena;
X : Group;
Y : Group;

M := {i : I (P (E A)) & sum (I (P (E A))) (N (P (E A)) i)};
action : (G X) -> M -> (G Y) -> M;

(*action_identity : forall (m P (E A) M),
action identity m identity = m;
action_compatible : forall (m P (E A) M
) (g g' :(@G X)) (h h' :(@G Y)),
action (mult g g') m (mult h h') = 
action g (action g' m h) h';

coherence_1 : forall (m n P (E A) M) (g :@(@G X)) (h :@(@G Y)),
leq m n -> leq (action g m h) (action g n h);
coherence_2 : forall (m M M) (g : (@G X)) (h : (@G Y)),
polarity (action g m h) = polarity m;
coherence_3 : forall (m : M) (g : (@G X)),
(polarity m = false /\ forall (n : M), 
leq m n -> n = action g n identity) -> 
m = action g m identity;
coherence_4 : forall (m : M) (h : (@G Y)),
(polarity m = true /\ forall (n : M), 
leq m n -> n = action identity n h) -> 
m = action identity m h*)
}.
