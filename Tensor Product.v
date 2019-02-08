Require Import List.
Require Import ZArith.
Require Import Lia.
Require Import Init.Nat.
Require Import Logic.Eqdep.
Require Import Logic.Eqdep_dec.
Require Import Arith.PeanoNat.
Require Import Bool.Bool.
Require Import AsynchronousGames.

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