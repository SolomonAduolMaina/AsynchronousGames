Require Import List.
Require Import ZArith.
Require Import Lia.
Require Import Init.Nat.
Require Import Logic.Eqdep.
Require Import Logic.Eqdep_dec.
Require Import Arith.PeanoNat.
Require Import Bool.Bool.
Require Import Group.
Require Import AsynchronousGames.
Require Import Lifting.

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
- intros. destruct i. unfold iff. split.
+ intros. inversion H.
++ auto.
++ subst. inversion H1.
++ subst. inversion H1.
+ intros. subst. apply leq_tensor_least with (m:=m).
- intros. inversion H.
+ auto.
+ subst. inversion H1. inversion H2. subst. auto.
+ subst. inversion H1. inversion H2. subst. auto.
Defined.

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
++++ unfold iff. split.
+++++ intros. simpl. left. inversion H.
++++++ subst. apply inj_pairT2 in H6. subst.
apply inj_pairT2 in H3. subst. auto.
++++++ subst. inversion H2.
++++++ subst. inversion H2.
+++++ intros. destruct H.
++++++ inversion H. subst. apply inj_pairT2 in H. subst.
apply leq_tensor_least.
++++++ contradiction H.
+++ destruct n.
++++ simpl. unfold iff. split.
+++++ intros. apply in_map_iff. inversion H.
++++++ subst. inversion H6. subst. 
apply inj_pairT2 in H3. subst.
refine (ex_intro _ (existT _ i (inl tt)) _). split.
+++++++ auto.
+++++++ apply ideal_finite. apply unit_is_least. auto.
++++++ subst. inversion H2. subst. apply inj_pairT2 in H2.
inversion H2. subst. inversion H1. subst. apply inj_pairT2 in H1.
subst. refine (ex_intro _ (existT _ i3 (inr m)) _). split.
+++++++ auto.
+++++++ apply ideal_finite. auto.
++++++ subst. inversion H2.
+++++ intros. apply in_map_iff in H. destruct H. destruct x. destruct s.
++++++ destruct u. inversion H. subst. inversion H0. subst.
apply inj_pairT2 in H0. subst. apply ideal_finite in H1. 
apply unit_is_least in H1. subst. apply leq_tensor_least.
++++++ destruct H. inversion H. subst. apply inj_pairT2 in H. subst.
apply ideal_finite in H0. assert (H1 := H0).
apply leq_same_component in H0. subst.
apply leq_tensor_left with (i:=i) (j:=i2) (m:=n0) (m':=n). auto. auto.
auto.
++++ unfold iff. split.
+++++ intros. apply in_map_iff. inversion H.
++++++ subst. apply inj_pairT2 in H3. subst.
refine (ex_intro _ (existT _ i0 (inl tt)) _). split.
+++++++ auto.
+++++++ apply ideal_finite. apply unit_is_least. auto.
++++++ subst. inversion H1. subst. apply inj_pairT2 in H1. subst.
inversion H2.
++++++ subst. inversion H2. subst. apply inj_pairT2 in H2. inversion H2.
subst. inversion H1. subst. apply inj_pairT2 in H7. subst.
refine (ex_intro _ (existT _ j (inr m)) _). split.
+++++++ auto.
+++++++ apply ideal_finite. auto.
+++++ intros.
++++++ apply in_map_iff in H. destruct H. destruct x. destruct H. 
apply ideal_finite in H0. assert (H1 := H0). apply leq_same_component in H0. subst.
destruct s. 
+++++++ destruct u. inversion H. subst. apply inj_pairT2 in H. subst.
apply leq_tensor_least.
+++++++ inversion H. subst. apply inj_pairT2 in H. subst.
apply leq_tensor_right with (i:=i1) (j:=i2) (m:=n0) (m':=n). auto. auto. auto.
- intros. destruct H. inversion H.
+ subst. inversion H0.
++ apply incomp_tensor_least. auto.
++ subst. inversion H3. subst. apply incomp_tensor_least. auto.
++ subst. inversion H3. subst. apply incomp_tensor_least. auto.
+ subst. inversion H0.
++ subst. inversion H3. subst. apply inj_pairT2 in H3. inversion H3.
subst. apply incomp_tensor_left with (m:=m) (m':=m'0). apply incompatible_closed
with (y:=(existT (fun i0 : I (P E) => (unit + N (P E) i0)%type)
     (fst (i, j)) (inr m0))). auto. auto. auto.
++ subst. inversion H3.
+ subst. inversion H0.
++ subst. inversion H3.
++ subst. inversion H3. subst. apply inj_pairT2 in H3. inversion H3.
subst. apply incomp_tensor_right with (m:=m) (m':=m'0). apply incompatible_closed
with (y:=(existT (fun i0 : I (P F) => (unit + N (P F) i0)%type)
     (snd (i, j)) (inr m0))). auto. auto. auto.
Defined.

Fixpoint cast_tensor_to_left E F (l : Position (event_structure_tensor E F))
: Position E :=
match l with
| nil => nil
| (existT _ (i,j) (inl tt)) :: xs
=> (existT _ i (inl tt)) :: (cast_tensor_to_left E F xs)
| (existT _ (i,j) (inr (inl m))) :: xs
=> (existT _ i (inr m)) :: (cast_tensor_to_left E F xs)
| (existT _ i (inr (inr _))) :: xs
=> cast_tensor_to_left E F xs
end.

Fixpoint cast_tensor_to_right E F (l : Position (event_structure_tensor E F))
: Position F :=
match l with
| nil => nil
| (existT _ (i,j) (inl tt)) :: xs
=> (existT _ j (inl tt)) :: (cast_tensor_to_right E F xs)
| (existT _ (i,j) (inr (inr m))) :: xs
=> (existT _ j (inr m)) :: (cast_tensor_to_right E F xs)
| (existT _ i (inr (inl _))) :: xs
=> cast_tensor_to_right E F xs
end.

CoFixpoint cast_tensor_inf_to_left E F (l : InfinitePosition (event_structure_tensor E F))
: InfinitePosition E :=
match l with
| Cons _ (existT _ (i, j) (inl tt)) f =>
Cons _ (existT _ i (inl tt)) (cast_tensor_inf_to_left E F f)
| Cons _ (existT _ (i, j) (inr (inl m))) f =>
Cons _ (existT _ i (inr m)) (cast_tensor_inf_to_left E F f)
| Cons _ (existT _ (i, j) (inr (inr _))) f =>
Eps _ (cast_tensor_inf_to_left E F f)
| Eps _ s => Eps _ (cast_tensor_inf_to_left E F s)
end.

CoFixpoint cast_tensor_inf_to_right E F (l : InfinitePosition (event_structure_tensor E F))
: InfinitePosition F :=
match l with
| Cons _ (existT _ (i, j) (inl tt)) f =>
Cons _ (existT _ j (inl tt)) (cast_tensor_inf_to_right E F f)
| Cons _ (existT _ (i, j) (inr (inr m))) f =>
Cons _ (existT _ j (inr m)) (cast_tensor_inf_to_right E F f)
| Cons _ (existT _ (i, j) (inr (inl _))) f =>
Eps _ (cast_tensor_inf_to_right E F f)
| Eps _ s => Eps _ (cast_tensor_inf_to_right E F s)
end.

Definition tensor (p q : Z) :=
if Z.ltb p 0 then 
(if Z.ltb q 0 then Z.add p q else p)
else
(if Z.ltb q 0 then q else Z.add p q).

Definition tensor_infinity (p q : Infinity) :=
match p, q with
| plus_infinity, plus_infinity => plus_infinity
| _, _ => minus_infinity
end.

Fact second_in_tensor_is_second :
forall E F m, second_move (P (event_structure_tensor E F)) m <->
((exists i j k, m = existT _ (i,j) (inr (inl k)) /\ 
second_move (P E) (existT _ i (inr k)))
\/
(exists i j k, m = existT _ (i,j) (inr (inr k)) /\ 
second_move (P F) (existT _ j (inr k)))).
Proof. unfold iff. split.
+ intros. unfold second_move in H. destruct H.
rewrite initial_is_unit in H. destruct m. destruct s.
++ contradiction H. refine (ex_intro _ x _). destruct u. auto.
++ destruct x. destruct n.
+++ left. refine (ex_intro _ i _). refine (ex_intro _ i0 _).
refine (ex_intro _ n _). split.
++++ auto.
++++ unfold second_move. unfold not. intros. split.
+++++ intros. rewrite initial_is_unit in H1. destruct H1.
inversion H1.
+++++ intros. destruct n0.
++++++ destruct s.
+++++++ destruct u. apply initial_is_unit.
refine (ex_intro _ x _). auto.
+++++++ destruct H1. assert (H3 := H1).
apply leq_same_component in H3. subst.
assert (initial_move (P (event_structure_tensor E F))
(existT
          (fun i : I (P (event_structure_tensor E F)) =>
           (unit + N (P (event_structure_tensor E F)) i)%type)
          (i, i0) (inr (inl n0)))).
{apply H0. split.
+ apply leq_tensor_left with (i:=i) (j:=i0) (m:=n0) (m':=n).
++ auto.
++ auto.
++ auto.
+ unfold not. intros. apply inj_pairT2 in H3. inversion H3. subst.
contradiction H2. auto. }
apply initial_is_unit in H3. destruct H3. inversion H3.
+++ simpl. right. refine (ex_intro _ i _). refine (ex_intro _ i0 _).
refine (ex_intro _ n _). split.
++++ auto.
++++ unfold second_move. split.
+++++ unfold not. intros. apply initial_is_unit in H1. destruct H1.
inversion H1.
+++++ intros. destruct H1. assert (H3 := H1). destruct n0.
++++++ apply leq_same_component in H3. subst. destruct s.
+++++++ apply initial_is_unit. destruct u. refine (ex_intro _ i0 _).
auto.
+++++++
assert (initial_move (P (event_structure_tensor E F))
(existT
          (fun i : I (P (event_structure_tensor E F)) =>
           (unit + N (P (event_structure_tensor E F)) i)%type)
          (i, i0) (inr (inr n0)))).
{apply H0. split.
+ apply leq_tensor_right with (i:=i) (j:=i0) (m:=n0) (m':=n).
++ auto.
++ auto.
++ auto.
+ unfold not. intros. apply inj_pairT2 in H3. inversion H3. subst.
contradiction H2. auto.
 } apply initial_is_unit in H3. destruct H3. inversion H3.
+ intros. destruct H. 
++ destruct H. destruct H. destruct H. destruct H. subst. unfold second_move.
split.
+++ unfold not. intros. apply initial_is_unit in H. destruct H. inversion H.
+++ intros. destruct H. unfold second_move in H0. destruct H0. destruct n.
++++ destruct s.
+++++ apply initial_is_unit. destruct u. refine (ex_intro _ x2 _). auto.
+++++ inversion H.
++++++ subst. inversion H5. subst. apply inj_pairT2 in H5. inversion H5.
subst. inversion H4. subst. apply inj_pairT2 in H4. inversion H4. subst.
assert (initial_move (P E) (existT (fun i : I (P E) => (unit + N (P E) i)%type) i
          (inr m))).
{apply H2. split.
+ auto.
+ unfold not. intros. apply inj_pairT2 in H6. inversion H6. subst. contradiction H1. auto.
} apply initial_is_unit in H6. destruct H6. inversion H6.
++++++ subst. inversion H5.
++ destruct H. destruct H. destruct H. destruct H. subst. unfold second_move. split.
+++ unfold not. intros. apply initial_is_unit in H. destruct H. inversion H.
+++ intros. destruct H. unfold second_move in H0. destruct H0. destruct n.
++++ destruct s.
+++++ apply initial_is_unit. destruct u. refine (ex_intro _ x2 _). auto.
+++++ inversion H.
++++++ subst. inversion H5.
++++++ subst. inversion H5. subst. apply inj_pairT2 in H5. inversion H5.
subst. inversion H4. subst. apply inj_pairT2 in H4. inversion H4. subst.
assert (initial_move (P F) (existT (fun i : I (P F) => (unit + N (P F) i)%type) j
          (inr m))).
{apply H2. split.
+ auto.
+ unfold not. intros. apply inj_pairT2 in H6. inversion H6. subst. contradiction H1. auto.
} apply initial_is_unit in H6. destruct H6. inversion H6.
Qed. 

Definition asynchronous_arena_tensor (A B : AsynchronousArena) 
(positive1 : (finite_payoff_position A) nil = (-1)%Z)
(positive2 : (finite_payoff_position B) nil = (-1)%Z)
: AsynchronousArena.
  refine({| 
            E := event_structure_tensor (E A) (E B);
            polarity m := match m with
                          | existT _ (i,j) (inl ll) => true
                          | existT _ (i,j) (inr (inl m)) => (polarity A) (existT _ i (inr m))
                          | existT _ (i,j) (inr (inr m)) => (polarity B) (existT _ j (inr m))
                          end;
            finite_payoff_position l :=
              (match l with
                | nil => (-1)%Z
                | _ => let left := finite_payoff_position A (cast_tensor_to_left _ _ l) in
                       let right := finite_payoff_position B (cast_tensor_to_right _ _ l) in
                       tensor left right
              end);
            finite_payoff_walk w :=
              let fp := cast_tensor_to_left _ _ (fst (fst w)) in
              let fm := cast_tensor_to_left _ _ (snd (fst w)) in
              let sp := cast_tensor_to_left _ _ (fst (snd w)) in
              let sm := cast_tensor_to_left _ _ (snd (snd w)) in
              let left := finite_payoff_walk A ((fp, fm), (sp, sm)) in
              let fp := cast_tensor_to_right _ _ (fst (fst w)) in
              let fm := cast_tensor_to_right _ _ (snd (fst w)) in
              let sp := cast_tensor_to_right _ _ (fst (snd w)) in
              let sm := cast_tensor_to_right _ _ (snd (snd w)) in
              let right := finite_payoff_walk B ((fp, fm), (sp, sm)) in
              tensor left right;
            infinite_payoff l :=
              let left := infinite_payoff A (cast_tensor_inf_to_left _ _ l) in
              let right := infinite_payoff B (cast_tensor_inf_to_right _ _ l) in
              tensor_infinity left right;
         |}).
Proof.
- left. auto.
- intros. apply initial_is_unit in H. destruct H. subst.
destruct x. easy.
- intros. apply second_in_tensor_is_second in H. destruct H.
+ destruct H. destruct H. destruct H. destruct H. subst. apply polarity_second in H0.
rewrite positive1 in H0. auto.
+ destruct H. destruct H. destruct H. destruct H. subst. apply polarity_second in H0.
rewrite positive2 in H0. auto.
- intros. destruct H. destruct w. destruct p. destruct p0. simpl in *. subst. simpl.
assert ((finite_payoff_walk A
     (cast_tensor_to_left (E A) (E B) p, nil,
     (cast_tensor_to_left (E A) (E B) p0, nil))) = 0%Z).
{apply initial_null. auto. }
assert ((finite_payoff_walk B
     (cast_tensor_to_right (E A) (E B) p, nil,
     (cast_tensor_to_right (E A) (E B) p0, nil))) = 0%Z).
{apply initial_null. auto. }
assert (forall a b f, a = 0%Z /\ b = 0%Z /\ f 0%Z 0%Z  = 0%Z
-> f a b = 0%Z).
{intros. destruct H1. destruct H2. subst. auto. }
apply H1. auto.
Defined.

Definition asynchronous_game_tensor_positive (G H: AsynchronousGame) 
(pos1 : (finite_payoff_position (A G)) nil = (-1)%Z)
(pos2 : (finite_payoff_position (A H)) nil = (-1)%Z)
: AsynchronousGame.
  refine({| 
             A := asynchronous_arena_tensor (A G) (A H) pos1 pos2;
             X := product_group (X G) (X H);
             Y := product_group (Y G) (Y H);
             action g m h := match m with
                                | existT _ (i,j) (inl tt) => 
                                  (match action G (fst g) (existT _ i (inl tt)) (fst h),
                                         action H (snd g) (existT _ j (inl tt)) (snd h) with
                                    | existT _ i _, existT _ j _ => existT _ (i,j) (inl tt)
                                  end)
                                | existT _ (i,j) (inr (inl m)) => 
                                  (match action G (fst g) (existT _ i (inr m)) (fst h),
                                         action H (snd g) (existT _ j (inl tt)) (snd h) with
                                    | existT _ i (inl tt), existT _ j _ => existT _ (i,j) (inl tt)
                                    | existT _ i (inr m), existT _ j _ => existT _ (i,j) (inr (inl m))
                                  end)
                                | existT _ (i,j) (inr (inr m)) => 
                                  (match action G (fst g) (existT _ i (inl tt)) (fst h),
                                         action H (snd g) (existT _ j (inr m)) (snd h) with
                                    | existT _ i _, existT _ j (inl tt) => existT _ (i,j) (inl tt)
                                    | existT _ i _, existT _ j (inr m) => existT _ (i,j) (inr (inr m))
                                  end)
                             end;
        |}).
Proof.
- intros. destruct m. destruct x. destruct s.
+ destruct u. rewrite action_id. rewrite action_id. simpl. auto.
+ destruct n.
++ simpl in *. flatten_all.
+++ subst. rewrite action_id in e. inversion e.
+++ subst. rewrite action_id in e. inversion e. subst. rewrite action_id in e1.
inversion e1. subst. auto.
++ flatten_all.
+++ subst. simpl in e. rewrite action_id in e. inversion e. subst.
rewrite action_id in e0. inversion e0.
+++ subst. simpl in e. rewrite action_id in e. inversion e. subst.
rewrite action_id in e0. inversion e0. subst. apply inj_pairT2 in e0. inversion e0. subst.
auto.
- intros. destruct g. destruct g'. destruct h. destruct h'. flatten_all
+ subst. simpl in *. inversion e6. subst. inversion e5. subst. 
apply inj_pairT2 in e5. subst.
rewrite action_compatible in e3.
rewrite action_compatible in e4. rewrite e6 in e3.
assert (leq _
(action G g (existT (fun i : I (P (E (A G))) => 
(unit + N (P (E (A G))) i)%type) i1 (inl tt)) g5)
(action G g (existT (fun i : I (P (E (A G))) => 
(unit + N (P (E (A G))) i)%type) i1 s3) g5)).
{apply coherence_1. apply unit_is_least. auto. } rewrite e3 in H0.
rewrite e11 in H0. apply leq_same_component in H0. subst.
rewrite e7 in e4.
assert (leq _
(action H g0 (existT (fun i : I (P (E (A H))) =>
(unit + N (P (E (A H))) i)%type) i2 (inl tt)) g6)
(action H g0 (existT (fun i : I (P (E (A H))) =>
(unit + N (P (E (A H))) i)%type) i2 s4) g6)).
{apply coherence_1. apply unit_is_least. auto. }
rewrite e12 in H0. rewrite e4 in H0. apply leq_same_component in H0. subst. auto.
+ subst. simpl in *. inversion e5.
+ subst. simpl in *. inversion e5.
+ subst. simpl in *. inversion e5.
+ subst. simpl in *. inversion e5.
+ subst. simpl in *. inversion e6. subst.
rewrite action_compatible in e3. rewrite action_compatible in H1. assert (exists k k1,
action G g1 (existT (fun i : I (P (E (A G))) => (unit + N (P (E (A G))) i)%type) i (inr n0)) g3 =
     existT (fun i : I (P (E (A G))) => (unit + N (P (E (A G))) i)%type) k (inr k1)).
{apply action_preserves_non_initial. }
destruct H0. destruct H0. rewrite e8 in H0. inversion H0.
+ subst. simpl in *. inversion e7. 
+ subst. simpl in *. inversion e7. 
+ subst. simpl in *. inversion e7.
+ subst. simpl in *. inversion e7.
+ subst. simpl in *. inversion e7. 
+ subst. simpl in *. inversion e6. subst. 
assert (exists k k1,
action G g
        (existT (fun i : I (P (E (A G))) => (unit + N (P (E (A G))) i)%type) i1
           (inr n3)) g5 =
      existT (fun i : I (P (E (A G))) => (unit + N (P (E (A G))) i)%type) k
        (inr k1)).
{apply action_preserves_non_initial. }
destruct H0. destruct H0. rewrite e14 in H0. inversion H0.
+ subst. simpl in *. inversion e6. subst. rewrite action_compatible in e3.
assert (exists k k1,
action G g1
          (existT
             (fun i : I (P (E (A G))) => (unit + N (P (E (A G))) i)%type) i
             (inr n0)) g3 = 
existT (fun i : I (P (E (A G))) => (unit + N (P (E (A G))) i)%type) k
       (inr k1)
).
{apply action_preserves_non_initial. }
destruct H0. destruct H0. rewrite H0 in e3.
assert (exists k k1,
action G g
       (existT (fun i : I (P (E (A G))) => (unit + N (P (E (A G))) i)%type)
          x (inr x2)) g5 = 
existT (fun i : I (P (E (A G))) => (unit + N (P (E (A G))) i)%type) k
       (inr k1)).
{apply action_preserves_non_initial. }
destruct H2. destruct H2. rewrite e3 in H2. inversion H2.
+ subst. simpl in *. inversion e7.
+ subst. simpl in *. inversion e7.
+ subst. simpl in *. inversion e6. subst. inversion e5. subst.
rewrite action_compatible in e3.
assert (exists k k1,
action G g1
       (existT (fun i : I (P (E (A G))) => (unit + N (P (E (A G))) i)%type)
          i (inr n0)) g3 = 
existT (fun i : I (P (E (A G))) => (unit + N (P (E (A G))) i)%type) k
       (inr k1)).
{apply action_preserves_non_initial. }
destruct H0. destruct H0. rewrite e7 in H0. inversion H0.
+ subst. simpl in *. inversion e6.
+ subst. simpl in *. inversion e6.
+ subst. simpl in *. inversion e6.
+ subst. simpl in *. inversion e6.
+ subst. simpl in *. inversion e6.
+ subst. simpl in *. inversion e6. rewrite action_compatible in e3.
assert (exists k k1,
action G g
        (existT
           (fun i : I (P (E (A G))) => (unit + N (P (E (A G))) i)%type) i1
           (inr n4)) g5 = 
existT (fun i : I (P (E (A G))) => (unit + N (P (E (A G))) i)%type)
        k (inr k1)
).
{apply action_preserves_non_initial. }
destruct H0. destruct H0. rewrite e13 in H0. inversion H0.
+ subst. simpl in *. inversion e6. subst. apply inj_pairT2 in e6. inversion e6. subst. 
rewrite action_compatible in e3. rewrite action_compatible in e5. rewrite e7 in e3.
rewrite e13 in e3. inversion e3. subst. apply inj_pairT2 in e3. inversion e3. subst.
rewrite e9 in e5. 
assert (leq _
(action H g0
        (existT
           (fun i : I (P (E (A H))) => (unit + N (P (E (A H))) i)%type)
           i2 (inl tt)) g6)
(action H g0
       (existT
          (fun i : I (P (E (A H))) => (unit + N (P (E (A H))) i)%type) i2
          s4) g6)).
{apply coherence_1. apply unit_is_least. auto. }
rewrite e5 in H0. rewrite e15 in H0. apply leq_same_component in H0. subst. auto.
+ subst. simpl in *. inversion e6.
+ subst. simpl in *. inversion e6.
+ subst. simpl in *.
assert (exists k k1,
action H g2
       (existT (fun i : I (P (E (A H))) => (unit + N (P (E (A H))) i)%type)
          i0 (inr n0)) g4 = 
existT (fun i : I (P (E (A H))) => (unit + N (P (E (A H))) i)%type) k
       (inr k1)).
{apply action_preserves_non_initial. }
destruct H0. destruct H0. rewrite e9 in H0. inversion H0.
+ subst. simpl in *. inversion e7.
+ subst. simpl in *. inversion e7.
+ subst. simpl in *. inversion e7.
+ subst. simpl in *. inversion e7.
+ subst. simpl in *. inversion e7.
+ subst. simpl in *. inversion e7.
+ subst. simpl in *. inversion e7.
+ subst. simpl in *.
assert (exists k k1,
action H g0
        (existT
           (fun i : I (P (E (A H))) => (unit + N (P (E (A H))) i)%type) i2
           (inr n3)) g6 =
existT (fun i : I (P (E (A H))) => (unit + N (P (E (A H))) i)%type)
        k (inr k1)).
{apply action_preserves_non_initial. }
destruct H0. destruct H0. rewrite e15 in H0. inversion H0.
+ subst. simpl in *. rewrite action_compatible in e4.
assert (exists k k1,
action H g2
          (existT
             (fun i : I (P (E (A H))) =>
              (unit + N (P (E (A H))) i)%type) i0
             (inr n0)) g4 =
existT (fun i : I (P (E (A H))) => (unit + N (P (E (A H))) i)%type) k
       (inr k1)).
{apply action_preserves_non_initial. }
destruct H0. destruct H0. rewrite H0 in e4. 
assert (exists k k1,
action H g0
          (existT
             (fun i : I (P (E (A H))) =>
              (unit + N (P (E (A H))) i)%type) x
             (inr x2)) g6 =
existT (fun i : I (P (E (A H))) => (unit + N (P (E (A H))) i)%type) k
       (inr k1)).
{apply action_preserves_non_initial. }
destruct H1. destruct H1. rewrite H1 in e4. inversion e4.
+ subst. simpl in *.
assert (exists k k1,
action H g2
       (existT (fun i : I (P (E (A H))) => (unit + N (P (E (A H))) i)%type)
          i0 (inr n0)) g4 = 
existT (fun i : I (P (E (A H))) => (unit + N (P (E (A H))) i)%type) k
       (inr k1)).
{apply action_preserves_non_initial. }
destruct H0. destruct H0. rewrite e8 in H0. inversion H0.
+ subst. simpl in *. inversion e6.
+ subst. simpl in *. inversion e6.
+ subst. simpl in *. inversion e6.
+ subst. simpl in *. inversion e6.
+ subst. simpl in *. inversion e6.
+ subst. simpl in *. inversion e6.
+ subst. simpl in *. inversion e6.
+ subst. simpl in *. 
assert (exists k k1,
action H g0
        (existT
           (fun i : I (P (E (A H))) => (unit + N (P (E (A H))) i)%type) i2
           (inr n4)) g6 =
existT (fun i : I (P (E (A H))) => (unit + N (P (E (A H))) i)%type)
        k (inr k1)).
{apply action_preserves_non_initial. }
destruct H0. destruct H0. rewrite e14 in H0. inversion H0.
+ subst. simpl in *. rewrite action_compatible in e3. inversion e6. subst.
apply inj_pairT2 in e6. inversion e6. subst. rewrite action_compatible in e4.
rewrite e8 in e4. rewrite e7 in e3. rewrite e4 in e14. inversion e14. subst.
apply inj_pairT2 in e14. inversion e14. subst.
assert (leq _
(action G g
        (existT
           (fun i : I (P (E (A G))) =>
            (unit + N (P (E (A G))) i)%type) i1
           (inl tt)) g5)
(action G g
       (existT
          (fun i : I (P (E (A G))) =>
           (unit + N (P (E (A G))) i)%type) i1 s3) g5)).
{apply coherence_1. apply unit_is_least. auto. }
rewrite e13 in H0. rewrite e3 in H0. apply leq_same_component in H0. subst. auto.
- intros. destruct g. destruct h. flatten_all; subst; simpl in *; try (
inversion H0; subst; inversion H2; try (subst; inversion H3 )).
+ inversion H0.
++ subst. apply inj_pairT2 in H6. subst. rewrite e3 in e9. inversion e9. subst.
apply inj_pairT2 in e9. subst. rewrite e4 in e10. inversion e10. subst. apply inj_pairT2 in e10.
subst. auto. apply leq_tensor_least.
++ subst. inversion H2.
++ subst. inversion H2.
+ assert (exists k k1, action G g
       (existT (fun i : I (P (E (A G))) => (unit + N (P (E (A G))) i)%type)
          i1 (inr n1)) g1 = 
existT (fun i : I (P (E (A G))) => (unit + N (P (E (A G))) i)%type) k
       (inr k1)).
{apply action_preserves_non_initial. }
destruct H1. destruct H1. rewrite e9 in H1. inversion H1.
+ inversion H0.
++ subst.
assert (leq _ (action G g
       (existT
          (fun i : I (P (E (A G))) => (unit + N (P (E (A G))) i)%type) i1
          (inl tt)) g1) (action G g
       (existT
          (fun i : I (P (E (A G))) => (unit + N (P (E (A G))) i)%type) i1
          (inr n1)) g1 )).
{apply coherence_1. apply unit_is_least. auto. }
rewrite e9 in H1. rewrite e3 in H1. assert (H2 := H1).
apply leq_same_component in H1. subst. rewrite e4 in e11. inversion e11. subst.
apply leq_tensor_least.
++ subst. inversion H2.
++ subst. inversion H2.
+ inversion H0.
++ subst. rewrite e3 in e9. inversion e9. subst.
assert (leq _ (action H g0
       (existT (fun i : I (P (E (A H))) => (unit + N (P (E (A H))) i)%type) i2
          (inl tt)) g2) (action H g0
        (existT (fun i : I (P (E (A H))) => (unit + N (P (E (A H))) i)%type) i2
           (inr n1)) g2)).
{apply coherence_1. apply unit_is_least. auto. }
rewrite e10 in H1. rewrite e4 in H1. apply leq_same_component in H1. subst. 
apply leq_tensor_least.
++ subst. inversion H3.
++ subst. inversion H2. 
+ inversion H0.
++ subst. rewrite e3 in e9. inversion e9. subst.
assert (leq _ (action H g0
       (existT (fun i : I (P (E (A H))) => (unit + N (P (E (A H))) i)%type) i2
          (inl tt)) g2) (action H g0
        (existT (fun i : I (P (E (A H))) => (unit + N (P (E (A H))) i)%type) i2
           (inr n1)) g2)).
{apply coherence_1. apply unit_is_least. auto. }
rewrite e10 in H1. rewrite e4 in H1. apply leq_same_component in H1. subst. 
apply leq_tensor_least.
++ subst. inversion H3.
++ subst. inversion H2.
+ inversion H0.
++ subst. inversion H3.
assert (exists k k1,
action G g
        (existT (fun i : I (P (E (A G))) => (unit + N (P (E (A G))) i)%type) i3
           (inr n3)) g1
= existT (fun i : I (P (E (A G))) => (unit + N (P (E (A G))) i)%type) k
        (inr k1)).
{apply action_preserves_non_initial. }
destruct H6. destruct H6. rewrite e11 in H6. inversion H6.
++ subst. inversion H2.
assert (exists k k1,
action G g
        (existT (fun i : I (P (E (A G))) => (unit + N (P (E (A G))) i)%type) i3
           (inr n3)) g1
= existT (fun i : I (P (E (A G))) => (unit + N (P (E (A G))) i)%type) k
        (inr k1)).
{apply action_preserves_non_initial. }
destruct H6. destruct H6. rewrite e11 in H6. inversion H6.
+ inversion H0.
++ subst. inversion H2. subst. inversion H3. subst.
assert (exists k k1,
action G g
        (existT (fun i : I (P (E (A G))) => (unit + N (P (E (A G))) i)%type) i3
           (inr n1)) g1
= existT (fun i : I (P (E (A G))) => (unit + N (P (E (A G))) i)%type) k
        (inr k1)).
{apply action_preserves_non_initial. }
destruct H9. destruct H9. rewrite e3 in H9. inversion H9.
++ subst. inversion H2.
assert (exists k k1,
action G g
        (existT (fun i : I (P (E (A G))) => (unit + N (P (E (A G))) i)%type) i3
           (inr n1)) g1
= existT (fun i : I (P (E (A G))) => (unit + N (P (E (A G))) i)%type) k
        (inr k1)).
{apply action_preserves_non_initial. }
destruct H6. destruct H6. rewrite e3 in H6. inversion H6.

+ inversion H0.
++ subst. inversion H2. subst. inversion H3.
assert (exists k k1,
 action G g
        (existT (fun i : I (P (E (A G))) => (unit + N (P (E (A G))) i)%type)
           i3 (inr n4)) g1 = 
existT (fun i : I (P (E (A G))) => (unit + N (P (E (A G))) i)%type) k
        (inr k1)).
{apply action_preserves_non_initial. }
destruct H9. destruct H9. rewrite e10 in H9. inversion H9.
++ assert (exists k k1,
action G g
        (existT (fun i : I (P (E (A G))) => (unit + N (P (E (A G))) i)%type)
           i1 (inr n4)) g1 = 
existT (fun i : I (P (E (A G))) => (unit + N (P (E (A G))) i)%type) k
        (inr k1)).
{apply action_preserves_non_initial. }
destruct H11. destruct H11. rewrite e10 in H11. inversion H11.
+ inversion H0.
++ subst. inversion H2. subst. inversion H5. apply inj_pairT2 in H5. inversion H5. subst.
inversion H6. subst. apply inj_pairT2 in H6. inversion H6. subst. auto.
inversion H8. subst. apply inj_pairT2 in H8. inversion H8. subst. apply inj_pairT2 in H7.
inversion H7. subst. apply inj_pairT2 in H3. inversion H3. subst.
assert (leq _
(action G g (existT (fun i : I (P (E (A G))) => (unit + N (P (E (A G))) i)%type) i (inr m0)) g1)
(action G g
        (existT
           (fun i : I (P (E (A G))) =>
            (unit + N (P (E (A G))) i)%type) i 
           (inr m')) g1)).
{apply coherence_1. auto. }
rewrite e10 in H9. rewrite e3 in H9. assert (H10 := H9). apply leq_same_component in H10. subst.
rewrite e5 in e12. inversion e12. subst.
apply leq_tensor_left with (i:=x3) (j:=x4) (m:=n2) (m':=n5). auto. auto. auto.
++ subst. inversion H2. inversion H7.
+ inversion H0.
++ subst. inversion H2. subst. inversion H3. inversion H8.
++ subst. inversion H2.
assert (exists k k1,
action H g0
       (existT (fun i : I (P (E (A H))) => (unit + N (P (E (A H))) i)%type) j (inr n1)) g2 = 
existT (fun i : I (P (E (A H))) => (unit + N (P (E (A H))) i)%type) k (inr k1)).
{apply action_preserves_non_initial. }
destruct H6. destruct H6. rewrite e4 in H6. inversion H6.
+ inversion H0.
++ subst. inversion H2. subst. inversion H3. subst. inversion H7.
++ subst.
assert (exists k k1,
action H g0
       (existT (fun i : I (P (E (A H))) => (unit + N (P (E (A H))) i)%type) j
          (inr n1)) g2 = 
existT (fun i : I (P (E (A H))) => (unit + N (P (E (A H))) i)%type) k
       (inr k1)).
{apply action_preserves_non_initial. }
destruct H5. destruct H5. rewrite e4 in H5. inversion H5.
+ inversion H0.
++ subst. inversion H2. subst. inversion H3. subst. inversion H7.
++ subst.
assert (exists k k1,
action H g0
       (existT (fun i : I (P (E (A H))) => (unit + N (P (E (A H))) i)%type) j
          (inr n4)) g2 = 
existT (fun i : I (P (E (A H))) => (unit + N (P (E (A H))) i)%type) k
       (inr k1)).
{apply action_preserves_non_initial. }
destruct H5. destruct H5. rewrite e11 in H5. inversion H5.
+ inversion H0.
++ subst. inversion H2. subst. inversion H3. subst. inversion H7.
++ subst. inversion H8. subst. apply inj_pairT2 in H8. inversion H8. subst.
apply inj_pairT2 in H7. inversion H7. subst. apply inj_pairT2 in H3. inversion H3. subst. rewrite e3 in e10.
inversion e10. subst.
assert (leq _
(action H g0
       (existT (fun i : I (P (E (A H))) => (unit + N (P (E (A H))) i)%type) j0
          (inr m0)) g2)
(action H g0
        (existT (fun i : I (P (E (A H))) => (unit + N (P (E (A H))) i)%type) j0
           (inr m')) g2)).
{apply coherence_1. auto. }
rewrite e11 in H5. rewrite e4 in H5. assert (H6 := H5). apply leq_same_component in H6. subst.
apply leq_tensor_right with (i:=x3) (j:=x4) (m:=n2) (m':=n5). auto. auto. auto.
- intros. destruct g. destruct h. flatten_all; subst; simpl in *.
+ auto.
+ assert (exists k k1,
action G g
       (existT (fun i : I (P (E (A G))) => (unit + N (P (E (A G))) i)%type) i
          (inr n0)) g1 = 
existT (fun i : I (P (E (A G))) => (unit + N (P (E (A G))) i)%type) k
       (inr k1)).
{apply action_preserves_non_initial. }
destruct H0. destruct H0. rewrite e3 in H0. inversion H0.
+ rewrite <- e3. apply coherence_2.
+ assert (exists k k1,
action H g0
       (existT (fun i : I (P (E (A H))) => (unit + N (P (E (A H))) i)%type) i0
          (inr n0)) g2 = 
existT (fun i : I (P (E (A H))) => (unit + N (P (E (A H))) i)%type) k
       (inr k1)).
{apply action_preserves_non_initial. }
destruct H0. destruct H0. rewrite e4 in H0. inversion H0.
+ rewrite <- e4. apply coherence_2.
- intros. destruct g. flatten_all; subst; simpl in *; destruct H0.
+ inversion H0.
+ assert (exists k k1,
action G g
       (existT (fun i : I (P (E (A G))) => (unit + N (P (E (A G))) i)%type) i
          (inr n0)) (id (Y G)) = 
existT (fun i : I (P (E (A G))) => (unit + N (P (E (A G))) i)%type) k
       (inr k1)).
{apply action_preserves_non_initial. }
destruct H2. destruct H2. rewrite e3 in H2. inversion H2.
+ remember (existT
          (fun i : I (P (E (A G))) * I (P (E (A H))) =>
           (unit +
            (N (P (E (A G))) (fst i) +
             N (P (E (A H))) (snd i)))%type) 
          (i, i0) (inr (inl n0))).
 assert ( s =
     (let (x, s) := s in
      (let
         (i, j) as x0
          return
            (unit + (N (P (E (A G))) (fst x0) + N (P (E (A H))) (snd x0)) ->
             M (partial_order_tensor (P (E (A G))) (P (E (A H))))) := x in
       fun s0 : unit + (N (P (E (A G))) i + N (P (E (A H))) j) =>
       match s0 with
       | inl tt =>
           let (i0, _) :=
             action G g
               (existT (fun i0 : I (P (E (A G))) => (unit + N (P (E (A G))) i0)%type) i (inl tt))
               (id (Y G)) in
           let (j0, _) :=
             action H g0
               (existT (fun i1 : I (P (E (A H))) => (unit + N (P (E (A H))) i1)%type) j (inl tt))
               (id (Y H)) in
           existT
             (fun i1 : I (P (E (A G))) * I (P (E (A H))) =>
              (unit + (N (P (E (A G))) (fst i1) + N (P (E (A H))) (snd i1)))%type) 
             (i0, j0) (inl tt)
       | inr (inl m) =>
           let (i0, s1) :=
             action G g
               (existT (fun i0 : I (P (E (A G))) => (unit + N (P (E (A G))) i0)%type) i (inr m))
               (id (Y G)) in
           match s1 with
           | inl tt =>
               let (j0, _) :=
                 action H g0
                   (existT (fun i1 : I (P (E (A H))) => (unit + N (P (E (A H))) i1)%type) j
                      (inl tt)) (id (Y H)) in
               existT
                 (fun i1 : I (P (E (A G))) * I (P (E (A H))) =>
                  (unit + (N (P (E (A G))) (fst i1) + N (P (E (A H))) (snd i1)))%type) 
                 (i0, j0) (inl tt)
           | inr m0 =>
               let (j0, _) :=
                 action H g0
                   (existT (fun i1 : I (P (E (A H))) => (unit + N (P (E (A H))) i1)%type) j
                      (inl tt)) (id (Y H)) in
               existT
                 (fun i1 : I (P (E (A G))) * I (P (E (A H))) =>
                  (unit + (N (P (E (A G))) (fst i1) + N (P (E (A H))) (snd i1)))%type) 
                 (i0, j0) (inr (inl m0))
           end
       | inr (inr m) =>
           let (i0, _) :=
             action G g
               (existT (fun i0 : I (P (E (A G))) => (unit + N (P (E (A G))) i0)%type) i (inl tt))
               (id (Y G)) in
           let (j0, s2) :=
             action H g0
               (existT (fun i1 : I (P (E (A H))) => (unit + N (P (E (A H))) i1)%type) j (inr m))
               (id (Y H)) in
           match s2 with
           | inl tt =>
               existT
                 (fun i1 : I (P (E (A G))) * I (P (E (A H))) =>
                  (unit + (N (P (E (A G))) (fst i1) + N (P (E (A H))) (snd i1)))%type) 
                 (i0, j0) (inl tt)
           | inr m0 =>
               existT
                 (fun i1 : I (P (E (A G))) * I (P (E (A H))) =>
                  (unit + (N (P (E (A G))) (fst i1) + N (P (E (A H))) (snd i1)))%type) 
                 (i0, j0) (inr (inr m0))
           end
       end) s)).
{apply H1. rewrite Heqs. apply leq_tensor_left with (i:=i) (j:=i0) (m:=n0) (m':=n0). 
apply reflexive. auto. auto. }
rewrite Heqs in H2. simpl in H2. rewrite e3 in H2. rewrite e5 in H2. auto.
+ assert (exists k k1,
action H g0
       (existT (fun i : I (P (E (A H))) => (unit + N (P (E (A H))) i)%type) i0 (inr n0))
       (id (Y H)) = 
existT (fun i : I (P (E (A H))) => (unit + N (P (E (A H))) i)%type) k (inr k1)).
{apply action_preserves_non_initial. }
destruct H2. destruct H2. rewrite e4 in H2. inversion H2.
+ remember (existT
          (fun i : I (P (E (A G))) * I (P (E (A H))) =>
           (unit + (N (P (E (A G))) (fst i) + N (P (E (A H))) (snd i)))%type) 
          (i, i0) (inr (inr n0))).
assert 
(s =
     (let (x, s) := s in
      (let
         (i, j) as x0
          return
            (unit + (N (P (E (A G))) (fst x0) + N (P (E (A H))) (snd x0)) ->
             M (partial_order_tensor (P (E (A G))) (P (E (A H))))) := x in
       fun s0 : unit + (N (P (E (A G))) i + N (P (E (A H))) j) =>
       match s0 with
       | inl tt =>
           let (i0, _) :=
             action G g
               (existT (fun i0 : I (P (E (A G))) => (unit + N (P (E (A G))) i0)%type) i
                  (inl tt)) (id (Y G)) in
           let (j0, _) :=
             action H g0
               (existT (fun i1 : I (P (E (A H))) => (unit + N (P (E (A H))) i1)%type) j
                  (inl tt)) (id (Y H)) in
           existT
             (fun i1 : I (P (E (A G))) * I (P (E (A H))) =>
              (unit + (N (P (E (A G))) (fst i1) + N (P (E (A H))) (snd i1)))%type) 
             (i0, j0) (inl tt)
       | inr (inl m) =>
           let (i0, s1) :=
             action G g
               (existT (fun i0 : I (P (E (A G))) => (unit + N (P (E (A G))) i0)%type) i
                  (inr m)) (id (Y G)) in
           match s1 with
           | inl tt =>
               let (j0, _) :=
                 action H g0
                   (existT (fun i1 : I (P (E (A H))) => (unit + N (P (E (A H))) i1)%type) j
                      (inl tt)) (id (Y H)) in
               existT
                 (fun i1 : I (P (E (A G))) * I (P (E (A H))) =>
                  (unit + (N (P (E (A G))) (fst i1) + N (P (E (A H))) (snd i1)))%type)
                 (i0, j0) (inl tt)
           | inr m0 =>
               let (j0, _) :=
                 action H g0
                   (existT (fun i1 : I (P (E (A H))) => (unit + N (P (E (A H))) i1)%type) j
                      (inl tt)) (id (Y H)) in
               existT
                 (fun i1 : I (P (E (A G))) * I (P (E (A H))) =>
                  (unit + (N (P (E (A G))) (fst i1) + N (P (E (A H))) (snd i1)))%type)
                 (i0, j0) (inr (inl m0))
           end
       | inr (inr m) =>
           let (i0, _) :=
             action G g
               (existT (fun i0 : I (P (E (A G))) => (unit + N (P (E (A G))) i0)%type) i
                  (inl tt)) (id (Y G)) in
           let (j0, s2) :=
             action H g0
               (existT (fun i1 : I (P (E (A H))) => (unit + N (P (E (A H))) i1)%type) j
                  (inr m)) (id (Y H)) in
           match s2 with
           | inl tt =>
               existT
                 (fun i1 : I (P (E (A G))) * I (P (E (A H))) =>
                  (unit + (N (P (E (A G))) (fst i1) + N (P (E (A H))) (snd i1)))%type)
                 (i0, j0) (inl tt)
           | inr m0 =>
               existT
                 (fun i1 : I (P (E (A G))) * I (P (E (A H))) =>
                  (unit + (N (P (E (A G))) (fst i1) + N (P (E (A H))) (snd i1)))%type)
                 (i0, j0) (inr (inr m0))
           end
       end) s)).
{apply H1. rewrite Heqs. apply leq_tensor_right with (i:=i) (j:=i0)
(m:=n0) (m':=n0). apply reflexive. auto. auto. }
rewrite Heqs in H2. rewrite e3 in H2. rewrite e4 in H2. auto.
- intros. destruct h. flatten_all; subst; simpl in *; destruct H0.
+ remember (existT
          (fun i : I (P (E (A G))) * I (P (E (A H))) =>
           (unit + (N (P (E (A G))) (fst i) + N (P (E (A H))) (snd i)))%type)
          (i, i0) (inl tt)).
assert (s =
     (let (x, s) := s in
      (let
         (i, j) as x0
          return
            (unit + (N (P (E (A G))) (fst x0) + N (P (E (A H))) (snd x0)) ->
             M (partial_order_tensor (P (E (A G))) (P (E (A H))))) := x in
       fun s0 : unit + (N (P (E (A G))) i + N (P (E (A H))) j) =>
       match s0 with
       | inl tt =>
           let (i0, _) :=
             action G (id (X G))
               (existT
                  (fun i0 : I (P (E (A G))) => (unit + N (P (E (A G))) i0)%type) i
                  (inl tt)) g in
           let (j0, _) :=
             action H (id (X H))
               (existT
                  (fun i1 : I (P (E (A H))) => (unit + N (P (E (A H))) i1)%type) j
                  (inl tt)) g0 in
           existT
             (fun i1 : I (P (E (A G))) * I (P (E (A H))) =>
              (unit + (N (P (E (A G))) (fst i1) + N (P (E (A H))) (snd i1)))%type)
             (i0, j0) (inl tt)
       | inr (inl m) =>
           let (i0, s1) :=
             action G (id (X G))
               (existT
                  (fun i0 : I (P (E (A G))) => (unit + N (P (E (A G))) i0)%type) i
                  (inr m)) g in
           match s1 with
           | inl tt =>
               let (j0, _) :=
                 action H (id (X H))
                   (existT
                      (fun i1 : I (P (E (A H))) => (unit + N (P (E (A H))) i1)%type)
                      j (inl tt)) g0 in
               existT
                 (fun i1 : I (P (E (A G))) * I (P (E (A H))) =>
                  (unit + (N (P (E (A G))) (fst i1) + N (P (E (A H))) (snd i1)))%type)
                 (i0, j0) (inl tt)
           | inr m0 =>
               let (j0, _) :=
                 action H (id (X H))
                   (existT
                      (fun i1 : I (P (E (A H))) => (unit + N (P (E (A H))) i1)%type)
                      j (inl tt)) g0 in
               existT
                 (fun i1 : I (P (E (A G))) * I (P (E (A H))) =>
                  (unit + (N (P (E (A G))) (fst i1) + N (P (E (A H))) (snd i1)))%type)
                 (i0, j0) (inr (inl m0))
           end
       | inr (inr m) =>
           let (i0, _) :=
             action G (id (X G))
               (existT
                  (fun i0 : I (P (E (A G))) => (unit + N (P (E (A G))) i0)%type) i
                  (inl tt)) g in
           let (j0, s2) :=
             action H (id (X H))
               (existT
                  (fun i1 : I (P (E (A H))) => (unit + N (P (E (A H))) i1)%type) j
                  (inr m)) g0 in
           match s2 with
           | inl tt =>
               existT
                 (fun i1 : I (P (E (A G))) * I (P (E (A H))) =>
                  (unit + (N (P (E (A G))) (fst i1) + N (P (E (A H))) (snd i1)))%type)
                 (i0, j0) (inl tt)
           | inr m0 =>
               existT
                 (fun i1 : I (P (E (A G))) * I (P (E (A H))) =>
                  (unit + (N (P (E (A G))) (fst i1) + N (P (E (A H))) (snd i1)))%type)
                 (i0, j0) (inr (inr m0))
           end
       end) s)).
{apply H1. rewrite Heqs. apply leq_tensor_least. } rewrite Heqs in H2.
rewrite e3 in H2. rewrite e4 in H2. auto.
+ assert (exists k k1,
action G (id (X G))
       (existT (fun i : I (P (E (A G))) => (unit + N (P (E (A G))) i)%type) i
          (inr n0)) g = 
     existT (fun i : I (P (E (A G))) => (unit + N (P (E (A G))) i)%type) k (inr k1)).
{apply action_preserves_non_initial. }
destruct H2. destruct H2. rewrite e3 in H2. inversion H2.
+ remember (existT
          (fun i : I (P (E (A G))) * I (P (E (A H))) =>
           (unit + (N (P (E (A G))) (fst i) + N (P (E (A H))) (snd i)))%type)
          (i, i0) (inr (inl n0))).
assert (s =
     (let (x, s) := s in
      (let
         (i, j) as x0
          return
            (unit + (N (P (E (A G))) (fst x0) + N (P (E (A H))) (snd x0)) ->
             M (partial_order_tensor (P (E (A G))) (P (E (A H))))) := x in
       fun s0 : unit + (N (P (E (A G))) i + N (P (E (A H))) j) =>
       match s0 with
       | inl tt =>
           let (i0, _) :=
             action G (id (X G))
               (existT
                  (fun i0 : I (P (E (A G))) => (unit + N (P (E (A G))) i0)%type) i
                  (inl tt)) g in
           let (j0, _) :=
             action H (id (X H))
               (existT
                  (fun i1 : I (P (E (A H))) => (unit + N (P (E (A H))) i1)%type) j
                  (inl tt)) g0 in
           existT
             (fun i1 : I (P (E (A G))) * I (P (E (A H))) =>
              (unit + (N (P (E (A G))) (fst i1) + N (P (E (A H))) (snd i1)))%type)
             (i0, j0) (inl tt)
       | inr (inl m) =>
           let (i0, s1) :=
             action G (id (X G))
               (existT
                  (fun i0 : I (P (E (A G))) => (unit + N (P (E (A G))) i0)%type) i
                  (inr m)) g in
           match s1 with
           | inl tt =>
               let (j0, _) :=
                 action H (id (X H))
                   (existT
                      (fun i1 : I (P (E (A H))) => (unit + N (P (E (A H))) i1)%type)
                      j (inl tt)) g0 in
               existT
                 (fun i1 : I (P (E (A G))) * I (P (E (A H))) =>
                  (unit + (N (P (E (A G))) (fst i1) + N (P (E (A H))) (snd i1)))%type)
                 (i0, j0) (inl tt)
           | inr m0 =>
               let (j0, _) :=
                 action H (id (X H))
                   (existT
                      (fun i1 : I (P (E (A H))) => (unit + N (P (E (A H))) i1)%type)
                      j (inl tt)) g0 in
               existT
                 (fun i1 : I (P (E (A G))) * I (P (E (A H))) =>
                  (unit + (N (P (E (A G))) (fst i1) + N (P (E (A H))) (snd i1)))%type)
                 (i0, j0) (inr (inl m0))
           end
       | inr (inr m) =>
           let (i0, _) :=
             action G (id (X G))
               (existT
                  (fun i0 : I (P (E (A G))) => (unit + N (P (E (A G))) i0)%type) i
                  (inl tt)) g in
           let (j0, s2) :=
             action H (id (X H))
               (existT
                  (fun i1 : I (P (E (A H))) => (unit + N (P (E (A H))) i1)%type) j
                  (inr m)) g0 in
           match s2 with
           | inl tt =>
               existT
                 (fun i1 : I (P (E (A G))) * I (P (E (A H))) =>
                  (unit + (N (P (E (A G))) (fst i1) + N (P (E (A H))) (snd i1)))%type)
                 (i0, j0) (inl tt)
           | inr m0 =>
               existT
                 (fun i1 : I (P (E (A G))) * I (P (E (A H))) =>
                  (unit + (N (P (E (A G))) (fst i1) + N (P (E (A H))) (snd i1)))%type)
                 (i0, j0) (inr (inr m0))
           end
       end) s)).
{apply H1. rewrite Heqs. apply leq_tensor_left with (i:=i) (j:=i0) (m:=n0) (m':=n0). 
apply reflexive. auto. auto. }
rewrite Heqs in H2. rewrite e3 in H2. rewrite e5 in H2. auto.
+ assert (exists k k1,
action H (id (X H))
       (existT (fun i : I (P (E (A H))) => (unit + N (P (E (A H))) i)%type) i0
          (inr n0)) g0 = 
     existT (fun i : I (P (E (A H))) => (unit + N (P (E (A H))) i)%type) k (inr k1)).
{apply action_preserves_non_initial. }
destruct H2. destruct H2. rewrite e4 in H2. inversion H2.
+ remember (existT
          (fun i : I (P (E (A G))) * I (P (E (A H))) =>
           (unit + (N (P (E (A G))) (fst i) + N (P (E (A H))) (snd i)))%type)
          (i, i0) (inr (inr n0))).
assert 
(s =
     (let (x, s) := s in
      (let
         (i, j) as x0
          return
            (unit + (N (P (E (A G))) (fst x0) + N (P (E (A H))) (snd x0)) ->
             M (partial_order_tensor (P (E (A G))) (P (E (A H))))) := x in
       fun s0 : unit + (N (P (E (A G))) i + N (P (E (A H))) j) =>
       match s0 with
       | inl tt =>
           let (i0, _) :=
             action G (id (X G))
               (existT
                  (fun i0 : I (P (E (A G))) => (unit + N (P (E (A G))) i0)%type) i
                  (inl tt)) g in
           let (j0, _) :=
             action H (id (X H))
               (existT
                  (fun i1 : I (P (E (A H))) => (unit + N (P (E (A H))) i1)%type) j
                  (inl tt)) g0 in
           existT
             (fun i1 : I (P (E (A G))) * I (P (E (A H))) =>
              (unit + (N (P (E (A G))) (fst i1) + N (P (E (A H))) (snd i1)))%type)
             (i0, j0) (inl tt)
       | inr (inl m) =>
           let (i0, s1) :=
             action G (id (X G))
               (existT
                  (fun i0 : I (P (E (A G))) => (unit + N (P (E (A G))) i0)%type) i
                  (inr m)) g in
           match s1 with
           | inl tt =>
               let (j0, _) :=
                 action H (id (X H))
                   (existT
                      (fun i1 : I (P (E (A H))) => (unit + N (P (E (A H))) i1)%type)
                      j (inl tt)) g0 in
               existT
                 (fun i1 : I (P (E (A G))) * I (P (E (A H))) =>
                  (unit + (N (P (E (A G))) (fst i1) + N (P (E (A H))) (snd i1)))%type)
                 (i0, j0) (inl tt)
           | inr m0 =>
               let (j0, _) :=
                 action H (id (X H))
                   (existT
                      (fun i1 : I (P (E (A H))) => (unit + N (P (E (A H))) i1)%type)
                      j (inl tt)) g0 in
               existT
                 (fun i1 : I (P (E (A G))) * I (P (E (A H))) =>
                  (unit + (N (P (E (A G))) (fst i1) + N (P (E (A H))) (snd i1)))%type)
                 (i0, j0) (inr (inl m0))
           end
       | inr (inr m) =>
           let (i0, _) :=
             action G (id (X G))
               (existT
                  (fun i0 : I (P (E (A G))) => (unit + N (P (E (A G))) i0)%type) i
                  (inl tt)) g in
           let (j0, s2) :=
             action H (id (X H))
               (existT
                  (fun i1 : I (P (E (A H))) => (unit + N (P (E (A H))) i1)%type) j
                  (inr m)) g0 in
           match s2 with
           | inl tt =>
               existT
                 (fun i1 : I (P (E (A G))) * I (P (E (A H))) =>
                  (unit + (N (P (E (A G))) (fst i1) + N (P (E (A H))) (snd i1)))%type)
                 (i0, j0) (inl tt)
           | inr m0 =>
               existT
                 (fun i1 : I (P (E (A G))) * I (P (E (A H))) =>
                  (unit + (N (P (E (A G))) (fst i1) + N (P (E (A H))) (snd i1)))%type)
                 (i0, j0) (inr (inr m0))
           end
       end) s)).
{apply H1. rewrite Heqs. apply leq_tensor_right with (i:=i) (j:=i0) (m:=n0) (m':=n0).
apply reflexive. auto. auto. }
rewrite Heqs in H2. rewrite e4 in H2. rewrite e3 in H2. auto.
- intros. destruct i. destruct
(action G (fst g)
       (existT (fun i1 : I (P (E (A G))) => (unit + N (P (E (A G))) i1)%type) i
          (inl tt)) (fst h)).
destruct (action H (snd g)
       (existT (fun i2 : I (P (E (A H))) => (unit + N (P (E (A H))) i2)%type) i0
          (inl tt)) (snd h)). refine (ex_intro _ (x,x0) _). auto.
- intros. destruct i. destruct m. 
+ destruct (action G (fst g)
       (existT (fun i1 : I (P (E (A G))) => (unit + N (P (E (A G))) i1)%type) i
          (inr n)) (fst h)) eqn:eqn1. destruct s.
++ assert (exists k k1,
action G (fst g)
         (existT (fun i1 : I (P (E (A G))) => (unit + N (P (E (A G))) i1)%type) i
            (inr n)) (fst h) =
existT (fun i : I (P (E (A G))) => (unit + N (P (E (A G))) i)%type) k (inr k1)).
{apply action_preserves_non_initial. }
destruct H0. destruct H0. rewrite eqn1 in H0. inversion H0.
++ destruct (action H (snd g)
       (existT (fun i1 : I (P (E (A H))) => (unit + N (P (E (A H))) i1)%type) i0
          (inl tt)) (snd h)) eqn:eqn2. refine (ex_intro _ (x,x0) _). refine (ex_intro _ (inl n0) _).
auto.
+ destruct (action G (fst g)
       (existT (fun i1 : I (P (E (A G))) => (unit + N (P (E (A G))) i1)%type) i
          (inl tt)) (fst h)) eqn:eqn1. destruct s.
++ destruct (action H (snd g)
       (existT (fun i1 : I (P (E (A H))) => (unit + N (P (E (A H))) i1)%type) i0
          (inr n)) (snd h)) eqn:eqn2. destruct s.
+++ assert (exists k k1,
action H (snd g)
         (existT (fun i1 : I (P (E (A H))) => (unit + N (P (E (A H))) i1)%type) i0
            (inr n)) (snd h) =
existT (fun i : I (P (E (A H))) => (unit + N (P (E (A H))) i)%type) k
         (inr k1)).
{apply action_preserves_non_initial. }
destruct H0. destruct H0. rewrite eqn2 in H0. inversion H0.
+++ refine (ex_intro _ (x,x0) _). refine (ex_intro _ (inr n0) _). auto.
++ assert (exists k,
action G (fst g)
         (existT (fun i1 : I (P (E (A G))) => (unit + N (P (E (A G))) i1)%type) i
            (inl tt)) (fst h) = 
existT (fun i : I (P (E (A G))) => (unit + N (P (E (A G))) i)%type) k
         (inl tt)).
{apply action_preserves_initial. }
destruct H0. rewrite eqn1 in H0. inversion H0.
Defined.

Definition asynchronous_game_tensor_left (G H: AsynchronousGame) 
(neg : (finite_payoff_position (A G)) nil = (1)%Z)
(pos : (finite_payoff_position (A H)) nil = (-1)%Z) : AsynchronousGame :=
asynchronous_game_tensor_positive
(asynchronous_game_lifting G neg (1)%Z)
H
(positive_lifting_is_positive G neg (1)%Z)
pos.

Definition asynchronous_game_tensor_right (G H: AsynchronousGame) 
(pos : (finite_payoff_position (A G)) nil = (-1)%Z)
(neg : (finite_payoff_position (A H)) nil = (1)%Z) : AsynchronousGame :=
asynchronous_game_tensor_positive
G
(asynchronous_game_lifting H neg (1)%Z)
pos
(positive_lifting_is_positive H neg (1)%Z).

Definition asynchronous_game_tensor_negative (G H: AsynchronousGame) 
(neg1 : (finite_payoff_position (A G)) nil = (1)%Z)
(neg2 : (finite_payoff_position (A H)) nil = (1)%Z) : AsynchronousGame :=
asynchronous_game_tensor_positive
(asynchronous_game_lifting G neg1 (1)%Z)
(asynchronous_game_lifting H neg2 (1)%Z)
(positive_lifting_is_positive G neg1 (1)%Z)
(positive_lifting_is_positive H neg2 (1)%Z).

Definition asynchronous_game_tensor (G H: AsynchronousGame) :
AsynchronousGame :=
match initial_payoff (A G), initial_payoff (A H) with
| left p, left p' => asynchronous_game_tensor_positive G H p p'
| left p, right p' => asynchronous_game_tensor_right G H p p'
| right p, left p' => asynchronous_game_tensor_left G H p p'
| right p, right p' => asynchronous_game_tensor_negative G H p p'
end.

