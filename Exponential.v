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

Inductive leq_exponential (P : PartialOrder) :
{i : ((I P) * nat) & (sum unit (N P (fst i))) } ->
{i : ((I P) * nat) & (sum unit (N P (fst i))) } ->
Prop :=
| leq_exponential_unique : forall i m m' n a b,
leq P (existT _ i m) (existT _ i m') ->
a = (existT _ (i, n) m) ->
b = (existT _ (i, n) m') ->
leq_exponential P a b.

Definition partial_order_exponential (P : PartialOrder) : PartialOrder.
  refine({| 
            I := (I P) * nat;
            N x := N P (fst x);
            leq := leq_exponential P
         |}).
Proof. 
- intros. destruct x. destruct x. apply leq_exponential_unique
with (i:=i) (m:=s) (m':=s) (n:=n). apply reflexive. auto. auto.
- intros. destruct x. destruct y. destruct H. inversion H. subst.
inversion H0. subst. inversion H6. subst. apply inj_pairT2 in H6. subst.
inversion H5. subst. apply inj_pairT2 in H5. subst. inversion H3. subst.
apply inj_pairT2 in H3. subst. inversion H2. subst. apply inj_pairT2 in H2.
subst.
assert ((existT
          (fun i : I P =>
           (unit + N P i)%type) i m) = 
       (existT
          (fun i : I P =>
           (unit + N P i)%type) i m')).
{apply anti_symmetric. auto. } apply inj_pairT2 in H2. subst. auto.
- intros. destruct x. destruct y. destruct z. destruct H. inversion H.
inversion H0. subst. inversion H8. subst. apply inj_pairT2 in H8. subst.
inversion H7. subst. inversion H7. subst. apply inj_pairT2 in H7. subst.
inversion H3. subst. inversion H3. subst. apply inj_pairT2 in H3. subst.
inversion H2. subst. inversion H2. subst. apply inj_pairT2 in H2. subst.
assert
(leq P
       (existT
          (fun i : I P =>
           (unit + N P i)%type) i m)
       (existT
          (fun i : I P =>
           (unit + N P i)%type) i m'0)).
{apply transitive with (y:=(existT
          (fun i : I P =>
           (unit + N P i)%type) i m')). auto. }
apply leq_exponential_unique with (i:=i) (m:=m) (m':=m'0) (n:=n).
auto. auto. auto.
- intros. unfold iff. split.
+ intros. inversion H. subst. inversion H2. subst. apply inj_pairT2 in H2.
subst. inversion H1. subst. apply inj_pairT2 in H1. subst. auto.
+ intros. subst. destruct i'.
apply leq_exponential_unique with (i:=i) (m:=inl tt) (m':=m) (n:=n).
apply unit_is_least. auto. auto. auto.
- intros. inversion H. subst. inversion H2. subst. apply inj_pairT2 in H2.
subst. inversion H1. subst. inversion H1. subst. auto.
Defined.

Inductive incompatible_exponential (E : EventStructure) :
(M (partial_order_exponential (P E))) ->
(M (partial_order_exponential (P E))) ->
Prop :=
| incomp_exponential_unique : forall i m m' n a b,
incompatible E (existT _ i m) (existT _ i m') ->
a = (existT _ (i,n) m) ->
b = (existT _ (i,n) m') ->
incompatible_exponential E a b.

Definition event_structure_exponential (E : EventStructure) : EventStructure.
  refine({| 
            P := partial_order_exponential (P E);
            incompatible := incompatible_exponential E;
            ideal m := match m with
                      | existT _ (i, n) m =>
                      map (fun x => match x with
                                    | existT _ i (inl tt) => existT _ (i, n) (inl tt)
                                    | existT _ i (inr m) => existT _ (i, n) (inr m)
                          end) (ideal E (existT _ i m))
                      end;
         |}).
Proof.
- intros. inversion H. subst. apply incomp_exponential_unique with
(i:=i) (m:=m') (m':=m) (n:=n). apply symmetric. auto. auto. auto.
- unfold not. intros. inversion H. subst. apply inj_pairT2 in H2. subst.
assert (~ (incompatible E
       (existT (fun i : I (P E) => (unit + N (P E) i)%type) i
          m')
       (existT (fun i : I (P E) => (unit + N (P E) i)%type) i
          m'))).
{apply irreflexive. }
contradiction H1.
- intros. unfold iff. split.
+ intros. destruct x. destruct y. destruct x. destruct x0.
apply in_map_iff. refine (ex_intro _ (existT _ i0 s0) _). split.
destruct s0.
++ destruct u. simpl in H. inversion H. subst. inversion H2. subst.
inversion H1. subst. auto.
++ simpl in H. inversion H. subst. inversion H1. inversion H2. subst. auto.
++ simpl in H. inversion H. subst. inversion H1. inversion H2. subst.
apply inj_pairT2 in H1. subst. apply inj_pairT2 in H9. subst. apply inj_pairT2 in H2.
subst. apply ideal_finite. auto.
+ destruct x. destruct y. destruct x. destruct x0. intros. apply in_map_iff in H.
destruct H. destruct x. destruct s1.
++ destruct u. destruct H. inversion H. subst. apply inj_pairT2 in H. subst.
apply ideal_finite in H0. simpl. assert (H2:=H0). apply leq_same_component in H2.
subst. apply leq_exponential_unique with
(i:=i) (m:=inl tt) (m':=s) (n:=n0). auto. auto. auto.
++ destruct H. apply ideal_finite in H0. inversion H. subst. apply inj_pairT2 in H.
subst. assert (H2:=H0). apply leq_same_component in H2. subst. simpl.
apply leq_exponential_unique with
(i:=i) (m:=inr n1) (m':=s) (n:=n0). auto. auto. auto.
- intros. destruct H. inversion H. subst. simpl in H0. inversion H0. subst.
inversion H3. subst. apply inj_pairT2 in H3. subst. apply incomp_exponential_unique with
(i:=i0) (m:=m) (m':=m'0) (n:=n0). apply incompatible_closed with
(y:=(existT (fun i : I (P E) => (unit + N (P E) i)%type) i0 m0)).
auto. auto. auto.
Defined.

Fact second_in_exponential_is_second :
forall E m, second_move (P (event_structure_exponential E)) m <->
((exists i n k, m = existT _ (i,n) k /\ 
second_move (P E) (existT _ i k))).
Proof. unfold iff. split.
+ intros. unfold second_move in H. destruct H.
rewrite initial_is_unit in H. destruct m. destruct x.
 refine (ex_intro _ i _). refine (ex_intro _ n _). refine (ex_intro _ s _). split.
++ auto.
++ unfold second_move. split.
+++ unfold not. intros. apply initial_is_unit in H1. destruct H1. inversion H1.
subst. apply inj_pairT2 in H1. subst. contradiction H. refine (ex_intro _ (x,n) _). auto.
+++ intros. destruct H1. destruct n0. assert (H3 := H1). apply leq_same_component in H1.
subst.
assert (initial_move (P (event_structure_exponential E)) 
(existT _ (i,n) s0)). apply H0. split.
++++ simpl. apply leq_exponential_unique with
(i:=i) (m:=s0) (m':=s) (n:=n). auto. auto. auto.
++++ unfold not. intros. apply inj_pairT2 in H1. subst. contradiction H2. auto.
++++ apply initial_is_unit in H1. destruct H1. inversion H1. subst.
apply inj_pairT2 in H1. subst. apply initial_is_unit. refine (ex_intro _ i _).
auto.
+ intros. destruct H. destruct H. destruct H. destruct H. subst. unfold second_move. 
unfold second_move in H0. destruct H0. split.
++ unfold not. intros. apply initial_is_unit in H1. destruct H1. inversion H1. subst.
apply inj_pairT2 in H1. subst. contradiction H. apply initial_is_unit.
refine (ex_intro _ x _). auto.
++ intros. destruct H1. destruct n. assert (H3 := H1).
apply leq_same_component in H3. subst.
assert (initial_move _ (existT _ x s)).
{apply H0. split.
+ simpl in H1. inversion H1. subst. inversion H4. subst. apply inj_pairT2 in H4. subst.
apply inj_pairT2 in H5. subst. auto.
+ unfold not. intros. apply inj_pairT2 in H3. subst. contradiction H2. auto. }
apply initial_is_unit in H3. destruct H3. inversion H3. subst. apply inj_pairT2 in H3. subst.
apply initial_is_unit. refine (ex_intro _ (x2,x0) _). auto.
Qed.

Fixpoint project_exponential E (l : list (M (P (event_structure_exponential E))))
: (list nat) * (nat -> list (M (P E))) :=
match l with
| nil => (nil, fun _ => nil)
| (existT _ (i,n) m) :: xs
=> let (is, f) := project_exponential E xs in
(match (in_dec Nat.eq_dec n is) with
| left _ => (is, fun s => if Nat.eqb s n then (existT _ i m) :: (f s) else f s)
| right _ => (n::is, fun s => if Nat.eqb s n then (existT _ i m) :: (f s) else f s)
end)
end.

Definition tensor (p q : Z) :=
if Z.ltb p 0 then 
(if Z.ltb q 0 then Z.add p q else p)
else
(if Z.ltb q 0 then q else Z.add p q).

Fixpoint exponential_walk_payoff A (l1 l2 l3 l4 : list (list (M (P (E A))))) : Z :=
match l1, l2, l3, l4 with
| x1 :: xs1, x2 :: xs2, x3 :: xs3, x4 :: xs4 =>
tensor (finite_payoff_walk A ((x1, x2), (x3, x4))) (exponential_walk_payoff A xs1 xs2 xs3 xs4)
| _, _, _, _ => 0%Z
end.

Definition exponential_move_is_in_n (A: AsynchronousArena) 
(m : M (P (event_structure_exponential (E A)))) (n : nat) : Prop :=
match m with
| existT _ (i, k) _ => k = n
end.

Definition exponential_move_is_projection (A: AsynchronousArena) 
(m : M (P (event_structure_exponential (E A)))) (m' : M (P (E A))) : Prop :=
exists i n k, m = existT _ (i,n) k /\ m' = existT _ i k.

Definition infinite_projection_to_n
(A : AsynchronousArena) 
(f : nat -> M (P (event_structure_exponential (E A))))
(g : (nat -> (M (P (E A)))))
(n : nat) :=
exists (h : nat -> nat),
(strictly_increasing h) /\
(forall m, 
(exponential_move_is_in_n A (f m) n -> 
(exists k, m = h k /\ exponential_move_is_projection A (f (h k)) (g k) ))).

Definition finite_projection_to_n
(A : AsynchronousArena) 
(f : nat -> M (P (event_structure_exponential (E A))))
(g : list (M (P (E A))))
(n : nat) :=
exists (h : list nat),
(strictly_increasing_list h) /\
(forall m, 
(exponential_move_is_in_n A (f m) n -> 
(exists index move, index_of m h = Some index /\ nth_error g index = Some move /\
exponential_move_is_projection A (f m) move))).

Definition minus_infinity_exists (A : AsynchronousArena) 
(f : nat -> M (P (event_structure_exponential (E A))) ) :=
exists n g, infinite_projection_to_n A f g n /\ (infinite_payoff A g minus_infinity).

Definition plus_infinity_exists (A : AsynchronousArena) 
(f : nat -> M (P (event_structure_exponential (E A))) ) :=
exists n g, infinite_projection_to_n A f g n /\ (infinite_payoff A g plus_infinity).

Definition finite_negative_exists (A : AsynchronousArena) 
(f : nat -> M (P (event_structure_exponential (E A)))) :=
exists g n, finite_projection_to_n A f g n /\ 
Z.lt (finite_payoff_walk A ((nil, nil),(nil, g))) 0%Z.

Definition all_finite_and_positive (A : AsynchronousArena) 
(f : nat -> M (P (event_structure_exponential (E A)))) :=
forall n, exists g, finite_projection_to_n A f g n /\ 
Z.le 0%Z (finite_payoff_walk A ((nil, nil),(nil, g))).

Definition infinite_payoff_exponential (A : AsynchronousArena) 
(f : nat -> M (P (event_structure_exponential (E A))) ) 
(inf : Infinity) :=
match inf with
| plus_infinity => (~(minus_infinity_exists A f)) /\
(plus_infinity_exists A f \/ all_finite_and_positive A f)
| minus_infinity => (minus_infinity_exists A f) \/
(~(plus_infinity_exists A f) /\ finite_negative_exists A f)
end.

Definition asynchronous_arena_exponential (A : AsynchronousArena) 
(positive1 : (finite_payoff_position A) nil = (-1)%Z)
: AsynchronousArena.
  refine({| 
            E := event_structure_exponential (E A);
            polarity m := match m with
                          | existT _ (i,n) m => polarity A (existT _ i m)
                          end;
            finite_payoff_position l :=  
              match l with
                | nil => (-1)%Z
                | _ => let (l, f) := project_exponential _ l in
                       let l := map f l in 
                       let l := map (finite_payoff_position A) l in
                       fold_right tensor 0%Z l
              end;
            finite_payoff_walk w :=
              let (l_fp, f_fp) := project_exponential _ (fst (fst w)) in
              let l_fp := map f_fp l_fp in
              let (l_fm, f_fm) := project_exponential _ (snd (fst w)) in
              let l_fm := map f_fm l_fm in
              let (l_sp, f_sp) := project_exponential _ (fst (snd w)) in
              let l_sp := map f_sp l_sp in
              let (l_sm, f_sm) := project_exponential _ (snd (snd w)) in
              let l_sm := map f_sm l_sm in
              exponential_walk_payoff A l_fp l_fm l_sp l_sm;
            infinite_payoff f inf := infinite_payoff_exponential A f inf
         |}).
Proof.
- left. auto.
- intros. destruct m. apply initial_is_unit in H. destruct H. inversion H. subst.
apply inj_pairT2 in H. subst. simpl. destruct x0. split.
+ auto.
+ intros. apply polarity_first in H. lia. apply initial_is_unit. refine (ex_intro _ i _). auto.
- intros. apply second_in_exponential_is_second in H. destruct H. destruct H. destruct H. destruct H. subst.
apply polarity_second in H0. destruct H0. split.
+ intros. apply H in H1. lia.
+ auto.
- intros. destruct H. destruct w. destruct p. destruct p0. simpl in *. subst. simpl.
destruct (project_exponential (E A) p). destruct (project_exponential (E A) p0).
destruct (map l0 l); destruct (map l2 l1); simpl; auto.
Defined.

Definition asynchronous_game_exponential_positive (G: AsynchronousGame) 
(pos1 : (finite_payoff_position (A G)) nil = (-1)%Z)
: AsynchronousGame.
  refine({| 
             A := asynchronous_arena_exponential (A G) pos1;
             X := indexed_product_group (X G) nat;
             Y := wreath_product (Y G);
             actl g m := match m with
                            | existT _ (i,n) m =>
                              (match actl G (g n) (existT _ i m) with
                                | existT _ i m => existT _ (i, n) m
                               end)
                         end;
             actr m h :=  match m,h with
                          | existT _ (i,n) m, (f, exist _ (pi,_) _) =>
                            (match actr G (existT _ i m) (f n) with
                              | existT _ i m => existT _ (i, pi n) m
                             end)
                        end;
        |}).
Proof.
- assert (left_action _ _ (actl G)).
{apply actl_is_action. } unfold left_action in H. destruct H.
split.
+ intros. destruct x. destruct x. flatten_all. subst.
rewrite H in e. inversion e. subst. apply inj_pairT2 in e. subst. auto.
+ intros. destruct x. destruct x. flatten_all. subst. simpl in e3.
inversion e. subst. apply inj_pairT2 in e. subst. 
rewrite <- H0 in e3. rewrite e0 in e3. rewrite e2 in e3. inversion e3. subst.
apply inj_pairT2 in e3. subst. auto.
- assert (right_action _ _ (actr G)).
{apply actr_is_action. } unfold right_action in H. destruct H.
split.
+ intros. destruct x. destruct x. flatten_all. subst. simpl in e. inversion e. subst.
rewrite H in e2. inversion e2. subst. apply inj_pairT2 in e2. subst. auto.
+ intros. destruct x. destruct x. flatten_all. subst. simpl in e3.
inversion e. subst. apply inj_pairT2 in e. subst. simpl in e9. inversion e9. subst.
rewrite <- H0 in e12. rewrite e3 in e12. rewrite e8 in e12. inversion e12. subst. auto.
- intros. destruct m. destruct x. flatten_all. subst.
inversion e6. subst. apply inj_pairT2 in e6. subst. inversion e. subst. apply inj_pairT2 in e. subst.
rewrite <- e0 in e5. rewrite action_compatible in e5. rewrite e7 in e5.


 destruct m. destruct x. flatten_all. subst. simpl in *. inversion e. subst. rewrite action_id in e2. inversion e2.
subst. apply inj_pairT2 in e2. subst. auto.
- intros. destruct m. destruct x. flatten_all. subst. simpl in *. inversion e. subst.
rewrite action_compatible in e2. inversion e3. subst. apply inj_pairT2 in e3. subst.
rewrite e7 in e2. admit.
- intros. destruct m. destruct n. destruct x. destruct x0. destruct h. destruct g1. destruct x.
flatten_all. simpl in H. inversion H. subst. inversion H2. subst. apply inj_pairT2 in H2.
subst. inversion H1. subst. apply inj_pairT2 in H1. subst. simpl. 
assert (leq _
(action G (g n3)
      (existT (fun i : I (P (E (A G))) => (unit + N (P (E (A G))) i)%type) i1 m)
      (g0 n3))
(action G (g n3)
       (existT (fun i : I (P (E (A G))) => (unit + N (P (E (A G))) i)%type) i1 m')
       (g0 n3))).
{apply coherence_1. auto. } rewrite e in H1. rewrite e0 in H1. assert (H2:=H1).
apply leq_same_component in H2. subst. apply leq_exponential_unique with
(i:=x0) (n:=n1 n3) (m:=s1) (m':=s2). auto. auto. auto.
- intros. destruct m. destruct x. destruct h. destruct g1. destruct x. flatten_all.
simpl. rewrite <- e. apply coherence_2.
- intros. destruct m. destruct x. destruct H. flatten_all. subst. inversion e. subst.
simpl in H.
assert (action G (g n)
       (existT (fun i : I (P (E (A G))) => (unit + N (P (E (A G))) i)%type) i s)
       (id (Y G)) = 
(existT (fun i : I (P (E (A G))) => (unit + N (P (E (A G))) i)%type) i s)).
{symmetry. apply coherence_3. split.
+ auto.
+ intros. destruct n0. assert (H2:=H1). apply leq_same_component in H2. subst.
assert (leq (P (E (asynchronous_arena_exponential (A G) pos1)))
       (existT
          (fun i : I (P (E (asynchronous_arena_exponential (A G) pos1))) =>
           (unit + N (P (E (asynchronous_arena_exponential (A G) pos1))) i)%type) 
          (x, n) s) (existT
          (fun i : I (P (E (asynchronous_arena_exponential (A G) pos1))) =>
           (unit + N (P (E (asynchronous_arena_exponential (A G) pos1))) i)%type) 
          (x, n) s1)).
{simpl. apply leq_exponential_unique with (i:=x) (n:=n) (m:=s) (m':=s1). auto. auto. auto. }
apply H0 in H2. destruct (action G (g n)
          (existT (fun i : I (P (E (A G))) => (unit + N (P (E (A G))) i)%type) x s1)
          (id (Y G))). inversion H2. subst. apply inj_pairT2 in H2. subst. auto.
} rewrite e2 in H1. inversion H1. subst. apply inj_pairT2 in H1. auto.
- intros. destruct m. destruct x. destruct h. destruct g0. destruct x. destruct H.  
simpl in *.
assert (action G (id (X G))
       (existT (fun i : I (P (E (A G))) => (unit + N (P (E (A G))) i)%type) i s)
       (g n) = 
       (existT (fun i : I (P (E (A G))) => (unit + N (P (E (A G))) i)%type) i s)).
{symmetry. apply coherence_4. split.
+ auto.
+ intros. destruct n2. assert (H2:=H1). apply leq_same_component in H2. subst.
assert (leq (P (E (asynchronous_arena_exponential (A G) pos1)))
       (existT
          (fun i : I (P (E (asynchronous_arena_exponential (A G) pos1))) =>
           (unit + N (P (E (asynchronous_arena_exponential (A G) pos1))) i)%type) 
          (x, n) s) (existT
          (fun i : I (P (E (asynchronous_arena_exponential (A G) pos1))) =>
           (unit + N (P (E (asynchronous_arena_exponential (A G) pos1))) i)%type) 
          (x, n) s0)).
{simpl. apply leq_exponential_unique with (i:=x) (n:=n) (m:=s) (m':=s0). auto. auto. auto. }
apply H0 in H2. destruct (action G (id (X G))
          (existT (fun i : I (P (E (A G))) => (unit + N (P (E (A G))) i)%type)
             x s0) (g n)). inversion H2. subst. rewrite <- H5 in H2. apply inj_pairT2 in H2. subst. auto.
} flatten_all. inversion H1. subst. apply inj_pairT2 in H1. subst.
assert (leq_exponential (P (E (A G)))
       (existT
          (fun i : I (P (E (A G))) * nat =>
           (unit + N (P (E (A G))) (fst i))%type) 
          (i, n) s) (existT
          (fun i : I (P (E (A G))) * nat =>
           (unit + N (P (E (A G))) (fst i))%type) 
          (i, n) s) ).
{apply leq_exponential_unique with (i:=i) (n:=n) (m:=s) (m':=s). apply reflexive. auto. auto. }
apply H0 in H1. destruct (action G (id (X G))
          (existT
             (fun i : I (P (E (A G))) =>
              (unit + N (P (E (A G))) i)%type) i s) 
          (g n)). inversion H1. subst. rewrite <- H5. rewrite <- H5. auto.
- intros. destruct h. destruct g1. destruct x. destruct i.
destruct (action G (g n1) (existT (fun i0 : I (P (E (A G))) => (unit + N (P (E (A G))) i0)%type) i (inl tt))
       (g0 n1)) eqn:eqn1.
refine (ex_intro _ (x, n n1) _). flatten_all.
assert 
( existT (fun i : I (P (E (A G))) => (unit + N (P (E (A G))) i)%type) x s =  
existT (fun i : I (P (E (A G))) => (unit + N (P (E (A G))) i)%type) x0 s0).
{rewrite <- eqn1. rewrite <- e. auto. }
inversion H. subst. apply inj_pairT2 in H. subst.
assert (exists k,
action G (g n1)
      (existT (fun i : I (P (E (A G))) => (unit + N (P (E (A G))) i)%type) i (inl tt))
      (g0 n1) =
      (existT (fun i : I (P (E (A G))) => (unit + N (P (E (A G))) i)%type) k (inl tt))).
{apply action_preserves_initial. }
destruct H. rewrite eqn1 in H. inversion H. subst. apply inj_pairT2 in H. subst. auto.
- intros. destruct h. destruct g1. destruct x. destruct i.
destruct (action G (g n1)
       (existT (fun i0 : I (P (E (A G))) => (unit + N (P (E (A G))) i0)%type)
          i (inr m)) (g0 n1)) eqn:eqn1.
refine (ex_intro _ (x, n n1) _).
assert (exists k k1,
action G (g n1)
         (existT
            (fun i0 : I (P (E (A G))) => (unit + N (P (E (A G))) i0)%type) i
            (inr m)) (g0 n1) = 
existT (fun i : I (P (E (A G))) => (unit + N (P (E (A G))) i)%type) k (inr k1)).
{apply action_preserves_non_initial. } destruct H. destruct H. rewrite eqn1 in H.
inversion H. subst. apply inj_pairT2 in H. subst. 
refine (ex_intro _ x1 _). auto.
Admitted.

Definition asynchronous_game_exponential_negative (G: AsynchronousGame) 
(neg : (finite_payoff_position (A G)) nil = (1)%Z) :=
asynchronous_game_exponential_positive
(asynchronous_game_lifting G neg 0%Z)
(positive_lifting_is_positive G neg 0%Z).


Definition asynchronous_game_exponential (G: AsynchronousGame) :
AsynchronousGame :=
match initial_payoff (A G) with
| left p  => asynchronous_game_exponential_positive G p
| right p => asynchronous_game_exponential_negative G p
end.

