Require Import List.
Require Import ZArith.
Require Import Lia.
Require Import Init.Nat.
Require Import Logic.Eqdep.
Require Import Logic.Eqdep_dec.
Require Import Arith.PeanoNat.
Require Import Bool.Bool.
Require Import Util.
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

Definition partial_order_exponential (P : PartialOrder) : PartialOrder :=
         {| 
            I := (I P) * nat;
            N x := N P (fst x);
            leq := leq_exponential P;
         |}.

Inductive incompatible_exponential (E : EventStructure) :
(M (partial_order_exponential (P E))) ->
(M (partial_order_exponential (P E))) ->
Prop :=
| incomp_exponential_unique : forall i m m' n a b,
incompatible E (existT _ i m) (existT _ i m') ->
a = (existT _ (i,n) m) ->
b = (existT _ (i,n) m') ->
incompatible_exponential E a b.

Definition event_structure_exponential (E : EventStructure) : EventStructure :=
        {| 
            P := partial_order_exponential (P E);
            incompatible := incompatible_exponential E;
            ideal m := match m with
                      | existT _ (i, n) m =>
                      map (fun x => match x with
                                    | existT _ i (inl tt) => existT _ (i, n) (inl tt)
                                    | existT _ i (inr m) => existT _ (i, n) (inr m)
                          end) (ideal E (existT _ i m))
                      end;
         |}.

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

Definition tensor_nat (p q : Z) :=
if Z.ltb p 0 then 
(if Z.ltb q 0 then Z.add p q else p)
else
(if Z.ltb q 0 then q else Z.add p q).

Fixpoint exponential_walk_payoff A (l1 l2 l3 l4 : list (list (M (P (E A))))) : Z :=
match l1, l2, l3, l4 with
| x1 :: xs1, x2 :: xs2, x3 :: xs3, x4 :: xs4 =>
tensor_nat (finite_payoff_walk A ((x1, x2), (x3, x4))) (exponential_walk_payoff A xs1 xs2 xs3 xs4)
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
(forall m, 
(exponential_move_is_in_n A (f m) n -> 
(exists k, m = h k /\ exponential_move_is_projection A (f (h k)) (g k) ))).

Definition finite_projection_to_n
(A : AsynchronousArena) 
(f : nat -> M (P (event_structure_exponential (E A))))
(g : list (M (P (E A))))
(n : nat) :=
exists (h : list nat),
(forall m, 
(exponential_move_is_in_n A (f m) n -> 
(exists index move, index_of m h = Some index /\ nth_error g index = Some move /\
exponential_move_is_projection A (f m) move))).

Definition minus_infinity_exists (A : AsynchronousArena) 
(f : nat -> M (P (event_structure_exponential (E A))) ) :=
exists n g, infinite_projection_to_n A f g n /\ (infinite_payoff A g false).

Definition plus_infinity_exists (A : AsynchronousArena) 
(f : nat -> M (P (event_structure_exponential (E A))) ) :=
exists n g, infinite_projection_to_n A f g n /\ (infinite_payoff A g true).

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
(inf : bool) :=
if inf then (~(minus_infinity_exists A f)) /\
(plus_infinity_exists A f \/ all_finite_and_positive A f)
else (minus_infinity_exists A f) \/
(~(plus_infinity_exists A f) /\ finite_negative_exists A f).

Definition asynchronous_arena_exponential (A : AsynchronousArena) 
: AsynchronousArena :=
        {| 
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
                       fold_right tensor_nat 0%Z l
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
            infinite_payoff f inf := infinite_payoff_exponential A f inf;
            positive_or_negative := true;
         |}.

Definition asynchronous_game_exponential_positive (G: AsynchronousGame) 
: AsynchronousGame :=
         {| 
             A := asynchronous_arena_exponential (A G);
             X := indexed_product_group (X G) nat;
             Y := wreath_product (Y G);
             action g move h := 
                match move,h with
                  | existT _ (i,n) m, (f, exist _ (pi,_) _) =>
                    (match action G (g n) (existT _ i m) (f n) with
                      | existT _ i m => existT _ (i, pi n) m
                     end)
                end;
        |}.

Definition exponential (G : AsynchronousGame) : AsynchronousGame := 
match positive_or_negative (A G) with
| true => asynchronous_game_exponential_positive (lifting (lifting G (0)%Z false) (0)%Z true)
| false => asynchronous_game_exponential_positive (lifting G (0)%Z true)
end.
(*
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
- intros. destruct i. destruct j. destruct (index_equality P i i0).
+ subst. destruct (Nat.eq_dec n n0).
++ subst. left. auto.
++ right. unfold not. intros. inversion H. contradiction n1.
+ right. unfold not. intros. inversion H. contradiction n1.
Defined.


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


Proof.
- unfold left_action. split.
+ intros. destruct x. destruct x. simpl.
assert (left_action _ _ (actl G)).
{apply restriction_to_left_is_action. }
destruct H. unfold actl in *. rewrite H. auto.
+ intros. destruct x. destruct x. simpl.
assert (left_action _ _ (actl G)).
{apply restriction_to_left_is_action. }
destruct H. unfold actl in *.
destruct (action G (h n)
       (existT (fun i0 : I (P (E (A G))) => (unit + N (P (E (A G))) i0)%type)
          i s) (id (Y G))) eqn:eqn1.
destruct (action G (g n)
     (existT (fun i0 : I (P (E (A G))) => (unit + N (P (E (A G))) i0)%type) x
        s0) (id (Y G))) eqn:eqn2.
destruct (action G (mult (X G) (g n) (h n))
     (existT (fun i0 : I (P (E (A G))) => (unit + N (P (E (A G))) i0)%type) i
        s) (id (Y G))) eqn:eqn3.
rewrite <- H0 in eqn3. rewrite eqn1 in eqn3. rewrite eqn2 in eqn3. inversion eqn3.
subst. apply inj_pairT2 in eqn3. subst. auto.
- unfold right_action. 
assert (right_action _ _ (actr G)).
{apply restriction_to_right_is_action. }
destruct H. unfold actr in *. split.
+ intros. destruct x. destruct x. simpl. rewrite H. auto.
+ intros. destruct x. destruct x. destruct g. destruct h. destruct g0. destruct g2. destruct x.
destruct x0. simpl.
destruct (action G (id (X G))
       (existT (fun i0 : I (P (E (A G))) => (unit + N (P (E (A G))) i0)%type)
          i s) (g n)) eqn:eqn1.
destruct (action G (id (X G))
     (existT (fun i0 : I (P (E (A G))) => (unit + N (P (E (A G))) i0)%type) x
        s0) (g1 (n0 n))) eqn:eqn2.
destruct (action G (id (X G))
     (existT (fun i0 : I (P (E (A G))) => (unit + N (P (E (A G))) i0)%type) i
        s) (mult (Y G) (g n) (g1 (n0 n)))) eqn:eqn3.
rewrite <- H0 in eqn3. rewrite eqn1 in eqn3. rewrite eqn2 in eqn3. inversion eqn3. subst.
subst. apply inj_pairT2 in H3. subst. auto.
- intros. inversion H. subst. destruct h. destruct g1. destruct x.
destruct (action G (g n0)
       (existT (fun i0 : I (P (E (A G))) => (unit + N (P (E (A G))) i0)%type)
          i m0) (g0 n0)) eqn:eqn1.
destruct (action G (g n0)
       (existT (fun i0 : I (P (E (A G))) => (unit + N (P (E (A G))) i0)%type)
          i m') (g0 n0)) eqn:eqn2.
assert (leq _
(action G (g n0)
         (existT
            (fun i0 : I (P (E (A G))) => (unit + N (P (E (A G))) i0)%type) i
            m0) (g0 n0))
(action G (g n0)
         (existT
            (fun i0 : I (P (E (A G))) => (unit + N (P (E (A G))) i0)%type) i
            m') (g0 n0))).
{apply coherence_1. auto. }
rewrite eqn1 in H1. rewrite eqn2 in H1. assert (H2:=H1).
apply leq_same_component in H2. subst. apply leq_exponential_unique with
(i:=x0) (n:=n n0) (m:=s) (m':=s0). auto. auto. auto.
- intros. simpl. destruct m. destruct x. destruct h. destruct g1. destruct x.
destruct (action G (g n)
       (existT (fun i0 : I (P (E (A G))) => (unit + N (P (E (A G))) i0)%type)
          i s) (g0 n)) eqn:eqn1. rewrite <- eqn1. apply coherence_2.
- intros. destruct h. destruct i. destruct g1. destruct x. flatten_all.
assert (exists k, 
action G (g n)
         (existT (fun i0 : I (P (E (A G))) => (unit + N (P (E (A G))) i0)%type) i
            (inl tt)) (g0 n) = 
existT (fun i : I (P (E (A G))) => (unit + N (P (E (A G))) i)%type) k (inl tt)).
{apply action_preserves_initial. }
destruct H.
assert (existT (fun i : I (P (E (A G))) => (unit + N (P (E (A G))) i)%type) x s = 
existT (fun i : I (P (E (A G))) => (unit + N (P (E (A G))) i)%type) x0 (inl tt)).
{rewrite <- e. rewrite <- H. auto. }
inversion H0. subst. apply inj_pairT2 in H0. subst. refine (ex_intro _ (x0, n0 n) _).
auto.
- intros. flatten_all. subst. 
assert (exists k k1,
action G (g n)
       (existT (fun i : I (P (E (A G))) => (unit + N (P (E (A G))) i)%type) i0
          (inr m)) (g0 n) = 
     existT (fun i : I (P (E (A G))) => (unit + N (P (E (A G))) i)%type) k (inr k1)).
{apply action_preserves_non_initial. }
destruct H. destruct H. rewrite e3 in H. inversion H. subst. apply inj_pairT2 in H.
subst. refine (ex_intro _ (x, n0 n) _). refine (ex_intro _ x1 _). auto.
Defined.

*)
