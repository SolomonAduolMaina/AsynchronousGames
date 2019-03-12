Require Import ZArith.
Require Import Arith.Even.
Require Import ZArith.Int.
Require Import Logic.Eqdep_dec.
Require Import Logic.FunctionalExtensionality.
Require Import Bool.Bool.
Require Import Lia.
Require Import List.
Require Import Util.
Require Import Group.
Require Import AsynchronousGames.
Require Import Strategy.
Require Import LinearLogic.
Require Import Conversion.
Require Import Tensor.
Require Import Sum.
Require Import Exponential.
Require Import Dual.
Require Import Lifting.

 Fact unfold_dual:
    forall AG XG YG actionG,
      dual {|
          A := AG;
          X := XG;
          Y := YG;
          action := actionG
        |} =
      {|
        A := asynchronous_arena_dual AG;
        X := Group.opposite_group YG;
        Y := Group.opposite_group XG;
        action := fun g m h => actionG h m g
      |}.
  Proof.
    intros.
    unfold dual; simpl.
    reflexivity.
  Qed.

Theorem zero_has_no_winning_strategy :
not (exists (s : Strategy ZERO), winning _ s).
Proof. unfold not. intros. destruct H. unfold winning in H.
destruct H. destruct H. assert (positive ZERO). unfold positive. simpl. auto.
unfold strategy_never_stalls in H.
assert (x nil <> None).
{apply H. auto. simpl. apply Even.even_O. }
destruct (x nil).
+ destruct m. destruct x0.
+ contradiction H3. auto.
Qed.

Theorem conversion_is_sound :
forall (l : sequent) (f : interpretation),
(forall l, well_formed_asynchronousgame (interpret l f)) ->
valid l -> exists (s : Strategy (interpret l f)),
winning _ s /\ innocent _ s /\ uniform _ s.
- intros. 
assert (well_formed_asynchronousgame (interpret l f)).
{apply H. } induction H0.
+ subst. simpl. unfold interpret. simpl. unfold game_par.
destruct (positive_or_negative (A (dual (f s)))) eqn:eqn1.
++ destruct (positive_or_negative (A (dual (dual (f s))))) eqn:eqn2.
+++ simpl in *. rewrite eqn1 in eqn2. simpl in *. inversion eqn2.
+++ simpl in *. unfold tensor. rewrite negb_involutive in eqn2.
simpl. rewrite eqn2. simpl. destruct (f s) eqn:eqn3. rewrite unfold_dual.

remember ((fun x => match x with
                        | existT _ i (inl tt) => 
                         (existT _ i (inr (inr  (existT _ (fst i) (inl tt))   )))
                        | existT _ i (inr (inl m)) => 
                         (existT _ i (inr (inr  (existT _ (fst i) (inr m))   )))
                        | existT _ i (inr (inr (existT _ j (inl tt) )))  => 
                         (existT _ i (inl tt))
                        | existT _ i (inr (inr (existT _ j (inr m) ))) =>
                         (existT _ (j,tt) (inr (inl m)))
                    end) : 
(M (P (E (AsynchronousGames.A (dual
            (asynchronous_game_tensor_positive
               {|
               A := asynchronous_arena_dual A;
               X := opposite_group Y;
               Y := opposite_group X;
               action := fun (g : G (opposite_group Y))
                           (m : M (P (E (asynchronous_arena_dual A))))
                           (h : G (opposite_group X)) => action h m g |}
               (lifting
                  (dual
                     {|
                     A := asynchronous_arena_dual A;
                     X := opposite_group Y;
                     Y := opposite_group X;
                     action := fun (g : G (opposite_group Y))
                                 (m : M (P (E (asynchronous_arena_dual A))))
                                 (h : G (opposite_group X)) => 
                               action h m g |}) 1))))))) ->
(M (P (E (AsynchronousGames.A (dual
            (asynchronous_game_tensor_positive
               {|
               A := asynchronous_arena_dual A;
               X := opposite_group Y;
               Y := opposite_group X;
               action := fun (g : G (opposite_group Y))
                           (m : M (P (E (asynchronous_arena_dual A))))
                           (h : G (opposite_group X)) => action h m g |}
               (lifting
                  (dual
                     {|
                     A := asynchronous_arena_dual A;
                     X := opposite_group Y;
                     Y := opposite_group X;
                     action := fun (g : G (opposite_group Y))
                                 (m : M (P (E (asynchronous_arena_dual A))))
                                 (h : G (opposite_group X)) => 
                               action h m g |}) 1))) ))))) as copy_move.
remember (fun l => match l with
                        | nil => None
                        | x :: _ => Some (copy_move x)
                    end) as sigma.
refine (ex_intro _ sigma _). unfold interpret in H1. simpl in H1. unfold game_par in H1. 
split.
++++ intros. unfold winning. split.
+++++ unfold strategy_never_stalls. unfold positive. unfold negative. simpl. split.
++++++ intros. inversion H0.
++++++ intros. rewrite odd_equiv in H2. unfold Nat.Odd in H2. destruct H2.
assert (length p <> 0). {lia. }
assert (exists k xs, p = k :: xs).
{destruct p.
+ simpl in H3. lia.
+ refine (ex_intro _ m _). refine (ex_intro _ p _). auto. }
destruct H4. destruct H4. subst. destruct x0. simpl. destruct s0. easy. destruct n. easy. destruct n.
destruct s0. easy. easy.
+++++ split.
++++++ unfold strategy_preserves_validity. intros. generalize dependent k. induction p.
+++++++ intros. destruct H0. subst sigma. inversion H2.
+++++++ intros. destruct H0. destruct a. simpl in H2. destruct s0.
++++++++ destruct u. destruct x. simpl in H2. subst sigma. subst copy_move. inversion H2. subst k.

 intros. simpl.
assert (forall p, strategy_induces_play
       (dual
          (asynchronous_game_tensor_positive
             {|
             A := asynchronous_arena_dual A;
             X := opposite_group Y;
             Y := opposite_group X;
             action := fun (g : G (opposite_group Y)) (m : M (P (E (asynchronous_arena_dual A)))) (h : G (opposite_group X)) =>
                       action h m g |}
             (lifting
                (dual
                   {|
                   A := asynchronous_arena_dual A;
                   X := opposite_group Y;
                   Y := opposite_group X;
                   action := fun (g : G (opposite_group Y)) (m : M (P (E (asynchronous_arena_dual A)))) (h : G (opposite_group X))
                             => action h m g |}) 1))) sigma p ->
( ((cast_tensor_to_left (E A) (event_structure_lifting (E A)) p) = 
(cast_to_original (E A) (cast_tensor_to_right (E A) (event_structure_lifting (E A)) p))) \/
(exists k, ((cast_tensor_to_left (E A) (event_structure_lifting (E A)) p) = 
(cast_to_original (E A) (cast_tensor_to_right (E A) (event_structure_lifting (E A)) p)) ++ (k :: nil) ) ))).
{ intros.induction p0.
+ simpl. left. auto.
+ assert (cast_tensor_to_left (E A) (event_structure_lifting (E A)) p0 =
       cast_to_original (E A)
         (cast_tensor_to_right (E A) (event_structure_lifting (E A)) p0) \/
       (exists k : M (P (E A)),
          cast_tensor_to_left (E A) (event_structure_lifting (E A)) p0 =
          cast_to_original (E A)
            (cast_tensor_to_right (E A) (event_structure_lifting (E A)) p0) ++
          k :: nil)).
{apply IHp0.

