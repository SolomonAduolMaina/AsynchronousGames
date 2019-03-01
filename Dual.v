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

Fixpoint neg_inf i :=
match i with
| plus_infinity => minus_infinity
| minus_infinity => plus_infinity
end.

Definition asynchronous_arena_dual (A: AsynchronousArena) 
: AsynchronousArena.
  refine({| 
            E := E A ;
            polarity m := negb (polarity A m);
            finite_payoff_position l := Z.sub 0 (finite_payoff_position A l);
            finite_payoff_walk w := Z.sub 0 (finite_payoff_walk A w);
            infinite_payoff f inf := ~ (infinite_payoff A f inf);
         |}).
Proof.
- intros. simpl. 
assert ((finite_payoff_position A nil = (-1)%Z) +
    (finite_payoff_position A nil = (1)%Z)).
{destruct (initial_payoff A).
+ left. auto.
+ right. auto. }
assert ((- finite_payoff_position A nil)%Z = (-1)%Z <->
(finite_payoff_position A nil)%Z = (1)%Z).
{lia. }
assert ((- finite_payoff_position A nil)%Z = 1%Z <->
(finite_payoff_position A nil)%Z = (-1)%Z).
{lia. } destruct H.
+ rewrite <- H1 in e. right. auto.
+ rewrite <- H0 in e. left. auto.
- intros. simpl. split.
+ intros. apply negb_true_iff in H0. apply polarity_first in H.
apply H in H0.
assert ((- finite_payoff_position A nil)%Z = (-1)%Z <->
(finite_payoff_position A nil)%Z = (1)%Z).
{lia. } apply H1. auto.
+ intros. apply negb_false_iff in H0. apply polarity_first in H.
apply H in H0.
assert ((- finite_payoff_position A nil)%Z = 1%Z <->
(finite_payoff_position A nil)%Z = (-1)%Z).
{lia. } apply H1. auto.
- intros. apply polarity_second in H. split.
+ intros. apply negb_true_iff in H0. apply H in H0. simpl.
assert ((- finite_payoff_position A nil)%Z = 1%Z <->
(finite_payoff_position A nil)%Z = (-1)%Z).
{lia. } rewrite H1. auto.
+ intros. apply negb_false_iff in H0. apply H in H0. simpl.
assert ((- finite_payoff_position A nil)%Z = (-1)%Z <->
(finite_payoff_position A nil)%Z = (1)%Z).
{lia. } apply H1. auto.
- intros. simpl.
assert ((- finite_payoff_walk A w)%Z = 0%Z <->
(finite_payoff_walk A w)%Z = 0%Z).
{lia. } apply H0. apply initial_null. auto.
Defined.

Definition asynchronous_game_dual (G: AsynchronousGame) 
: AsynchronousGame.
  refine({| 
            A := asynchronous_arena_dual (A G) ;
            X := opposite_group (Y G);
            Y := opposite_group (X G);
            action g m h := action G h m g;
         |}).
Proof. 
- unfold left_action. split.
+ intros. simpl.
assert (left_action _ _ (actl G)).
{apply restriction_to_left_is_action. }
unfold left_action in *. destruct H. unfold actl in H. apply H.
+ intros. simpl.
assert (right_action _ _ (actr G)).
{apply restriction_to_right_is_action. }
unfold right_action in H. destruct H. unfold actr in *. apply H0.
- unfold right_action. split.
+ intros. simpl.
assert (left_action _ _ (actl G)).
{apply restriction_to_left_is_action. }
unfold left_action in *. destruct H. unfold actl in H. apply H.
+ intros. simpl.
assert (left_action _ _ (actl G)).
{apply restriction_to_left_is_action. }
unfold left_action in H. destruct H. unfold actl in *. apply H0.
- intros. simpl in H. simpl. apply coherence_1. auto.
- intros. simpl. rewrite coherence_2. auto.
- intros. apply action_preserves_initial.
- intros. apply action_preserves_non_initial.
Defined.
