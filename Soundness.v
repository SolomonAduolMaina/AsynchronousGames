Require Import ZArith.
Require Import Lia.
Require Import AsynchronousGames.
Require Import Strategy.
Require Import LinearLogic.
Require Import Conversion.
Require Import Tensor.
Require Import Sum.
Require Import Exponential.
Require Import Dual.

Theorem conversion_is_sound :
forall (l : sequent) (f : interpretation),
valid l -> exists (s : Strategy (interpret l f)),
winning _ s /\ innocent _ s.
- intros. induction H.
+ subst. simpl. unfold interpret. simpl. unfold game_par.
unfold tensor. destruct (initial_payoff (A (dual (f s)))).
++ destruct (initial_payoff (A (dual (dual (f s))))).
+++ simpl in *. omega.
+++ 