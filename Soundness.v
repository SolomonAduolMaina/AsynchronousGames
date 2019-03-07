Require Import ZArith.
Require Import ZArith.Int.
Require Import Logic.Eqdep_dec.
Require Import Lia.
Require Import List.
Require Import Util.
Require Import AsynchronousGames.
Require Import Strategy.
Require Import LinearLogic.
Require Import Conversion.
Require Import Tensor.
Require Import Sum.
Require Import Exponential.
Require Import Dual.
Require Import Lifting.

Theorem zero_has_no_winning_strategy :
not (exists (s : Strategy ZERO), winning _ s).
Proof. unfold not. intros. destruct H. unfold winning in H.
destruct H. destruct H0.
assert ((0 <=? finite_payoff_position ZERO nil)%Z = true).
{apply H. split.
+ unfold valid_path. simpl. intros. split.
++ assert (n = 0). lia. subst. unfold valid_position. intros.
simpl. tauto.
++ assert (n = 0). lia. subst. intros. lia.
+ unfold alternating. intros. simpl in H2. destruct k.
++ simpl in H2. destruct H2. inversion H2.
++ simpl in H2. destruct H2. inversion H2.
+ intros. unfold strategy_induces_play. split.
++ intros. destruct H3. simpl in H4. assert (n = 0). {lia. }
subst. simpl. destruct (x nil) eqn:eqn.
+++ destruct m. destruct x0.
+++ auto.
++ intros. assert (positive ZERO). {unfold positive. auto. }
unfold positive in H4. unfold negative in H2. rewrite H2 in H4. inversion H4. }
apply Z.leb_le in H2. assert (finite_payoff_position ZERO nil = (-1)%Z). {auto. }
rewrite H3 in H2. lia.
Qed.

Theorem conversion_is_sound :
forall (l : sequent) (f : interpretation),
valid l -> exists (s : Strategy (interpret l f)),
winning _ s /\ innocent _ s /\ uniform _ s.
- intros. induction H.
+ subst. simpl. unfold interpret. simpl. unfold game_par.
destruct (positive_or_negative ((dual (f s)))) eqn:eqn1.
++ destruct (positive_or_negative ((dual (dual (f s))))) eqn:eqn2.
+++ simpl in *. rewrite eqn1 in eqn2. simpl in *. inversion eqn2.
+++ simpl in *.
remember
(fun (l : list (M (dual (tensor (dual (f s)) (dual (dual (f s)))))))  => 
match l with
  | nil => None
  | x :: _ => (match (last l x) with
                  | existT _ i (inl tt) => 
                  Some (existT _ i (inr (inr  (existT _ (fst i) (inl tt))   )))
                  | existT _ i (inr (inl m)) => 
                  Some (existT _ i (inr (inr  (existT _ (fst i) (inr m))   )))
                  | existT _ i (inr (inr (existT _ j (inl tt) )))  => 
                  Some (existT _ i (inl tt))
                  | existT _ i (inr (inr (existT _ j (inr m) ))) =>
                  Some (existT _ (j,tt) (inr (inl m)))
              end)
end).