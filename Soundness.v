Require Import ZArith.
Require Import ZArith.Int.
Require Import Logic.Eqdep_dec.
Require Import Lia.
Require Import List.
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
assert (positive ZERO).
{unfold positive. simpl. auto. }
assert ((0 <=? finite_payoff_position (A ZERO) nil)%Z = true).
{apply H. split.
+ unfold valid_path. simpl. intros. split.
++ assert (n = 0). lia. subst. unfold valid_position. intros.
simpl. tauto.
++ assert (n = 0). lia. subst. intros. lia.
+ unfold alternating. intros. simpl in H3. destruct k.
++ simpl in H3. destruct H3. inversion H3.
++ simpl in H3. destruct H3. inversion H3.
+ intros. unfold strategy_induces_play. split.
++ intros. destruct H4. simpl in H5. assert (n = 0). {lia. }
subst. simpl. destruct (x nil) eqn:eqn.
+++ destruct m. destruct x0.
+++ auto.
++ intros. unfold positive in H2. unfold negative in H3.
rewrite H2 in H3. lia. }
apply Z.leb_le in H3. unfold positive in H2. rewrite H2 in H3. lia.
Qed.

Theorem conversion_is_sound :
forall (l : sequent) (f : interpretation),
valid l -> exists (s : Strategy (interpret l f)),
winning _ s /\ innocent _ s.
- intros. induction H.
+ subst. simpl. unfold interpret. simpl. unfold game_par.
unfold tensor. destruct (initial_payoff (A (dual (f s)))).
++ destruct (initial_payoff (A (dual (dual (f s))))).
+++ simpl in *. omega.
+++ unfold asynchronous_game_tensor_right. unfold dual. simpl.
refine (ex_intro _
(fun l => 
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
                      (*(match index_equality _ j (fst i) with
                          | left p =>
                              Some (existT _ i (inr (inl 
                              ( (eq_rect j (fun j => N (P (E (A (dual (dual (f s)))))) j) m ) 
                                (fst i) p) )  ))
                          | right _ => None
                      end)*)
              end)
end
)
 _).