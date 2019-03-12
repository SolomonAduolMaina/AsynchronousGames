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
unfold strategy_is_total in H.
assert (x nil <> None).
{apply H. auto. simpl. apply Even.even_O. }
destruct (x nil).
+ destruct m. destruct x0.
+ contradiction H3. auto.
Qed.

Definition copycat_strategy (G : AsynchronousGame) :
Strategy (dual (tensor (dual G) (dual (dual G)))).
Proof. destruct G. rewrite unfold_dual.
remember ({|
        A := asynchronous_arena_dual A;
        X := opposite_group Y;
        Y := opposite_group X;
        action := fun (g : Group.G (opposite_group Y))
                    (m : M (P (E (asynchronous_arena_dual A))))
                    (h : Group.G (opposite_group X)) => 
                  action h m g |}).
unfold tensor. destruct (positive_or_negative (AsynchronousGames.A a)) eqn:eqn1.
+ simpl. rewrite eqn1. simpl.
remember ((fun l =>
match l with
| nil => None
| x :: xs => Some (match x with
                        | existT _ i (inl tt) => 
                         (existT _ i (inr (inr  (existT _ (fst i) (inl tt))   )))
                        | existT _ i (inr (inl m)) => 
                         (existT _ i (inr (inr  (existT _ (fst i) (inr m))   )))
                        | existT _ i (inr (inr (existT _ j (inl tt) )))  => 
                         (existT _ i (inl tt))
                        | existT _ i (inr (inr (existT _ j (inr m) ))) =>
                         (existT _ (j,tt) (inr (inl m)))
                    end)
end) : Strategy (dual (asynchronous_game_tensor_positive a (lifting (dual a) 1)))).
apply s.
+ simpl. rewrite eqn1. simpl.
remember ((fun l =>
match l with
| nil => None
| x :: xs => Some (match x with
                        | existT _ i (inl tt) => 
                         (existT _ i (inr (inl  (existT _ (snd i) (inl tt))   )))
                        | existT _ i (inr (inr m)) => 
                         (existT _ i (inr (inl  (existT _ (snd i) (inr m))   )))
                        | existT _ i (inr (inl (existT _ j (inl tt) )))  => 
                         (existT _ i (inl tt))
                        | existT _ i (inr (inl (existT _ j (inr m) ))) =>
                         (existT _ (tt, j) (inr (inr m)))
                    end)
end) : Strategy (dual (asynchronous_game_tensor_positive (lifting (dual a) 1) a))).
apply s.
Defined.

Fact copycat_is_total (G : AsynchronousGame) :
strategy_is_total (dual (tensor (dual G) (dual (dual G)))) (copycat_strategy G).
Proof. unfold strategy_is_total. split.
+ intros. destruct G. rewrite unfold_dual in *. 
remember
{|
            A := asynchronous_arena_dual A;
            X := opposite_group Y;
            Y := opposite_group X;
            action := fun (g : G (opposite_group Y)) (m : M (P (E (asynchronous_arena_dual A)))) (h : G (opposite_group X))
                      => action h m g |}.
unfold tensor in H. destruct (positive_or_negative (AsynchronousGames.A a)) eqn:eqn1.
++ unfold positive in H. simpl in H. rewrite eqn1 in H. simpl in H. inversion H.
++ unfold positive in H. simpl in H. rewrite eqn1 in H. simpl in H. inversion H.
+ intros. destruct G. rewrite unfold_dual in *. 
remember
{|
            A := asynchronous_arena_dual A;
            X := opposite_group Y;
            Y := opposite_group X;
            action := fun (g : G (opposite_group Y)) (m : M (P (E (asynchronous_arena_dual A)))) (h : G (opposite_group X))
                      => action h m g |}.
unfold tensor in H. rewrite odd_equiv in H0. unfold Nat.Odd in H0. destruct H0.
assert (exists k xs, p = k :: xs).
{destruct p.
+ simpl in H0. lia.
+ simpl. refine (ex_intro _ m _). refine (ex_intro _ p _). auto.
} destruct H1. destruct H1. subst p. destruct x0. rewrite unfold_dual in x0.
(* I NEED TO DESTRUCT x0 AGAIN HERE BUT THE TYPE OF x0 IS NOT
   SUFFICIENTLY UNFOLDED TO DESTRUCT! ALSO CANNOT USE unfold_dual IN x0 BECAUSE
  "Cannot change x0, it is used in conclusion." SO ANNOYING! *)




Theorem conversion_is_sound :
forall (l : sequent) (f : interpretation),
(forall l, well_formed_asynchronousgame (interpret l f)) ->
valid l -> exists (s : Strategy (interpret l f)),
winning _ s /\ innocent _ s /\ uniform _ s.
- intros. 
assert (well_formed_asynchronousgame (interpret l f)).
{apply H. } induction H0.
+ subst. simpl. unfold interpret. simpl. unfold game_par.
refine (ex_intro _ (copycat_strategy (f s)) _). unfold interpret in H1.
simpl in H1. unfold game_par in H1.
