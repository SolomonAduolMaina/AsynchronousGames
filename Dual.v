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

Definition dual (G: AsynchronousGame) : AsynchronousGame :=
         {| 
            I := I G;
            N := N G;
            leq := leq G;

            incompatible := incompatible G;
            ideal := ideal G;

            polarity m := negb (polarity G m);
            finite_payoff_position l := Z.sub 0 (finite_payoff_position G l);
            finite_payoff_walk w := Z.sub 0 (finite_payoff_walk G w);
            infinite_payoff f inf := (infinite_payoff G f (negb inf));
            positive_or_negative := negb (positive_or_negative G);

            X := opposite_group (Y G);
            Y := opposite_group (X G);
            action g m h := action G h m g;
         |}.

(* Definition E_def (A : AsynchronousArena) := E A.

Definition polarity_def (A : AsynchronousArena) :=
fun m => negb (polarity A m).

Definition finite_payoff_position_def (A : AsynchronousArena) :=
fun l => Z.sub 0 (finite_payoff_position A l).

Definition initial_payoff_def (A : AsynchronousArena) := 
fun l => Z.sub 0 (finite_payoff_position A l).

Definition finite_payoff_walk_def (A : AsynchronousArena) := 
fun w => Z.sub 0 (finite_payoff_walk A w).

Definition infinite_payoff_def (A : AsynchronousArena) := 
fun f inf => (infinite_payoff A f (negb inf)).

Fact initial_payoff_proof (A : AsynchronousArena) :
sumbool 
(finite_payoff_position_def A nil = (-1)%Z) 
(finite_payoff_position_def A nil = (1)%Z).
Proof.
intros. simpl. 
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
Qed.

Fact polarity_first_proof (A : AsynchronousArena) :
forall m, initial_move (P (E_def A)) m -> 
    ((polarity_def A m = true -> finite_payoff_position_def A nil = (-1)%Z)
    /\
    (polarity_def A m = false -> finite_payoff_position_def A nil = (1)%Z)).
Proof.
intros. simpl. split.
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
Qed.

Fact polarity_second_proof (A : AsynchronousArena) :
forall m, second_move (P (E_def A)) m -> 
    ((polarity_def A m = true -> finite_payoff_position_def A nil = (1)%Z)
    /\
    (polarity_def A m = false -> finite_payoff_position_def A nil = (-1)%Z)).
Proof.
intros. apply polarity_second in H. split.
+ intros. apply negb_true_iff in H0. apply H in H0. simpl.
assert ((- finite_payoff_position A nil)%Z = 1%Z <->
(finite_payoff_position A nil)%Z = (-1)%Z).
{lia. } rewrite H1. auto.
+ intros. apply negb_false_iff in H0. apply H in H0. simpl.
assert ((- finite_payoff_position A nil)%Z = (-1)%Z <->
(finite_payoff_position A nil)%Z = (1)%Z).
{lia. } apply H1. auto.
Qed.

Fact initial_null_proof (A : AsynchronousArena) :
forall (w : Walk (E_def A)),
    (snd (fst w) = nil /\ snd (snd w) = nil) -> 
    finite_payoff_walk_def A w = 0%Z.
Proof. intros. simpl.
assert ((- finite_payoff_walk A w)%Z = 0%Z <->
(finite_payoff_walk A w)%Z = 0%Z).
{lia. } apply H0. apply initial_null. auto.
Qed.*)



(*Definition A_def (G: AsynchronousGame) := asynchronous_arena_dual (A G).

Definition X_def (G: AsynchronousGame) := opposite_group (Y G).

Definition Y_def (G: AsynchronousGame) := opposite_group (X G).

Definition action_def (G: AsynchronousGame) :=
fun g m h => action G h m g.

Definition actl_def (G: AsynchronousGame) := 
(fun g m => action_def G g m (id (Y_def G))).

Definition actr_def (G: AsynchronousGame) := 
(fun m h => action_def G (id (X_def G)) m h).

Fact restriction_to_left_is_action_proof (G: AsynchronousGame) :
left_action (X_def G) (M (P (E (A G)))) (actl_def G).
Proof.
unfold left_action. split.
+ intros. simpl.
assert (left_action _ _ (actl G)).
{apply restriction_to_left_is_action. }
unfold left_action in *. destruct H. unfold actl in H. apply H.
+ intros. simpl.
assert (right_action _ _ (actr G)).
{apply restriction_to_right_is_action. }
unfold right_action in H. destruct H. unfold actr in *. apply H0.
Qed.

Fact restriction_to_right_is_action_proof (G: AsynchronousGame) :
right_action (Y_def G) (M (P (E (A G)))) (actr_def G).
Proof.
unfold right_action. split.
+ intros. simpl.
assert (left_action _ _ (actl G)).
{apply restriction_to_left_is_action. }
unfold left_action in *. destruct H. unfold actl in H. apply H.
+ intros. simpl.
assert (left_action _ _ (actl G)).
{apply restriction_to_left_is_action. }
unfold left_action in H. destruct H. unfold actl in *. apply H0.
Qed.

Fact coherence_1_proof (G: AsynchronousGame) :
forall m n g h,
    leq (P (E (A G))) m n -> 
    leq (P (E (A G))) (action_def G g m h) (action_def G g n h).
Proof.
intros. simpl in H. simpl. apply coherence_1. auto.
Qed.

Fact coherence_2_proof (G: AsynchronousGame) :
forall m g h,
    polarity (A_def G) (action_def G g m h) = polarity (A_def G) m.
Proof.
intros. simpl. unfold polarity_def. unfold action_def. rewrite coherence_2. auto.
Qed.

Fact action_preserves_initial_proof (G: AsynchronousGame) :
forall i g h,
exists i', action_def G g (existT _ i (inl tt)) h = existT _ i' (inl tt).
Proof.
intros. apply action_preserves_initial.
Qed.

Fact action_preserves_non_initial_proof (G: AsynchronousGame) :
forall i g h m,
    exists i' m', action_def G g (existT _ i (inr m)) h = existT _ i' (inr m').
Proof.
intros. apply action_preserves_non_initial.
Qed.
*)

