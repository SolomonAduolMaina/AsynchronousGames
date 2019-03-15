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

Definition asynchronous_arena_dual (A: AsynchronousArena) 
: AsynchronousArena :=
        {| 
            E := E A ;
            polarity m := negb (polarity A m);
            finite_payoff_position l := Z.sub 0 (finite_payoff_position A l);
            finite_payoff_walk w := Z.sub 0 (finite_payoff_walk A w);
            infinite_payoff f inf := (infinite_payoff A f (negb inf));
            positive_or_negative := negb (positive_or_negative A);
         |}.

Definition dual (G: AsynchronousGame)  : AsynchronousGame :=
        {| 
            A := asynchronous_arena_dual (A G) ;
            X := opposite_group (Y G);
            Y := opposite_group (X G);
            action g m h := action G h m g;
         |}.

(*Fact dual_preserves_well_formedness :
forall G, well_formed_asynchronousgame G ->
well_formed_asynchronousgame (dual G).
Proof. intros. unfold well_formed_asynchronousgame. unfold well_formed_asynchronousgame in H.
split.
+ simpl. unfold well_formed_asynchronous_arena. simpl. destruct H. 
unfold well_formed_asynchronous_arena in H. split.
++ apply H.
++ unfold polarity_first. destruct H. destruct H1. unfold polarity_first in H1.
split.
+++ intros. simpl. simpl in H3. split.
++++ intros. apply negb_true_iff in H4.
assert (finite_payoff_position (A G) nil = 1%Z).
{apply H1 with (m:=m). auto. auto. } lia.
++++ intros. apply negb_false_iff in H4.
assert (finite_payoff_position (A G) nil = (-1)%Z).
{apply H1 with (m:=m). auto. auto. } lia.
+++ split.
++++ destruct H2. unfold polarity_second. unfold polarity_second in H2.
intros. simpl. split.
+++++ intros. apply negb_true_iff in H5. simpl in H4.
assert (finite_payoff_position (A G) nil = (-1)%Z).
{apply H2 with (m:=m). auto. auto. } lia.
+++++ intros. apply negb_false_iff in H5. simpl in H4.
assert (finite_payoff_position (A G) nil = 1%Z).
{apply H2 with (m:=m). auto. auto. } lia.
++++ split.
+++++ unfold initial_null. intros. destruct w. simpl in H3.
destruct p. destruct p0. simpl in H3. destruct H3. subst. simpl.
assert (finite_payoff_walk (A G) (p, nil, (p0, nil)) = 0%Z).
{ destruct H2. destruct H3. unfold initial_null in H3. apply H3. simpl. auto. }
assert ((- finite_payoff_walk (A G) (p, nil, (p0, nil)))%Z = 
finite_payoff_walk (A G) (p, nil, (p0, nil))).
{rewrite H3. lia. }
assert (forall A (a b c : A), a = b /\ b = c -> a = c).
{intros. destruct H5. subst. auto. }
apply H5 with (b:=finite_payoff_walk (A G) (p, nil, (p0, nil))).
auto.
+++++ unfold positive_iff_player_always_starts. simpl. split.
++++++ intros. apply negb_true_iff. destruct H2. destruct H5.
unfold positive_iff_player_always_starts in H6.
apply negb_true_iff in H3. apply H6. auto. auto.
++++++ intros. apply negb_false_iff. destruct H2. destruct H5.
unfold positive_iff_player_always_starts in H6.
apply negb_true_iff in H3. apply H6. auto. auto.
*)
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

