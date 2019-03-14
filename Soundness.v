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
Require Import LinearLogic.
Require Import AsynchronousGames.
Require Import Strategy.
Require Import Dual.
Require Import Lifting.
Require Import Tensor.
Require Import Sum.
Require Import Exponential.
Require Import Conversion.


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
assert (x nil <> None).
{apply H. auto. simpl. unfold valid_play. unfold valid_position. split.
+ apply NoDup_nil.
+ intros. destruct m. destruct x0.
+ simpl. apply even_O. }
destruct (x nil).
+ destruct m. destruct x0.
+ contradiction H3. auto.
Qed.

Fact top_has_winning_strategy :
(exists (s : Strategy TOP), winning _ s).
Proof. refine (ex_intro _ (fun _ => None) _). unfold winning. split.
+ unfold strategy_is_total. unfold positive. unfold negative. simpl. split.
++ intros. inversion H.
++ intros. assert (exists x xs, p = x :: xs).
{destruct p.
+ inversion H1.
+ refine (ex_intro _ m _). refine (ex_intro _ p _). auto. }
destruct H2. destruct x. destruct x.
+ split.
++ unfold strategy_preserves_validity. intros. destruct k. destruct x.
++ split.
+++ intros. destruct p.
++++ simpl. apply Z.leb_le. lia.
++++ destruct m. destruct x.
+++ split.
++++ intros. destruct (f 0). destruct x.
++++ intros. destruct w. destruct p. destruct p0.
destruct p.
+++++ destruct l.
++++++ destruct p0.
+++++++ destruct l0.
++++++++ simpl. apply Z.leb_le. lia.
++++++++ destruct m. destruct x.
+++++++ destruct m. destruct x.
++++++ destruct m. destruct x.
+++++ destruct m. destruct x.
Qed.

Fact one_has_a_winning_strategy :
(exists (s : Strategy ONE), winning _ s).
Proof. remember
((fun l =>
match l with
| nil => Some (existT _ tt (inl tt))
| _ => None
end) : Strategy ONE) as sigma.
refine (ex_intro _ sigma _). 
assert (strategy_is_total _ sigma).
{unfold strategy_is_total. split.
++ unfold positive. simpl. intros. destruct p.
+++ subst. easy.
+++ inversion H1. subst.
assert (exists k xs, p = k :: xs).
{destruct p.
+ inversion H3.
+ refine (ex_intro _ m0 _). refine (ex_intro _ p _). auto. }
destruct H2. destruct H2. subst.
assert (m <> x).
{unfold not. intros. subst. unfold valid_play in H0. unfold valid_position in H0.
destruct H0. inversion H0. contradiction H6. left. auto. }
destruct m. destruct x1. destruct s.
++++ destruct x. destruct x. destruct s.
+++++ destruct u. destruct u0. contradiction H2. auto.
+++++ destruct n. destruct x.
++++ destruct n. destruct x1.
++ intros. unfold negative in H. simpl in H. inversion H. }
assert (~ strategy_induces_play ONE sigma nil).
{unfold not. intros.
unfold strategy_induces_play in H0. unfold positive in *. unfold negative in *.
simpl negative in *. simpl positive_or_negative in *. 
assert (sigma (lastn 0 nil) =
      nth_error_from_back nil 0).
{destruct H0. apply H0. auto. split.
+ apply even_O.
+ lia. } unfold lastn in H1. unfold nth_error_from_back in H1. simpl in H1. 
subst. inversion H1. }
unfold winning. split.
+ apply H.
+ split.
++ unfold strategy_preserves_validity. intros. destruct H1. destruct H2. subst.
inversion H3.
++ split.
+++ intros. simpl. destruct p.
++++ contradiction H0.
++++ destruct m. destruct x. destruct s.
+++++ destruct u. destruct p.
++++++ apply Z.leb_le. lia.
++++++ apply Z.leb_le. lia.
+++++ apply Z.leb_le. lia.
+++ split.
++++ intros. unfold valid_alternating_infinite_play in H1. destruct H1.
unfold valid_infinite_play in H1. destruct n.
+++++ simpl finite_part in *. contradiction H0.
+++++ simpl finite_part in *. destruct n.
++++++ simpl in *. destruct (f 0). destruct x. destruct s.
+++++++ destruct u. apply Z.leb_le; lia.
+++++++ apply Z.leb_le; lia.
++++++ simpl finite_part in *.
assert (valid_play (E (A ONE))
       (finite_part (M (partial_order_lifting zero_partial_order)) f 2 0)).
{apply H1. }
simpl finite_part in *. unfold valid_play in H4. destruct H4.
assert (f 0 <> f 1).
{unfold not. intros. rewrite H6 in H4. inversion H4. contradiction H9. left. auto. }
destruct (f 0). destruct x. destruct s.
+++++++ destruct u. destruct (f 1).
++++++++ destruct x. destruct s.
+++++++++ destruct u. contradiction H6. auto.
+++++++++ destruct n0. destruct x.
+++++++ destruct n0. destruct x.
++++ intros. destruct w. destruct p. destruct p0. destruct p.
+++++ destruct l.
++++++ destruct l0. 
+++++++ simpl. apply Z.leb_le. lia.
+++++++ simpl. apply Z.leb_le. lia.
++++++ simpl. apply Z.leb_le. lia.
+++++ simpl. destruct l.
++++++ destruct p0.
+++++++ destruct l0.
++++++++ apply Z.leb_le. lia.
++++++++ apply Z.leb_le. lia.
+++++++ destruct l0.
++++++++ apply Z.leb_le. lia.
++++++++ apply Z.leb_le. lia.
++++++ destruct p0.
+++++++ apply Z.leb_le. lia.
+++++++ apply Z.leb_le. lia.
Qed.

Theorem bottom_has_no_winning_strategy :
not (exists (s : Strategy BOTTOM), winning _ s).
Proof. unfold not. intros. destruct H. unfold winning in H.
destruct H. unfold strategy_is_total in H. unfold positive in *.
unfold negative in *. simpl positive_or_negative in *. destruct H.
assert (valid_play (E (A (BOTTOM))) ((existT _ tt (inl tt)) :: nil)).
{unfold valid_play. split.
+ apply NoDup_cons.
++ auto.
++ apply NoDup_nil.
+ split.
++ intros. destruct m. destruct n. destruct H2. destruct H3.
simpl in H3. destruct x0. unfold nth_error_from_back in H2.
simpl in H2.
assert (a < length ((existT
          (fun _ : unit => (unit + M zero_partial_order)%type)
          tt (inl tt) :: nil))).
{apply nth_error_Some. unfold not. intros.
assert (forall A (a b c : A), a = b /\ b = c -> a = c).
{intros. destruct H6. subst. auto. }
assert (Some (existT (fun _ : unit => (unit + M zero_partial_order)%type) x1 s0)
= None).
{apply H6 with (b:= (nth_error
       (existT
          (fun _ : unit =>
           (unit + M zero_partial_order)%type)
          tt (inl tt) :: nil) a)). auto. } inversion H7. }
simpl in H5. assert (a = 0). {lia. } subst. simpl in H2. inversion H2.
subst. destruct s.
+++ destruct u. contradiction H4. auto.
+++ contradiction H3.
++ intros. destruct H2. simpl in H2. simpl in H3. destruct H2.
+++ destruct H3.
++++ subst. simpl. auto.
++++ contradiction H3.
+++ contradiction H2. }
destruct H0.
assert (x (existT
          (fun i : I (P (E (A BOTTOM))) =>
           (unit + N (P (E (A BOTTOM))) i)%type) tt 
          (inl tt) :: nil) <> None).
{apply H1. auto. auto. simpl. apply odd_S. apply even_O. }
assert (strategy_induces_play BOTTOM x nil).
{unfold strategy_induces_play. unfold positive. unfold negative.
simpl. split.
+ intros. inversion H5.
+ intros. destruct H6. assert (n = 0). {lia. } subst. inversion H6. }
unfold strategy_preserves_validity in H0. destruct 
(x
       (existT
          (fun i : I (P (E (A BOTTOM))) =>
           (unit + N (P (E (A BOTTOM))) i)%type) tt 
          (inl tt) :: nil)) eqn:eqn1.
+
assert (valid_play (E (A BOTTOM)) (m :: (existT
            (fun i : I (P (E (A BOTTOM))) =>
             (unit + N (P (E (A BOTTOM))) i)%type) tt
            (inl tt) :: nil))).
{apply H0. auto. }
unfold valid_play in H6. destruct H6.
assert (m <> existT
             (fun i : I (P (E (A BOTTOM))) =>
              (unit + N (P (E (A BOTTOM))) i)%type) tt
             (inl tt)).
{unfold not. intros. subst. inversion H6. contradiction H10. 
simpl. left. auto. }
destruct m. destruct x0. destruct s.
++ destruct u. contradiction H8. auto.
++ destruct n. destruct x0.
+ contradiction H4. auto.
Qed.

Fact conversion_is_sound :
forall (l : sequent) (f : interpretation),
(forall l, well_formed_asynchronousgame (interpret l f)) ->
valid l -> exists (s : Strategy (interpret l f)),
winning _ s /\ innocent _ s /\ uniform _ s.
- intros. 
assert (well_formed_asynchronousgame (interpret l f)).
{apply H. } induction H0.
+ subst. simpl. unfold interpret in H1. simpl in H1. unfold game_par in H1.
unfold interpret. simpl. unfold game_par.
destruct (f s). rewrite unfold_dual. unfold tensor.
remember ({|
                  A := asynchronous_arena_dual A;
                  X := opposite_group Y;
                  Y := opposite_group X;
                  action := fun (g : G (opposite_group Y))
                              (m : M (P (E (asynchronous_arena_dual A))))
                              (h : G (opposite_group X)) => action h m g |}).
simpl. destruct (positive_or_negative (AsynchronousGames.A a)) eqn:eqn1.
++ simpl. 
remember ((fun x => match x with
                        | existT _ i (inl tt) => 
                         (existT _ i (inr (inr  (existT _ (fst i) (inl tt))   )))
                        | existT _ i (inr (inl m)) => 
                         (existT _ i (inr (inr  (existT _ (fst i) (inr m))   )))
                        | existT _ i (inr (inr (existT _ j (inl tt) )))  => 
                         (existT _ i (inl tt))
                        | existT _ i (inr (inr (existT _ j (inr m) ))) =>
                         (existT _ (j,tt) (inr (inl m)))
                    end)
: M (P (E (AsynchronousGames.A (dual (asynchronous_game_tensor_positive a (lifting (dual a) 1)))))) ->
M (P (E (AsynchronousGames.A (dual (asynchronous_game_tensor_positive a (lifting (dual a) 1))))))
) as copy_move.
remember ((fun l =>
match l with
| nil => None
| x :: xs => Some (copy_move x)
end) : Strategy (dual (asynchronous_game_tensor_positive a (lifting (dual a) 1)))).
refine (ex_intro _ s0 _). split.
+++ unfold winning. split.
++++ unfold strategy_is_total. split.
+++++ intros. unfold positive in H0. simpl in H0. inversion H0.
+++++ intros.
assert (exists k xs, p = k :: xs).
{destruct p.
+ inversion H2.
+ refine (ex_intro _ m _). refine (ex_intro _ p _). auto. }
destruct H3. destruct H3. subst. simpl. destruct x. destruct s0.
++++++ destruct u. easy.
++++++ destruct n; easy.
++++ split.
+++++ assert
