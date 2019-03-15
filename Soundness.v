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
(forall s, well_formed_asynchronousgame (convert (prop_variable s) f)) ->
valid l -> exists (s : Strategy (interpret l f)),
winning _ s /\ innocent _ s /\ uniform _ s.
- intros. assert (True). {auto. } induction H0.
+ subst. simpl. unfold interpret. simpl. unfold game_par.
destruct (f s) eqn:ORIG. rewrite unfold_dual. unfold tensor.
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
end) : Strategy (dual (asynchronous_game_tensor_positive a (lifting (dual a) 1)))) as copycat.
refine (ex_intro _ copycat _). split.
+++ unfold winning.
assert (strategy_is_total _ copycat).
{ unfold strategy_is_total. split.
+ intros. unfold positive in H0. simpl in H0. inversion H0.
+ intros.
assert (exists k xs, p = k :: xs).
{destruct p.
+ inversion H3.
+ refine (ex_intro _ m _). refine (ex_intro _ p _). auto. }
destruct H4. destruct H4. subst. simpl. destruct x. destruct s0.
++ destruct u. easy.
++ destruct n; easy. }
assert (forall p, strategy_induces_play _ copycat p ->
valid_play _ p ->
(forall n, (odd n /\ n < length p) -> (exists k,
nth_error_from_back p (n-1) = Some k /\ 
nth_error_from_back p n = Some (copy_move k)))).
{ remember (fun p => strategy_induces_play _ copycat p ->
valid_play _ p ->
(forall n, (odd n /\ n < length p) -> (exists k,
nth_error_from_back p (n-1) = Some k /\ 
nth_error_from_back p n = Some (copy_move k)))) as P.
assert (P nil).
{subst P. intros. destruct H4. simpl in H5. lia. }
assert (forall x y l, P l -> P (x :: y :: l)).
{subst P. intros. unfold nth_error_from_back. simpl. destruct H6.
rewrite <- app_assoc. simpl in H7.
assert (nth_error (rev l ++ (y :: nil) ++ x :: nil) (n - 1) <> None).
{apply nth_error_Some. simpl. rewrite app_length. rewrite rev_length.
simpl. simpl in H7. lia. }
assert (strategy_induces_play _ copycat l).
{apply strategy_closed_under_prefix with (x:=x) (y:=y).
+ auto.
+ auto.
+ auto. }
assert (valid_play _ (y :: l)).
{apply validity_closed_under_prefix with (m:=x). auto. }
assert (valid_play _ l).
{apply validity_closed_under_prefix with (m:=y). auto. }
assert (forall n : nat,
     odd n /\ n < length l ->
     exists k,
       nth_error_from_back l (n - 1) = Some k /\
       nth_error_from_back l n = Some (copy_move k)).
{apply H3. auto. auto. }
destruct (le_lt_dec (length l) n).
+ assert (n = length l \/ n = length l + 1).
{inversion l0.
+ left. auto.
+ subst n.
assert (forall a b, a < S b -> a <= b).
{intros. lia. }
assert (m <= length l). {apply H14. auto. }
assert (m = length l). {lia. } subst m. right. lia. }
destruct H13.
++ subst n.
assert (strategy_is_total (dual
                 (asynchronous_game_tensor_positive a
                    (lifting (dual a) 1))) copycat -> 
(forall p, strategy_induces_play (dual
                 (asynchronous_game_tensor_positive a
                    (lifting (dual a) 1))) copycat p -> valid_play _ p ->
((positive (dual
                 (asynchronous_game_tensor_positive a
                    (lifting (dual a) 1))) -> odd (length p)) /\ (negative (dual
                 (asynchronous_game_tensor_positive a
                    (lifting (dual a) 1))) -> even (length p))))).
{apply induced_play_length. }
assert (even (length l)).
{apply H13.
+ auto.
+ auto.
+ auto.
+ unfold negative. simpl. auto. }
contradiction (not_even_and_odd (length l)).
++ subst n. simpl. assert (length l + 1 - 1 = length l). {lia. }
assert (nth_error (rev l ++ (y :: nil) ++ x :: nil) (length l) = 
nth_error ((y :: nil) ++ x :: nil) (length l - length (rev l))).
{apply nth_error_app2. rewrite rev_length. auto. }
rewrite rev_length in H14. assert (length l - length l = 0). {lia. }
rewrite H15 in H14. simpl in H14.
assert (nth_error (rev l ++ (y :: nil) ++ x :: nil) (length l + 1) = 
nth_error ((y :: nil) ++ x :: nil) ((length l + 1) - length (rev l))).
{apply nth_error_app2. rewrite rev_length. auto. }
rewrite rev_length in H16. assert (length l + 1 - length l = 1). {lia. }
rewrite H17 in H16. simpl in H16. refine (ex_intro _ y _). split.
+++ rewrite <- H14. auto.
+++ assert (H18:=H4). unfold strategy_induces_play in H18. unfold negative in *.
unfold positive in *. simpl positive_or_negative in *. destruct H18.
unfold lastn in H19. unfold nth_error_from_back in H19. simpl in H19.
rewrite <- app_assoc in H19. 
assert (copycat (rev (firstn (length l + 1) (rev l ++ (y :: nil) ++ x :: nil))) =
      nth_error (rev l ++ (y :: nil) ++ x :: nil) (length l + 1)).
{apply H19. auto. split.
+ auto.
+ lia. }
assert (firstn (length l + 1) ((rev l ++ (y :: nil)) ++ x :: nil) = 
firstn (length l + 1) (rev l ++ (y :: nil))).
{apply firstn_app. rewrite app_length. rewrite rev_length. simpl. lia. }
rewrite <- app_assoc in H21. rewrite H21 in H20.
assert (firstn (length l + 1) (rev l ++ y :: nil) = (rev l ++ y :: nil)).
{apply firstn_all2. rewrite app_length. rewrite rev_length. simpl. lia. }
rewrite H22 in H20. rewrite rev_unit in H20. rewrite rev_involutive in H20.
rewrite H16.
assert (forall A (a b c : A), a = b /\ b = c -> a = c).
{intros. destruct H23. subst a0. subst b. auto. }
assert (copycat (y :: l)  = Some x).
{apply H23 with (b:=nth_error (rev l ++ (y :: nil) ++ x :: nil) (length l + 1)).
auto. } subst copycat. auto.
+ assert (odd n /\ n < length l). {auto. }
apply H12 in H13. simpl in H13. unfold nth_error_from_back in H13.
destruct H13. refine (ex_intro _ x0 _). destruct H13. split.
++ rewrite <- H13. apply nth_error_app1. rewrite rev_length.
assert (forall a b, a < b -> a - 1 < b). {intros. lia. }
apply H15. auto.
++ rewrite <- H14. apply nth_error_app1. rewrite rev_length. auto. }
assert (forall l, even (length l) -> P l).
{apply even_length_list_induction. auto. }
subst P. intros. apply H4.
assert (strategy_is_total _ copycat -> 
(forall p, strategy_induces_play _ copycat p -> valid_play _ p ->
((positive (dual
                (asynchronous_game_tensor_positive a
                   (lifting (dual a) 1))) -> odd (length p)) /\ 
(negative (dual
                (asynchronous_game_tensor_positive a
                   (lifting (dual a) 1))) -> even (length p))))).
{apply induced_play_length. }
apply H8. auto. auto. auto. unfold negative. simpl positive_or_negative.
auto. auto. auto. auto. }
assert (well_formed_asynchronousgame (convert (prop_variable s) f)).
{apply H. } simpl in H3. rewrite ORIG in H3.
unfold well_formed_asynchronousgame in H3. destruct H3.
unfold well_formed_asynchronous_arena in H3. destruct H3.
unfold well_formed_event_structure in H3. destruct H3.
unfold well_formed_partial_order in H3. 
assert (forall k, polarity _ k = negb (polarity _ (copy_move k))).
{ intros. destruct k. destruct x. destruct i0. 
assert (forall i, initial_move (P (E A)) 
  (existT (fun i0 : I (P (E A)) => (unit + N (P (E A)) i0)%type) i
     (inl tt))).
{ intros. apply initial_is_unit. auto. refine (ex_intro _ i0 _). auto. }
destruct s0.
+ destruct u. rewrite Heqcopy_move. simpl. subst a. simpl.
rewrite negb_involutive.
rewrite negb_involutive. simpl in eqn1. apply negb_true_iff in eqn1.
assert (initial_move (P (E A)) 
  (existT (fun i0 : I (P (E A)) => (unit + N (P (E A)) i0)%type) i
     (inl tt))).
{apply H7. }
destruct H5. unfold polarity_first in H5. apply H5 in H8.
destruct H8. destruct H9. destruct H11. unfold positive_iff_player_always_starts in H12.
simpl positive_or_negative in H12. rewrite eqn1 in H12. symmetry. apply H12. auto.
apply initial_is_unit. auto. subst. refine (ex_intro _ i _). auto.
+ destruct n.
++ rewrite Heqcopy_move. simpl. rewrite negb_involutive. auto.
++ rewrite Heqcopy_move. simpl. destruct n.
+++ destruct s0.
++++ destruct u. rewrite negb_involutive. simpl. subst a. simpl.
assert (initial_move _ (existT
        (fun i0 : I (P (E A)) =>
         (unit + N (P (E A)) i0)%type) x 
        (inl tt))).
{apply H7. }
destruct H5. unfold polarity_first in H5. apply H5 in H8.
destruct H8. destruct H9. destruct H10. destruct H11. unfold positive_iff_player_always_starts in H11.
simpl positive_or_negative in H11. simpl in eqn1. apply negb_true_iff in eqn1. rewrite eqn1 in H11. apply H11. auto.
apply H7. apply negb_true_iff. destruct H11. 
unfold positive_iff_player_always_starts in H11.
simpl positive_or_negative in H11. simpl in eqn1. apply negb_true_iff in eqn1. rewrite eqn1 in H11. apply H11. auto.
apply H7.
++++ auto. }



