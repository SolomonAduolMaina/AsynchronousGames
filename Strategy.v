Require Import List.
Require Import Lia.
Require Import ZArith.
Require Import Arith.Even.
Require Import Util.
Require Import AsynchronousGames.
Require Import Logic.Classical.
Require Import Bool.Bool.

Definition lastn {A} n (l : list A) := rev (firstn n (rev l)).

Definition nth_error_from_back {A} (l : list A) n := nth_error (rev l) n.

Fact nth_error_some_iff_nth_error_from_back A : forall n (l : list A),
nth_error l n <> None <-> nth_error_from_back l n <> None.
Proof. intros. unfold iff. split.
+ intros. apply nth_error_Some in H. unfold nth_error_from_back.
apply nth_error_Some. rewrite rev_length. auto.
+ intros. unfold nth_error_from_back in H. apply nth_error_Some in H.
rewrite rev_length in H. apply nth_error_Some. auto.
Qed.

Fact nth_error_from_back_formula A : forall n (l : list A),
n < length l ->
nth_error l n = nth_error_from_back l ((length l) - n - 1).
Proof. intros. generalize dependent n. induction l.
+ intros. simpl. destruct n; auto.
+ intros. simpl length.
assert ((S (length l) - n - 1) = (length l) - n). {lia. }
rewrite H0. destruct n.
++ simpl. unfold nth_error_from_back. simpl.
assert (length l - 0 = length l). {lia. } rewrite H1.
assert (nth_error (rev l ++ a :: nil) (length l) = 
nth_error (a :: nil) (length l - length (rev l))).
{apply nth_error_app2. rewrite rev_length. auto. }
rewrite H2. assert (length l - length (rev l) = 0).
{rewrite rev_length. lia. }
rewrite H3. simpl. auto.
++ simpl. assert (length l - S n = (length l - n - 1)). {lia. }
rewrite H1. unfold nth_error_from_back. simpl. rewrite IHl.
+++ unfold nth_error_from_back. symmetry. apply nth_error_app1.
rewrite rev_length. simpl in H. lia.
+++ simpl in H. lia.
Qed.

Fact nth_error_cons_same A : forall n (l:list A) x a, 
nth_error_from_back l n = Some a -> nth_error_from_back (x::l) n = Some a.
Proof. intros. unfold nth_error_from_back in H. unfold nth_error_from_back. 
rewrite <- H. simpl. apply nth_error_app1. rewrite rev_length. apply nth_error_Some. apply nth_error_some_iff_nth_error_from_back. unfold
nth_error_from_back. rewrite H. easy.
Qed.

Definition Play (E : EventStructure) := list (M (P E)).

Definition valid_play (E : EventStructure) (p : Play E) :=
NoDup p /\ 
(forall m n, 
(forall a, (nth_error_from_back p a = Some n /\ leq (P E) m n /\ m <> n) ->
exists b, (nth_error_from_back p b = Some m /\ b < a))
/\
(In m p /\ In n p ->  not (incompatible E m n))).

Definition get_index {A} {P} (x : (sigT P)) : A :=
match x with
| existT _ i _ => i 
end.

Fact valid_play_same_component (E : EventStructure) (p : Play E) :
well_formed_event_structure E ->
valid_play E p ->
(forall m n, (In m p /\ In n p) -> get_index m = get_index n).
Proof. intros. assert (not (incompatible E m n)).
{apply H0. auto. }
destruct m. destruct n. simpl. apply H in H2. auto.
Qed.

Definition alternating_play (A : AsynchronousArena) p :=
forall k m m', 
((nth_error_from_back p k = Some m /\ nth_error_from_back p (S k) = Some m') ->
negb (polarity A m) = polarity A m').

Definition valid_alternating_play (A : AsynchronousArena) p :=
valid_play (E A) p /\ alternating_play A p.

(* Use of excluded middle could be done away with here *)
Fact valid_starting_player E :
forall p m, valid_play E p ->
nth_error_from_back p 0 = Some m ->
initial_move (P E) m.
Proof.  intros. 
destruct (nth_error_from_back p 0) eqn:eqn1.
++ inversion H0. subst. unfold initial_move. intros.
assert ((n=m) \/ (n<>m)).
{apply classic. }
destruct H2.
++++ auto.
++++ unfold valid_play in H.
assert ((forall a : nat,
      nth_error_from_back p a = Some m /\
      leq (P E) n m /\ n <> m ->
      exists b : nat,
        nth_error_from_back p b = Some n /\ b < a)).
{apply H. }
assert (exists b : nat,
       nth_error_from_back p b = Some n /\ b < 0).
{apply H3. auto. } destruct H4. destruct H4. lia.
++ inversion H0.
Qed.

Fact alternating_polarity A :
forall p, alternating_play A p ->
((forall k m n, nth_error_from_back p 0 = Some m ->
nth_error_from_back p (2 * k) = Some n ->
polarity _ m = polarity _ n)
/\
(forall k m n, nth_error_from_back p 1 = Some m ->
nth_error_from_back p (2 * k + 1) = Some n ->
polarity _ m = polarity _ n)).
Proof. intros. split. 
+ induction k.
++ intros. simpl in H1. rewrite H0 in H1. inversion H1. auto.
++ intros. 
assert ((2 * (S k)) < length (rev p)).
{apply nth_error_Some. unfold nth_error_from_back in H1. rewrite H1. easy. }
assert (2 * k < length (rev p)). {lia. }
assert (nth_error_from_back p (2 * k) <> None).
{unfold nth_error_from_back. apply nth_error_Some. auto. }
assert (exists q, nth_error_from_back p (2 * k) = Some q).
{destruct (nth_error_from_back p (2 * k)).
+ refine (ex_intro _ m0 _). auto.
+ contradiction H4. auto. }
assert (S(2 * k) < length (rev p)). {lia. }
assert (nth_error_from_back p (S(2 * k)) <> None).
{unfold nth_error_from_back. apply nth_error_Some. auto. }
assert (exists q, nth_error_from_back p (S(2 * k)) = Some q).
{destruct (nth_error_from_back p (S(2 * k))).
+ refine (ex_intro _ m0 _). auto.
+ contradiction H7. auto. }
destruct H5, H8.
assert (S (S(2*k)) = 2* (S k)). {lia. }
rewrite <- H9 in H1.
assert (polarity A m = polarity A x).
{apply IHk. auto. auto. }
assert (negb (polarity A x) = polarity A x0).
{unfold alternating_play in H. apply H with (k:=2*k). auto. }
assert (negb (polarity A x0) = polarity A n).
{unfold alternating_play in H. apply H with (k:=S(2*k)). auto. }
rewrite H10. rewrite <- H11 in H12. rewrite negb_involutive in H12. auto.
+ induction k.
++ intros. simpl in H1. rewrite H0 in H1. inversion H1. auto.
++ intros. 
assert ((2 * (S k) + 1) < length (rev p)).
{apply nth_error_Some. unfold nth_error_from_back in H1. rewrite H1. easy. }
assert (2 * k  + 1 < length (rev p)). {lia. }
assert (nth_error_from_back p (2 * k + 1) <> None).
{unfold nth_error_from_back. apply nth_error_Some. auto. }
assert (exists q, nth_error_from_back p (2 * k + 1) = Some q).
{destruct (nth_error_from_back p (2 * k + 1)).
+ refine (ex_intro _ m0 _). auto.
+ contradiction H4. auto. }
assert (S(2 * k) + 1 < length (rev p)). {lia. }
assert (nth_error_from_back p (S(2 * k) + 1) <> None).
{unfold nth_error_from_back. apply nth_error_Some. auto. }
assert (exists q, nth_error_from_back p (S(2 * k) + 1) = Some q).
{destruct (nth_error_from_back p (S(2 * k) + 1)).
+ refine (ex_intro _ m0 _). auto.
+ contradiction H7. auto. }
destruct H5, H8.
assert (polarity A m = polarity A x).
{apply IHk. auto. auto. }
assert (S (2 * k) + 1 = S(2 * k + 1)). {lia. }
rewrite  H10 in H8.
assert (negb (polarity A x) = polarity A x0).
{unfold alternating_play in H. apply H with (k:=2*k+1). auto. }
assert ((2 * S k + 1) = S (S (2 * k + 1))). {lia. }
rewrite H12 in H1.
assert (negb (polarity A x0) = polarity A n).
{unfold alternating_play in H. apply H with (k:=(S (2 * k + 1))). auto. }
rewrite H9. rewrite <- H11 in H13. rewrite negb_involutive in H13. auto.
Qed.

Fact validity_closed_under_prefix (A : AsynchronousArena) :
forall m p, valid_alternating_play A (m :: p) -> valid_alternating_play A p.
Proof. intros. unfold valid_alternating_play in H. destruct H.
unfold valid_play in H. destruct H. unfold valid_alternating_play. split.
- unfold valid_play. split.
+ apply NoDup_cons_iff in H. apply H.
+ intros. split.
++ intros. destruct H2.
assert (nth_error_from_back (m :: p) a = Some n).
{apply nth_error_cons_same. auto. } 
assert ((forall a : nat,
      nth_error_from_back (m :: p) a = Some n /\
      leq (P (E A)) m0 n /\ m0 <> n ->
      exists b : nat,
        nth_error_from_back (m :: p) b = Some m0 /\
        b < a)).
{ apply H1. }
assert (exists b : nat,
       nth_error_from_back (m :: p) b = Some m0 /\
       b < a).
{apply H5. auto. } destruct H6. refine (ex_intro _ x _).
assert (a < length p).
{unfold nth_error_from_back in H2. 
assert (nth_error (rev p) a <> None). {rewrite H2. easy. }
simpl. apply nth_error_Some in H7. simpl in H7. rewrite rev_length in H7. auto. }
destruct H6. assert (x < length p). lia.
unfold nth_error_from_back in H6. simpl in H6.
assert (nth_error (rev p ++ m :: nil) x = nth_error (rev p) x).
{apply nth_error_app1. rewrite rev_length. auto. }
unfold nth_error_from_back. rewrite <- H10. auto.
++ intros. destruct H2.
assert (In m0 (m :: p) /\ In n (m :: p)).
{split; apply in_cons; auto. }
apply H1. auto.
- intros. unfold alternating_play. unfold alternating_play in H0. intros.
destruct H2. unfold nth_error_from_back in H2. unfold nth_error_from_back in H3.
assert ((S k) < length p).
{rewrite <- rev_length. apply nth_error_Some. rewrite H3. easy. }
unfold nth_error_from_back in H0. simpl rev in H0. 
assert (nth_error (rev p ++ m :: nil) k = nth_error (rev p) k).
{apply nth_error_app1. rewrite rev_length. lia. }
assert (nth_error (rev p ++ m :: nil) (S k) = nth_error (rev p) (S k)).
{apply nth_error_app1. rewrite rev_length. lia. }
apply H0 with (k:=k). rewrite H5. rewrite H6. auto.
Qed.

Definition valid_alternating_path (A : AsynchronousArena) (p : Path (E A)) :=
valid_play (E A) ((snd p) ++ (fst p)) /\ alternating_play A (snd p).

Fixpoint finite_part A (f : nat -> A) (n : nat) (counter : nat) : list A :=
match n with
| 0 => nil
| S m => (f counter) :: (finite_part A f m (S counter))
end.

Definition valid_alternating_infinite_play (A : AsynchronousArena) 
(f : nat -> (M (P (E A)))) := forall n,
valid_play (E A) (finite_part _ f n 0) /\ negb (polarity A (f n)) = polarity A (f (S n)).

Definition valid_alternating_walk (A : AsynchronousArena) (w : Walk (E A)) :=
valid_alternating_path A (fst w) /\ valid_alternating_path A (snd w).

Definition incomparable P m n := (not (leq P m n)) /\ (not (leq P m n)).

Definition compatible E m n := not (incompatible E m n).

Definition independent E m n := (compatible E m n) /\ (incomparable (P E) m n).

Definition Strategy (G : AsynchronousGame) := 
(list (M (P (E (A G))))) -> option (M (P (E (A G)))).

Definition positive (G : AsynchronousGame) := positive_or_negative (A G) = true.

Definition negative (G : AsynchronousGame) := positive_or_negative (A G) = false.

Definition strategy_induces_play (G : AsynchronousGame) (sigma : Strategy G) p :=
(positive G -> (forall n, (even n /\ n <= length p) -> 
(sigma (lastn n p)) = nth_error_from_back p n))
/\
(negative G -> (forall n, (odd n /\ n <= length p) -> 
(sigma (lastn n p)) = nth_error_from_back p n )).

Definition strategy_preserves_validity (G : AsynchronousGame) (sigma : Strategy G) :=
forall p k m, (strategy_induces_play G sigma p /\ valid_alternating_play _ (k :: p) /\
sigma (k :: p) = Some m) -> valid_alternating_play _ (m :: k :: p).

Definition strategy_is_total (G : AsynchronousGame) (sigma : Strategy G) :=
(positive G -> (forall p, valid_alternating_play _ p -> even (length p) -> sigma p <> None)) /\
(negative G -> (forall p, valid_alternating_play _ p -> odd (length p) -> sigma p <> None)).

Fact induced_play_length (G : AsynchronousGame) (sigma : Strategy G) :
strategy_is_total G sigma -> 
(forall p, strategy_induces_play G sigma p -> valid_alternating_play _ p ->
((positive G -> odd (length p)) /\ (negative G -> even (length p)))).
Proof. intros. unfold strategy_is_total in H. destruct H. 
unfold strategy_induces_play in H0. destruct H0.
split.
+ intros. destruct (even_odd_dec (length p)).
++ assert (sigma p <> None). {apply H. auto. auto. auto. }
assert (sigma (lastn (length p) p) = nth_error_from_back p (length p)).
{apply H0. auto. auto. } unfold lastn in H6. rewrite <- rev_length in H6.
rewrite firstn_all in H6. rewrite rev_involutive in H6. unfold nth_error_from_back in H6.
rewrite H6 in H5. apply nth_error_Some in H5. lia.
++ auto.
+ intros. destruct (even_odd_dec (length p)).
++ auto.
++ assert (sigma p <> None). {apply H2. auto. auto. auto. }
assert (sigma (lastn (length p) p) = nth_error_from_back p (length p)).
{apply H3. auto. auto. } unfold lastn in H6. rewrite <- rev_length in H6.
rewrite firstn_all in H6. rewrite rev_involutive in H6. unfold nth_error_from_back in H6.
rewrite H6 in H5. apply nth_error_Some in H5. lia.
Qed.

Fact firstn_app : forall A n (l1 : list A) l2, n <= length l1 ->
firstn n (l1 ++ l2) = firstn n l1.
Proof. induction n.
+ intros. simpl. auto.
+ intros. simpl. destruct l1.
++ simpl in H. lia.
++ simpl. simpl in H. assert (n <= length l1). {lia. }
apply IHn with (l2:=l2) in H0. rewrite H0. auto.
Qed.

Fact strategy_closed_under_prefix (G : AsynchronousGame) (sigma : Strategy G) :
forall x y p, strategy_is_total G sigma ->
strategy_induces_play G sigma (x :: y :: p) -> valid_alternating_play _ (x :: y :: p) ->
strategy_induces_play G sigma p.
Proof. intros. assert (Hk:=H0). unfold strategy_induces_play in H0.
destruct H0. unfold strategy_induces_play. split.
+ intros. apply induced_play_length in Hk. assert (H5:=H3).
apply Hk in H3. simpl in H3. inversion H3. subst. inversion H7. subst.
assert (n < length p).
{destruct H4. inversion H6. subst. contradiction
(not_even_and_odd (length p)). lia. }
apply H0 with (n:=n) in H5.
assert (nth_error_from_back (x :: y :: p) n = 
 nth_error_from_back p n).
{unfold nth_error_from_back. simpl. rewrite <- app_assoc.
apply nth_error_app1. rewrite rev_length. auto. } rewrite H9 in H5.
assert (lastn n (x :: y :: p) = lastn n p).
{unfold lastn. simpl. rewrite <- app_assoc.
assert (firstn n (rev p ++ (y :: nil) ++ x :: nil) = 
firstn n (rev p)).
{apply firstn_app. rewrite rev_length. lia. } rewrite H10. auto. }
rewrite H10 in H5. auto.
++ split.
+++ apply H4.
+++ simpl. lia.
++ auto.
++ auto.
+ intros. apply induced_play_length in Hk. assert (H5:=H3).
apply Hk in H3. simpl in H3. inversion H3. subst. inversion H7. subst.
assert (n < length p).
{destruct H4. inversion H6. subst. contradiction
(not_even_and_odd (length p)). lia. }
apply H2 with (n:=n) in H5.
assert (nth_error_from_back (x :: y :: p) n = 
 nth_error_from_back p n).
{unfold nth_error_from_back. simpl. rewrite <- app_assoc.
apply nth_error_app1. rewrite rev_length. auto. } rewrite H9 in H5.
assert (lastn n (x :: y :: p) = lastn n p).
{unfold lastn. simpl. rewrite <- app_assoc.
assert (firstn n (rev p ++ (y :: nil) ++ x :: nil) = 
firstn n (rev p)).
{apply firstn_app. rewrite rev_length. lia. } rewrite H10. auto. }
rewrite H10 in H5. auto.
++ split.
+++ apply H4.
+++ simpl. lia.
++ auto.
++ auto.
Qed.

Definition strategy_induces_path (G : AsynchronousGame) (sigma : Strategy G)
(p : Path (E (A G))) := exists s, (forall k, In k s <-> In k (fst p)) /\ 
strategy_induces_play G sigma s /\
strategy_induces_play G sigma ((snd p) ++ s).

Definition winning (G : AsynchronousGame) (sigma : Strategy G) :=
(strategy_is_total G sigma) (* PROGRESS *)
/\
(strategy_preserves_validity G sigma) (* PRESERVATION *)
/\
(forall p, valid_alternating_path (A G) (nil, p) ->
strategy_induces_play G sigma p ->
Z.leb 0%Z (finite_payoff_position (A G) p) = true)
/\
(forall f n, valid_alternating_infinite_play (A G) f ->
strategy_induces_play G sigma (finite_part _ f n 0) -> 
Z.leb 0%Z (finite_payoff_position (A G) (finite_part _ f n 0)) = true)
/\
(forall w, valid_alternating_walk (A G) w ->
(strategy_induces_path G sigma (fst w) /\ 
strategy_induces_path G sigma (snd w)) ->
Z.leb 0%Z (finite_payoff_walk (A G) w) = true).

Definition backward_consistent G sigma :=
forall s1 m1 n1 m2 n2 s2,
(strategy_induces_play G sigma (s2 ++ (n2 :: m2 :: n1 :: m1 :: s1 :: nil))
/\ independent _ n1 m2 /\ independent _ m1 m2) ->
(strategy_induces_play G sigma (s2 ++ (n1 :: m1 :: n2 :: m2 :: s1 :: nil))
/\ independent _ n1 n2 /\ independent _ m1 n2).

Definition forward_consistent (G : AsynchronousGame) (sigma : Strategy G) :=
forall s1 m1 n1 m2 n2,
(sigma (m1 :: s1) = Some n1 /\ sigma (m2 :: s1) = Some n2
/\ independent _ m1 m2 /\ independent _ m2 n1) ->
(sigma (m2 :: n1 :: m1 :: s1) = Some n2 /\ independent _ m1 n2 /\ independent _ n1 n2).

Definition innocent (G : AsynchronousGame) (sigma : Strategy G) :=
forward_consistent G sigma /\ backward_consistent G sigma.

Definition play_action (G : AsynchronousGame) g h p :=
map (fun m => action G g m h) p.

Definition uniform (G : AsynchronousGame) (sigma : Strategy G) :=
forall p h, strategy_induces_play G sigma p ->
exists g, strategy_induces_play G sigma (play_action G g h p).

