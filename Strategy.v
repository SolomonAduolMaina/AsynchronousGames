Require Import List.
Require Import Lia.
Require Import ZArith.
Require Import Arith.Even.
Require Import Util.
Require Import AsynchronousGames.

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

Fact nth_error_cons_same A : forall n (l:list A) x a, 
nth_error_from_back l n = Some a -> nth_error_from_back (x::l) n = Some a.
Proof. intros. unfold nth_error_from_back in H. unfold nth_error_from_back. 
rewrite <- H. simpl. apply nth_error_app1. rewrite rev_length. apply nth_error_Some. apply nth_error_some_iff_nth_error_from_back. unfold
nth_error_from_back. rewrite H. easy.
Qed.

Definition valid_play (E : EventStructure) (p : Position E) :=
NoDup p /\ 
(forall m n, 
(forall a, (nth_error_from_back p a = Some n /\ leq (P E) m n /\ m <> n) ->
exists b, (nth_error_from_back p b = Some m /\ b < a))
/\
(In m p /\ In n p ->  not (incompatible E m n))).

Definition valid_position (E : EventStructure) (p : Position E) := valid_play E p.

Fact validity_closed_under_prefix (E : EventStructure) :
forall m p, valid_play E (m :: p) -> valid_play E p.
Proof. intros. unfold valid_play in H. destruct H. unfold valid_play. split.
+ apply NoDup_cons_iff in H. apply H.
+ intros. split.
++ intros. destruct H1.
assert (nth_error_from_back (m :: p) a = Some n).
{apply nth_error_cons_same. auto. } 
assert ((forall a : nat,
      nth_error_from_back (m :: p) a = Some n /\
      leq (P E) m0 n /\ m0 <> n ->
      exists b : nat,
        nth_error_from_back (m :: p) b = Some m0 /\
        b < a)).
{ apply H0. }
assert (exists b : nat,
       nth_error_from_back (m :: p) b = Some m0 /\
       b < a).
{apply H4. auto. } destruct H5. refine (ex_intro _ x _).
assert (a < length p).
{unfold nth_error_from_back in H1. 
assert (nth_error (rev p) a <> None). {rewrite H1. easy. }
simpl. apply nth_error_Some in H6. simpl in H6. rewrite rev_length in H6. auto. }
destruct H5. assert (x < length p). lia.
unfold nth_error_from_back in H5. simpl in H5.
assert (nth_error (rev p ++ m :: nil) x = nth_error (rev p) x).
{apply nth_error_app1. rewrite rev_length. auto. }
unfold nth_error_from_back. rewrite <- H9. auto.
++ intros. destruct H1.
assert (In m0 (m :: p) /\ In n (m :: p)).
{split; apply in_cons; auto. }
apply H0. auto.
Qed.

Definition valid_infinite_position
(E : EventStructure) (f : InfinitePosition E) :=
forall m n, (exists k, (f k = m -> (exists l, f l = n)))
/\
((exists k l, (f k = m /\ f l = n)) -> (not (incompatible E m n))).

Definition move_from (E : EventStructure) (m : (M (P E))) (p q: Position E) :=
(In m q) /\ (~ In m p) /\ (forall n, In n p -> In n q).

Definition valid_path (E: EventStructure) (p : Path E) :=
valid_play E ((snd p) ++ (fst p)).


Definition valid_walk (E: EventStructure) (w : Walk E) := 
valid_path E (fst w) /\ valid_path E (snd w) /\
(forall x,  In x (fst (fst w)) <-> In x (fst (snd w))).

Definition alternating (A : AsynchronousArena) (p : Path (E A)) :=
forall k m m', 
((nth_error_from_back (snd p) k = Some m /\ nth_error_from_back (snd p) (S k) = Some m') ->
negb (polarity A m) = polarity A m').

Definition valid_alternating_path (A : AsynchronousArena) (p : Path (E A)) :=
valid_path (E A) p /\ alternating A p.

Fixpoint finite_part A (f : nat -> A) (n : nat) (counter : nat) : list A :=
match n with
| 0 => nil
| S m => (f counter) :: (finite_part A f m (S counter))
end.

Definition valid_infinite_play (E: EventStructure) (f : nat -> (M (P E))) := 
forall n, valid_play E (finite_part _ f n 0).

Definition alternating_infinite_play (A : AsynchronousArena) 
(f : nat -> (M (P (E A)))) :=
forall n, negb (polarity A (f n)) = polarity A (f (S n)).

Definition valid_alternating_infinite_play (A : AsynchronousArena) 
(f : nat -> (M (P (E A)))) :=
valid_infinite_play (E A) f /\ alternating_infinite_play A f.

Definition valid_alternating_walk (A : AsynchronousArena) (w : Walk (E A)) :=
valid_walk (E A) w /\ alternating A (fst w) /\ alternating A (snd w).

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
forall p k m, (strategy_induces_play G sigma p /\ valid_play _ (k :: p) /\
sigma (k :: p) = Some m) -> valid_play _ (m :: k :: p).

Definition strategy_is_total (G : AsynchronousGame) (sigma : Strategy G) :=
(positive G -> (forall p, valid_play _ p -> even (length p) -> sigma p <> None)) /\
(negative G -> (forall p, valid_play _ p -> odd (length p) -> sigma p <> None)).

Fact induced_play_length (G : AsynchronousGame) (sigma : Strategy G) :
strategy_is_total G sigma -> 
(forall p, strategy_induces_play G sigma p -> valid_play _ p ->
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
strategy_induces_play G sigma (x :: y :: p) -> valid_play _ (x :: y :: p) ->
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

