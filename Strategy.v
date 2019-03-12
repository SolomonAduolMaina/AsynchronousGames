Require Import List.
Require Import Lia.
Require Import ZArith.
Require Import Arith.Even.
Require Import AsynchronousGames.

Definition lastn {A} n (l : list A) := rev (firstn n (rev l)).

Definition nth_error_from_back {A} (l : list A) n := nth_error (rev l) n.

Definition valid_position (E : EventStructure) (p : Position E) :=
NoDup p /\ 
(forall m n, 
(forall a, (nth_error p a = Some n /\ leq (P E) m n /\ m <> n) ->
exists b, (nth_error p b = Some m /\ b > a))
/\
(In m p /\ In n p ->  not (incompatible E m n))).

Definition valid_infinite_position
(E : EventStructure) (f : InfinitePosition E) :=
forall m n, (exists k, (f k = m -> (exists l, f l = n)))
/\
((exists k l, (f k = m /\ f l = n)) -> (not (incompatible E m n))).

Definition move_from (E : EventStructure) (m : (M (P E))) (p q: Position E) :=
(In m q) /\ (~ In m p) /\ (forall n, In n p -> In n q).

Definition valid_path (E: EventStructure) (p : Path E) :=
forall n, 0 <= n <= length (snd p) ->
(valid_position E ((lastn n (snd p)) ++ (fst p)) /\
(n > 0 -> (exists m, (nth_error_from_back (snd p) (n-1)) = Some m /\
move_from E m ((lastn (n-1) (snd p)) ++ (fst p))
((lastn n (snd p)) ++ (fst p))))).


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

Definition valid_infinite_play (E: EventStructure)
(f : nat -> (M (P E))) :=
forall n, (valid_position E (finite_part _ f n 0)) /\
move_from E (f n) (finite_part _ f n 0) (finite_part _ f (S n) 0).

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

Definition strategy_never_stalls (G : AsynchronousGame) (sigma : Strategy G) :=
(positive G -> (forall p, even (length p) -> sigma p <> None)) /\
(negative G -> (forall p, odd (length p) -> sigma p <> None)).

Fact induced_play_length (G : AsynchronousGame) (sigma : Strategy G) :
strategy_never_stalls G sigma ->
(forall p, strategy_induces_play G sigma p ->
((positive G -> odd (length p)) /\ (negative G -> even (length p)))).
Proof. intros. unfold strategy_never_stalls in H. destruct H. 
unfold strategy_induces_play in H0. destruct H0.
split.
+ intros. destruct (even_odd_dec (length p)).
++ assert (sigma p <> None). {apply H. auto. auto. }
assert (sigma (lastn (length p) p) = nth_error_from_back p (length p)).
{apply H0. auto. auto. } unfold lastn in H5. rewrite <- rev_length in H5.
rewrite firstn_all in H5. rewrite rev_involutive in H5. unfold nth_error_from_back in H5.
rewrite H5 in H4. apply nth_error_Some in H4. lia.
++ auto.
+ intros. destruct (even_odd_dec (length p)).
++ auto.
++ assert (sigma p <> None). {apply H1. auto. auto. }
assert (sigma (lastn (length p) p) = nth_error_from_back p (length p)).
{apply H2. auto. auto. } unfold lastn in H5. rewrite <- rev_length in H5.
rewrite firstn_all in H5. rewrite rev_involutive in H5. unfold nth_error_from_back in H5.
rewrite H5 in H4. apply nth_error_Some in H4. lia.
Qed.

Definition strategy_preserves_validity (G : AsynchronousGame) (sigma : Strategy G) :=
forall p k, valid_position (E (A G)) p /\ sigma p = Some k ->
valid_position (E (A G)) (k :: p).

Definition strategy_induces_path (G : AsynchronousGame) (sigma : Strategy G)
(p : Path (E (A G))) := exists s, (forall k, In k s <-> In k (fst p)) /\ 
strategy_induces_play G sigma s /\
strategy_induces_play G sigma ((snd p) ++ s).

Definition winning (G : AsynchronousGame) (sigma : Strategy G) :=
(strategy_never_stalls G sigma)
/\
(strategy_preserves_validity G sigma)
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

