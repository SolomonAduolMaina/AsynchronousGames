Require Import List.
Require Import ZArith.
Require Import AsynchronousGames.

Definition valid_position (E : AsynchronousGame) (p : Position (M E)) :=
forall m n, (In n p -> leq E m n -> In m p)
/\
(In m p /\ In n p ->  not (incompatible E m n)).

Definition valid_infinite_position
(E : AsynchronousGame) (f : InfinitePosition (M E)) :=
forall m n, (exists k, (f k = m -> (exists l, f l = n)))
/\
((exists k l, (f k = m /\ f l = n)) -> (not (incompatible E m n))).

Definition move_from A (m : A) (p q: list A) :=
(In m q) /\ (~ In m p) /\ (forall n, In n p -> In n q).

Definition valid_path (E: AsynchronousGame) (p : Path (M E)) :=
forall n, 0 <= n <= length (snd p) ->
(valid_position E ((fst p) ++ (firstn n (snd p))) /\
(n > 0 -> (exists m, (nth_error (snd p) (n-1)) = Some m /\
move_from (M E) m ((fst p) ++ (firstn (n-1) (snd p)))
((fst p) ++ (firstn n (snd p)))))).

Definition valid_walk (E: AsynchronousGame) (w : Walk (M E)) := 
valid_path E (fst w) /\ valid_path E (snd w) /\
(forall x, In x (fst (fst w)) <-> In x (fst (snd w))).

Definition alternating (A : AsynchronousGame) (p : Path (M A)) :=
forall k m m', 
((nth_error (snd p) k = Some m /\ nth_error (snd p) (S k) = Some m') ->
negb (polarity A m) = polarity A m').

Definition valid_alternating_path (A : AsynchronousGame) (p : Path (M A)) :=
valid_path A p /\ alternating A p.

Fixpoint finite_part A (f : nat -> A) (n : nat) (counter : nat) : list A :=
match n with
| 0 => nil
| S m => (f counter) :: (finite_part A f m (S counter))
end.

Definition valid_infinite_play (E: AsynchronousGame)
(f : InfinitePosition (M E)) :=
forall n, (valid_position E (finite_part _ f n 0)) /\
move_from (M E) (f n) (finite_part _ f n 0) (finite_part _ f (S n) 0).

Definition alternating_infinite_play (A : AsynchronousGame) 
(f : InfinitePosition (M A)) :=
forall n, negb (polarity A (f n)) = polarity A (f (S n)).

Definition valid_alternating_infinite_play (A : AsynchronousGame) 
(f : InfinitePosition (M A)) :=
valid_infinite_play A f /\ alternating_infinite_play A f.

Definition valid_alternating_walk (A : AsynchronousGame) (w : Walk (M A)) :=
valid_walk A w /\ alternating A (fst w) /\ alternating A (snd w).

Definition incomparable P m n := (not (leq P m n)) /\ (not (leq P m n)).

Definition compatible E m n := not (incompatible E m n).

Definition independent E m n := (compatible E m n) /\ (incomparable E m n).

Definition Strategy (G : AsynchronousGame) := (Play (M G)) -> option (M G).

Definition positive (G : AsynchronousGame) := positive_or_negative G = true.

Definition negative (G : AsynchronousGame) := positive_or_negative G = false.

Definition strategy_induces_play (G : AsynchronousGame) (sigma : Strategy G) p :=
(positive G -> (forall n, (Nat.even n = true /\ n <= length p) -> 
(sigma (firstn n p)) = nth_error p n))
/\
(negative G -> (forall n, (Nat.odd n = true /\ n <= length p) -> 
(sigma (firstn n p)) = nth_error p n )).

Definition strategy_induces_path (G : AsynchronousGame) (sigma : Strategy G)
(p : Path (M G)) :=
exists l, (forall k, In k l <-> In k (fst p)) /\ 
strategy_induces_play G sigma (l ++ (snd p)).

Definition winning (G : AsynchronousGame) (sigma : Strategy G) :=
(forall p, valid_alternating_path G (nil, p) ->
strategy_induces_play G sigma p ->
Z.leb 0%Z (finite_payoff_position G p) = true)
/\
(forall f n, valid_alternating_infinite_play G f ->
strategy_induces_play G sigma (finite_part _ f n 0) -> 
Z.leb 0%Z (finite_payoff_position G (finite_part _ f n 0)) = true)
/\
(forall w, valid_alternating_walk G w ->
(strategy_induces_path G sigma (fst w) /\ 
strategy_induces_path G sigma (snd w)) ->
Z.leb 0%Z (finite_payoff_walk G w) = true).

Definition backward_consistent G sigma :=
forall s1 m1 n1 m2 n2 s2,
(strategy_induces_play G sigma (s1 ++ (m1 :: n1 :: m2 :: n2 :: nil) ++ s2)
/\ independent _ n1 m2 /\ independent _ m1 m2) ->
(strategy_induces_play G sigma (s1 ++ (m2 :: n2 :: m1 :: n1 :: nil) ++ s2)
/\ independent _ n1 n2 /\ independent _ m1 n2).

Definition forward_consistent (G : AsynchronousGame) (sigma : Strategy G) :=
forall s1 m1 n1 m2 n2,
(sigma (s1 ++ (m1 :: nil)) = Some n1 /\ sigma (s1 ++ (m2 :: nil)) = Some n2
/\ independent _ m1 m2 /\ independent _ m2 n1) ->
(sigma (s1 ++ (m1 :: n1 :: m2 :: nil)) = Some n2
/\ independent _ m1 n2 /\ independent _ n1 n2).

Definition innocent (G : AsynchronousGame) (sigma : Strategy G) :=
forward_consistent G sigma /\ backward_consistent G sigma.

Definition play_action (G : AsynchronousGame) g h p :=
map (fun m => action G g m h) p.

Definition uniform (G : AsynchronousGame) (sigma : Strategy G) :=
forall p h, strategy_induces_play G sigma p ->
exists g, strategy_induces_play G sigma (play_action G g h p).
