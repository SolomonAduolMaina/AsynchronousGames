Require Import List.
Require Import ZArith.
Require Import AsynchronousGames.

Definition valid_position (E : EventStructure) (p : Position E) :=
forall m n, (In n p -> leq (P E) m n -> In m p)
/\
(In m p /\ In n p ->  not (incompatible E m n)).

Definition valid_infinite_position
(E : EventStructure) (f : InfinitePosition E) :=
forall m n, (exists k, (f k = m -> (exists l, f l = n)))
/\
((exists k l, (f k = m /\ f l = n)) -> (not (incompatible E m n))).

Definition move_from (E : EventStructure) (m : (M (P E))) (p q: Position E) :=
(In m q) /\ (~ In m p) /\ (forall n, In n p -> In n q).

Definition valid_path (E: EventStructure) (p : Path E) :=
forall n, 0 <= n <= length (snd p) ->
(valid_position E ((fst p) ++ (firstn n (snd p))) /\
(n > 0 -> (exists m, (nth_error (snd p) (n-1)) = Some m /\
move_from E m ((fst p) ++ (firstn (n-1) (snd p)))
((fst p) ++ (firstn n (snd p)))))).


Definition valid_walk (E: EventStructure) (w : Walk E) := 
valid_path E (fst w) /\ valid_path E (snd w) /\
(forall x,  In x (fst (fst w)) <-> In x (fst (snd w))).

Definition alternating (A : AsynchronousArena) (p : Path (E A)) :=
forall k m m', 
((nth_error (snd p) k = Some m /\ nth_error (snd p) (S k) = Some m') ->
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

Definition positive (G : AsynchronousGame) := 
finite_payoff_position (A G) nil = (-1)%Z.

Definition negative (G : AsynchronousGame) := 
finite_payoff_position (A G) nil = (1)%Z.

Definition strategy_induces_play (G : AsynchronousGame) (sigma : Strategy G) p :=
(positive G -> (forall n, (Nat.even n = true /\ n <= length p) -> 
(sigma (firstn n p)) = nth_error p n))
/\
(negative G -> (forall n, (Nat.odd n = true /\ n <= length p) -> 
(sigma (firstn n p)) = nth_error p n )).


Definition strategy_induces_path (G : AsynchronousGame) (sigma : Strategy G)
(p : Path (E (A G))) :=
exists (q : Path (E (A G))) l, q = (nil, l) /\
(forall k, In k l <-> In k (fst p)) /\ 
strategy_induces_play G sigma (l ++ (snd p)).

Definition winning (G : AsynchronousGame) (sigma : Strategy G) :=
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
