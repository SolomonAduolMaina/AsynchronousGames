Require Import List.
Require Import ZArith.

Record PartialOrder :=
  {
    I : Type; 
    N : I -> Type;
    M := {i : I & (sum unit (N i))};
    (* the set of moves is given by a choice of component, and either
       the initial move in that component (unit) or a non-initial move
       in that component. *)

    leq : M -> M -> Prop;

    reflexive : forall (x : M), leq x x;
    anti_symmetric : forall (x y : M), leq x y /\ leq y x -> x = y;
    transitive : forall (x y z : M), leq x y /\ leq y z -> leq x z;
  }.

Record EventStructure := 
  {
    P : PartialOrder;
    incompatible : (M P) -> (M P) -> Prop;

    ideal : (M P)  -> list (M P);

    symmetric : forall x y, incompatible x y -> incompatible y x;
    irreflexive : forall x, not (incompatible x x);
    ideal_finite : forall x y, leq P y x <-> In y (ideal x);
    incompatible_closed : forall x y z, (incompatible x y) /\ (leq P y z) -> incompatible x z
  }.

Definition Position (E : EventStructure) := list (M (P E)).

Definition valid_position (E : EventStructure) (p : Position E) :=
forall m n, (In n p -> leq (P E) m n -> In m p)
/\
(In m p /\ In n p ->  not (incompatible E m n)).

Definition move_from (E : EventStructure) (m : (M (P E))) (p q: Position E) :=
(In m q) /\ (~ In m p) /\ (forall n, In n p -> In n q).

Definition Path (E: EventStructure) := prod (Position E) (list (M (P E))).

Definition valid_path (E: EventStructure) (p : Path E) :=
forall n, 0 <= n <= length (snd p) ->
(valid_position E ((fst p) ++ (firstn n (snd p))) /\
(n > 0 -> (exists m, (nth_error (snd p) (n-1)) = Some m /\
move_from E m ((fst p) ++ (firstn (n-1) (snd p)))
((fst p) ++ (firstn n (snd p)))))).

Definition Walk (E: EventStructure) := prod (Path E) (Path E).

Definition valid_walk (E: EventStructure) (w : Walk E) := 
valid_path E (fst w) /\ valid_path E (snd w) /\
(forall x,  In x (fst (fst w)) <-> In x (fst (snd w))).

Inductive Infinity : Type :=
| plus_infinity : Infinity
| minus_infinity : Infinity.

Inductive InfinitePosition (E : EventStructure) : Type := 
| stream : (M (P E)) -> (unit -> InfinitePosition E)
-> InfinitePosition E .

Definition initial_move (P : PartialOrder) (m : M P) :=
forall n, leq P n m -> n = m.

Definition second_move (P : PartialOrder) (m : M P) :=
(~ initial_move P m) /\ (forall n, leq P n m -> initial_move P n).

Record AsynchronousArena := {
    E : EventStructure;
    polarity : (M (P E)) -> bool;
    finite_payoff_position : Position E -> Z;
    finite_payoff_walk : Walk E -> Z;
    infinite_payoff : InfinitePosition E  -> Infinity;

    initial_payoff :
    finite_payoff_position nil = (-1)%Z \/ finite_payoff_position nil = (1)%Z;

    polarity_first : forall m, initial_move (P E) m -> 
    ((polarity m = true -> finite_payoff_position nil = (-1)%Z)
    /\
    (polarity m = false -> finite_payoff_position nil = (1)%Z));

    polarity_second : forall m, second_move (P E) m -> 
    ((polarity m = true -> finite_payoff_position nil = (-1)%Z)
    /\
    (polarity m = false -> finite_payoff_position nil = (1)%Z));

    initial_null : forall (w : Walk E),
    (valid_walk E w /\ snd (fst w) = nil /\ snd (snd w) = nil) -> 
    finite_payoff_walk w = 0%Z;

    (*noninitial_payoff : forall (w : Walk E) (p : Position E),
    (valid_walk E w /\
    ((length (snd (fst w)) > 0) \/  (length (snd (fst w)) > 0)) /\ 
    (fst (fst w)) = nil) -> 
    finite_payoff_walk w = 
    finite_payoff_position ((fst (snd w)) ++ (snd (snd w)));*)
}.

Record Group := {
      G : Type;
      mult : G -> G -> G;
      id : G;
      inverse : G -> G;

      associative : forall (x y z : G),
      mult x (mult y z) = mult (mult x y) z;
      id_exists : forall (x : G), 
      mult id x = x /\ mult x id = x;
      inverses_exist : forall (x : G),
      mult x (inverse x) = id /\ mult (inverse x) x = id;
}.

Record AsynchronousGame  := 
{
    A : AsynchronousArena;
    X : Group;
    Y : Group;

    action : (G X) -> M (P (E A)) -> (G Y) -> M (P (E A));

    action_id : forall m, action (id X) m (id Y) = m;
    action_compatible : forall m g g' h h',
    action (mult X g g') m (mult Y h h') = 
    action g (action g' m h) h';

    coherence_1 : forall m n g h,
    leq (P (E A)) m n -> leq (P (E A)) (action g m h) (action g n h);
    coherence_2 : forall m g h,
    polarity A (action g m h) = polarity A m;
    coherence_3 : forall m g,
    (polarity A m = false /\ (forall n, 
    leq (P (E A)) m n -> n = action g n (id Y))) -> 
    m = action g m (id Y);
    coherence_4 : forall m h,
    (polarity A m = true /\ (forall n, 
    leq (P (E A)) m n -> n = action (id X) n h)) -> 
    m = action (id X) m h
}.
