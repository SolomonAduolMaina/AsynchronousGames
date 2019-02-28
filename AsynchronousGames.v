Require Import List.
Require Import ZArith.
Require Import Group.

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

    unit_is_least : forall i i' m, 
    leq (existT _ i (inl tt)) (existT _ i' m) <-> i = i';

    leq_same_component : forall i i' m m',
    leq (existT _ i m) (existT _ i' m') -> i = i';
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

Definition Path (E: EventStructure) := prod (Position E) (list (M (P E))).

Definition Walk (E: EventStructure) := prod (Path E) (Path E).

Inductive Infinity : Type :=
| plus_infinity : Infinity
| minus_infinity : Infinity.

Definition initial_move (P : PartialOrder) (m : M P) :=
forall n, leq P n m -> n = m.

Fact initial_is_unit :
forall E m, initial_move E m <->
(exists i, m = existT _ i (inl tt)).
Proof. unfold iff. split.
+ intros. unfold initial_move in H. destruct m. 
refine (ex_intro _ x _). symmetry. apply H.
apply unit_is_least. auto.
+ intros. unfold initial_move. intros. destruct H. subst.
apply anti_symmetric. split.
++ auto.
++ destruct n. apply leq_same_component in H0. subst. 
apply unit_is_least. auto.
Qed.

Definition second_move (P : PartialOrder) (m : M P) :=
(~ initial_move P m) /\ 
(forall n, (leq P n m /\ (n <> m)) -> initial_move P n).

Record AsynchronousArena := {
    E : EventStructure;
    polarity : (M (P E)) -> bool;
    finite_payoff_position : Position E -> Z;
    finite_payoff_walk : Walk E -> Z;
    infinite_payoff : (nat -> (M (P (E)))) -> Infinity -> Prop;

    initial_payoff : sumbool
    (finite_payoff_position nil = (-1)%Z)
    (finite_payoff_position nil = (1)%Z);

    polarity_first : forall m, initial_move (P E) m -> 
    ((polarity m = true -> finite_payoff_position nil = (-1)%Z)
    /\
    (polarity m = false -> finite_payoff_position nil = (1)%Z));

    polarity_second : forall m, second_move (P E) m -> 
    ((polarity m = true -> finite_payoff_position nil = (1)%Z)
    /\
    (polarity m = false -> finite_payoff_position nil = (-1)%Z));

    initial_null : forall (w : Walk E),
    (snd (fst w) = nil /\ snd (snd w) = nil) -> 
    finite_payoff_walk w = 0%Z;

    (*noninitial_payoff : forall (w : Walk E) (p : Position E),
    (((length (snd (fst w)) > 0) \/  (length (snd (fst w)) > 0)) /\ 
    (fst (fst w)) = nil) -> 
    finite_payoff_walk w = 
    finite_payoff_position ((fst (snd w)) ++ (snd (snd w)));*)
}.

Record AsynchronousGame  := 
{
    A : AsynchronousArena;
    X : Group;
    Y : Group;

    actl : (G X) -> M (P (E A)) -> M (P (E A));
    actr : M (P (E A)) -> (G Y) -> M (P (E A));

    actl_is_action : left_action X (M (P (E A))) actl;
    actr_is_action : right_action Y (M (P (E A))) actr;

    action_compatible : forall m g h,
    actr (actl g m) h = actl g (actr m h);

    coherence_1 : forall m n g h,
    leq (P (E A)) m n -> 
    leq (P (E A)) (actl g (actr m h)) (actl g (actr n h));
    coherence_2 : forall m g h,
    polarity A (actl g (actr m h)) = polarity A m;
    coherence_3 : forall m g,
    (polarity A m = false /\ (forall n, 
    leq (P (E A)) m n -> n = actl g (actr n (id Y)) )) -> 
    m = actl g (actr m (id Y));
    coherence_4 : forall m h,
    (polarity A m = true /\ (forall n, 
    leq (P (E A)) m n -> n = actl (id X) (actr n h))) -> 
    m = actl (id X) (actr m h);

    action_preserves_initial : forall i g h,
    exists i', actl g (actr (existT _ i (inl tt)) h) = existT _ i' (inl tt);

    action_preserves_non_initial : forall i g h m,
    exists i' m', actl g (actr (existT _ i (inr m)) h) = existT _ i' (inr m');
}.

Definition valid_position (E : EventStructure) (p : Position E) :=
forall m n, (In n p -> leq (P E) m n -> In m p)
/\
(In m p /\ In n p ->  not (incompatible E m n)).

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

Definition strictly_increasing f := forall m n, m < n -> f m < f n.

Definition strictly_increasing_list l :=
forall m n, m < n < length l ->
(exists k k', nth_error l m = Some k /\ nth_error l n = Some k' /\ k < k').

Fixpoint index_of n l : option nat :=
match l with
| nil => None
| x :: xs => if Nat.eqb n x then Some 0 else
  (match (index_of n xs) with
    | None => None
    | Some k => Some (S k)
  end)
end.

Ltac flatten_all :=
  repeat (let e := fresh "e" in
      match goal with
      | h: context[match ?x with | _ => _ end] |- _ => destruct x eqn:e
      | |- context[match ?x with | _ => _ end] => destruct x eqn:e
      end).

Ltac flatten :=
  repeat (let e := fresh "e" in
      match goal with
      | h: context[match ?x with | _ => _ end] |- _ => destruct x eqn:e
      | |- context[match ?x with | _ => _ end] => destruct x eqn:e
      end).

