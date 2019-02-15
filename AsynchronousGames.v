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

Inductive InfinitePosition (E : EventStructure) : Type := 
| stream : (M (P E)) -> (unit -> InfinitePosition E)
-> InfinitePosition E .

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
    infinite_payoff : InfinitePosition E  -> Infinity;

    initial_payoff :
    finite_payoff_position nil = (-1)%Z \/ finite_payoff_position nil = (1)%Z;

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
    m = action (id X) m h;

    action_preserves_initial : forall i g h,
    exists i', action g (existT _ i (inl tt)) h = existT _ i' (inl tt);

    action_preserves_non_initial : forall i g h m,
    exists i' m', action g (existT _ i (inr m)) h = existT _ i' (inr m');
}.

Fact inverse_is_unique (G: Group) : forall x y z,
mult G x y = id G /\ mult G x z = id G -> y = z.
Proof. intros. destruct H. rewrite <- H in H0.
assert (mult G (inverse G x) (mult G x z) = 
mult G (inverse G x) (mult G x y) ).
{  rewrite H0. reflexivity. }
rewrite associative in H1. rewrite associative in H1.
assert (mult G (inverse G x) x = id G).
{ apply inverses_exist. }
rewrite H2 in H1. 
assert (mult G (id G) z = z /\ mult G (id G) y = y).
{ split. 
+ apply id_exists.
+ apply id_exists. }
destruct H3. rewrite H3 in H1. rewrite H4 in H1. auto.
Qed.

Fact mult_inverse (G: Group) : forall g g',
mult G (inverse G g') (inverse G g) = inverse G (mult G g g').
Proof. intros. 
assert (mult G (mult G g g') (mult G (inverse G g') (inverse G g)) = id G /\
mult G (mult G g g') (inverse G (mult G g g')) = id G).
{ assert (mult G (mult G g g') (inverse G (mult G g g')) = id G).
{ apply inverses_exist. }
assert (mult G (mult G g g') (mult G (inverse G g') (inverse G g)) = id G).
{ rewrite associative. 
assert (mult G (mult G g g') (inverse G g') = g).
{ rewrite <- associative.
assert (mult G g' (inverse G g') = id G).
{ apply inverses_exist. }
rewrite H0. apply id_exists.
  }
rewrite H0. apply inverses_exist.
 }
rewrite H. rewrite H0. auto.
} apply inverse_is_unique with (G0:=G) (x:=mult G g g')
(y:=mult G (inverse G g') (inverse G g)) (z:=inverse G (mult G g g')).
auto.
Qed.

Fact inverse_id_is_id (G: Group) : inverse G (id G) = id G.
Proof. apply inverse_is_unique with (G0:=G) (x:=id G) 
(y:= inverse G (id G)) (z:=id G). 
split.
+ apply inverses_exist.
+ apply id_exists.
Qed.

Definition trivial_group : Group.
refine({|
          G := unit;
          mult a b := tt;
          id := tt
      |}).
Proof.
- auto.
- auto.
- intros. destruct x. auto.
- auto.
Defined.

Definition product_group (X Y : Group) : Group.
refine ({|
        G := (G X) * (G Y);
        mult m n := (mult _ (fst m) (fst n), mult _ (snd m) (snd n));
        id := (id _, id _);
        inverse m := (inverse _ (fst m), inverse _ (snd m))
       |}).
Proof.
- intros. destruct x. destruct y. destruct z. simpl.
rewrite associative. rewrite associative. reflexivity.
- intros. destruct x. simpl.
assert (mult _ (id _) g = g /\ mult _ g (id _) = g).
{ apply id_exists. }
assert (mult _ (id _) g0 = g0 /\ mult _ g0 (id _) = g0).
{ apply id_exists. }
destruct H0. destruct H. rewrite H. rewrite H1. rewrite H0. rewrite H2. auto.
- intros. destruct x. simpl. 
assert (mult _ g (inverse _ g) = id _ /\ mult _ (inverse _ g) g = id _).
{ apply inverses_exist. }
assert (mult _ g0 (inverse _ g0) = id _ /\ mult _ (inverse _ g0) g0 = id _).
{ apply inverses_exist. }
destruct H. destruct H0. rewrite H. rewrite H1. rewrite H0. rewrite H2. auto.
Defined.

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




