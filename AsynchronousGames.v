Require Import Util.
Require Import List.
Require Export ZArith.
Require Import Group.

Record PartialOrder :=
  {
    I : Type;
    N : I -> Type;
    M := {i : I & (sum unit (N i))};
    leq : M -> M -> Prop;
}.

Record EventStructure := 
  {
    P : PartialOrder;
    incompatible : (M P) -> (M P) -> Prop;
    ideal : (M P)  -> list (M P);
}.

Definition Position (E : EventStructure) := list (M (P E)).

Definition Path (E: EventStructure) := prod (Position E) (list (M (P E))).

Definition Walk (E: EventStructure) := prod (Path E) (Path E).

Definition InfinitePosition (E : EventStructure) := nat -> (M (P E)).

Definition initial_move (P : PartialOrder) (m : M P) :=
forall n, leq P n m -> n = m.

Definition second_move (P : PartialOrder) (m : M P) :=
(~ initial_move P m) /\ 
(forall n, (leq P n m /\ (n <> m)) -> initial_move P n).

Record AsynchronousArena := {
    E : EventStructure;
    polarity : (M (P E)) -> bool;
    finite_payoff_position : Position E -> Z;
    finite_payoff_walk : Walk E -> Z;
    infinite_payoff : (InfinitePosition E) -> bool -> Prop;
    positive_or_negative : bool;
}.

Record AsynchronousGame  := 
{
    A : AsynchronousArena;
    X : Group;
    Y : Group;

    action : (G X) -> M (P (E A)) -> (G Y) -> M (P (E A));
}.

Definition reflexive (P : PartialOrder) := forall x, leq P x x.

Definition anti_symmetric (P : PartialOrder) :=
forall x y, leq P x y /\ leq P y x -> x = y.

Definition transitive (P : PartialOrder) :=
forall x y z, leq P x y /\ leq P y z -> leq P x z.

Definition unit_is_least (P : PartialOrder) := 
forall i i' m, leq P (existT _ i (inl tt)) (existT _ i' m) <-> i = i'.

Definition leq_same_component (P : PartialOrder) :=
forall i i' m m', leq P (existT _ i m) (existT _ i' m') -> i = i'.

Definition well_formed_partial_order (P : PartialOrder) :=
reflexive P /\ anti_symmetric P /\ transitive P /\ unit_is_least P /\
leq_same_component P.


Definition symmetric (E : EventStructure) :=
forall x y, incompatible E x y -> incompatible E y x.

Definition irreflexive (E : EventStructure) :=
forall x, not (incompatible E x x).

Definition ideal_finite (E : EventStructure) :=
forall x y, leq (P E) y x <-> In y (ideal E x).

Definition incompatible_closed (E : EventStructure) :=
forall x y z, (incompatible E x y) /\ (leq (P E) y z) -> incompatible E x z.

Definition well_formed_event_structure (E : EventStructure) :=
well_formed_partial_order (P E) /\
symmetric E /\ irreflexive E /\ ideal_finite E /\
incompatible_closed E.

Definition polarity_first (A : AsynchronousArena) :=
forall m, initial_move (P (E A)) m -> 
    ((polarity A m = true -> finite_payoff_position A nil = (-1)%Z)
    /\
    (polarity A m = false -> finite_payoff_position A nil = (1)%Z)).

Definition polarity_second (A : AsynchronousArena) :=
forall m, second_move (P (E A)) m -> 
    ((polarity A m = true -> finite_payoff_position A nil = (1)%Z)
    /\
    (polarity A m = false -> finite_payoff_position A nil = (-1)%Z)).

Definition initial_null (A : AsynchronousArena) :=
forall w, (snd (fst w) = nil /\ snd (snd w) = nil) -> 
    finite_payoff_walk A w = 0%Z.

Definition positive_iff_player_always_starts (A : AsynchronousArena) :=
(positive_or_negative A = true ->
(forall m, initial_move (P (E A)) m -> polarity A m = true)) /\ 
(positive_or_negative A = false ->
(forall m, initial_move (P (E A)) m -> polarity A m = false)).


(*Definition noninitial_payoff (A : AsynchronousArena) :=
forall w,
    (((length (snd (fst w)) > 0) \/  (length (snd (snd w)) > 0)) /\ 
    (fst (fst w)) = nil) -> 
    finite_payoff_walk A w = 
    finite_payoff_position A ((fst (snd w)) ++ (snd (snd w))).*)

Definition well_formed_asynchronous_arena (A : AsynchronousArena) :=
well_formed_event_structure (E A) /\
polarity_first A /\ polarity_second A /\
initial_null A /\
positive_iff_player_always_starts A.

Definition restriction_to_left_is_action (G : AsynchronousGame) :=
left_action _ _ (fun g m => action G g m (id (Y G))).

Definition restriction_to_right_is_action (G : AsynchronousGame) :=
right_action _ _ (fun m h => action G (id (X G)) m h).

Definition coherence_1 (G : AsynchronousGame) := forall m n g h,
    leq (P (E (A G))) m n -> 
    leq (P (E (A G))) (action G g m h) (action G g n h).

Definition coherence_2 (G : AsynchronousGame) := forall m g h,
    polarity (A G) (action G g m h) = polarity (A G) m.

(*Definition coherence_3 (G : AsynchronousGame) : forall m g,
(polarity (A G) m = false /\ 
(forall n, (leq (P (E (A G))) n m /\ m <> n) -> 
n = (fun g m => action G g m (id (Y G))) g n)) -> 
m = (fun g m => action G g m (id (Y G))) g m.

Definition coherence_4 (G : AsynchronousGame) : forall m h,
(polarity (A G) m = true /\ 
(forall n, (leq (P (E (A G))) n m /\ m <> n) -> 
n = (fun m h => action G (id (X G)) m h) n h)) -> 
m = (fun m h => action G (id (X G)) m h) m h.*)

Definition action_preserves_initial (G : AsynchronousGame) :=
forall i g h,
    exists i', action G g (existT _ i (inl tt)) h = existT _ i' (inl tt).

Definition action_preserves_non_initial (G : AsynchronousGame) :=
forall i g h m,
    exists i' m', action G g (existT _ i (inr m)) h = existT _ i' (inr m').

Definition well_formed_asynchronousgame (G : AsynchronousGame) :=
well_formed_asynchronous_arena (A G) /\
restriction_to_left_is_action G /\
restriction_to_right_is_action G /\
coherence_1 G /\
coherence_2 G /\
action_preserves_initial G /\
action_preserves_non_initial G.

Fact action_does_not_send_inr_to_inl : forall G i i' g h s,
well_formed_asynchronousgame G ->
~ (action G g (existT _ i (inr s)) h = existT _ i' (inl tt)).
Proof. intros. unfold not. intros.
assert (exists k k1,
 action G g
      (existT
         (fun i : I (P (E (A G))) =>
          (unit + N (P (E (A G))) i)%type) i 
         (inr s)) h = 
existT
      (fun i : I (P (E (A G))) =>
       (unit + N (P (E (A G))) i)%type) k (inr k1)).
{ destruct H. destruct H1. destruct H2. destruct H3. destruct H4.
 apply H5. }
destruct H1. destruct H1. rewrite H0 in H1. inversion H1.
Qed.

Fact initial_is_unit :
forall P m, well_formed_partial_order P ->
(initial_move P m <-> (exists i, m = existT _ i (inl tt))).
Proof. unfold iff. split.
+ intros. unfold initial_move in H0. destruct m. 
refine (ex_intro _ x _). symmetry. apply H0.
unfold well_formed_partial_order in H. destruct H. destruct H1.
destruct H2. destruct H3. unfold unit_is_least in H3.
apply H3. auto.
+ intros. destruct H0. subst. unfold initial_move. intros.
unfold well_formed_partial_order in H. destruct H. destruct H1.
destruct H2. destruct H3. destruct n. destruct s.
++ destruct u. apply H3 in H0. subst. auto.
++ assert (H6:=H0). apply H4 in H0. subst. 
assert (leq _
(existT (fun i : I P0 => (unit + N P0 i)%type) x
          (inl tt))
(existT (fun i : I P0 => (unit + N P0 i)%type) x
          (inr n))).
{apply H3. auto. }
apply H1. auto.
Qed.
