Require Import List.
Require Import LinearLogic.
Require Import AsynchronousGames.

Inductive valid_trace (G : Game) (T : Trace Move) : Prop :=
| empty_is_valid : T = nil -> valid_trace G T
| non_empty_is_valid : forall m ms,
valid_trace G ms /\ (valid_move ms (polarity m) m) ->
T = m :: ms ->
valid_trace G T.

Definition Strategy (G : Game) := (Trace Move) -> Move.

Definition winning_strategy (G : Game) (s : Strategy G) :=
True.
(* Strategies are total by definition i.e.
for every Trace there is a Move, hence for every Trace
with Player to play next there is a Move.

We still need to define:
1. payoff condtions
2. consistency conditions
3. uniformity conditions. *)




