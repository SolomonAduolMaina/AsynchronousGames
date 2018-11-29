Require Import Lia.
Require Import List.
Require Import Coq.Program.Wf.
Require Import ZArith.
Require Import Init.Nat.
Require Import Logic.Eqdep.

Generalizable All Variables.

Class PartialOrder (Index : Type) (A : Type) := {
leq : A -> A -> Prop;
initial_moves : Index -> A;

reflexive : forall (x : A), leq x x;
anti_symmetric : forall (x y : A), leq x y /\ leq y x -> x = y;
transitive : forall (x y z : A), leq x y /\ leq y z -> leq x z;

least_elements : forall b,
((forall a, leq a b -> a = b)
<-> (exists i, initial_moves i = b))
}.

Inductive Singleton : Type :=
| new : Singleton.

Instance canonical `(P : PartialOrder Index A) (i : Index)
: PartialOrder Singleton A (* What should this type be? *) :=
{leq x y :=
leq x y /\ (leq x (initial_moves i));

initial_moves x := initial_moves i;
}.
Proof.
- intros. split.
+ apply reflexive.
+ Abort. 
(* We need to restrict A to {a : A | leq a (intial_moves i)} but...*)

Instance canonical_new `(P : PartialOrder Index A) (i : Index)
: PartialOrder Singleton {a : A | leq a (initial_moves i)}:=
{leq x y :=
match x, y with
| exist _ a p, exist _ b q => leq a b
end;

initial_moves _ := (exist _ (initial_moves i) _);
}.
Proof.
- apply reflexive.
- intros. destruct x. apply reflexive.
- intros. destruct x. destruct y. apply anti_symmetric in H.
subst. Abort. (* No way of proving this! *)
