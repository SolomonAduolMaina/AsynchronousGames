Require Import Lia.
Require Import List.
Require Import Coq.Program.Wf.
Require Import ZArith.
Require Import Init.Nat.
Require Import Logic.Eqdep.

Generalizable All Variables.

Class PartialOrder (A : Type) := {
leq : A -> A -> Prop;

reflexive : forall (x : A), leq x x;
anti_symmetric : forall (x y : A), leq x y /\ leq y x -> x = y;
transitive : forall (x y z : A), leq x y /\ leq y z -> leq x z
}.

Class EventStructure `(E : PartialOrder M) := 
{incompatible : M -> M -> Prop;
ideal : M -> list M;

symmetric : forall (x y: M), incompatible x y -> incompatible y x;
irreflexive : forall (x : M), not (incompatible x x);
ideal_finite : forall (x y : M), leq y x <-> In y (ideal x);
incompatible_closed : forall (x y z : M),
(incompatible x y) /\ (leq y z) -> incompatible x z
}.

Definition initial_move `(E: EventStructure M) (m : M) :=
forall (n : M), In n (ideal m) <-> m = n.

(* FAILED ATTEMPT 1 *)
Inductive leq_sum `(A : PartialOrder P)
`(E : EventStructure M)
: sigT (fun (m : M) => sig 
(fun (x : {m : M | initial_move E m} ) => let (x, y) := x in leq m x))
 -> sigT (fun (m : M) => sig 
(fun (x : {m : M | initial_move E m} ) => let (x, y) := x in leq m x))
 -> Prop :=
| leq_sum_proof : forall i a b x y, leq (proj1_sig a) (proj1_sig b) ->
leq_sum _ _ (existT _ i (exist _ a x)) (existT _ i (exist _ b y)).

Instance canonical_form `(A : PartialOrder P)
`(E : EventStructure M)
: PartialOrder
(sigT (fun (m : M) => sig 
(fun (x : {m : M | initial_move E m} ) => let (x, y) := x in leq m x)))
:= {leq x y := leq_sum A E x y}.
Proof.
- intros. destruct x. destruct s. apply leq_sum_proof. apply reflexive.
- intros. destruct x. destruct y. destruct s. destruct s0. destruct H.
inversion H. subst. destruct x1. destruct x2.
inversion H0. subst. simpl in *.
assert (x1 = x).
{apply anti_symmetric. auto. }
subst. 
Abort. (* No way of proving this! *) 
