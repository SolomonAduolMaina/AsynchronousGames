Require Import Lia.
Require Import List.
Require Coq.Program.Wf.
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

Definition Position `(E: EventStructure M) := 
{f : M -> bool |
forall (x y z: M), 
(f x = true /\ f y = true ->  not (incompatible x y))
 /\ 
(f x = true /\ leq y x -> f y = true)}.

Definition EmptyPositionHelper `(E: EventStructure M) : Position E.
  refine (exist _ (fun _ => false) _). split.
- intros. destruct H. inversion H.
- intros. destruct H. inversion H.
Defined.

Definition finite_position `(E : EventStructure M) (f : Position E) :=
let (f, p) := f in
exists (l : list M),forall (n : M), f n = true <-> In n l.

Definition FinitePosition `(E : EventStructure M) :=
{f : Position E | finite_position E f}.

Definition EmptyPosition `(E: EventStructure M) : FinitePosition E.
  refine (exist _ (EmptyPositionHelper E) _). simpl.
pose (witness := nil : list M).
refine (ex_intro _ witness _).
intros. simpl. unfold iff. split.
- intros. inversion H.
- intros. contradiction H.
Defined.

Definition InfinitePosition `(E : EventStructure M) :=
{f : Position E | not (finite_position E f)}.

(* TODO : Change the nat to int *)
Program Fixpoint valid_walk `(E: EventStructure M) 
(w : list (FinitePosition E + (M * nat))) {measure (length w)} := 
match w with
| inl(p1) :: nil => True
| inl(p1) :: inr(m, ep) :: inl(p2) :: xs => 
(valid_walk E (inl(p2) :: xs)) /\ 
(
(ep = 1 /\ p2 m = false /\ forall (n : M), n <> m -> p1 n = p2 n)
\/
(ep = 0 /\ p1 m = false /\ forall (n : M), n <> m -> p1 n = p2 n)
)
| _ => False
end.
Next Obligation.
simpl. lia. Qed.
Next Obligation.
split.
- intros. discriminate.
- intros. discriminate. Qed.
Next Obligation.
split.
- intros. discriminate.
- intros. discriminate. Qed.
Next Obligation.
split.
- intros. discriminate.
- intros. discriminate. Qed.
Next Obligation.
split.
- intros. discriminate.
- intros. discriminate. Qed.
Next Obligation.
split.
- intros. discriminate.
- intros. discriminate. Qed.

Definition Walk `(E: EventStructure M) := 
{w : list (FinitePosition E + (M * nat)) | valid_walk E w}.

Inductive Infinity : Type :=
| plus_infinity : Infinity
| minus_infinity : Infinity.

Definition initial_move `(E: EventStructure M) (m : M) :=
forall (n : M), In n (ideal m) <-> m = n.

Definition second_move `(E: EventStructure M) (m : M) :=
forall (n : M), In n (ideal m) ->  n = m \/ 
initial_move E m.

Class AsynchronousArena `(E : EventStructure M) := {
(* TODO : Change nat to int *)
polarity : M -> {n : nat | n = 0 \/ n = 1};
(* TODO : Change nat to int *)
finite_payoff : (FinitePosition E + Walk E) -> nat;
(* TODO: Is infinity already represented in coq? *)
infinite_payoff : InfinitePosition E -> Infinity;

initial_incompatible :
forall (m n : M), initial_move E m /\ initial_move E n 
-> incompatible m n;

(* TODO : Change nat to int *)
initial_payoff :
forall (f : FinitePosition E), 
let (g, _) := f in 
let (h, _) := g in
forall (m : M), h m = false -> finite_payoff (inl f) = 0 \/
finite_payoff (inl f) = 1;

(* TODO : change nat to int, change sign *)
polarity_first :
forall (m : M), initial_move E m -> 
let (n, _) := polarity m in n = finite_payoff (inl(EmptyPosition E));

(* TODO : Change nat to int *)
polarity_second :
forall (m : M), second_move E m -> 
let (n, _) := polarity m in n = finite_payoff (inl(EmptyPosition E));

empty_null :
forall (w : Walk E), 
let (l, _) := w in length l = 1 -> finite_payoff (inr w) = 0;

nonempty_payoff :
forall (w : Walk E) (p : FinitePosition E),
let (l, _) := w in length l > 1 /\ hd_error (rev l) = Some (inl p) /\
In (inl (EmptyPosition E)) l -> 
finite_payoff (inr w) = finite_payoff (inl p)
}.

(* TODO : Change nat to int *)
Definition Path `(E : EventStructure M) := 
{w : Walk E | let (l,_) := w in
forall (m : M) (n : nat), In (inr(m,n)) l -> n = 1
}.

(* TODO : Change the nat to int. Change sign *)
Program Fixpoint alternating_path `(E: EventStructure M) 
(p : Path E) 
{measure (let (p,_) := p in 
let (l,_) := p in
length l)} := 
let (p,_) := p in 
let (l,_) := p in
match l with
| inl(pos) :: nil => True
| inl(pos1) :: inr(m1, ep1) :: inl(pos2) :: nil => True
| inl(pos1) :: inr(m1, ep1) :: inl(pos2) :: inr(m2, ep2) :: xs => 
(valid_walk E (inl(pos2) :: inr(m2, ep2) :: xs)) /\ ep1 = ep2
| _ => False
end.
Next Obligation.
now split. Qed.
Next Obligation.
now split. Qed.
Next Obligation.
now split. Qed.
Next Obligation.
now split. Qed.
Next Obligation.
now split. Qed.
Next Obligation.
now split. Qed.

Definition Play `(E : EventStructure M) := 
{p : Path E | 
let (w, _) := p in
let (l, _) := w in
hd_error l = Some (inl(EmptyPosition E))
}.

Definition EmptyWalk `(E: EventStructure M) : Walk E.
  refine (exist _ (inl(EmptyPosition E) :: nil) _).
simpl. compute. auto.
Defined.

Definition EmptyPath `(E: EventStructure M) : Path E.
  refine (exist _ (EmptyWalk E) _).
simpl. intros. destruct H.
- inversion H.
- contradiction H.
Defined.

Definition EmptyPlay `(E: EventStructure M) : Play E.
refine (exist _ (EmptyPath E) _).
simpl. reflexivity.
Defined.

(* Definition EmptyPosition `(E: EventStructure M) : FinitePosition E.
  refine (exist _ (EmptyPositionHelper E) _). simpl.
pose (witness := nil : list M).
refine (ex_intro _ witness _).
intros. simpl. unfold iff. split.
- intros. inversion H.
- intros. contradiction H.
Defined.
*)