Require Import AsynchronousGames.
Require Import Lia.
Require Import List.
Require Import Coq.Program.Wf.
Require Import ZArith.
Require Import Init.Nat.

Generalizable All Variables.

Definition Path `(E : EventStructure M) := Walk E.

Definition valid_path `(E : EventStructure M) (p : Walk E) :=
valid_walk E p /\
forall (m : M) (b : bool), In (inr(m, b)) p -> b = true.

Definition Play `(E: EventStructure M) := Walk E.

Definition valid_play `(E : EventStructure M) (p : Walk E) :=
valid_path E p /\
hd_error p = Some (inl(nil : Position E)).

Fixpoint valid_alternating_play `(E: EventStructure M)
(A : AsynchronousArena E) (p : Path E) := 
valid_play E p /\
match p with
| inl(pos) :: nil => True
| inl(pos1) :: inr(m1, ep1) :: inl(pos2) :: nil => True
| inl(pos1) :: inr(m1, ep1) :: ((inl(pos2) :: inr(m2, ep2) :: xs) as s) => 
(valid_walk E s) /\ (polarity m1 = negb (polarity m2))
| _ => False
end.

Definition initialPlay `(E: EventStructure M) : Play E :=
inl(nil : Position E) :: nil.

Fact initial_play_is_valid `(E: EventStructure M) :
valid_play E (initialPlay E).
Proof. unfold valid_play. split.
- unfold valid_path. split.
+ split. 
++ intros. simpl in H. destruct H. contradiction H.
++ intros. destruct H. simpl in H. contradiction H.
+ intros. simpl in H. destruct H.
++ inversion H.
++ contradiction H.
- simpl. reflexivity.
Qed.

Fact initial_play_is_alternating `(E: EventStructure M)
(A : AsynchronousArena E) :
valid_alternating_play E A (initialPlay E).
Proof. simpl. split.
- apply initial_play_is_valid.
- auto. Qed. 


Definition player_move
`(E: EventStructure M) (A : AsynchronousArena E) (m : M):=
polarity m = true.

Definition opponent_move
`(E: EventStructure M) (A : AsynchronousArena E) (m : M):=
polarity m = false.

Definition Strategy `(E: EventStructure M) (A : AsynchronousArena E) :=
Play E -> bool.

Definition valid_strategy
`(E: EventStructure M) (A : AsynchronousArena E)
(f : Strategy E A) :=
(forall (s : Play E), 
f s = true -> valid_alternating_play E A s) 
/\
(f (initialPlay E) = true)
 /\
(forall (s : Play E),
f s = true /\ length s > 1 -> 
exists (m1 m2 : M) (b1 b2 : bool), 
nth_error s 1 = Some (inr(m1, b1)) /\
nth_error (rev s) 1 = Some (inr(m2, b2)) /\
opponent_move E A m1 /\ player_move E A m2)
/\
(forall (s : Play E) (x y z: Position E) (m n: M),
hd_error s = Some (inl (nil : Position E)) /\
hd_error (rev s) = Some (inl x) /\
move_from E m x y /\
opponent_move E A m /\
move_from E n y z /\
player_move E A n ->
f (s ++ ((inr (m,false) :: (inl y) :: 
(inr (n,true)) :: (inl z) :: nil))) = true -> f s = true)
/\
(forall (s : Play E) (x y z1 z2: Position E) (m n1 n2: M),
hd_error s = Some (inl (nil : Position E)) /\
hd_error (rev s) = Some (inl x) /\
move_from E m x y /\
opponent_move E A m /\
move_from E n1 y z1 /\
player_move E A n1 /\
move_from E n2 y z2 /\
player_move E A n2 ->
f (s ++ ((inr (m,false) :: (inl y) :: 
(inr (n1,true)) :: (inl z1) :: nil))) = true 
/\
f (s ++ ((inr (m,false) :: (inl y) :: 
(inr (n2,true)) :: (inl z2) :: nil))) = true 
-> n1 = n2)
.

Definition independent `(E: EventStructure M) (m n : M) :=
incompatible m n /\ not (leq m n) /\ not (leq n m).

Definition backward_consistent 
`(E: EventStructure M) (A : AsynchronousArena E)
(s : Strategy E A) :=
valid_strategy E A s
/\
forall (s1 : Play E) (s2 : Path E) (m1 m2 n1 n2 : M)
, 
valid_play E s1 /\ valid_path E s2 /\
(exists (p1 p2 p3: Position E),
s (s1 ++ (inr(m1,true) :: inl(p1) :: 
inr(n1,true) :: inl(p2) :: inr(m2,true) :: 
inl(p3) :: inr(n2, true) :: nil) ++ s2) = true
/\ (independent E n1 m2) /\ (independent E m1 m2)
-> 
(independent E n1 n2) /\ (independent E m1 n2) /\
exists (p1' p2' p3': Position E),
s (s1 ++ (inr(m2,true) :: inl(p1') :: 
inr(n2,true) :: inl(p2') :: inr(m1,true) :: 
inl(p3') :: inr(n1, true) :: nil) ++ s2) = true
)
.

Definition forward_consistent 
`(E: EventStructure M) (A : AsynchronousArena E)
(s : Strategy E A) :=
valid_strategy E A s
/\
forall (s1 : Play E) (m1 m2 n1 n2 : M), 
valid_play E s1 /\
(exists (p1 p2 p3 p4: Position E), 
s (s1 ++ (inr(m1,true) :: inl(p1) :: inr(n1,true) :: inl(p2) :: nil)) = true
/\ 
s (s1 ++ (inr(m2,true) :: inl(p3) :: inr(n2,true) :: inl(p4) :: nil)) = true
/\
(independent E m1 m2) 
/\
(independent E m2 n1)
-> 
(independent E m1 n2) 
/\ (independent E n1 n2) /\
exists (p1' p2' p3' p4': Position E),
s (s1 ++ (inr(m1,true) :: inl(p1') :: 
inr(n1,true) :: inl(p2') :: inr(m2,true) :: 
inl(p3') :: inr(n2, true) :: inl(p4') :: nil)) = true
)
.

Definition innocent `(E: EventStructure M) (A : AsynchronousArena E)
(s : Strategy E A) :=
forward_consistent E A s /\ backward_consistent E A s.

Definition InfinitePlay `(E: EventStructure M) :=
nat -> (Position E + M).

Definition even (n : nat) := exists (m : nat), n = 2*m.

Definition infinite_play_valid `(E: EventStructure M)
(p : InfinitePlay E) := 
p 0 = inl(nil : Position E) /\

forall (n : nat), even n -> 
exists (m : M) (x x' : Position E),
p n = inl(x) /\ p (n+1) = inr (m) /\ p (n+2) = inl(x') /\
move_from E m x x'.

Definition total_strategy
 `(E: EventStructure M) (A : AsynchronousArena E) (sigma : Strategy E A) :=
forall (s : Play E) (m : M) (pos : Position E),
(valid_play E (s ++ (inr(m,true) :: inl(pos) :: nil)) /\
sigma s = true /\ opponent_move E A m)
-> exists (n : M) (pos' : Position E),
(sigma (s ++ (inr(m,true) :: inl(pos) :: inr(n,true) :: inl(pos') :: nil)) 
= true /\ player_move E A n).

Definition finite_nonnegative
 `(E: EventStructure M) (A : AsynchronousArena E) (sigma : Strategy E A) :=
forall (x : Position E),
(exists (s : Play E), sigma s = true 
/\ hd_error (rev s) = Some (inl(x)))
-> Z.geb (finite_payoff (inl (x))) (0%Z) = true.

Fixpoint subsequence_helper
`(E: EventStructure M) (s : InfinitePlay E) (m : nat) (temp : Play E) :=
match m with
| 0 => 
(match (s 0) with
  | inl(p) => inl(p) :: temp
  | inr(m) => inr(m,true) :: temp
end)
| S m' => 
(match (s m) with
  | inl(p) => subsequence_helper E s m' (inl(p) :: temp)
  | inr(m) => subsequence_helper E s m' (inr(m, true) :: temp)
end)
end.

Definition subsequence
`(E: EventStructure M) (s : InfinitePlay E) (m : nat):=
subsequence_helper E s m nil.

Definition infinite_position_of_strategy
`(E: EventStructure M) (A : AsynchronousArena E) 
(x : InfinitePosition E) (sigma : Strategy E A) :=
exists (s : InfinitePlay E),
valid_infinite_position E x
/\
infinite_play_valid E s 
/\
forall (k : nat), sigma (subsequence E s (4 * k)) = true
/\
forall (m : M) (a : nat) (p : Position E), 
(x m = true <-> (exists (b : nat), s b = inl(p) /\ In m p)).


Definition infinite_nonnegative
`(E: EventStructure M) (A : AsynchronousArena E) 
(sigma : Strategy E A) :=
forall (x : InfinitePosition E),
infinite_position_of_strategy E A x sigma
-> infinite_payoff x = plus_infinity.

Definition multiply_bool (b1 b2 : bool) :=
match b1,b2 with
| true, true => true
| true, false => false
| false, true => false
| false, false => true
end.

Fixpoint alternating_walk `(E: EventStructure M)
(A : AsynchronousArena E) (w : Walk E) := 
valid_walk E w /\
match w with
| inl(pos) :: nil => True
| inl(pos1) :: inr(m1, ep1) :: inl(pos2) :: nil => True
| inl(pos1) :: inr(m1, ep1) :: ((inl(pos2) :: inr(m2, ep2) :: xs) as s) => 
(alternating_walk E A s) /\
(multiply_bool (polarity m1) ep1 = 
negb (multiply_bool (polarity m2) ep2))
| _ => False
end.

Definition is_position `(E: EventStructure M)
(A : AsynchronousArena E) (p : Position E) (sigma : Strategy E A) :=
exists (s : Play E),
sigma s = true /\ nth_error (rev s) 1 = Some (inl(p)).

Definition walk_on_strategy `(E: EventStructure M)
(A : AsynchronousArena E) (w : Walk E) (sigma : Strategy E A) :=
alternating_walk E A w /\
(length w <= 3
\/
(exists (m n : M) (p q : bool),
nth_error w 1 = Some(inr(m, p)) /\
nth_error (rev w) 1 = Some(inr(n, q)) /\
multiply_bool (polarity m) p = false /\
multiply_bool (polarity n) q = true
)
/\
forall (b : Position E) (a : nat), 4 * a < length w /\
nth_error w (4 * a) = Some (inl(b)) -> 
is_position E A b sigma
).

Definition walk_payoff `(E: EventStructure M)
(A : AsynchronousArena E) (sigma : Strategy E A) :=
forall (w : Walk E),
walk_on_strategy E A w sigma ->
Z.geb (finite_payoff (inr (w))) (0%Z) = true.

Definition winning_strategy
`(E: EventStructure M)
(A : AsynchronousArena E) (sigma : Strategy E A) :=
total_strategy E A sigma /\
finite_nonnegative E A sigma /\
infinite_nonnegative E A sigma /\
walk_payoff E A sigma.

Fixpoint action_play `(E : EventStructure M) 
(A : AsynchronousArena E) `(X : Group G) `(Y : Group H)
(B : AsynchronousGame E A X Y)
 (p : Play E) (g : G) (h : H) : Play E :=
match p with
| nil => nil
| inl (s) :: xs => inl (s) :: action_play E A X Y B xs g h
| inr (m,b) :: xs =>
inr (action g m h,b) :: action_play E A X Y B xs g h
end.

Definition uniform_strategy `(E : EventStructure M) 
(A : AsynchronousArena E) `(X : Group G) `(Y : Group H)
(B : AsynchronousGame E A X Y) (sigma : Strategy E A) :=
forall (s : Play E) (h : H),
sigma s = true -> exists (g : G),
sigma (action_play E A X Y B s g h) = true.