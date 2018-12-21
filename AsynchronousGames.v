Require Import List.
Require Import Program.Program.
Require Import Arith.PeanoNat.

Definition Player := bool.

Definition Trace Move := list Move.
(* If a Trace is of the form x :: xs then x is the last move *)

Class Game :=
{
Move : Type; 

eqb_move : Move -> Move -> bool;
(* Needed for checking if a Trace is a sub-Trace
 of another Trace to define exponential *)

eqb_move_is_eq : forall m m',
(eqb_move m m' = true -> m = m')
/\
(eqb_move m m' = false -> not (m = m'));

valid_move : (Trace Move) -> Player -> Move -> Prop;
independent : Move -> Move -> Prop;

first_player : Player;
polarity : Move -> Player;

(* Add payoff info to define  winning strategies. *)


}.

Inductive empty_type := .

Instance ZERO : Game :=
{ Move := empty_type;
independent _ _ := False;
eqb_move _ _ := true; 
valid_move _ _ _ := False;
first_player := true;
polarity m := true
}.
Proof. intros. destruct m. Defined.

Instance dual (G : Game) : Game :=
{ independent := independent; 
Move := Move; 
eqb_move := eqb_move; 
valid_move pos player m := valid_move pos (negb player) m;
first_player :=  negb first_player;
polarity m := negb (polarity m)
}.
Proof. intros. apply eqb_move_is_eq. Defined.

Definition TOP := dual ZERO.

Fixpoint cast_to_left (A B :Type) (l : list (A + B)) : list A := 
match l with
| nil => nil
| inl(x) :: xs => x :: (cast_to_left A B xs)
| inr(x) :: xs => (cast_to_left A B xs)
end.

Fixpoint cast_to_right (A B :Type) (l : list (A + B)) : list B := 
match l with
| nil => nil
| inr(x) :: xs => x :: (cast_to_right A B xs)
| inl(x) :: xs => (cast_to_right A B xs)
end.

Instance positive_lifting (G : Game) : Game :=
{ Move := unit + Move; 
independent m n :=
match m,n with
| inl _ , _ => False
| _, inl _ => False
| inr m, inr n => independent m n
end;
eqb_move m m' :=
match m,m' with
| inl m, inl m' => true
| inr m, inr m' => eqb_move m m'
| _, _ => false
end;
valid_move pos player m :=
match pos, player, m with
| nil, true, inl tt => True
| _, _, inr m => 
valid_move (cast_to_right unit Move pos) player m
| _, _, _ => False
end;
first_player := true;
polarity m := match m with
| inl tt => true
| inr m => polarity m
end
}. Proof. intros. destruct m.
+ destruct m'.
++ destruct u. destruct u0. split.
+++ intros. auto.
+++ intros. inversion H.
++ split.
+++ intros. inversion H.
+++ intros. unfold not. intros. inversion H0.
+ destruct m'.
++ split.
+++ intros. inversion H.
+++ intros. unfold not. intros. inversion H0.
++ split.
+++ intros.
assert (m=m0).
{apply eqb_move_is_eq. auto. }
subst. auto.
+++ intros.
assert (not(m=m0)).
{apply eqb_move_is_eq. auto. }
unfold not. intros. inversion H1. subst. contradiction H0.
auto. Defined.

Definition ONE := positive_lifting TOP.

Definition BOTTOM := dual ONE.

Instance sum_positive (G : Game) (G' : Game) 
(positive1 : (@first_player G) = true)
(positive2 : (@first_player G') = true) : Game :=
{ Move := (@Move G) + (@Move G'); 
independent m n :=
match m, n with
| inl m, inl n => independent m n
| inr m, inr n => independent m n
| _, _ => False
end;
eqb_move m m' :=
match m, m' with
| inl m, inl m' => eqb_move m m'
| inr m, inr m' => eqb_move m m'
| _, _ => false
end;
valid_move pos player m :=
let left := cast_to_left (@Move G) (@Move G') pos in
let right := cast_to_right (@Move G) (@Move G') pos in
match left, right, m with
| nil, nil, inl m => valid_move nil player m
| nil, nil, inr m => valid_move nil player m
| x :: nil, nil, inl m => valid_move (x :: nil) player m
| nil, x :: nil, inr m => valid_move (x :: nil) player m
| _, _, _ => False
end;
first_player := true;
polarity m := match m with
| inl m => polarity m
| inr m => polarity m
end
}. Proof. intros. destruct m.
+ destruct m'.
++ split.
+++ intros.
assert (m = m0).
{ apply eqb_move_is_eq. auto. }
rewrite H0. auto.
+++ intros.
assert (not (m = m0)).
{apply eqb_move_is_eq. auto. }
unfold not. intros. inversion H1. subst. contradiction H0.
auto.
++ split.
+++ intros. inversion H.
+++ intros. unfold not. intros. inversion H0.
+ destruct m'.
++ split.
+++ intros. inversion H.
+++ intros. unfold not. intros. inversion H0.
++ split.
+++ intros.
assert (m=m0).
{apply eqb_move_is_eq. auto. }
subst. auto.
+++ intros.
assert (not (m=m0)).
{apply eqb_move_is_eq. auto. }
unfold not. intros. inversion H1. subst. contradiction H0.
auto.
Defined.

Fact positive_lifting_is_positive (G : Game):
(@first_player (positive_lifting G)) = true.
Proof. simpl. auto. Qed.

Definition sum_left_negative
(G : Game) (G' : Game) 
(positive1 : (@first_player G) = false)
(positive2 : (@first_player G') = true)
:= sum_positive (positive_lifting G) G'
(positive_lifting_is_positive G) positive2.

Definition sum_right_negative
(G : Game) (G' : Game) 
(positive1 : (@first_player G) = true)
(positive2 : (@first_player G') = false)
:= sum_positive G (positive_lifting G')
positive1 (positive_lifting_is_positive G').

Definition sum_negative
(G : Game) (G' : Game) 
(positive1 : (@first_player G) = false)
(positive2 : (@first_player G') = false)
:= sum_positive 
(positive_lifting G) 
(positive_lifting G')
(positive_lifting_is_positive G)
(positive_lifting_is_positive G').

Program Definition sum (G : Game) (G' : Game) :=
match (@first_player G), (@first_player G') with
| true, true => sum_positive G G' _ _
| true, false => sum_right_negative G G' _ _
| false, true => sum_left_negative G G' _ _
| false, false => sum_negative G G' _ _
end.

Instance tensor_positive (G : Game) (G' : Game) 
(positive1 : (@first_player G) = true)
(positive2 : (@first_player G') = true) : Game :=
{ Move := (@Move G) + (@Move G');
independent m n :=
match m, n with
| inl m, inl n => independent m n
| inr m, inr n => independent m n
| _, _ => True
end;
eqb_move m m' :=
match m, m' with
| inl m, inl m' => eqb_move m m'
| inr m, inr m' => eqb_move m m'
| _, _ => false
end;
valid_move pos player m :=
match m with
| inl m => valid_move (cast_to_left (@Move G) (@Move G') pos) player m
| inr m => valid_move (cast_to_right (@Move G) (@Move G') pos) player m
end;
first_player := true;
polarity m := match m with
| inl m => polarity m
| inr m => polarity m
end
}. Proof. intros. destruct m.
+ destruct m'.
++ split.
+++ intros.
assert (m = m0).
{ apply eqb_move_is_eq. auto. }
rewrite H0. auto.
+++ intros.
assert (not (m = m0)).
{apply eqb_move_is_eq. auto. }
unfold not. intros. inversion H1. subst. contradiction H0.
auto.
++ split.
+++ intros. inversion H.
+++ intros. unfold not. intros. inversion H0.
+ destruct m'.
++ split.
+++ intros. inversion H.
+++ intros. unfold not. intros. inversion H0.
++ split.
+++ intros.
assert (m=m0).
{apply eqb_move_is_eq. auto. }
subst. auto.
+++ intros.
assert (not (m=m0)).
{apply eqb_move_is_eq. auto. }
unfold not. intros. inversion H1. subst. contradiction H0.
auto.
Defined.

Definition tensor_left_negative
(G : Game) (G' : Game) 
(positive1 : (@first_player G) = false)
(positive2 : (@first_player G') = true)
:= tensor_positive (positive_lifting G) G'
(positive_lifting_is_positive G) positive2.

Definition tensor_right_negative
(G : Game) (G' : Game) 
(positive1 : (@first_player G) = true)
(positive2 : (@first_player G') = false)
:= tensor_positive G (positive_lifting G')
positive1 (positive_lifting_is_positive G').

Definition tensor_negative
(G : Game) (G' : Game) 
(positive1 : (@first_player G) = false)
(positive2 : (@first_player G') = false)
:= tensor_positive 
(positive_lifting G) 
(positive_lifting G')
(positive_lifting_is_positive G)
(positive_lifting_is_positive G').

Program Definition tensor (G : Game) (G' : Game) :=
match (@first_player G), (@first_player G') with
| true, true => tensor_positive G G' _ _
| true, false => tensor_right_negative G G' _ _
| false, true => tensor_left_negative G G' _ _
| false, false => tensor_negative G G' _ _
end.

Fixpoint nat_in_list n l :=
match l with
| nil => false
| x :: xs => if (Nat.eqb x n) then true else nat_in_list n xs
end.

Fixpoint cast_to_all A (l : list (nat * A))
: (nat -> (list A)) * (list nat) :=
match l with
| nil => ((fun _ => nil), nil)
| (n, move) :: xs => 
let (f, l) := cast_to_all A xs in
if nat_in_list n l then
((fun y => if Nat.eqb y n then move :: (f n) else f y), l) else
((fun y => if Nat.eqb y n then move :: (f n) else f y), n :: l)
end.

Fixpoint proper_initial_segment A l l' (f : A -> A -> bool) : 
(bool * (option A)) :=
match l,l' with
| nil, (x :: _) => (true, Some x)
| _ , nil => (false, None)
| x :: xs, y :: ys => 
if f x y then proper_initial_segment A xs ys f
else (false, None)
end.

Fixpoint check_if_not_valid A 
(candidates : list nat)
(f : nat -> (list A))
(eq : A -> A -> bool)
(initial : list A) 
(move : A) :=
match candidates with
| nil => false
| x :: xs => 
let bigger := rev (f x) in
let (b, opt) := proper_initial_segment A initial bigger eq in
(match b, opt with
| true, Some x => if (negb (eq move x)) then true 
else check_if_not_valid A xs f eq initial move
| _, _ => check_if_not_valid A xs f eq initial move
end)
end.

Instance exponential_positive (G : Game)
(positive : (@first_player G) = true) : Game :=
{ Move := nat * Move;
independent m n :=
let (_, m) := m in
let (_, n) := n in
independent m n;
eqb_move m m' := if Nat.eqb (fst m) (fst m') then 
eqb_move (snd m) (snd m') else false;
valid_move pos player m :=
let (f, l) := cast_to_all Move pos in
if negb player then valid_move (f (fst m)) player (snd m)
else 
(match rev (f (fst m)) with
| nil => valid_move nil player (snd m)
| initial => 
if check_if_not_valid Move l f eqb_move initial (snd m)
then False else valid_move (f (fst m)) player (snd m)
end
);
first_player := true;
polarity m := polarity (snd m)}.
Proof. intros. split.
+ destruct m. destruct m'. simpl. 
destruct (Nat.eqb n n0) eqn:H.
++ intros. apply Nat.eqb_eq in H. subst.
assert (m=m0).
{ apply eqb_move_is_eq. auto. }
subst. auto.
++ intros. inversion H0.
+ destruct m. destruct m'. simpl.
destruct (Nat.eqb n n0) eqn:H.
++ intros. apply Nat.eqb_eq in H. subst.
assert (not (m=m0)).
{ apply eqb_move_is_eq. auto. }
unfold not. intros. inversion H1. subst.
contradiction H. auto.
++ intros. unfold not. intros. inversion H1.
subst. 
assert (forall n, n =? n = true).
{intros. induction n.
+ auto. 
+ simpl. auto. }
assert (n0 =? n0 = true).
{apply H2. }
rewrite H in H3. inversion H3.
Defined.

Definition exponential_negative (G : Game)
(negative : (@first_player G) = false)
:= exponential_positive 
(positive_lifting G) 
(positive_lifting_is_positive G).

Program Definition exponential (G : Game):=
match (@first_player G) with
| true => exponential_positive G _
| false => exponential_negative G _
end.








