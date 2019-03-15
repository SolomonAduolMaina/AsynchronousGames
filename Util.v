Require Import List.
Require Import Lia.
Require Import Arith.Even.

Inductive empty_type := .

Fact empty_type_gives_anything : forall A, empty_type -> A.
Proof. easy. Qed.

Fact odd_length_induction :
forall A (P : (list A) -> Prop),
(forall x, P (x :: nil) /\
(forall x y l, P l -> P (x :: y :: l))) ->
(forall k l, length l = 2 * k + 1 -> P l).
Proof. induction k.
+ intros. assert (length l = 1). {lia. } destruct l.
++ simpl in H1. lia.
++ simpl in H0. assert (length l = 0). {lia. }
apply length_zero_iff_nil in H2. subst. apply H.
+ intros. assert (length l = 2 * k + 3). {lia. } destruct l.
++ simpl in H1. lia.
++ destruct l.
+++ simpl in H1. lia.
+++ apply H.
++++ apply a.
++++ apply IHk. simpl in H0. lia.
Qed.

Fact even_length_induction :
forall A (P : (list A) -> Prop),
(P nil /\
(forall x y l, P l -> P (x :: y :: l))) ->
(forall k l, length l = 2 * k -> P l).
Proof. induction k.
+ intros. assert (length l = 0). {lia. }
apply length_zero_iff_nil in H1. subst. apply H.
+ intros. assert (length l = 2 * k + 2). {lia. }
destruct l.
++ simpl in H1. lia.
++ destruct l.
+++ simpl in H1. lia.
+++ apply H. apply IHk. simpl in H0. lia.
Qed.

Fact even_length_list_induction :
forall A (P : (list A) -> Prop),
(P nil /\
(forall x y l, P l -> P (x :: y :: l))) ->
(forall l, even (length l) -> P l).
Proof. intros. apply even_equiv in H0. 
unfold PeanoNat.Nat.Even in H0.  destruct H0. 
apply even_length_induction with (k := x).
+ auto.
+ auto.
Qed.

Fact odd_length_list_induction :
forall A (P : (list A) -> Prop),
(forall x, P (x :: nil) /\
(forall x y l, P l -> P (x :: y :: l))) ->
(forall l, odd (length l) -> P l).
Proof. intros. apply odd_equiv in H0. 
unfold PeanoNat.Nat.Odd in H0.  destruct H0. 
apply odd_length_induction with (k := x).
+ auto.
+ auto.
Qed.


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
