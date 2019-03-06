Require Import List.

Inductive empty_type := .

Fact empty_type_gives_anything : forall A, empty_type -> A.
Proof. easy. Qed.

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
