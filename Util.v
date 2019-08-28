Require Import List.

Fixpoint take {A} (n : nat) (l : list A)  :=
  match l, n with
    | _, 0 => nil
    | nil, _ => nil
    | x :: xs, S n => x :: (take n xs)
  end.

Fixpoint sum (l : list nat) :=
  match l with
    | nil => 0
    | x :: xs => x + (sum xs)
  end.

Fixpoint fst_list {A B} (l : list (A * B)) : list A :=
  match l with
    | nil => nil
    | (a, _) :: xs => a :: (fst_list xs)
  end.