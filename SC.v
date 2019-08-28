Require Import Strings.String.
Require Import List.
Require Import ZArith.
Require Import IMP.
Require Import Util.

Definition size_mapping := nat -> (option nat).
Definition global_store := nat -> (option Z).
Definition memory_model := size_mapping * global_store.

Definition allocate (start : nat) (finish : nat) (init : list Z) (g : global_store) : global_store :=
(fun n => if andb (Nat.leb start n) (Nat.leb n finish) then Some (nth (n - start) init (0%Z)) else g 0).

Definition update_global (val : nat * Z) (g : global_store) : global_store :=
(fun n => if Nat.eqb n (fst val) then Some (snd val) else g n).

Definition update_sizes (location : nat) (size : nat) (g : size_mapping) : size_mapping :=
(fun n => if Nat.eqb n location then Some size else g n).

Inductive memstep : memory_model -> mem_event -> memory_model -> Prop :=
  | ST_tau_step : forall mem, memstep mem Tau mem
  | ST_read :  forall global value location offset sizes size,
               sizes location = Some size ->
               offset < size ->
               global (location + offset) = Some value ->
               memstep (sizes, global) (Read location offset value) (sizes, global)
  | ST_write : forall global global' offset value location sizes size,
               sizes location = Some size ->
               offset < size ->
               global' = update_global (location + offset, value) global ->
               memstep (sizes, global) (Write location offset value) (sizes, global')
  | ST_allocate_array : forall global global' init location size sizes sizes',
               (forall n, location <= n < location + size -> global n = None) ->
               size > 0 ->
               length init <= size ->
               sizes location = None ->
               sizes' = update_sizes location size sizes ->
               global' = allocate location (location + size - 1) init global ->
               memstep (sizes, global) (Allocate location size init) (sizes', global').

(* A program is a 4-tuple (init, s1, s2, s3)
  1. init : (list (nat * (list Z))) denoting sizes of variables with respective inital values,
  2. s1 : term denotes the program running on the first thread,
  3. s2 : term denotes the program running on the second thread.
  4. s3 : term denotes the program running on the third thread.
*)
Definition program := (list (nat * (list Z))) * term * term * term.

Definition SC_machine := program * memory_model.

Inductive pstep : SC_machine -> SC_machine -> Prop :=
  | ST_init_allocate_array : forall xs n s1 s2 s3 mem mem' size id init,
                      id = length xs ->
                      n = sum (fst_list xs) ->
                      memstep mem (Allocate n size init) mem' ->
                      pstep ((xs ++ ((size, init) :: nil), s1, s2, s3), mem)
                            ((xs, [id:=ref n]s1, [id:=ref n]s2, [id:=ref n]s3), mem')
  | ST_synchronize1 : forall s1 event s1' mem mem' s2 s3,
                      step s1 event s1' ->
                      memstep mem event mem' ->
                      pstep ((nil, s1, s2, s3), mem)
                            ((nil, s1', s2, s3), mem')
  | ST_synchronize2 : forall s1 event s2' mem mem' s2 s3,
                      step s2 event s2' ->
                      memstep mem event mem' ->
                      pstep ((nil, s1, s2, s3), mem)
                            ((nil, s1, s2', s3), mem')
  | ST_synchronize3 : forall s1 event s3' mem mem' s2 s3,
                      step s3 event s3' ->
                      memstep mem event mem' ->
                      pstep ((nil, s1, s2, s3), mem)
                            ((nil, s1, s2, s3'), mem').
