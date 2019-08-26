Require Import Strings.String.
Require Import List.
Require Import ZArith.
Require Import IMP.

Definition memory_model := nat -> (option Z).

Definition allocate (start : nat) (finish : nat) (init : list Z) (g : memory_model) : memory_model :=
(fun n => if andb (Nat.leb start n) (Nat.leb n finish) then Some (nth (n - start) init (0%Z)) else g 0).

Definition update_model (val : nat * Z) (g : memory_model) : memory_model :=
(fun n => if Nat.eqb n (fst val) then Some (snd val) else g n).

Inductive memstep : memory_model -> mem_event -> memory_model -> Prop :=
  | ST_tau_step : forall mem, memstep mem Tau mem
  | ST_read :  forall model value location offset,
               model (location + offset) = Some value ->
               memstep model (Read location offset value) model
  | ST_write : forall model model' offset value location,
               model' = update_model (location + offset, value) model ->
               memstep model (Write location offset value) model'
  | ST_allocate_pointer : forall model model' init location size,
               (forall n, location <= n < location + size -> model n = None) ->
               length init <= size ->
               model' = allocate location (location + size - 1) init model ->
               memstep model (Allocate location size init) model'.

(* A program is a 4-tuple (init, s1, s2, s3)
  1. init : (list (nat * (list Z))) denoting sizes of variables with respective inital values,
  2. s1 : term denotes the program running on the first thread,
  3. s2 : term denotes the program running on the second thread.
  4. s3 : term denotes the program running on the third thread.
*)
Definition program := (list (nat * (list Z))) * term * term * term.

Definition SC_machine := program * memory_model.

Inductive pstep : SC_machine -> SC_machine -> Prop :=
  | ST_init_allocate_pointer : forall xs s1 s2 s3 mem mem' size id init,
                      id = length ((size, init) :: xs) ->
                      memstep mem (Allocate id size init) mem' ->
                      pstep (((size, init) :: xs, s1, s2, s3), mem)
                            ((xs, [id:=ref id size]s1, [id:=ref id size]s2, [id:=ref id size]s3), mem')
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

