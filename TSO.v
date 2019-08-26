Require Import List.
Require Import ZArith.
Require Import IMP.

Definition thread_id := bool.
Definition buffer_size := nat.
Definition local_buffers := thread_id -> list (nat * Z). (* address , value *)
Definition global_store := nat -> (option Z).
Definition memory_model := buffer_size * local_buffers * global_store.

Definition queue (id : thread_id) (val : nat * Z) (local : local_buffers) : local_buffers :=
(fun b => if Bool.eqb b id then (local id) ++ (val :: nil) else local id).

Definition allocate (start : nat) (finish : nat) (init : list Z) (g : global_store) : global_store :=
(fun n => if andb (Nat.leb start n) (Nat.leb n finish) then Some (nth (n - start) init (0%Z)) else g 0).

Fixpoint contains_buffered_write (address : nat)  (l : list (nat * Z)) :=
  match l with
    | nil => false
    | (a, _) :: xs => orb (Nat.eqb a address) (contains_buffered_write address xs)
  end.

Definition update_global (val : nat * Z) (g : global_store) : global_store :=
(fun n => if Nat.eqb n (fst val) then Some (snd val) else g n).

Inductive memstep : memory_model -> (thread_id * mem_event) -> memory_model -> Prop :=
  | ST_tau_step : forall mem thread, memstep mem (thread, Tau) mem
  | ST_local_read :
               forall buffer local global thread xs ys value location offset,
               local thread = xs ++ ((location + offset, value) :: nil) ++ ys ->
               contains_buffered_write (location + offset) xs = false ->
               memstep (buffer, local, global)
                       (thread, Read location offset value)
                       (buffer, local, global)
  | ST_global_read :
               forall buffer local global thread value location offset,
               contains_buffered_write (location + offset) (local thread) = false ->
               global (location + offset) = Some value ->
               memstep (buffer, local, global)
                       (thread, Read location offset value)
                       (buffer, local, global)
  | ST_write : forall buffer local local' global offset value location thread,
               length (local thread) < buffer ->
               local' = queue thread (location + offset, value) local ->
               memstep (buffer, local, global)
                       (thread, Write location offset value)
                       (buffer, local', global)
  | ST_allocate_pointer : forall buffer local global global' init location thread size,
               (forall n, location <= n < location + size -> global n = None) ->
               length init <= size ->
               global' = allocate location (location + size - 1) init global ->
               memstep (buffer, local, global)
                       (thread, Allocate location size init)
                       (buffer, local, global').

(* A program is a 4-tuple (buf_size, init, s1, s2)
  1. buf_size : nat denoting the size of the store buffers,
  2. init : (list (nat * (list Z))) denoting sizes of variables with respective inital values,
  3. s1 : term denotes the program running on the first thread,
  4. s2 : term denotes the program running on the second thread.
*)
Definition program := nat * (list (nat * (list Z))) * term * term.

Definition TSO_machine := program * memory_model.

Inductive pstep : TSO_machine -> TSO_machine -> Prop :=
  | ST_init_allocate : forall buffer xs s1 s2 mem mem' size id init,
                      id = length ((size, init) :: xs) ->
                      memstep mem (true, Allocate id size init) mem'->
                      pstep ((buffer, (size, init) :: xs, s1, s2), mem)
                            ((buffer, xs, [id:=ref id size]s1, [id:=ref id size]s2), mem')
  | ST_synchronize1 : forall s1 event s1' mem mem' buffer s2,
                      step s1 event s1' ->
                      memstep mem (true, event) mem' ->
                      pstep ((buffer, nil, s1, s2), mem)
                            ((buffer, nil, s1', s2), mem')
  | ST_synchronize2 : forall s1 event s2' mem mem' buffer s2,
                      step s2 event s2' ->
                      memstep mem (false, event) mem' ->
                      pstep ((buffer, nil, s1, s2), mem)
                            ((buffer, nil, s1, s2'), mem')
  | ST_flush : forall local local' thread address value xs global global' program buffer,
               local thread = ((address, value) :: xs) ->
               local' thread = xs ->
               local' (negb thread) = local (negb thread) ->
               global' = update_global (address, value) global ->
               pstep (program, (buffer, local, global))
                     (program, (buffer,local', global')).

