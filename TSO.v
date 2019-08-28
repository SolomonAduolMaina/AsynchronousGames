Require Import List.
Require Import ZArith.
Require Import IMP.
Require Import Util.

Definition thread_id := bool.
Definition buffer_size := nat.
Definition local_buffers := thread_id -> list (nat * Z). (* address , value *)
Definition global_store := nat -> (option Z).
Definition size_mapping := nat -> (option nat).
Definition memory_model := buffer_size * size_mapping * local_buffers * global_store.

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

Definition update_sizes (location : nat) (size : nat) (g : size_mapping) : size_mapping :=
(fun n => if Nat.eqb n location then Some size else g n).

Inductive memstep : memory_model -> (thread_id * mem_event) -> memory_model -> Prop :=
  | ST_tau_step : forall mem thread, memstep mem (thread, Tau) mem
  | ST_local_read :
               forall buffer local global thread xs ys value location offset sizes size,
               sizes location = Some size ->
               offset < size ->
               local thread = xs ++ ((location + offset, value) :: nil) ++ ys ->
               contains_buffered_write (location + offset) xs = false ->
               memstep (buffer, sizes, local, global)
                       (thread, Read location offset value)
                       (buffer, sizes, local, global)
  | ST_global_read :
               forall buffer local global thread value location offset sizes size,
               sizes location = Some size ->
               offset < size ->
               contains_buffered_write (location + offset) (local thread) = false ->
               global (location + offset) = Some value ->
               memstep (buffer, sizes, local, global)
                       (thread, Read location offset value)
                       (buffer, sizes, local, global)
  | ST_write : forall buffer local local' global offset value location thread sizes size,
               length (local thread) < buffer ->
               sizes location = Some size ->
               offset < size ->
               local' = queue thread (location + offset, value) local ->
               memstep (buffer, sizes, local, global)
                       (thread, Write location offset value)
                       (buffer, sizes, local', global)
  | ST_allocate_array : forall buffer local global global' init location thread size sizes sizes',
               (forall n, location <= n < location + size -> global n = None) ->
               size > 0 ->
               length init <= size ->
               sizes location = None ->
               sizes' = update_sizes location size sizes ->
               global' = allocate location (location + size - 1) init global ->
               memstep (buffer, sizes, local, global)
                       (thread, Allocate location size init)
                       (buffer, sizes', local, global').

(* A program is a 4-tuple (buf_size, init, s1, s2)
  1. buf_size : nat denoting the size of the store buffers,
  2. init : (list (nat * (list Z))) denoting sizes of variables with respective inital values,
  3. s1 : term denotes the program running on the first thread,
  4. s2 : term denotes the program running on the second thread.
*)
Definition program := nat * (list (nat * (list Z))) * term * term.

Definition TSO_machine := program * memory_model.

Inductive pstep : TSO_machine -> TSO_machine -> Prop :=
  | ST_init_allocate : forall buffer xs n s1 s2 mem mem' size id init,
                      id = length xs ->
                      n = sum (fst_list xs) ->
                      memstep mem (true, Allocate n size init) mem'->
                      pstep ((buffer, xs ++ ((size, init) :: nil), s1, s2), mem)
                            ((buffer, xs, [id:=ref n]s1, [id:=ref n]s2), mem')
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
