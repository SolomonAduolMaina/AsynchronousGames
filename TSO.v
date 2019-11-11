Require Import List.
Require Import Lambda.
Require Import Util.

Definition thread_id := bool.
Definition buffer_size := nat.
Definition local_buffers := thread_id -> list (nat * nat * nat). (* thread_id -> (address, offset, value) *)
Definition global_store := nat -> (option nat). (* location -> value *)
Definition location_state := nat -> (option (nat * nat * bool)). (* location -> (base, size, locked) *)
Definition memory_model := buffer_size * location_state * local_buffers * global_store.

Definition queue (id : thread_id) (val : nat * nat * nat) (local : local_buffers) : local_buffers :=
(fun b => if Bool.eqb b id then (local id) ++ (val :: nil) else local id).

Definition allocate (start : nat) (finish : nat) (init : list nat) (g : global_store) : global_store :=
(fun n => if andb (Nat.leb start n) (Nat.leb n finish) then Some (nth (n - start) init (0%nat)) else g 0).

Fixpoint contains_buffered_write (loc : nat * nat)  (l : list (nat * nat * nat)) :=
  match l with
    | nil => false
    | ((a, b), _) :: xs => orb (andb (Nat.eqb a (fst loc)) (Nat.eqb b (snd loc))) (contains_buffered_write loc xs)
  end.

Definition update_global (val : nat * nat) (g : global_store) : global_store :=
(fun n => if Nat.eqb n (fst val) then Some (snd val) else g n).

Definition update_location_state (location : nat) (base : nat) (size : nat) (locked : bool) (g : location_state) : location_state :=
(fun n => if Nat.eqb n location then Some (base, size, locked) else g n).

Inductive memstep : memory_model -> (thread_id * mem_event) -> memory_model -> Prop :=
  | ST_tau_step : forall mem thread, memstep mem (thread, Tau) mem
  | ST_local_read :
               forall buffer local global thread xs ys value location offset location_state base size,
               location_state location = Some (base, size, false) ->
               offset < size ->
               local thread = xs ++ ((base, offset, value) :: nil) ++ ys ->
               contains_buffered_write (base, offset) xs = false ->
               memstep (buffer, location_state, local, global)
                       (thread, Read location offset value)
                       (buffer, location_state, local, global)
  | ST_global_read :
               forall buffer local global thread value location offset location_state base size,
               location_state location = Some (base, size, false) ->
               offset < size ->
               contains_buffered_write (base, offset) (local thread) = false ->
               global (base + offset) = Some value ->
               memstep (buffer, location_state, local, global)
                       (thread, Read location offset value)
                       (buffer, location_state, local, global)
  | ST_write : forall buffer local local' global offset value location thread location_state size base,
               length (local thread) < buffer ->
               location_state location = Some (base, size, false) ->
               offset < size ->
               local' = queue thread (base, offset, value) local ->
               memstep (buffer, location_state, local, global)
                       (thread, Write location offset value)
                       (buffer, location_state, local', global)
  | ST_allocate_array : forall buffer local global global' init location thread base size location_state location_state',
               (forall n, base <= n < base + size -> global n = None) ->
               location_state location = None ->
               location_state' = update_location_state location base size false location_state ->
               global' = allocate base (base + size - 1) init global ->
               memstep (buffer, location_state, local, global)
                       (thread, Allocate location size init)
                       (buffer, location_state', local, global')
  | ST_reference : forall buffer local global location thread base size location_state b,
               location_state location = Some (base, size, b) ->
               memstep (buffer, location_state, local, global)
                       (thread, Reference location base)
                       (buffer, location_state, local, global)
  | ST_cast : forall buffer local global location thread location_state base size b,
               location_state location = Some (base, size, b) ->
               memstep (buffer, location_state, local, global)
                       (thread, Cast base location)
                       (buffer, location_state, local, global)
  | ST_lock : forall buffer local global global' location thread base size location_state location_state',
               location_state location = Some (base, size, false) ->
               location_state' = update_location_state location base size true location_state ->
               memstep (buffer, location_state, local, global)
                       (thread, Lock location)
                       (buffer, location_state', local, global')
  | ST_unlock : forall buffer local global global' location thread base size location_state location_state',
               location_state location = Some (base, size, true) ->
               location_state' = update_location_state location base size false location_state ->
               memstep (buffer, location_state, local, global)
                       (thread, Lock location)
                       (buffer, location_state', local, global').


(* A program is a 3-tuple (buf_size, init, threads)
  1. buf_size : nat denoting the size of the store buffers,
  2. init : (list (nat * (list nat))) denoting array variables with respective size and inital values,
  3. threads : bool -> term denotes the two running threads
*)
Definition program := nat * (list (nat * (list nat))) * (bool -> term).

Definition TSO_machine := program * memory_model.

Inductive pstep : TSO_machine -> TSO_machine -> Prop :=
  | ST_init_allocate : forall buffer xs threads mem mem' size init,
                      size > 0 ->
                      length init <= size ->
                      memstep mem (true, Allocate (length xs) size init) mem'->
                      pstep ((buffer, xs ++ ((size, init) :: nil), threads), mem)
                            ((buffer, xs, threads), mem')
  | ST_synchronize : forall threads thread event e mem mem' buffer threads',
                      step (threads thread) event e ->
                      memstep mem (true, event) mem' ->
                      (forall t, threads' t = if Bool.eqb thread t then e else threads t) ->
                      pstep ((buffer, nil, threads), mem) ((buffer, nil, threads'), mem')
  | ST_flush : forall local local' thread address value xs global global' location_state program offset buffer,
               local thread = ((address, offset, value) :: xs) ->
               snd (fst program) = nil ->
               local' thread = xs ->
               local' (negb thread) = local (negb thread) ->
               global' = update_global (address + offset, value) global ->
               pstep (program, (buffer, location_state, local, global))
                     (program, (buffer, location_state, local', global')).
