Require Import List.
Require Import IMP.
Require Import Util.

Definition thread_id := bool.
Definition buffer_size := nat.
Definition local_buffers := thread_id -> list (nat * nat * nat). (* address, offset, value *)
Definition global_store := nat -> (option nat).
Definition mapping := nat -> (option (nat * nat)). (* base, size *)
Definition memory_model := buffer_size * mapping * local_buffers * global_store.

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

Definition update_mapping (location : nat) (base : nat) (size : nat)  (g : mapping) : mapping :=
(fun n => if Nat.eqb n location then Some (base, size) else g n).

Inductive memstep : memory_model -> (thread_id * mem_event) -> memory_model -> Prop :=
  | ST_tau_step : forall mem thread, memstep mem (thread, Tau) mem
  | ST_local_read :
               forall buffer local global thread xs ys value location offset mapping base size,
               mapping location = Some (base, size) ->
               offset < size ->
               local thread = xs ++ ((base, offset, value) :: nil) ++ ys ->
               contains_buffered_write (base, offset) xs = false ->
               memstep (buffer, mapping, local, global)
                       (thread, Read location offset value)
                       (buffer, mapping, local, global)
  | ST_global_read :
               forall buffer local global thread value location offset mapping base size,
               mapping location = Some (base, size) ->
               offset < size ->
               contains_buffered_write (base, offset) (local thread) = false ->
               global (base + offset) = Some value ->
               memstep (buffer, mapping, local, global)
                       (thread, Read location offset value)
                       (buffer, mapping, local, global)
  | ST_write : forall buffer local local' global offset value location thread mapping size base,
               length (local thread) < buffer ->
               mapping location = Some (base, size) ->
               offset < size ->
               local' = queue thread (base, offset, value) local ->
               memstep (buffer, mapping, local, global)
                       (thread, Write location offset value)
                       (buffer, mapping, local', global)
  | ST_allocate_array : forall buffer local global global' init location thread base size mapping mapping',
               (forall n, base <= n < base + size -> global n = None) ->
               mapping location = None ->
               mapping' = update_mapping location base size mapping ->
               global' = allocate base (base + size - 1) init global ->
               memstep (buffer, mapping, local, global)
                       (thread, Allocate location size init)
                       (buffer, mapping', local, global')
  | ST_reference : forall buffer local global location thread base size mapping,
               mapping location = Some (base, size) ->
               memstep (buffer, mapping, local, global)
                       (thread, Reference location base)
                       (buffer, mapping, local, global)
  | ST_cast : forall buffer local global location thread mapping base size,
               mapping location = Some (base, size) ->
               memstep (buffer, mapping, local, global)
                       (thread, Cast base location)
                       (buffer, mapping, local, global).

(* A program is a 4-tuple (buf_size, init, s1, s2)
  1. buf_size : nat denoting the size of the store buffers,
  2. init : (list (nat * (list nat))) denoting array variables with respective size and inital values,
  3. s1 : term denotes the program running on the first thread,
  4. s2 : term denotes the program running on the second thread.
*)
Definition program := nat * (list (nat * (list nat))) * term * term.

Definition TSO_machine := program * memory_model.

Inductive pstep : TSO_machine -> TSO_machine -> Prop :=
  | ST_init_allocate : forall buffer xs s1 s2 mem mem' size init,
                      size > 0 ->
                      length init <= size ->
                      memstep mem (true, Allocate (length xs) size init) mem'->
                      pstep ((buffer, xs ++ ((size, init) :: nil), s1, s2), mem)
                            ((buffer, xs, s1, s2), mem')
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
  | ST_flush : forall local local' thread address value xs global global' mapping program offset buffer,
               local thread = ((address, offset, value) :: xs) ->
               snd (fst (fst program)) = nil ->
               local' thread = xs ->
               local' (negb thread) = local (negb thread) ->
               global' = update_global (address + offset, value) global ->
               pstep (program, (buffer, mapping, local, global))
                     (program, (buffer, mapping, local', global')).
