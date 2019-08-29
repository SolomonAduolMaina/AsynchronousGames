Require Import List.
Require Import ZArith.
Require Import IMP.
Require Import Util.

Definition mapping := nat -> (option (nat * nat)). (* base, size*)
Definition global_store := nat -> (option Z).
Definition memory_model := mapping * global_store.

Definition allocate (start : nat) (finish : nat) (init : list Z) (g : global_store) : global_store :=
(fun n => if andb (Nat.leb start n) (Nat.leb n finish) then Some (nth (n - start) init (0%Z)) else g 0).

Definition update_global (val : nat * Z) (g : global_store) : global_store :=
(fun n => if Nat.eqb n (fst val) then Some (snd val) else g n).

Definition update_mapping (location : nat) (base : nat) (size : nat) (g : mapping) : mapping :=
(fun n => if Nat.eqb n location then Some (base, size) else g n).

Inductive memstep : memory_model -> mem_event -> memory_model -> Prop :=
  | ST_tau_step : forall mem, memstep mem Tau mem
  | ST_read :  forall global value location offset mapping base size,
               mapping location = Some (base, size) ->
               offset < size ->
               global (base + offset) = Some value ->
               memstep (mapping, global) (Read location offset value) (mapping, global)
  | ST_write : forall global global' offset value location mapping base size,
               mapping location = Some (base, size) ->
               offset < size ->
               global' = update_global (base + offset, value) global ->
               memstep (mapping, global) (Write location offset value) (mapping, global')
  | ST_allocate_array : forall global global' init location size mapping base mapping',
               (forall n, base <= n < base + size -> global n = None) ->
               size > 0 ->
               length init <= size ->
               mapping location = None ->
               mapping' = update_mapping location base size mapping ->
               global' = allocate base (base + size - 1) init global ->
               memstep (mapping, global) (Allocate location size init) (mapping', global')
  | ST_reference : forall global location base size mapping,
               mapping location = Some (base, size) ->
               memstep (mapping, global) (Reference location base) (mapping, global)
  | ST_cast : forall global location mapping base size,
               mapping location = Some (base, size) ->
               memstep (mapping, global) (Cast base location) (mapping, global).

(* A program is a 4-tuple (init, s1, s2, s3)
  2. init : (list (nat * (list Z))) denoting array variables with respective inital values,
  2. s1 : term denotes the program running on the first thread,
  3. s2 : term denotes the program running on the second thread.
  4. s3 : term denotes the program running on the third thread.
*)
Definition program := (list (nat * (list Z))) * term * term * term.

Definition SC_machine := program * memory_model.

Inductive pstep : SC_machine -> SC_machine -> Prop :=
  | ST_init_allocate_array : forall xs s1 s2 s3 mem mem' size init,
                      memstep mem (Allocate (length xs) size init) mem' ->
                      pstep ((xs ++ ((size, init) :: nil), s1, s2, s3), mem)
                            ((xs, s1, s2, s3), mem')
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
