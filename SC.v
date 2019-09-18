Require Import List.
Require Import Lambda.
Require Import Util.

Definition mapping := nat -> (option (nat * nat)). (* base, size*)
Definition global_store := nat -> (option nat).
Definition memory_model := mapping * global_store.

Definition allocate (start : nat) (finish : nat) (init : list nat) (g : global_store) : global_store :=
(fun n => if andb (Nat.leb start n) (Nat.leb n finish) then Some (nth (n - start) init (0%nat)) else g 0).

Definition update_global (val : nat * nat) (g : global_store) : global_store :=
(fun n => if Nat.eqb n (fst val) then Some (snd val) else g n).

Definition update_mapping (location : nat) (base : nat) (size : nat) (g : mapping) : mapping :=
(fun n => if Nat.eqb n location then Some (base, size) else g n).

Inductive memory_step : memory_model -> mem_event -> memory_model -> Prop :=
  | ST_tau_step : forall mem, memory_step mem Tau mem
  | ST_read :  forall global value location offset mapping base size,
               mapping location = Some (base, size) ->
               offset < size ->
               global (base + offset) = Some value ->
               memory_step (mapping, global) (Read location offset value) (mapping, global)
  | ST_write : forall global global' offset value location mapping base size,
               mapping location = Some (base, size) ->
               offset < size ->
               global' = update_global (base + offset, value) global ->
               memory_step (mapping, global) (Write location offset value) (mapping, global')
  | ST_allocate_array : forall global global' init location size mapping base mapping',
               (forall n, base <= n < base + size -> global n = None) ->
               mapping location = None ->
               mapping' = update_mapping location base size mapping ->
               global' = allocate base (base + size - 1) init global ->
               memory_step (mapping, global) (Allocate location size init) (mapping', global')
  | ST_reference : forall global location base size mapping,
               mapping location = Some (base, size) ->
               memory_step (mapping, global) (Reference location base) (mapping, global)
  | ST_cast : forall global location mapping base size,
               mapping location = Some (base, size) ->
               memory_step (mapping, global) (Cast base location) (mapping, global).

(* A program is a 4-tuple (init, s1, s2, s3)
  2. init : (list (nat * (list nat))) denoting array variables with respective inital values,
  2. s1 : term denotes the program running on the first thread,
  3. s2 : term denotes the program running on the second thread.
  4. s3 : term denotes the program running on the third thread.
*)
Definition program := (list (nat * (list nat))) * term * term * term.

Definition SC_machine := program * memory_model.

Inductive pstep : SC_machine -> SC_machine -> Prop :=
  | ST_init_allocate_array : forall xs s1 s2 s3 mem mem' size init,
                      size > 0 ->
                      length init <= size ->
                      memory_step mem (Allocate (length xs) size init) mem' ->
                      pstep ((xs ++ ((size, init) :: nil), s1, s2, s3), mem)
                            ((xs, s1, s2, s3), mem')
  | ST_synchronize1 : forall s1 event s1' mem mem' s2 s3,
                      step s1 event s1' ->
                      memory_step mem event mem' ->
                      pstep ((nil, s1, s2, s3), mem)
                            ((nil, s1', s2, s3), mem')
  | ST_synchronize2 : forall s1 event s2' mem mem' s2 s3,
                      step s2 event s2' ->
                      memory_step mem event mem' ->
                      pstep ((nil, s1, s2, s3), mem)
                            ((nil, s1, s2', s3), mem')
  | ST_synchronize3 : forall s1 event s3' mem mem' s2 s3,
                      step s3 event s3' ->
                      memory_step mem event mem' ->
                      pstep ((nil, s1, s2, s3), mem)
                            ((nil, s1, s2, s3'), mem').

Inductive SC_program_steps : SC_machine -> SC_machine -> Prop :=
  | SC_program_steps_reflexive : forall p, SC_program_steps p p
  | SC_program_steps_transitive : forall p q r, pstep p q -> SC_program_steps q r -> SC_program_steps p r.

Inductive SC_thread_steps : (term * memory_model) -> (term * memory_model) -> Prop :=
  | SC_thread_steps_reflexive : forall t, SC_thread_steps t t
  | SC_thread_steps_transitive : forall e e' e'' m m' m'' event, memory_step m event m' ->
      (step e event e' \/ e = e') -> SC_thread_steps (e', m') (e'', m'') ->
      SC_thread_steps (e, m) (e'', m'').

Fact SC_program_steps_to_SC_thread_steps : forall t t',
(SC_program_steps t t' ->
(SC_thread_steps (snd (fst (fst (fst t))), snd t) (snd (fst (fst (fst t'))), snd t') /\ 
SC_thread_steps (snd (fst (fst t)), snd t) (snd (fst (fst t')), snd t') /\ 
SC_thread_steps (snd (fst t), snd t) (snd (fst t'), snd t'))).
  Proof. intros. induction H. 
      ++ split. apply SC_thread_steps_reflexive. split. apply SC_thread_steps_reflexive. apply SC_thread_steps_reflexive.
      ++ destruct IHSC_program_steps. destruct H2. repeat (destruct p). destruct q. repeat (destruct p). destruct r. repeat (destruct p). simpl in *. inversion H; subst; clear H.
        +++ split. apply SC_thread_steps_transitive with (e':=t4) (event:=(Allocate (length l0) size init)) (m':=m0). auto. right. auto. auto. split. apply SC_thread_steps_transitive with (e':=t3) (event:=(Allocate (length l0) size init)) (m':=m0). auto. right. auto. auto. apply SC_thread_steps_transitive with (e':=t2) (event:=(Allocate (length l0) size init)) (m':=m0). auto. right. auto. auto.
        +++ split. apply SC_thread_steps_transitive with (event:=event) (e':=t4) (m':=m0). auto. left. auto.
auto. split. apply SC_thread_steps_transitive with (e':=t3) (event:=event) (m':=m0). auto. right. auto. auto.  apply SC_thread_steps_transitive with (e':=t2) (event:=event) (m':=m0). auto. right. auto. auto.
        +++ split. apply SC_thread_steps_transitive with (e':=t4) (event:=event) (m':=m0). auto. right. auto. auto. split.  apply SC_thread_steps_transitive with (e':=t3) (event:=event) (m':=m0). auto. left. auto. auto.  apply SC_thread_steps_transitive with (e':=t2) (event:=event) (m':=m0). auto. right. auto. auto.
        +++ split. apply SC_thread_steps_transitive with (e':=t4) (event:=event) (m':=m0). auto. right. auto. auto. split. apply SC_thread_steps_transitive with (e':=t3) (event:=event) (m':=m0). auto. right. auto. auto.  apply SC_thread_steps_transitive with (e':=t2) (event:=event) (m':=m0). auto. left. auto. auto.
Qed.
