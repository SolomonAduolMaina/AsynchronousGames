Require Import Strings.String.
Require Import List.
Require Import Lambda.
Require Import TSO.
Require Import SC.
Require Import Util.
Require Import Translation.


(* We will need more validity conditions on the memories besides finiteness *)
Definition related_memory_always (B : nat) (f : nat -> nat) (TSO_memory : TSO.memory_model) (SC_memory : SC.memory_model)  : Prop :=
  let buf_size := fst (fst (fst TSO_memory)) in
  let TSOGS := snd TSO_memory in
  let TSO_mapping := snd (fst (fst TSO_memory)) in
  let SC_mapping := fst SC_memory in
  let SCGS := snd SC_memory in
  (exists n, forall k, k >= n -> TSOGS k = None) /\ (* TSO memory is finite *)
  (exists n, forall k, k >= n -> SCGS k = None) /\ (* SC memory is finite *)
  (forall n m k, TSO_mapping n = Some (m, k) -> SC_mapping n = Some (f m, k)) /\
  (forall n m, TSOGS n = Some m -> SCGS (f n) = Some m).

Definition related_memory_after_initial (B : nat) (TSO_memory : TSO.memory_model) (SC_memory : SC.memory_model)  : Prop :=
  let buf_size := fst (fst (fst TSO_memory)) in
  let local := snd (fst TSO_memory) in
  let TSOGS := snd TSO_memory in
  let SC_mapping := fst SC_memory in
  let SCGS := snd SC_memory in
  (forall base offset value n, (nth_error (local true) n = Some (base, offset, value)) ->
      exists BASES OFFSETS VALUES FRONT REAR SIZE front rear size,
        (SC_mapping (B + LOOP_1_CONST) <> None /\
         SC_mapping (B + FOUND_1_CONST) <> None /\
         SC_mapping (B + RESULT_1_CONST) <> None /\
         SC_mapping (B + BUFFER_1A_CONST) = Some (BASES, buf_size) /\
         SC_mapping (B + BUFFER_1B_CONST) = Some (OFFSETS, buf_size) /\
         SC_mapping (B + BUFFER_1C_CONST) = Some (VALUES, buf_size) /\
         SC_mapping (B + FRONT_1_CONST) = Some (FRONT, buf_size) /\ SCGS FRONT = Some front /\
         SC_mapping (B + REAR_1_CONST) = Some (REAR, buf_size) /\ SCGS REAR = Some rear /\
         SC_mapping (B + SIZE_1_CONST) = Some (SIZE, buf_size) /\ SCGS SIZE = Some size /\
         Nat.modulo (front + size - rear - 1) buf_size = 0 /\
         SCGS SIZE = Some (length (local true)) /\
         SCGS (BASES + (Nat.modulo (front + n) buf_size)) = Some base /\
         SCGS (OFFSETS + (Nat.modulo (front + n) buf_size)) = Some offset /\
         SCGS (VALUES + (Nat.modulo (front + n) buf_size)) = Some value
        )
  ) /\
  (forall base offset value n, (nth_error (local true) n = Some (base, offset, value)) ->
      exists BASES OFFSETS VALUES FRONT REAR SIZE front rear size,
        (SC_mapping (B + LOOP_2_CONST) <> None /\
         SC_mapping (B + FOUND_2_CONST) <> None /\
         SC_mapping (B + RESULT_2_CONST) <> None /\
         SC_mapping (B + BUFFER_2A_CONST) = Some (BASES, buf_size) /\
         SC_mapping (B + BUFFER_2B_CONST) = Some (OFFSETS, buf_size) /\
         SC_mapping (B + BUFFER_2C_CONST) = Some (VALUES, buf_size) /\
         SC_mapping (B + FRONT_2_CONST) = Some (FRONT, buf_size) /\ SCGS FRONT = Some front /\
         SC_mapping (B + REAR_2_CONST) = Some (REAR, buf_size) /\ SCGS REAR = Some rear /\
         SC_mapping (B + SIZE_2_CONST) = Some (SIZE, buf_size) /\ SCGS SIZE = Some size /\
         Nat.modulo (front + size - rear - 1) buf_size = 0 /\
         SCGS SIZE = Some (length (local true)) /\
         SCGS (BASES + (Nat.modulo (front + n) buf_size)) = Some base /\
         SCGS (OFFSETS + (Nat.modulo (front + n) buf_size)) = Some offset /\
         SCGS (VALUES + (Nat.modulo (front + n) buf_size)) = Some value
        )
  ) /\
  (SC_mapping (B + SPECIAL_CONST) <> None /\ SC_mapping (B + DONE_COUNTER_CONST) <> None).

(*Inductive related_program (B : nat) (f : nat -> nat) : TSO_machine -> SC_machine -> Prop :=
  | related_initial : forall buf_size init s1 s2 t1 t2 m m',
    init <> nil ->
    related_memory_always B f m m' ->
    related_term B buf_size (s1, true) (t1, true) ->
    related_term B buf_size (s2, false) (t2, false) ->
    related_program B f ((buf_size, init, s1, s2), m)
    ((translate_arrays init buf_size,
     app (lam "x" (seq (write (DONE_COUNTER B) ZERO (minus (!(DONE_COUNTER B)) ONE)) (var "x"))) t1, 
     app (lam "x" (seq (write (DONE_COUNTER B) ZERO (minus (!(DONE_COUNTER B)) ONE)) (var "x"))) t2, 
     race_thread B), m')
  | related_after_initial : forall buf_size s1 s2 t1 t2 m m',
    related_memory_always B f m m' ->
    related_memory_after_initial B m m' ->
    related_term B buf_size (s1, true) (t1, true) ->
    related_term B buf_size (s2, false) (t2, false) ->
    related_program B f ((buf_size, nil, s1, s2), m)
    ((nil,
     app (lam "x" (seq (write (DONE_COUNTER B) ZERO (minus (!(DONE_COUNTER B)) ONE)) (var "x"))) t1, 
     app (lam "x" (seq (write (DONE_COUNTER B) ZERO (minus (!(DONE_COUNTER B)) ONE)) (var "x"))) t2, 
     race_thread B), m').*)

Inductive related_program (B : nat) (f : nat -> nat) : TSO_machine -> SC_machine -> Prop :=
  | related_after_initial : forall buf_size s1 s2 m m',
    related_memory_always B f m m' ->
    related_memory_after_initial B m m' ->
    related_program B f ((buf_size, nil, s1, s2), m) ((nil, (translate s1 true B buf_size), (translate s2 false B buf_size), race_thread B), m').

Inductive term_step : TSO_machine -> mem_event -> TSO_machine -> Prop :=
  | step_one : forall s1 s1' mem event mem' s2 buffer,
               step s1 event s1' ->
               memstep mem (true, event) mem' ->
               term_step ((buffer, nil, s1, s2), mem) event ((buffer, nil, s1', s2), mem')
  | step_2 : forall s2 s2' mem event mem' s1 buffer,
               step s2 event s2' ->
               memstep mem (false, event) mem' ->
               term_step ((buffer, nil, s1, s2), mem) event ((buffer, nil, s1, s2'), mem').

Inductive mem_flush_steps : TSO.memory_model -> TSO.memory_model -> Prop :=
  | flush_step_reflexive : forall m, mem_flush_steps m m
  | flush_step : forall local local' thread address value xs global global' mapping offset buffer m m' m'',
               m = (buffer, mapping, local, global) ->
               m' = (buffer, mapping, local', global') ->
               mem_flush_steps m' m'' ->
               local thread = ((address, offset, value) :: xs) ->
               local' thread = xs ->
               local' (negb thread) = local (negb thread) ->
               global' = update_global (address + offset, value) global ->
               mem_flush_steps m m''.

Inductive term_flush_steps : TSO_machine -> TSO_machine -> Prop :=
  | step_then_flush_star : forall s s' m'',
                           (exists event, term_step s event s' /\ mem_flush_steps (snd s') m'') ->
                           term_flush_steps s (fst s', m'').

Fact context_forward_simulation : forall f B buf_size m m0 m'' m' e e' E event s2,
    related_memory_always B f m m' ->
    related_memory_after_initial B m m' ->
    mem_flush_steps m0 m'' ->
    step e event e' ->
    memstep m (true, event) m0 ->
    (exists q' : SC_machine,
             related_program B f (buf_size, nil, e', s2, m'') q' /\
             SC_program_steps (nil, translate e true B buf_size, translate s2 false B buf_size, race_thread B, m')
               q') ->
    (exists q' : SC_machine,
    related_program B f (buf_size, nil, con_subst E e', s2, m'') q' /\
    SC_program_steps
      (nil, translate (con_subst E e) true B buf_size, translate s2 false B buf_size, race_thread B, m') q').
Proof. intros. destruct E; simpl in *.
  + auto.
  + Admitted.

Theorem forward_bisimulation : forall p p' q f B,
  term_flush_steps p p' -> related_program B f p q -> (exists q', related_program B f p' q' /\ SC_program_steps q q').
Proof. intros. inversion H0. clear H0. subst. inversion H. subst. clear H. destruct H0. destruct H. destruct s'. simpl in *. inversion H; subst.
  + induction H8; intros.
    ++ admit.
    ++ rewrite translate_app. rewrite translate_lam. admit.
    ++ rewrite translate_reference. rewrite translate_array. admit.
    ++ rewrite translate_cast. rewrite translate_num. admit.
    ++ rewrite translate_read. rewrite translate_num. rewrite translate_array. admit.
    ++ rewrite translate_write. rewrite translate_num. rewrite translate_num. rewrite translate_array. admit.
    ++ rewrite translate_plus. rewrite translate_num. rewrite translate_num. admit.
    ++ rewrite translate_minus. rewrite translate_num. rewrite translate_num. admit.
    ++ rewrite translate_modulo. rewrite translate_num. rewrite translate_num. admit.
    ++ rewrite translate_less_than. rewrite translate_num. rewrite translate_num. admit.
    ++ rewrite translate_less_than. rewrite translate_num. rewrite translate_num. admit.
    ++ rewrite translate_and. rewrite translate_tru. admit.
    ++ rewrite translate_and. rewrite translate_tru. rewrite translate_fls. admit.
    ++ rewrite translate_and. rewrite translate_fls. admit.
    ++ rewrite translate_not. rewrite translate_tru. admit.
    ++ rewrite translate_not. rewrite translate_fls. admit.
    ++ rewrite translate_case. rewrite translate_tru. admit.
    ++ rewrite translate_case. rewrite translate_fls. admit.
  + induction H8; intros.
    ++ admit.
    ++ rewrite translate_app. rewrite translate_lam. admit.
    ++ rewrite translate_reference. rewrite translate_array. admit.
    ++ rewrite translate_cast. rewrite translate_num. admit.
    ++ rewrite translate_read. rewrite translate_num. rewrite translate_array. admit.
    ++ rewrite translate_write. rewrite translate_num. rewrite translate_num. rewrite translate_array. admit.
    ++ rewrite translate_plus. rewrite translate_num. rewrite translate_num. admit.
    ++ rewrite translate_minus. rewrite translate_num. rewrite translate_num. admit.
    ++ rewrite translate_modulo. rewrite translate_num. rewrite translate_num. admit.
    ++ rewrite translate_less_than. rewrite translate_num. rewrite translate_num. admit.
    ++ rewrite translate_less_than. rewrite translate_num. rewrite translate_num. admit.
    ++ rewrite translate_and. rewrite translate_tru. admit.
    ++ rewrite translate_and. rewrite translate_tru. rewrite translate_fls. admit.
    ++ rewrite translate_and. rewrite translate_fls. admit.
    ++ rewrite translate_not. rewrite translate_tru. admit.
    ++ rewrite translate_not. rewrite translate_fls. admit.
    ++ rewrite translate_case. rewrite translate_tru. admit.
    ++ rewrite translate_case. rewrite translate_fls. admit.
Admitted.








