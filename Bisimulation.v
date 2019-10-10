Require Import Strings.String.
Require Import List.
Require Import Lambda.
Require Import TSO.
Require Import SC.
Require Import Util.
Require Import Translation.


(* We will need more validity conditions on the memories besides finiteness *)
Definition related_memory_always (B : nat) (TSO_memory : TSO.memory_model) (SC_memory : SC.memory_model)  : Prop :=
  let buf_size := fst (fst (fst TSO_memory)) in
  let TSOGS := snd TSO_memory in
  let TSO_mapping := snd (fst (fst TSO_memory)) in
  let SC_mapping := fst SC_memory in
  let SCGS := snd SC_memory in
  (exists n, forall k, k >= n -> TSOGS k = None) /\ (* TSO memory is finite *)
  (exists n, forall k, k >= n -> SCGS k = None) /\ (* SC memory is finite *)
  (forall n m k, TSO_mapping n = Some (m, k) -> SC_mapping n = Some (m, k)) /\
  (forall n m, TSOGS n = Some m -> SCGS n = Some m).

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

Inductive related_program (B : nat) : TSO_machine -> SC_machine -> Prop :=
  | related_after_initial : forall buf_size s1 s2 m m',
    related_memory_always B m m' ->
    related_memory_after_initial B m m' ->
    related_program B ((buf_size, nil, s1, s2), m) ((nil, (translate s1 true B buf_size), (translate s2 false B buf_size), race_thread B), m').

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

Fact context_left_step_simulation : forall B buf_size m m0 m'' m' E e e' event s2 s3 m'0,
  step e event e' ->
  memstep m (true, event) m0 ->
  mem_flush_steps m0 m'' ->
  SC_program_steps
    (nil, translate e true B buf_size, s2, s3, m')
    (nil, translate e' true B buf_size, s2, s3, m'0) ->
SC_program_steps
    (nil, translate (con_subst E e) true B buf_size, s2, s3, m')
    (nil, translate (con_subst E e') true B buf_size, s2, s3, m'0).
Proof. intros. induction E; intros; simpl; try (remember (nil, translate (con_subst E e) true B buf_size, s2, s3, m') as T; remember ((nil : list (nat * list nat)), translate (con_subst E e') true B buf_size, s2, s3, m'0) as T').
  + auto.
  + assert ((nil, app (translate (con_subst E e) true B buf_size) (translate t true B buf_size), s2, s3, m') = (fst (fst (fst (fst T))), app (snd (fst (fst (fst T)))) (translate t true B buf_size), snd (fst (fst T)), snd (fst T), snd T)). subst T. simpl. auto. assert ((nil, app (translate (con_subst E e') true B buf_size) (translate t true B buf_size), s2, s3, m'0) = (fst (fst (fst (fst T'))), app (snd (fst (fst (fst T')))) (translate t true B buf_size), snd (fst (fst T')), snd (fst T'), snd T')). subst T'. simpl. auto. rewrite H3. rewrite H4. apply steps_app_left with (l:=nil) (l':=nil) (e1:=translate (con_subst E e) true B buf_size) (e1':=translate (con_subst E e') true B buf_size) (e3:=s2) (e3':=s2) (e4:=s3) (e4':=s3) (m:=m') (m':=m'0). auto. auto. subst. auto.
  + destruct s. destruct e0. destruct H3. subst x. simpl. assert ((nil, app (lam x0 (flush_star true B buf_size;; translate x1 true B buf_size)) (translate (con_subst E e) true B buf_size), s2, s3, m') = (fst (fst (fst (fst T))), app (lam x0 (flush_star true B buf_size;; translate x1 true B buf_size)) (snd (fst (fst (fst T)))), snd (fst (fst T)), snd (fst T), snd T)). subst T. simpl. auto. assert ((nil, app (lam x0 (flush_star true B buf_size;; translate x1 true B buf_size)) (translate (con_subst E e') true B buf_size), s2, s3, m'0) = (fst (fst (fst (fst T'))), app (lam x0 (flush_star true B buf_size;; translate x1 true B buf_size)) (snd (fst (fst (fst T')))), snd (fst (fst T')), snd (fst T'), snd T')). subst T'. simpl. auto. rewrite H3. rewrite H4. apply steps_app_right with (l:=nil) (l':=nil) (e1:=translate (con_subst E e) true B buf_size) (e1':=translate (con_subst E e') true B buf_size) (e3:=s2) (e3':=s2) (e4:=s3) (e4':=s3) (m:=m') (m':=m'0). auto. auto. subst. auto.
  + remember (nil : (list (nat * list nat)), plus (translate (con_subst E e) true B buf_size) (translate t true B buf_size), s2, s3, m') as U. remember (nil : (list (nat * list nat)), plus (translate (con_subst E e') true B buf_size) (translate t true B buf_size), s2, s3, m'0) as U'. assert ((nil, app (lam "x" (flush_star true B buf_size;; var "x"))
      (plus (translate (con_subst E e) true B buf_size) (translate t true B buf_size)), s2, s3, m') = (fst (fst (fst (fst U))), app (lam "x" (flush_star true B buf_size;; var "x")) (snd (fst (fst (fst U)))), snd (fst (fst U)), snd (fst U), snd U)). subst U. simpl. auto. assert ((nil, app (lam "x" (flush_star true B buf_size;; var "x"))
      (plus (translate (con_subst E e') true B buf_size) (translate t true B buf_size)), s2, s3, m'0) = (fst (fst (fst (fst U'))), app (lam "x" (flush_star true B buf_size;; var "x")) (snd (fst (fst (fst U')))), snd (fst (fst U')), snd (fst U'), snd U')). subst U'. simpl. auto. rewrite H3. rewrite H4. apply steps_app_right with (l:=nil) (l':=nil) (e1:=plus (translate (con_subst E e) true B buf_size) (translate t true B buf_size)) (e1':=plus (translate (con_subst E e') true B buf_size) (translate t true B buf_size)) (e3:=s2) (e3':=s2) (e4:=s3) (e4':=s3) (m:=m') (m':=m'0). auto. auto. assert (U = (fst (fst (fst (fst T))), plus (snd (fst (fst (fst T)))) (translate t true B buf_size), snd (fst (fst T)), snd (fst T), snd T)). subst T. subst U. simpl. auto. assert (U' = (fst (fst (fst (fst T'))), plus (snd (fst (fst (fst T')))) (translate t true B buf_size), snd (fst (fst T')), snd (fst T'), snd T')). subst T'. subst U'. simpl. auto. rewrite H5. rewrite H6. apply steps_plus_left with (l:=nil) (l':=nil) (e1:=translate (con_subst E e) true B buf_size) (e1':=translate (con_subst E e') true B buf_size) (e3:=s2) (e3':=s2) (e4:=s3) (e4':=s3) (m:=m') (m':=m'0). auto. auto. auto.
  + destruct s. destruct e0. subst x. simpl. remember (nil : (list (nat * list nat)), plus (num x0) (translate (con_subst E e) true B buf_size), s2, s3, m') as U. remember (nil : (list (nat * list nat)), plus (num x0) (translate (con_subst E e') true B buf_size), s2, s3, m'0) as U'. assert ((nil, app (lam "x" (flush_star true B buf_size;; var "x"))
      (plus (num x0) (translate (con_subst E e) true B buf_size)), s2, s3, m') = (fst (fst (fst (fst U))), app (lam "x" (flush_star true B buf_size;; var "x")) (snd (fst (fst (fst U)))), snd (fst (fst U)), snd (fst U), snd U)). subst U. simpl. auto. assert ((nil, app (lam "x" (flush_star true B buf_size;; var "x"))
      (plus (num x0) (translate (con_subst E e') true B buf_size)), s2, s3, m'0) = (fst (fst (fst (fst U'))), app (lam "x" (flush_star true B buf_size;; var "x")) (snd (fst (fst (fst U')))), snd (fst (fst U')), snd (fst U'), snd U')). subst U'. simpl. auto. rewrite H3. rewrite H4. apply steps_app_right with (l:=nil) (l':=nil) (e1:=plus (num x0) (translate (con_subst E e) true B buf_size)) (e1':=plus (num x0) (translate (con_subst E e') true B buf_size)) (e3:=s2) (e3':=s2) (e4:=s3) (e4':=s3) (m:=m') (m':=m'0). auto. auto. assert (U = (fst (fst (fst (fst T))), plus (num x0) (snd (fst (fst (fst T)))), snd (fst (fst T)), snd (fst T), snd T)). subst T. subst U. simpl. auto. assert (U' = (fst (fst (fst (fst T'))), plus (num x0) (snd (fst (fst (fst T')))), snd (fst (fst T')), snd (fst T'), snd T')). subst T'. subst U'. simpl. auto. rewrite H5. rewrite H6. apply steps_plus_right with (l:=nil) (l':=nil) (e1:=translate (con_subst E e) true B buf_size) (e1':=translate (con_subst E e') true B buf_size) (e3:=s2) (e3':=s2) (e4:=s3) (e4':=s3) (m:=m') (m':=m'0). auto. auto. auto.
  + remember (nil : (list (nat * list nat)), minus (translate (con_subst E e) true B buf_size) (translate t true B buf_size), s2, s3, m') as U. remember (nil : (list (nat * list nat)), minus (translate (con_subst E e') true B buf_size) (translate t true B buf_size), s2, s3, m'0) as U'. assert ((nil, app (lam "x" (flush_star true B buf_size;; var "x"))
      (minus (translate (con_subst E e) true B buf_size) (translate t true B buf_size)), s2, s3, m') = (fst (fst (fst (fst U))), app (lam "x" (flush_star true B buf_size;; var "x")) (snd (fst (fst (fst U)))), snd (fst (fst U)), snd (fst U), snd U)). subst U. simpl. auto. assert ((nil, app (lam "x" (flush_star true B buf_size;; var "x"))
      (minus (translate (con_subst E e') true B buf_size) (translate t true B buf_size)), s2, s3, m'0) = (fst (fst (fst (fst U'))), app (lam "x" (flush_star true B buf_size;; var "x")) (snd (fst (fst (fst U')))), snd (fst (fst U')), snd (fst U'), snd U')). subst U'. simpl. auto. rewrite H3. rewrite H4. apply steps_app_right with (l:=nil) (l':=nil) (e1:=minus (translate (con_subst E e) true B buf_size) (translate t true B buf_size)) (e1':=minus (translate (con_subst E e') true B buf_size) (translate t true B buf_size)) (e3:=s2) (e3':=s2) (e4:=s3) (e4':=s3) (m:=m') (m':=m'0). auto. auto. assert (U = (fst (fst (fst (fst T))), minus (snd (fst (fst (fst T)))) (translate t true B buf_size), snd (fst (fst T)), snd (fst T), snd T)). subst T. subst U. simpl. auto. assert (U' = (fst (fst (fst (fst T'))), minus (snd (fst (fst (fst T')))) (translate t true B buf_size), snd (fst (fst T')), snd (fst T'), snd T')). subst T'. subst U'. simpl. auto. rewrite H5. rewrite H6. apply steps_minus_left with (l:=nil) (l':=nil) (e1:=translate (con_subst E e) true B buf_size) (e1':=translate (con_subst E e') true B buf_size) (e3:=s2) (e3':=s2) (e4:=s3) (e4':=s3) (m:=m') (m':=m'0). auto. auto. auto.
  + destruct s. destruct e0. subst x. simpl. remember (nil : (list (nat * list nat)), minus (num x0) (translate (con_subst E e) true B buf_size), s2, s3, m') as U. remember (nil : (list (nat * list nat)), minus (num x0) (translate (con_subst E e') true B buf_size), s2, s3, m'0) as U'. assert ((nil, app (lam "x" (flush_star true B buf_size;; var "x"))
      (minus (num x0) (translate (con_subst E e) true B buf_size)), s2, s3, m') = (fst (fst (fst (fst U))), app (lam "x" (flush_star true B buf_size;; var "x")) (snd (fst (fst (fst U)))), snd (fst (fst U)), snd (fst U), snd U)). subst U. simpl. auto. assert ((nil, app (lam "x" (flush_star true B buf_size;; var "x"))
      (minus (num x0) (translate (con_subst E e') true B buf_size)), s2, s3, m'0) = (fst (fst (fst (fst U'))), app (lam "x" (flush_star true B buf_size;; var "x")) (snd (fst (fst (fst U')))), snd (fst (fst U')), snd (fst U'), snd U')). subst U'. simpl. auto. rewrite H3. rewrite H4. apply steps_app_right with (l:=nil) (l':=nil) (e1:=minus (num x0) (translate (con_subst E e) true B buf_size)) (e1':=minus (num x0) (translate (con_subst E e') true B buf_size)) (e3:=s2) (e3':=s2) (e4:=s3) (e4':=s3) (m:=m') (m':=m'0). auto. auto. assert (U = (fst (fst (fst (fst T))), minus (num x0) (snd (fst (fst (fst T)))), snd (fst (fst T)), snd (fst T), snd T)). subst T. subst U. simpl. auto. assert (U' = (fst (fst (fst (fst T'))), minus (num x0) (snd (fst (fst (fst T')))), snd (fst (fst T')), snd (fst T'), snd T')). subst T'. subst U'. simpl. auto. rewrite H5. rewrite H6. apply steps_minus_right with (l:=nil) (l':=nil) (e1:=translate (con_subst E e) true B buf_size) (e1':=translate (con_subst E e') true B buf_size) (e3:=s2) (e3':=s2) (e4:=s3) (e4':=s3) (m:=m') (m':=m'0). auto. auto. auto.
  + remember (nil : (list (nat * list nat)), modulo (translate (con_subst E e) true B buf_size) (translate t true B buf_size), s2, s3, m') as U. remember (nil : (list (nat * list nat)), modulo (translate (con_subst E e') true B buf_size) (translate t true B buf_size), s2, s3, m'0) as U'. assert ((nil, app (lam "x" (flush_star true B buf_size;; var "x"))
      (modulo (translate (con_subst E e) true B buf_size) (translate t true B buf_size)), s2, s3, m') = (fst (fst (fst (fst U))), app (lam "x" (flush_star true B buf_size;; var "x")) (snd (fst (fst (fst U)))), snd (fst (fst U)), snd (fst U), snd U)). subst U. simpl. auto. assert ((nil, app (lam "x" (flush_star true B buf_size;; var "x"))
      (modulo (translate (con_subst E e') true B buf_size) (translate t true B buf_size)), s2, s3, m'0) = (fst (fst (fst (fst U'))), app (lam "x" (flush_star true B buf_size;; var "x")) (snd (fst (fst (fst U')))), snd (fst (fst U')), snd (fst U'), snd U')). subst U'. simpl. auto. rewrite H3. rewrite H4. apply steps_app_right with (l:=nil) (l':=nil) (e1:=modulo (translate (con_subst E e) true B buf_size) (translate t true B buf_size)) (e1':=modulo (translate (con_subst E e') true B buf_size) (translate t true B buf_size)) (e3:=s2) (e3':=s2) (e4:=s3) (e4':=s3) (m:=m') (m':=m'0). auto. auto. assert (U = (fst (fst (fst (fst T))), modulo (snd (fst (fst (fst T)))) (translate t true B buf_size), snd (fst (fst T)), snd (fst T), snd T)). subst T. subst U. simpl. auto. assert (U' = (fst (fst (fst (fst T'))), modulo (snd (fst (fst (fst T')))) (translate t true B buf_size), snd (fst (fst T')), snd (fst T'), snd T')). subst T'. subst U'. simpl. auto. rewrite H5. rewrite H6. apply steps_modulo_left with (l:=nil) (l':=nil) (e1:=translate (con_subst E e) true B buf_size) (e1':=translate (con_subst E e') true B buf_size) (e3:=s2) (e3':=s2) (e4:=s3) (e4':=s3) (m:=m') (m':=m'0). auto. auto. auto.
  + destruct s. destruct e0. subst x. simpl. remember (nil : (list (nat * list nat)), modulo (num x0) (translate (con_subst E e) true B buf_size), s2, s3, m') as U. remember (nil : (list (nat * list nat)), modulo (num x0) (translate (con_subst E e') true B buf_size), s2, s3, m'0) as U'. assert ((nil, app (lam "x" (flush_star true B buf_size;; var "x"))
      (modulo (num x0) (translate (con_subst E e) true B buf_size)), s2, s3, m') = (fst (fst (fst (fst U))), app (lam "x" (flush_star true B buf_size;; var "x")) (snd (fst (fst (fst U)))), snd (fst (fst U)), snd (fst U), snd U)). subst U. simpl. auto. assert ((nil, app (lam "x" (flush_star true B buf_size;; var "x"))
      (modulo (num x0) (translate (con_subst E e') true B buf_size)), s2, s3, m'0) = (fst (fst (fst (fst U'))), app (lam "x" (flush_star true B buf_size;; var "x")) (snd (fst (fst (fst U')))), snd (fst (fst U')), snd (fst U'), snd U')). subst U'. simpl. auto. rewrite H3. rewrite H4. apply steps_app_right with (l:=nil) (l':=nil) (e1:=modulo (num x0) (translate (con_subst E e) true B buf_size)) (e1':=modulo (num x0) (translate (con_subst E e') true B buf_size)) (e3:=s2) (e3':=s2) (e4:=s3) (e4':=s3) (m:=m') (m':=m'0). auto. auto. assert (U = (fst (fst (fst (fst T))), modulo (num x0) (snd (fst (fst (fst T)))), snd (fst (fst T)), snd (fst T), snd T)). subst T. subst U. simpl. auto. assert (U' = (fst (fst (fst (fst T'))), modulo (num x0) (snd (fst (fst (fst T')))), snd (fst (fst T')), snd (fst T'), snd T')). subst T'. subst U'. simpl. auto. rewrite H5. rewrite H6. apply steps_modulo_right with (l:=nil) (l':=nil) (e1:=translate (con_subst E e) true B buf_size) (e1':=translate (con_subst E e') true B buf_size) (e3:=s2) (e3':=s2) (e4:=s3) (e4':=s3) (m:=m') (m':=m'0). auto. auto. auto.
  + remember (nil : (list (nat * list nat)), less_than (translate (con_subst E e) true B buf_size) (translate t true B buf_size), s2, s3, m') as U. remember (nil : (list (nat * list nat)), less_than (translate (con_subst E e') true B buf_size) (translate t true B buf_size), s2, s3, m'0) as U'. assert ((nil, app (lam "x" (flush_star true B buf_size;; var "x"))
      (less_than (translate (con_subst E e) true B buf_size) (translate t true B buf_size)), s2, s3, m') = (fst (fst (fst (fst U))), app (lam "x" (flush_star true B buf_size;; var "x")) (snd (fst (fst (fst U)))), snd (fst (fst U)), snd (fst U), snd U)). subst U. simpl. auto. assert ((nil, app (lam "x" (flush_star true B buf_size;; var "x"))
      (less_than (translate (con_subst E e') true B buf_size) (translate t true B buf_size)), s2, s3, m'0) = (fst (fst (fst (fst U'))), app (lam "x" (flush_star true B buf_size;; var "x")) (snd (fst (fst (fst U')))), snd (fst (fst U')), snd (fst U'), snd U')). subst U'. simpl. auto. rewrite H3. rewrite H4. apply steps_app_right with (l:=nil) (l':=nil) (e1:=less_than (translate (con_subst E e) true B buf_size) (translate t true B buf_size)) (e1':=less_than (translate (con_subst E e') true B buf_size) (translate t true B buf_size)) (e3:=s2) (e3':=s2) (e4:=s3) (e4':=s3) (m:=m') (m':=m'0). auto. auto. assert (U = (fst (fst (fst (fst T))), less_than (snd (fst (fst (fst T)))) (translate t true B buf_size), snd (fst (fst T)), snd (fst T), snd T)). subst T. subst U. simpl. auto. assert (U' = (fst (fst (fst (fst T'))), less_than (snd (fst (fst (fst T')))) (translate t true B buf_size), snd (fst (fst T')), snd (fst T'), snd T')). subst T'. subst U'. simpl. auto. rewrite H5. rewrite H6. apply steps_less_than_left with (l:=nil) (l':=nil) (e1:=translate (con_subst E e) true B buf_size) (e1':=translate (con_subst E e') true B buf_size) (e3:=s2) (e3':=s2) (e4:=s3) (e4':=s3) (m:=m') (m':=m'0). auto. auto. auto.
  + destruct s. destruct e0. subst x. simpl. remember (nil : (list (nat * list nat)), less_than (num x0) (translate (con_subst E e) true B buf_size), s2, s3, m') as U. remember (nil : (list (nat * list nat)), less_than (num x0) (translate (con_subst E e') true B buf_size), s2, s3, m'0) as U'. assert ((nil, app (lam "x" (flush_star true B buf_size;; var "x"))
      (less_than (num x0) (translate (con_subst E e) true B buf_size)), s2, s3, m') = (fst (fst (fst (fst U))), app (lam "x" (flush_star true B buf_size;; var "x")) (snd (fst (fst (fst U)))), snd (fst (fst U)), snd (fst U), snd U)). subst U. simpl. auto. assert ((nil, app (lam "x" (flush_star true B buf_size;; var "x"))
      (less_than (num x0) (translate (con_subst E e') true B buf_size)), s2, s3, m'0) = (fst (fst (fst (fst U'))), app (lam "x" (flush_star true B buf_size;; var "x")) (snd (fst (fst (fst U')))), snd (fst (fst U')), snd (fst U'), snd U')). subst U'. simpl. auto. rewrite H3. rewrite H4. apply steps_app_right with (l:=nil) (l':=nil) (e1:=less_than (num x0) (translate (con_subst E e) true B buf_size)) (e1':=less_than (num x0) (translate (con_subst E e') true B buf_size)) (e3:=s2) (e3':=s2) (e4:=s3) (e4':=s3) (m:=m') (m':=m'0). auto. auto. assert (U = (fst (fst (fst (fst T))), less_than (num x0) (snd (fst (fst (fst T)))), snd (fst (fst T)), snd (fst T), snd T)). subst T. subst U. simpl. auto. assert (U' = (fst (fst (fst (fst T'))), less_than (num x0) (snd (fst (fst (fst T')))), snd (fst (fst T')), snd (fst T'), snd T')). subst T'. subst U'. simpl. auto. rewrite H5. rewrite H6. apply steps_less_than_right with (l:=nil) (l':=nil) (e1:=translate (con_subst E e) true B buf_size) (e1':=translate (con_subst E e') true B buf_size) (e3:=s2) (e3':=s2) (e4:=s3) (e4':=s3) (m:=m') (m':=m'0). auto. auto. auto.
  + remember (nil : (list (nat * list nat)), and (translate (con_subst E e) true B buf_size) (translate t true B buf_size), s2, s3, m') as U. remember (nil : (list (nat * list nat)), and (translate (con_subst E e') true B buf_size) (translate t true B buf_size), s2, s3, m'0) as U'. assert ((nil, app (lam "x" (flush_star true B buf_size;; var "x"))
      (and (translate (con_subst E e) true B buf_size) (translate t true B buf_size)), s2, s3, m') = (fst (fst (fst (fst U))), app (lam "x" (flush_star true B buf_size;; var "x")) (snd (fst (fst (fst U)))), snd (fst (fst U)), snd (fst U), snd U)). subst U. simpl. auto. assert ((nil, app (lam "x" (flush_star true B buf_size;; var "x"))
      (and (translate (con_subst E e') true B buf_size) (translate t true B buf_size)), s2, s3, m'0) = (fst (fst (fst (fst U'))), app (lam "x" (flush_star true B buf_size;; var "x")) (snd (fst (fst (fst U')))), snd (fst (fst U')), snd (fst U'), snd U')). subst U'. simpl. auto. rewrite H3. rewrite H4. apply steps_app_right with (l:=nil) (l':=nil) (e1:=and (translate (con_subst E e) true B buf_size) (translate t true B buf_size)) (e1':=and (translate (con_subst E e') true B buf_size) (translate t true B buf_size)) (e3:=s2) (e3':=s2) (e4:=s3) (e4':=s3) (m:=m') (m':=m'0). auto. auto. assert (U = (fst (fst (fst (fst T))), and (snd (fst (fst (fst T)))) (translate t true B buf_size), snd (fst (fst T)), snd (fst T), snd T)). subst T. subst U. simpl. auto. assert (U' = (fst (fst (fst (fst T'))), and (snd (fst (fst (fst T')))) (translate t true B buf_size), snd (fst (fst T')), snd (fst T'), snd T')). subst T'. subst U'. simpl. auto. rewrite H5. rewrite H6. apply steps_and_left with (l:=nil) (l':=nil) (e1:=translate (con_subst E e) true B buf_size) (e1':=translate (con_subst E e') true B buf_size) (e3:=s2) (e3':=s2) (e4:=s3) (e4':=s3) (m:=m') (m':=m'0). auto. auto. auto.
  +  destruct s. subst x. simpl. remember (nil : (list (nat * list nat)), and tru (translate (con_subst E e) true B buf_size), s2, s3, m') as U. remember (nil : (list (nat * list nat)), and tru (translate (con_subst E e') true B buf_size), s2, s3, m'0) as U'. assert ((nil, app (lam "x" (flush_star true B buf_size;; var "x"))
      (and tru (translate (con_subst E e) true B buf_size)), s2, s3, m') = (fst (fst (fst (fst U))), app (lam "x" (flush_star true B buf_size;; var "x")) (snd (fst (fst (fst U)))), snd (fst (fst U)), snd (fst U), snd U)). subst U. simpl. auto. assert ((nil, app (lam "x" (flush_star true B buf_size;; var "x"))
      (and tru (translate (con_subst E e') true B buf_size)), s2, s3, m'0) = (fst (fst (fst (fst U'))), app (lam "x" (flush_star true B buf_size;; var "x")) (snd (fst (fst (fst U')))), snd (fst (fst U')), snd (fst U'), snd U')). subst U'. simpl. auto. rewrite H3. rewrite H4. apply steps_app_right with (l:=nil) (l':=nil) (e1:=and tru (translate (con_subst E e) true B buf_size)) (e1':=and tru (translate (con_subst E e') true B buf_size)) (e3:=s2) (e3':=s2) (e4:=s3) (e4':=s3) (m:=m') (m':=m'0). auto. auto. assert (U = (fst (fst (fst (fst T))), and tru (snd (fst (fst (fst T)))), snd (fst (fst T)), snd (fst T), snd T)). subst T. subst U. simpl. auto. assert (U' = (fst (fst (fst (fst T'))), and tru (snd (fst (fst (fst T')))), snd (fst (fst T')), snd (fst T'), snd T')). subst T'. subst U'. simpl. auto. rewrite H5. rewrite H6. apply steps_and_right with (l:=nil) (l':=nil) (e1:=translate (con_subst E e) true B buf_size) (e1':=translate (con_subst E e') true B buf_size) (e3:=s2) (e3':=s2) (e4:=s3) (e4':=s3) (m:=m') (m':=m'0). auto. auto. auto.
  + unfold new_read. admit.
  + destruct s. destruct e0. subst x. rewrite translate_read. rewrite translate_read. unfold new_read. admit.
  + unfold new_write. admit.
  + destruct s. destruct e0. subst x. rewrite translate_write. rewrite translate_write. unfold new_write. admit.
  + destruct s. destruct s0. destruct e0. destruct e1. subst x. subst x0. rewrite translate_write. rewrite translate_write. unfold new_write. admit.
  + simpl. remember (nil : (list (nat * list nat)), CASE translate (con_subst E e) true B buf_size
    THEN flush_star true B buf_size;; translate t true B buf_size
    ELSE flush_star true B buf_size;; translate t0 true B buf_size ESAC, s2, s3, m') as U. remember (nil : (list (nat * list nat)), CASE translate (con_subst E e') true B buf_size
    THEN flush_star true B buf_size;; translate t true B buf_size
    ELSE flush_star true B buf_size;; translate t0 true B buf_size ESAC, s2, s3, m'0) as U'.  assert (U = (fst (fst (fst (fst T))), case (snd (fst (fst (fst T)))) (flush_star true B buf_size;; translate t true B buf_size) (flush_star true B buf_size;; translate t0 true B buf_size), snd (fst (fst T)), snd (fst T), snd T)). subst T. subst U. simpl. auto. assert (U' = (fst (fst (fst (fst T'))), case (snd (fst (fst (fst T')))) (flush_star true B buf_size;; translate t true B buf_size) (flush_star true B buf_size;; translate t0 true B buf_size), snd (fst (fst T')), snd (fst T'), snd T')). subst T'. subst U'. simpl. auto. rewrite H3. rewrite H4. apply steps_case_left with (l:=nil) (l':=nil) (e1:=translate (con_subst E e) true B buf_size) (e1':=translate (con_subst E e') true B buf_size) (e3:=s2) (e3':=s2) (e4:=s3) (e4':=s3) (m:=m') (m':=m'0). auto. auto. auto.
  + simpl. remember (nil : (list (nat * list nat)), not (translate (con_subst E e) true B buf_size), s2, s3, m') as U. remember (nil : (list (nat * list nat)), not (translate (con_subst E e') true B buf_size), s2, s3, m'0) as U'. assert ((nil, app (lam "x" (flush_star true B buf_size;; var "x"))
      (not (translate (con_subst E e) true B buf_size)), s2, s3, m') = (fst (fst (fst (fst U))), app (lam "x" (flush_star true B buf_size;; var "x")) (snd (fst (fst (fst U)))), snd (fst (fst U)), snd (fst U), snd U)). subst U. simpl. auto. assert ((nil, app (lam "x" (flush_star true B buf_size;; var "x"))
      (not (translate (con_subst E e') true B buf_size)), s2, s3, m'0) = (fst (fst (fst (fst U'))), app (lam "x" (flush_star true B buf_size;; var "x")) (snd (fst (fst (fst U')))), snd (fst (fst U')), snd (fst U'), snd U')). subst U'. simpl. auto. rewrite H3. rewrite H4. apply steps_app_right with (l:=nil) (l':=nil) (e1:=not (translate (con_subst E e) true B buf_size)) (e1':=not (translate (con_subst E e') true B buf_size)) (e3:=s2) (e3':=s2) (e4:=s3) (e4':=s3) (m:=m') (m':=m'0). auto. auto. assert (U = (fst (fst (fst (fst T))), not (snd (fst (fst (fst T)))), snd (fst (fst T)), snd (fst T), snd T)). subst T. subst U. simpl. auto. assert (U' = (fst (fst (fst (fst T'))), not (snd (fst (fst (fst T')))), snd (fst (fst T')), snd (fst T'), snd T')). subst T'. subst U'. simpl. auto. rewrite H5. rewrite H6. apply steps_not_left with (l:=nil) (l':=nil) (e1:=translate (con_subst E e) true B buf_size) (e1':=translate (con_subst E e') true B buf_size) (e3:=s2) (e3':=s2) (e4:=s3) (e4':=s3) (m:=m') (m':=m'0). auto. auto. auto.
  + simpl. remember (nil : (list (nat * list nat)), reference (translate (con_subst E e) true B buf_size), s2, s3, m') as U. remember (nil : (list (nat * list nat)), reference (translate (con_subst E e') true B buf_size), s2, s3, m'0) as U'. assert ((nil, app (lam "x" (flush_star true B buf_size;; var "x"))
      (reference (translate (con_subst E e) true B buf_size)), s2, s3, m') = (fst (fst (fst (fst U))), app (lam "x" (flush_star true B buf_size;; var "x")) (snd (fst (fst (fst U)))), snd (fst (fst U)), snd (fst U), snd U)). subst U. simpl. auto. assert ((nil, app (lam "x" (flush_star true B buf_size;; var "x"))
      (reference (translate (con_subst E e') true B buf_size)), s2, s3, m'0) = (fst (fst (fst (fst U'))), app (lam "x" (flush_star true B buf_size;; var "x")) (snd (fst (fst (fst U')))), snd (fst (fst U')), snd (fst U'), snd U')). subst U'. simpl. auto. rewrite H3. rewrite H4. apply steps_app_right with (l:=nil) (l':=nil) (e1:=reference (translate (con_subst E e) true B buf_size)) (e1':=reference (translate (con_subst E e') true B buf_size)) (e3:=s2) (e3':=s2) (e4:=s3) (e4':=s3) (m:=m') (m':=m'0). auto. auto. assert (U = (fst (fst (fst (fst T))), reference (snd (fst (fst (fst T)))), snd (fst (fst T)), snd (fst T), snd T)). subst T. subst U. simpl. auto. assert (U' = (fst (fst (fst (fst T'))), reference (snd (fst (fst (fst T')))), snd (fst (fst T')), snd (fst T'), snd T')). subst T'. subst U'. simpl. auto. rewrite H5. rewrite H6. apply steps_reference_left with (l:=nil) (l':=nil) (e1:=translate (con_subst E e) true B buf_size) (e1':=translate (con_subst E e') true B buf_size) (e3:=s2) (e3':=s2) (e4:=s3) (e4':=s3) (m:=m') (m':=m'0). auto. auto. auto.
  + simpl. remember (nil : (list (nat * list nat)), cast (translate (con_subst E e) true B buf_size), s2, s3, m') as U. remember (nil : (list (nat * list nat)), cast (translate (con_subst E e') true B buf_size), s2, s3, m'0) as U'. assert ((nil, app (lam "x" (flush_star true B buf_size;; var "x"))
      (cast (translate (con_subst E e) true B buf_size)), s2, s3, m') = (fst (fst (fst (fst U))), app (lam "x" (flush_star true B buf_size;; var "x")) (snd (fst (fst (fst U)))), snd (fst (fst U)), snd (fst U), snd U)). subst U. simpl. auto. assert ((nil, app (lam "x" (flush_star true B buf_size;; var "x"))
      (cast (translate (con_subst E e') true B buf_size)), s2, s3, m'0) = (fst (fst (fst (fst U'))), app (lam "x" (flush_star true B buf_size;; var "x")) (snd (fst (fst (fst U')))), snd (fst (fst U')), snd (fst U'), snd U')). subst U'. simpl. auto. rewrite H3. rewrite H4. apply steps_app_right with (l:=nil) (l':=nil) (e1:=cast (translate (con_subst E e) true B buf_size)) (e1':=cast (translate (con_subst E e') true B buf_size)) (e3:=s2) (e3':=s2) (e4:=s3) (e4':=s3) (m:=m') (m':=m'0). auto. auto. assert (U = (fst (fst (fst (fst T))), cast (snd (fst (fst (fst T)))), snd (fst (fst T)), snd (fst T), snd T)). subst T. subst U. simpl. auto. assert (U' = (fst (fst (fst (fst T'))), cast (snd (fst (fst (fst T')))), snd (fst (fst T')), snd (fst T'), snd T')). subst T'. subst U'. simpl. auto. rewrite H5. rewrite H6. apply steps_cast_left with (l:=nil) (l':=nil) (e1:=translate (con_subst E e) true B buf_size) (e1':=translate (con_subst E e') true B buf_size) (e3:=s2) (e3':=s2) (e4:=s3) (e4':=s3) (m:=m') (m':=m'0). auto. auto. auto.
  + admit.
  + destruct s. admit.
  + admit.
  + admit.
Admitted.



Fact context_forward_simulation : forall B buf_size m m0 m'' m' e e' E event s2,
    related_memory_always B m m' ->
    related_memory_after_initial B m m' ->
    mem_flush_steps m0 m'' ->
    step e event e' ->
    memstep m (true, event) m0 ->
    (exists q' : SC_machine,
             related_program B (buf_size, nil, e', s2, m'') q' /\
             SC_program_steps (nil, translate e true B buf_size, translate s2 false B buf_size, race_thread B, m')
               q') ->
    (exists q' : SC_machine,
    related_program B (buf_size, nil, con_subst E e', s2, m'') q' /\
    SC_program_steps
      (nil, translate (con_subst E e) true B buf_size, translate s2 false B buf_size, race_thread B, m') q').
Proof. intros. destruct E; simpl in *; destruct H4; destruct H4.
  + refine (ex_intro _ x _). auto.
  + inversion H4; subst. refine (ex_intro _ (nil, app (translate (con_subst E e') true B buf_size) (translate t true B buf_size), translate s2 false B buf_size, race_thread B, m'0) _). split.
    ++ apply related_after_initial. auto. auto.
    ++ remember ((nil : list (nat * list nat)), translate (con_subst E e) true B buf_size, translate s2 false B buf_size, race_thread B, m') as T. remember ((nil : list (nat * list nat)), translate (con_subst E e') true B buf_size, translate s2 false B buf_size, race_thread B, m'0) as T'.
assert ((fst (fst (fst (fst T))), app (snd (fst (fst (fst T)))) (translate t true B buf_size), snd (fst (fst T)), snd (fst T), snd T) = (nil, app (translate (con_subst E e) true B buf_size) (translate t true B buf_size), translate s2 false B buf_size, race_thread B, m')). subst T. simpl. auto.
assert ((fst (fst (fst (fst T'))), app (snd (fst (fst (fst T')))) (translate t true B buf_size), snd (fst (fst T')), snd (fst T'), snd T') = (nil, app (translate (con_subst E e') true B buf_size) (translate t true B buf_size), translate s2 false B buf_size, race_thread B, m'0)). subst T'. simpl. auto. rewrite <- H6. rewrite <- H7. apply steps_app_left with (l:=nil) (l':=nil) (e1:=translate (con_subst E e) true B buf_size) (e1':=translate (con_subst E e') true B buf_size) (e3:=translate s2 false B buf_size) (e3':=translate s2 false B buf_size) (e4:=race_thread B) (e4':=race_thread B) (m:=m') (m':=m'0). auto. auto. subst. simpl in *. clear H6. clear H7. admit.
  + destruct s. destruct e0. destruct H6. subst. inversion H4. subst. refine (ex_intro _ (nil, translate (app (lam x1 x2) (con_subst E e')) true B buf_size, translate s2 false B buf_size, race_thread B, m'0) _). split.
    ++ apply related_after_initial. auto. auto.
    ++ simpl. admit.
  + inversion H4. subst. refine (ex_intro _ (nil, translate (plus (con_subst E e') t) true B buf_size, translate s2 false B buf_size, race_thread B, m'0) _). split.
    ++ apply related_after_initial. auto. auto.
    ++ simpl. admit.
  + destruct s. destruct e0. subst. inversion H4. subst. refine (ex_intro _ (nil, translate (plus (num x1) (con_subst E e')) true B buf_size, translate s2 false B buf_size, race_thread B, m'0) _). split.
    ++ apply related_after_initial. auto. auto.
    ++ simpl. admit.
  + inversion H4; subst. refine (ex_intro _ (nil, translate (minus (con_subst E e') t) true B buf_size, translate s2 false B buf_size, race_thread B, m'0) _). split.
    ++ apply related_after_initial. auto. auto.
    ++ simpl. admit.
  + destruct s. destruct e0. subst. inversion H4. subst. refine (ex_intro _ (nil, translate (minus (num x1) (con_subst E e')) true B buf_size, translate s2 false B buf_size, race_thread B, m'0) _). split.
    ++ apply related_after_initial. auto. auto.
    ++ simpl. admit.
  + inversion H4; subst. refine (ex_intro _ (nil, translate (modulo (con_subst E e') t) true B buf_size, translate s2 false B buf_size, race_thread B, m'0) _). split.
    ++ apply related_after_initial. auto. auto.
    ++ simpl. admit.
  + destruct s. destruct e0. subst. inversion H4. subst. refine (ex_intro _ (nil, translate (modulo (num x1) (con_subst E e')) true B buf_size, translate s2 false B buf_size, race_thread B, m'0) _). split.
    ++ apply related_after_initial. auto. auto.
    ++ simpl. admit.
  + inversion H4; subst. refine (ex_intro _ (nil, translate (less_than (con_subst E e') t) true B buf_size, translate s2 false B buf_size, race_thread B, m'0) _). split.
    ++ apply related_after_initial. auto. auto.
    ++ simpl. admit.
  + destruct s. inversion H4. subst. refine (ex_intro _ (nil, translate (less_than x0 (con_subst E e')) true B buf_size, translate s2 false B buf_size, race_thread B, m'0) _). split.
    ++ apply related_after_initial. auto. auto.
    ++ simpl. admit.
  + inversion H4; subst. refine (ex_intro _ (nil, translate (and (con_subst E e') t) true B buf_size, translate s2 false B buf_size, race_thread B, m'0) _). split.
    ++ apply related_after_initial. auto. auto.
    ++ simpl. admit.
  + destruct s. subst. inversion H4. subst. refine (ex_intro _ (nil, translate (and tru (con_subst E e')) true B buf_size, translate s2 false B buf_size, race_thread B, m'0) _). split.
    ++ apply related_after_initial. auto. auto.
    ++ simpl. admit.
  + inversion H4; subst. refine (ex_intro _ (nil, translate (read (con_subst E e') t) true B buf_size, translate s2 false B buf_size, race_thread B, m'0) _). split.
    ++ apply related_after_initial. auto. auto.
    ++ simpl. admit.
  + destruct s. destruct e0. subst. inversion H4. subst. refine (ex_intro _ (nil, translate (read (array x1) (con_subst E e')) true B buf_size, translate s2 false B buf_size, race_thread B, m'0) _). split.
    ++ apply related_after_initial. auto. auto.
    ++ simpl. admit.
  + inversion H4; subst. refine (ex_intro _ (nil, translate (write (con_subst E e') t t0) true B buf_size, translate s2 false B buf_size, race_thread B, m'0) _). split.
    ++ apply related_after_initial. auto. auto.
    ++ simpl. admit.
  + destruct s. destruct e0. subst. inversion H4. subst. refine (ex_intro _ (nil, translate (write (array x1) (con_subst E e') t) true B buf_size, translate s2 false B buf_size, race_thread B, m'0) _). split.
    ++ apply related_after_initial. auto. auto.
    ++ simpl. admit.
  + destruct s. destruct e0. destruct s0. destruct e0. subst. inversion H4. subst. refine (ex_intro _ (nil, translate (write (array x1) (num x3) (con_subst E e')) true B buf_size, translate s2 false B buf_size, race_thread B, m'0) _). split.
    ++ apply related_after_initial. auto. auto.
    ++ simpl. admit.
  + inversion H4; subst. refine (ex_intro _ (nil, translate (case (con_subst E e') t t0) true B buf_size, translate s2 false B buf_size, race_thread B, m'0) _). split.
    ++ apply related_after_initial. auto. auto.
    ++ simpl. admit.
  + inversion H4. subst. refine (ex_intro _ (nil, translate (not (con_subst E e')) true B buf_size, translate s2 false B buf_size, race_thread B, m'0) _). split.
    ++ apply related_after_initial. auto. auto.
    ++ simpl. admit.
  + inversion H4; subst. refine (ex_intro _ (nil, translate (reference (con_subst E e')) true B buf_size, translate s2 false B buf_size, race_thread B, m'0) _). split.
    ++ apply related_after_initial. auto. auto.
    ++ simpl. admit.
  + inversion H4. subst. refine (ex_intro _ (nil, translate (cast (con_subst E e')) true B buf_size, translate s2 false B buf_size, race_thread B, m'0) _). split.
    ++ apply related_after_initial. auto. auto.
    ++ simpl. admit.
  + inversion H4; subst. refine (ex_intro _ (nil, translate (paire (con_subst E e') t) true B buf_size, translate s2 false B buf_size, race_thread B, m'0) _). split.
    ++ apply related_after_initial. auto. auto.
    ++ simpl. admit.
  + destruct s. inversion H4. subst. refine (ex_intro _ (nil, translate (paire x0 (con_subst E e')) true B buf_size, translate s2 false B buf_size, race_thread B, m'0) _). split.
    ++ apply related_after_initial. auto. auto.
    ++ simpl. admit.
  + inversion H4; subst. refine (ex_intro _ (nil, translate (first (con_subst E e')) true B buf_size, translate s2 false B buf_size, race_thread B, m'0) _). split.
    ++ apply related_after_initial. auto. auto.
    ++ simpl. admit.
  + inversion H4; subst. refine (ex_intro _ (nil, translate (second (con_subst E e')) true B buf_size, translate s2 false B buf_size, race_thread B, m'0) _). split.
    ++ apply related_after_initial. auto. auto.
    ++ simpl. admit.
Admitted.

Theorem forward_bisimulation : forall p p' q B,
  term_flush_steps p p' -> related_program B p q -> (exists q', related_program B p' q' /\ SC_program_steps q q').
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
    ++ rewrite translate_first. rewrite translate_paire. admit.
    ++ rewrite translate_second. rewrite translate_paire. admit.
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
    ++ rewrite translate_first. rewrite translate_paire. admit.
    ++ rewrite translate_second. rewrite translate_paire. admit.
Admitted.
