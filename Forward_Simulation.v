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

Definition race_thread (base : nat) : term :=
  WHILE (not (!(DONE_COUNTER base) == ZERO)) DO (SPECIAL base) ::= ZERO DONE.

Inductive related_program (B : nat) : TSO_machine -> SC_machine -> Prop :=
  | related_after_initial : forall buf_size f g m m',
    related_memory_always B m m' ->
    related_memory_after_initial B m m' ->
    g (inl true) = translate (f true) true B buf_size ->
    g (inl false) = translate (f false) false B buf_size ->
    g (inr tt) = race_thread B ->
    related_program B ((buf_size, nil, f), m) ((nil, g), m').

Inductive term_step : TSO_machine -> mem_event -> TSO_machine -> Prop :=
  | synchronize : forall threads thread event e mem mem' buffer threads',
                      step (threads thread) event e ->
                      memstep mem (thread, event) mem' ->
                      (forall t, threads' t = if Bool.eqb thread t then e else threads t) ->
                      term_step ((buffer, nil, threads), mem) event ((buffer, nil, threads'), mem').

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

Fact context_forward_simulation : forall B buf_size f m m0 m'' g m' thread threads' E e e' event,
  related_memory_always B m m' ->
  related_memory_after_initial B m m' ->
  mem_flush_steps m0 m'' ->
  memstep m (thread, event) m0 ->
  g (inl true) = translate (f true) true B buf_size ->
  g (inl false) = translate (f false) false B buf_size ->
  g (inr tt) = race_thread B ->
  step e event e' ->
  con_subst E e = f thread ->
  (forall (f : bool -> term),
           e = f thread ->
           forall g : bool + unit -> term,
           g (inl true) = translate (f true) true B buf_size ->
           g (inl false) = translate (f false) false B buf_size ->
           g (inr tt) = race_thread B ->
           forall threads' : bool -> term,
           (forall t : bool,
            threads' t = (if Bool.eqb thread t then e' else f t)) ->
           exists q' : SC_machine,
             related_program B (buf_size, nil, threads', m'') q' /\
             SC_program_steps (nil, g, m') q') ->
  ((forall t : bool, threads' t = (if Bool.eqb thread t then con_subst E e' else f t)) ->
  (exists q' : SC_machine,
    related_program B (buf_size, nil, threads', m'') q' /\
    SC_program_steps (nil, g, m') q')).
Proof. intros.
remember (fun t => if Bool.eqb thread t then e else f t) as ind_f. 
remember (fun thread' => 
  match thread' with
    | inl true => translate (ind_f true) true B buf_size
    | inl false => translate (ind_f false) false B buf_size
    | inr tt => race_thread B
  end) as ind_g.
remember (fun t => if Bool.eqb thread t then e' else ind_f t) as ind_threads'.
assert (exists q' : SC_machine,
         related_program B (buf_size, nil, ind_threads', m'') q' /\
         SC_program_steps (nil, ind_g, m') q'). apply H8 with (f:=ind_f). subst ind_f. simpl. rewrite Bool.eqb_reflx. auto. subst ind_g. auto. subst ind_g. auto. subst ind_g. auto. subst ind_threads'. auto. destruct H10. destruct H10. inversion H10. subst.
 (remember (fun thread' => 
  match thread' with
    | inl true => translate (threads' true) true B buf_size
    | inl false => translate (threads' false) false B buf_size
    | inr tt => race_thread B
  end) as solution; remember (fun thread' : bool + unit =>
          match thread' with
          | inl true =>
              translate (if Bool.eqb thread true then con_subst E e else f true) true B
                buf_size
          | inl false =>
              translate (if Bool.eqb thread false then con_subst E e else f false) false B
                buf_size
          | inr tt => race_thread B
          end) as ind_sol_threads;
remember (fun thread' : bool + unit =>
          match thread' with
          | inl true =>
              translate (if Bool.eqb thread true then con_subst E e' else f true) true B
                buf_size
          | inl false =>
              translate (if Bool.eqb thread false then con_subst E e' else f false) false B
                buf_size
          | inr tt => race_thread B
          end) as ind_sol_threads'). refine (ex_intro _ (nil, solution, m'0) _). split.
  + apply related_after_initial. auto. auto. subst. auto. subst. auto. subst. auto.
  + destruct thread.
    ++ rewrite <- H7 in H3. subst. rewrite H9. simpl. rewrite H9. simpl in *.
remember (fun t => if thread_equals t (inl true) then translate e true B buf_size else g t) as u. remember (fun t => if thread_equals t (inl true) then translate e' true B buf_size else g t) as v.
 apply translation_of_context_steps with (e:=e) (e':=e') (b:=true) (B:=B) (buf_size:=buf_size) (E:=E) (thread:=inl true) (f:=g) (u:=u) (v:=v). intros. destruct t. simpl in *. rewrite Hequ. destruct b. simpl. auto. simpl. auto. rewrite Hequ. auto. intros. rewrite Heqv. auto. intros. destruct t. destruct b. simpl. rewrite H3. auto. simpl. auto. simpl. auto. intros. destruct t. destruct b. simpl. auto. simpl. rewrite H4. auto. destruct u0. simpl. rewrite H5. auto. apply program_steps_same with (u:=fun thread' : bool + unit =>
          match thread' with
          | inl true => translate e true B buf_size
          | inl false => translate (f false) false B buf_size
          | inr tt => race_thread B
          end) (v:=g0). auto. rewrite Hequ. intros. destruct t. destruct b. simpl. auto. simpl. rewrite H4. auto. destruct u0. simpl. rewrite H5. auto. rewrite Heqv. intros. destruct t. destruct b. simpl. auto. simpl. rewrite H19. rewrite H4. auto. simpl. destruct u0. rewrite H20. rewrite H5. auto.
    ++ rewrite <- H7 in H4. subst. rewrite H9. simpl. rewrite H9. simpl in *.
remember (fun t => if thread_equals t (inl false) then translate e false B buf_size else g t) as u. remember (fun t => if thread_equals t (inl false) then translate e' false B buf_size else g t) as v.
 apply translation_of_context_steps with (e:=e) (e':=e') (b:=false) (B:=B) (buf_size:=buf_size) (E:=E) (thread:=inl false) (f:=g) (u:=u) (v:=v). intros. destruct t. simpl in *. rewrite Hequ. destruct b. simpl. auto. simpl. auto. rewrite Hequ. auto. intros. rewrite Heqv. auto. intros. destruct t. destruct b. simpl. rewrite H3. auto. simpl. auto. simpl. auto. intros. destruct t. destruct b. simpl. auto. simpl. auto. destruct u0. simpl. rewrite H5. auto.  apply program_steps_same with (u:=fun thread' : bool + unit =>
          match thread' with
          | inl false => translate e false B buf_size
          | inl true => translate (f true) true B buf_size
          | inr tt => race_thread B
          end) (v:=g0). auto. rewrite Hequ. intros. destruct t. destruct b. simpl. auto. simpl. auto. destruct u0. simpl. rewrite H5. auto. rewrite Heqv. intros. destruct t. destruct b. simpl. rewrite H17. rewrite H3. auto. simpl. rewrite H19. auto. destruct u0. simpl. rewrite H20. rewrite H5. auto.
Qed.                                                                     

Theorem forward_simulation : forall p p' q B,
  term_flush_steps p p' -> related_program B p q -> (exists q', related_program B p' q' /\ SC_program_steps q q').
Proof. intros. inversion H0. clear H0. subst. inversion H. subst. clear H. destruct H0. destruct H. destruct s'. simpl in *. inversion H; subst; clear H. generalize dependent threads'. generalize dependent g. remember (f thread) as e'. generalize dependent f. induction H11; intros.
  + apply context_forward_simulation with (f:=f) (m:=m) (m0:=m0) (thread:=thread) (E:=E) (e:=e) (e':=e') (event:=event). auto. auto. auto. auto. auto. auto. auto. auto. auto.
apply IHstep. auto. auto.
  + inversion H13. subst. destruct thread.
    ++ rewrite <- Heqe' in *. simpl in H3. 

(*assert (step (app (lam (flush_star true B buf_size;; translate e true B buf_size))  (translate v true B buf_size)) Tau (subst x (translate v true B buf_size) (flush_star true B buf_size;; translate e true B buf_size))). apply step_app. apply translation_of_value_is_value. auto. assert (SC_program_steps (nil, g, m') (nil,
(fun t => match t with
        | inl true => subst x (translate v true B buf_size) (flush_star true B buf_size;; translate e true B buf_size)
        | inl false => translate (f false) false B buf_size
        | inr tt => race_thread B
      end), m')). apply SC_program_steps_transitive with (q:=(nil,
    fun t : bool + unit =>
    match t with
    | inl true =>
        subst x (translate v true B buf_size)
          (flush_star true B buf_size;; translate e true B buf_size)
    | inl false => translate (f false) false B buf_size
    | inr tt => race_thread B
    end, m')). apply ST_synchronize with (thread:=inl true) (event:=Tau) (e:=subst x (translate v true B buf_size) (flush_star true B buf_size;; translate e true B buf_size)). rewrite H3. auto. apply ST_tau_step. intros. destruct t. destruct b. simpl (thread_equals (inl true) (inl true)). auto. simpl (thread_equals (inl false) (inl true)). rewrite H4. auto. destruct u. simpl (thread_equals (inr tt) (inl true)). rewrite H5. auto. apply SC_program_steps_reflexive. auto. rewrite seq_flush_subst in H7. rewrite <- trans_subst in H7.
unfold seq in H7.*)




 Admitted.
