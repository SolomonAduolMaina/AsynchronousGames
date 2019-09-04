Require Import List.
Require Import IMP.
Require Import TSO.
Require Import SC.
Require Import Util.
Require Import Translation.

Definition bisimilar_memory (TSO_memory : TSO.memory_model) (SC_memory : SC.memory_model) (B : nat) (f : nat -> nat) : Prop :=
  let buf_size := fst (fst (fst TSO_memory)) in
  let local := snd (fst TSO_memory) in
  let TSOGS := snd TSO_memory in
  let TSO_mapping := snd (fst (fst TSO_memory)) in
  let SC_mapping := fst SC_memory in
  let SCGS := snd SC_memory in
  (exists n, forall k, k >= n -> TSOGS k = None) /\ (* TSO memory is finite *)
  (exists n, forall k, k >= n -> SCGS k = None) /\ (* SC memory is finite *)
  (forall n m k, TSO_mapping n = Some (m, k) -> SC_mapping n = Some (f m, k)) /\
  (forall n m, TSOGS n = Some m -> SCGS (f n) = Some m) /\
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
  ).

Definition bisimilar (p : TSO_machine) (q : SC_machine) (f : nat -> nat) : Prop :=
  let TSO_program := fst p in
  let TSO_memory := snd p in
  let SC_program := fst q in
  let SC_memory := snd q in
  let init := snd (fst (fst TSO_program)) in
  let B := length init in
  translate_program TSO_program = SC_program /\
  bisimilar_memory TSO_memory SC_memory B f.

Theorem forward_bisimulation : forall p p' q f,
  TSO.pstep p p' -> bisimilar p q f -> (exists q', bisimilar p' q' f /\ psteps q q').
Proof. intros. inversion H.
  + subst. destruct q. destruct p. repeat (destruct p). destruct m. destruct mem. destruct mem'. repeat (destruct p0). repeat (destruct p).
    inversion H3. subst. destruct H0. simpl in *. inversion H0. subst.
    remember
    (translate_vars xs buffer,
     seq (translate s1 true (length (fst_list xs)) buffer) (flush_all true (length (fst_list xs)) buffer),
     seq (translate s2 false (length (fst_list xs)) buffer) (flush_all false (length (fst_list xs)) buffer),
     while tru (SPECIAL (length (fst_list xs)) [num 0]::= ZERO)) as answer_p.
    unfold bisimilar_memory in H4. simpl in *. destruct H4. destruct H5. destruct H5.
    remember (update_mapping x base size m, allocate x (x + size - 1) init g) as answer_m.
    refine (ex_intro _ (answer_p, answer_m) _). subst. split.
    ++ unfold bisimilar. simpl. split.
      +++ intros. reflexivity.
      +++ admit.
    ++ admit.
  + subst. generalize dependent q. induction H1 ; subst.
    ++ intros. assert (TSO.pstep (buffer, nil, e, s2, mem) (buffer, nil, e', s2, mem')).
       {apply TSO.ST_synchronize1 with (event:=event). auto. auto. }
       assert (forall q : SC_machine,
         bisimilar (buffer, nil, e, s2, mem) q f ->
         exists q' : SC_machine,
           bisimilar (buffer, nil, e', s2, mem') q' f /\
           psteps q q'). {apply IHstep. auto. auto. } destruct q.
       assert (bisimilar ((buffer, nil, e, s2), mem) (translate_program (buffer, nil, e, s2), m) f).
       {split.
          + reflexivity.
          + simpl. destruct H0. simpl in H5. auto. }
       apply H4 in H5. destruct H5. destruct H5. destruct H5. destruct x. simpl fst in *. 
       simpl snd in *. subst.
       refine (ex_intro _ (translate_program (buffer, nil, subst E e', s2), m0) _). split.
      +++ split.
        ++++ reflexivity.
        ++++ simpl. simpl in H7. auto.
      +++ unfold bisimilar in H0. destruct H0. simpl in *. subst.
          assert (steps (seq (translate e true 0 buffer) (flush_all true 0 buffer)) (seq (translate e' true 0 buffer) (flush_all true 0 buffer))).
          {apply psteps_inj_1 with (p:=(translate_vars nil buffer, seq (translate e true 0 buffer) (flush_all true 0 buffer),
           seq (translate s2 false 0 buffer) (flush_all false 0 buffer), while tru (SPECIAL 0 [num 0]::= ZERO), m))
           (q:=(translate_vars nil buffer, seq (translate e' true 0 buffer) (flush_all true 0 buffer),
           seq (translate s2 false 0 buffer) (flush_all false 0 buffer), while tru (SPECIAL 0 [num 0]::= ZERO), m0)). apply H6. }
          assert (steps (subst E e) (subst E e')).
          {apply psteps_transports. apply steps_transitive with (q:=e') (event:=event). auto. apply steps_reflexive. }


