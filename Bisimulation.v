Require Import Strings.String.
Require Import List.
Require Import Lambda.
Require Import TSO.
Require Import SC.
Require Import Util.
Require Import Translation.


Inductive related_term (base : nat) (buf_size : nat) : (term * bool) -> (term * bool) -> Prop :=
  | related_flush : forall e thread, related_term base buf_size (e, thread) (seq (flush_star thread base buf_size) (translate e thread base buf_size), thread).


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

Inductive related_program (B : nat) (f : nat -> nat) : TSO_machine -> SC_machine -> Prop :=
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
     race_thread B), m').



(*Fact contexts_respect_relation : forall E B s2 buffer f e event e' mem mem' m t0 l t1,
  related B buffer (s2, false) (t0, false) ->
  related_memory mem m B f ->
  step e event e' ->
  TSO.memstep mem (true, event) mem' ->
  related B buffer (con_subst E e, true) (t1, true) ->
  (forall re : term,
  related B buffer (e, true) (re, true) ->
  exists q' : SC_machine,
  related_program (buffer, nil, e', s2, mem') q' f B /\
  SC_program_steps (l, re, t0, while tru (SPECIAL B [num 0]::= ZERO), m) q') ->
  exists q' : SC_machine,
  (related_program (buffer, nil, con_subst E e', s2, mem') q' f B /\
  SC_program_steps (l, t1, t0, while tru (SPECIAL B [num 0]::= ZERO), m) q').
Proof. intros. generalize dependent t1. induction E; intros; simpl in *.
  + apply H4. auto.
  + assert (exists q' : SC_machine,
          related_program
            (buffer, nil, con_subst E e', s2, mem') q'
            f B /\
          SC_program_steps
            (l, translate (con_subst E e) true B buffer, t0,
            while tru (SPECIAL B [num 0]::= ZERO), m)
            q'). apply IHE. apply related_translate. destruct H5. destruct H5. destruct x. destruct p. destruct p. destruct p. destruct H5. simpl in *. unfold related_terms in H7. destruct H7. destruct H7. simpl in *. destruct H9. refine (ex_intro _ (l0, translate (app (con_subst E e') t) true B buffer, t3, WHILE tru DO SPECIAL B [num 0]::= ZERO DONE, m0) _). rewrite translate_app. inversion H3; inversion H7; subst.
    ++ admit.
    ++ admit.
    ++ admit.
    ++ admit. 
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
Admitted.


Theorem forward_bisimulation : forall p p' q f B,
  TSO.pstep p p' -> related_program p q f B -> (exists q', related_program p' q' f B /\ SC_program_steps q q').
  Proof. intros. inversion H; subst.
    + destruct q. destruct p. repeat (destruct p). destruct m. destruct mem. destruct mem'. repeat (destruct p0). repeat (destruct p). destruct H0. simpl in *. destruct H4. destruct H4. destruct H6. simpl in *. subst. assert (l = translate_arrays (xs ++ (size, init) :: nil) buffer). apply H0. intros C. symmetry in C. contradiction app_cons_not_nil with (x:=xs) (a:=(size, init)) (y:=nil). subst. remember (translate_arrays xs buffer, t1, t0, while tru (SPECIAL (length xs) [num 0]::= ZERO)) as answer_p. unfold related_memory in H5. simpl in *. destruct H5. destruct H7. destruct H7. remember (update_mapping (length xs) x size m, allocate x (x + size - 1) init g) as answer_m. refine (ex_intro _ (answer_p, answer_m) _); subst. admit.
    + destruct H0. simpl in *. destruct H3. destruct H3. destruct q. destruct p. destruct p. destruct p. simpl in *. clear H0. destruct H5. subst. generalize dependent t1. induction H1; intros; subst.
      ++ admit.
      ++ refine (ex_intro _ (nil, translate (subst x v e) true B buffer, t0, WHILE tru DO SPECIAL B [num 0]::= ZERO DONE, m) _). inversion H3; subst.
        +++ admit.
        +++ admit.
      ++ admit.
      ++ admit.
      ++ admit.
      ++ admit.
      ++ admit.
      ++ admit.
      ++ admit.
      ++ admit.
      ++ admit.
      ++ admit.
      ++ admit.
      ++ admit.
      ++ admit.
      ++ admit.
      ++ admit.
      ++ admit.
    + admit.
    + admit.
Admitted.
*)
