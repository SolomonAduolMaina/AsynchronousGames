Require Import Strings.String.
Require Import List.
Require Import Lambda.
Require Import TSO.
Require Import SC.
Require Import Util.
Require Import Translation.


Inductive related (base : nat) (buf_size : nat) : (term * bool) -> (term * bool) -> Prop :=
  | related_translate : forall e thread, related base buf_size (e, thread) (translate e thread base buf_size, thread)
  | related_flush : forall e thread, related base buf_size (e, thread) (seq (flush_star thread base buf_size) (translate e thread base buf_size), thread)
.
 

Definition related_terms (TSO_program : TSO.program) (SC_program : SC.program) (base : nat) : Prop :=
  let TSO1 := snd (fst TSO_program) in
  let TSO2 := snd TSO_program in
  let SC1 := snd (fst (fst SC_program)) in
  let SC2 := snd (fst SC_program)in
  let SC3 := snd SC_program in
  let buf_size := fst (fst (fst TSO_program)) in
  related base buf_size (TSO1, true) (SC1, true) /\
  related base buf_size (TSO2, false) (SC2, false) /\
  SC3 = while tru ((SPECIAL base) ::= ZERO).

Definition related_memory (TSO_memory : TSO.memory_model) (SC_memory : SC.memory_model) (B : nat) (f : nat -> nat) : Prop :=
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

Definition related_program (p : TSO_machine) (q : SC_machine) (f : nat -> nat) (B : nat) : Prop :=
  let TSO_program := fst p in
  let TSO_memory := snd p in
  let SC_program := fst q in
  let SC_memory := snd q in
  let TSO_init := snd (fst (fst TSO_program)) in
  let SC_init := fst (fst (fst SC_program)) in
  let buf_size := fst (fst (fst TSO_program)) in
  (TSO_init <> nil -> SC_init = translate_arrays TSO_init buf_size) /\
  related_terms TSO_program SC_program B /\
  related_memory TSO_memory SC_memory B f.

Fact psteps_app : forall t t' x e,
  SC_program_steps t t' ->
  SC_program_steps (fst (fst (fst (fst t))), app (lam x e) (snd (fst (fst (fst t)))), snd (fst (fst t)), snd (fst t), snd t) (fst (fst (fst (fst t'))), app (lam x e) (snd (fst (fst (fst t')))), snd (fst (fst t')), snd (fst t'), snd t').
Proof. intros. induction H.
  + apply SC_program_steps_reflexive.
  + destruct q. destruct p. destruct p. destruct p. destruct p. destruct r. destruct p. destruct p. destruct p. destruct p0. destruct p. destruct p. simpl in *. apply SC_program_steps_transitive with (q:=(l1, app (lam x e) t7, t6, t5, m)). inversion H; subst.
    ++ apply ST_init_allocate_array. auto. auto. auto.
    ++ apply ST_synchronize1 with (event:=event).
       assert (exists y e', lam x e = lam y e'). refine (ex_intro _ x _). refine (ex_intro _ e _). reflexivity. assert (app (lam x e) t1 = con_subst (Capp2 (exist _ (lam x e) H1) Hole) t1). simpl. reflexivity. assert (app (lam x e) t7 = con_subst (Capp2 (exist _ (lam x e) H1) Hole) t7). simpl. reflexivity. rewrite H2. rewrite H4. apply step_context. auto. auto.
    ++ apply ST_synchronize2 with (event:=event). auto. auto.
    ++ apply ST_synchronize3 with (event:=event). auto. auto.
    ++ auto.
Qed.

Fact contexts_respect_bisimilarity : forall E B s2 buffer f e event e' mem mem' m t0 l t1,
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
  + inversion H3; subst.
    ++
assert (exists q' : SC_machine,
          related_program
            (buffer, nil, con_subst E e', s2, mem') q'
            f B /\
          SC_program_steps
            (l, translate (con_subst E e) true B buffer, t0,
            while tru (SPECIAL B [num 0]::= ZERO), m)
            q'). apply IHE. apply related_translate. destruct H5. destruct H5. destruct x. destruct p. destruct p. destruct p. destruct H5. simpl in *. unfold related_terms in H7. destruct H7. destruct H7. simpl in *. inversion H7; subst.
      +++ refine (ex_intro _ (l0, translate (app (con_subst E e') t) true B buffer, t2, t1, m0) _). simpl. admit.
      +++ refine (ex_intro _ (l0, translate (app (con_subst E e') t) true B buffer, t2, t1, m0) _). simpl. admit.
    ++ assert (exists q' : SC_machine,
          related_program
            (buffer, nil, con_subst E e', s2, mem') q'
            f B /\
          SC_program_steps
            (l, translate (con_subst E e) true B buffer, t0,
            while tru (SPECIAL B [num 0]::= ZERO), m)
            q'). apply IHE. apply related_translate. destruct H5. destruct H5. destruct x. destruct p. destruct p. destruct p. destruct H5. simpl in *. unfold related_terms in H7. destruct H7. destruct H7. simpl in *. inversion H7; subst.
      +++ refine (ex_intro _ (l0, translate (app (con_subst E e') t) true B buffer, t2, t1, m0) _). simpl. admit.
      +++ refine (ex_intro _ (l0, translate (app (con_subst E e') t) true B buffer, t2, t1, m0) _). simpl. admit.
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
      ++ admit.
      ++ admit.
      ++ admit.
      ++ admit.
    + admit.
    + admit.
Admitted.
