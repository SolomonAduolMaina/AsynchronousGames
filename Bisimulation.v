Require Import List.
Require Import IMP.
Require Import TSO.
Require Import SC.
Require Import Util.
Require Import Translation.

Definition bisimilar (p : TSO_machine) (q : SC_machine) (f : nat -> nat) : Prop :=
  let TSO_program := fst p in
  let TSO_memory := snd p in
  let SC_program := fst q in
  let SC_memory := snd q in
  let buf_size := fst (fst (fst TSO_program)) in
  let local := snd (fst TSO_memory) in
  let TSOGS := snd TSO_memory in
  let TSO_mapping := snd (fst (fst TSO_memory)) in
  let SC_mapping := fst SC_memory in
  let SCGS := snd SC_memory in
  let init := snd (fst (fst TSO_program)) in
  let B := length init in
  let init' := fst (fst (fst SC_program)) in
  (translate_program TSO_program = SC_program) /\
  (forall n m k, TSO_mapping n = Some (m, k) -> SC_mapping n = Some (f m, k)) /\
  (forall n m, TSOGS n = Some m -> SCGS (f n) = Some m) /\
  (init' = nil ->
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
       )
  ).

Definition psteps (p : SC_machine) (q : SC_machine) :=
  exists l,
  (length l >= 2 /\ hd_error l = Some p /\ hd_error (rev l) = Some q /\
  (forall n a b, nth_error l n = Some a /\ nth_error l (S n) = Some b -> pstep a b)).


