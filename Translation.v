Require Import List.
Require Import IMP.
Require Import TSO.
Require Import SC.
Require Import Util.

Definition BUFFER_1A_CONST := 0.
Definition BUFFER_1B_CONST := 1.
Definition BUFFER_1C_CONST := 2.
Definition SIZE_1_CONST := 3.
Definition FRONT_1_CONST := 4.
Definition REAR_1_CONST := 5.
Definition LOOP_1_CONST := 6.
Definition FOUND_1_CONST := 7.
Definition RESULT_1_CONST := 8.
Definition BUFFER_2A_CONST := 9.
Definition BUFFER_2B_CONST := 10.
Definition BUFFER_2C_CONST := 11.
Definition SIZE_2_CONST := 12.
Definition FRONT_2_CONST := 13.
Definition REAR_2_CONST := 14.
Definition LOOP_2_CONST := 15.
Definition FOUND_2_CONST := 16.
Definition RESULT_2_CONST := 17.
Definition SPECIAL_CONST := 18.

Definition BUFFER_1A (base : nat) : term := var (base + BUFFER_1A_CONST).
Definition BUFFER_1B (base : nat) : term := var (base + BUFFER_1B_CONST).
Definition BUFFER_1C (base : nat) : term := var (base + BUFFER_1C_CONST).
Definition SIZE_1 (base : nat) : term := var (base + SIZE_1_CONST).
Definition FRONT_1 (base : nat) : term := var (base + FRONT_1_CONST).
Definition REAR_1 (base : nat) : term := var (base + REAR_1_CONST).
Definition LOOP_1 (base : nat) : term := var (base + LOOP_1_CONST).
Definition FOUND_1 (base : nat) : term := var (base + FOUND_1_CONST).
Definition RESULT_1 (base : nat) : term := var (base + RESULT_1_CONST).
Definition BUFFER_2A (base : nat) : term := var (base + BUFFER_2A_CONST).
Definition BUFFER_2B (base : nat) : term := var (base + BUFFER_2B_CONST).
Definition BUFFER_2C (base : nat) : term := var (base + BUFFER_2C_CONST).
Definition SIZE_2 (base : nat) : term := var (base + SIZE_2_CONST).
Definition FRONT_2 (base : nat) : term := var (base + FRONT_2_CONST).
Definition REAR_2 (base : nat) : term := var (base + REAR_2_CONST).
Definition LOOP_2 (base : nat) : term := var (base + LOOP_2_CONST).
Definition FOUND_2 (base : nat) : term := var (base + FOUND_2_CONST).
Definition RESULT_2 (base : nat) : term := var (base + RESULT_2_CONST).
Definition SPECIAL (base : nat) : term := var (base + SPECIAL_CONST).

Definition BUFFER_A (thread : bool) (base : nat) := 
  if thread then BUFFER_1A base else BUFFER_2A base.
Definition BUFFER_B (thread : bool) (base : nat) :=
  if thread then BUFFER_1B base else BUFFER_2B base.
Definition BUFFER_C (thread : bool) (base : nat) :=
  if thread then BUFFER_1C base else BUFFER_2C base.
Definition SIZE (thread : bool) (base : nat) :=
  if thread then SIZE_1 base else SIZE_2 base.
Definition FRONT (thread : bool) (base : nat) :=
  if thread then FRONT_1 base else FRONT_2 base.
Definition REAR (thread : bool) (base : nat) :=
  if thread then REAR_1 base else REAR_2 base.
Definition LOOP (thread : bool) (base : nat) :=
  if thread then LOOP_1 base else LOOP_2 base.
Definition FOUND (thread : bool) (base : nat) :=
  if thread then FOUND_1 base else FOUND_2 base.
Definition RESULT (thread : bool) (base : nat) :=
  if thread then RESULT_1 base else RESULT_2 base.

Definition ZERO : term := num 0.
Definition ONE : term  := num 0.

Definition translate_vars (init : list (nat * (list nat))) (buf_size : nat) : list (nat * (list nat)) :=
  init ++
  (buf_size,nil) :: (* BUFFER_1A *)
  (buf_size,nil) :: (* BUFFER_1B *)
  (buf_size,nil) :: (* BUFFER_1C *)
  (1,nil) :: (* SIZE_1 *)
  (1,nil) :: (* FRONT_1 *)
  (1, (buf_size - 1) :: nil) :: (* REAR_1 *)
  (1,nil) :: (* LOOP_1 *)
  (1,nil) :: (* FOUND_1 *)
  (1,nil) :: (* RESULT_1 *)
  (buf_size,nil) :: (* BUFFER_2A *)
  (buf_size,nil) :: (* BUFFER_2B *)
  (buf_size,nil) :: (* BUFFER_2C *)
  (1,nil) :: (* SIZE_2 *)
  (1,nil) :: (* FRONT_2 *)
  (1, (buf_size - 1) :: nil) :: (* REAR_2 *)
  (1,nil) :: (* LOOP_2 *)
  (1,nil) :: (* FOUND_2 *)
  (1,nil) :: (* RESULT_2 *)
  (1,nil) :: nil. (* SPECIAL *)

Definition read_code (thread : bool) (base : nat) (buf_size : nat) (location : term) (offset : term)  : term :=
  LOOP thread base ::= ZERO ;;
  FOUND thread base ::= ZERO ;;
  (WHILE !(LOOP thread base ) << (num buf_size) DO
    (CASE (and ( (BUFFER_A thread base ) [!(LOOP thread base)] == location ) ( (BUFFER_B thread base) [!(LOOP thread base)] == offset )) THEN
      RESULT thread base ::= (BUFFER_C thread base)[!(LOOP thread base)] ;;
      FOUND thread base ::= ONE
    ELSE
      yunit
    END)
  DONE);;
  CASE (!(FOUND thread base) == ONE) THEN !(RESULT thread base) ELSE (!(cast location)) END.

Definition flush (thread : bool) (base : nat) (buf_size : nat) : term :=
  CASE (!(SIZE thread base ) == ZERO) THEN yunit
  ELSE
    (write (cast ((BUFFER_A thread base )[!(FRONT thread base)])) ((BUFFER_B thread base)[!(FRONT thread base)]) ((BUFFER_C thread base)[!(FRONT thread base)]));;
    (FRONT thread base) ::= modulo (plus (!(FRONT thread base)) ONE) (num buf_size) ;;
    (SIZE thread base) ::= minus (!(SIZE thread base)) ONE
  END.

Definition write_code (thread : bool) (base : nat) (buf_size : nat) (location : term) (offset : term) (value : term) : term :=
  CASE (!(SIZE thread base) == (num buf_size)) THEN (flush thread buf_size base) ELSE yunit END ;;
  (REAR thread base) ::= modulo (plus (!(REAR thread base)) ONE) (num buf_size);;
  (BUFFER_A thread base)[!(REAR thread base)] ::= reference location;;
  (BUFFER_B thread base)[!(REAR thread base)] ::= offset;;
  (BUFFER_C thread base)[!(REAR thread base)] ::= value;;
  (SIZE thread base) ::= plus (!(SIZE thread base)) ONE.

Definition nd_flush (thread : bool) (base : nat) (buf_size : nat): term :=
  (SPECIAL base) ::= ONE ;;
  WHILE (and (!(SPECIAL base) == ONE) (not (!(SIZE thread base) == ZERO))) DO
    flush thread base buf_size
  DONE.

Definition flush_all (thread : bool) (base : nat) (buf_size : nat): term :=
  WHILE (not (!(SIZE thread base) == ZERO)) DO flush thread base buf_size DONE.

Fixpoint translate (s : term) (thread : bool) (base : nat) (buf_size : nat) : term :=
match s with
  | var k => (nd_flush thread base buf_size) ;; var k
  | num n => (nd_flush thread base buf_size) ;; num n
  | plus e1 e2 => (nd_flush thread base buf_size) ;; (plus (translate e1 thread base buf_size) (translate e2 thread base buf_size))
  | minus e1 e2 => (nd_flush thread base buf_size) ;; (minus (translate e1 thread base buf_size) (translate e2 thread base buf_size))
  | modulo e1 e2 => (nd_flush thread base buf_size) ;; (modulo (translate e1 thread base buf_size) (translate e2 thread base buf_size))
  | tru => (nd_flush thread base buf_size) ;; tru
  | fls => (nd_flush thread base buf_size) ;; fls
  | less_than e1 e2 => (nd_flush thread base buf_size) ;; (less_than (translate e1 thread base buf_size) (translate e2 thread base buf_size))
  | not e => (nd_flush thread base buf_size) ;; (not (translate e thread base buf_size))
  | and e1 e2 => (nd_flush thread base buf_size) ;; (and (translate e1 thread base buf_size) (translate e2 thread base buf_size))
  | yunit => (nd_flush thread base buf_size) ;; yunit
  | seq e1 e2 => (nd_flush thread base buf_size) ;; ((translate e1 thread base buf_size) ;; (translate e2 thread base buf_size))
  | ifterm e1 e2 e3 => (nd_flush thread base buf_size) ;; (ifterm (translate e1 thread base buf_size) (translate e2 thread base buf_size) (translate e3 thread base buf_size))
  | reference e => (nd_flush thread base buf_size) ;; (reference (translate e thread base buf_size))
  | cast e => (nd_flush thread base buf_size) ;; (cast (translate e thread base buf_size))
  | while e1 e2 => (nd_flush thread base buf_size) ;; (while (translate e1 thread base buf_size) (translate e2 thread base buf_size))
  | read e1 e2 => (nd_flush thread base buf_size) ;; (read_code thread base buf_size (translate e1 thread base buf_size) (translate e2 thread base buf_size))
  | write e1 e2 e3 => (nd_flush thread base buf_size) ;; (write_code thread base buf_size (translate e1 thread base buf_size) (translate e2 thread base buf_size) (translate e3 thread base buf_size))
end.

Fact translation_respects_stepping1 : forall e e' event thread base buf_size,
  step e event e' -> exists e'',
  steps (translate e thread base buf_size) (translate e'' thread base buf_size) /\
  steps (translate e' thread base buf_size) (translate e'' thread base buf_size).
  Proof. Admitted.

Fact translation_respects_stepping2 : forall e e' thread base buf_size,
  steps e e' -> exists e'',
  steps (translate e thread base buf_size) (translate e'' thread base buf_size) /\
  steps (translate e' thread base buf_size) (translate e'' thread base buf_size).
  Proof. Admitted.

Fixpoint translate_program (p : TSO.program) : SC.program :=  let buf_size := fst (fst (fst p)) in
  let init := snd (fst (fst p))  in
  let s1 := snd (fst p) in
  let s2 := snd p in
  let base := length (fst_list init) in
  (translate_vars init buf_size,
  seq (translate s1 true base buf_size) (flush_all true base buf_size),
  seq (translate s2 false base buf_size) (flush_all false base buf_size),
  while tru ((SPECIAL base) ::= ZERO)).

