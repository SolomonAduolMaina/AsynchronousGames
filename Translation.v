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
Definition ONE : term  := num 1.

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
    ESAC)
  DONE);;
  CASE (!(FOUND thread base) == ONE) THEN !(RESULT thread base) ELSE (!(cast location)) ESAC.

Definition flush (thread : bool) (base : nat) (buf_size : nat) : term :=
  CASE (!(SIZE thread base ) == ZERO) THEN yunit
  ELSE
    (write (cast ((BUFFER_A thread base )[!(FRONT thread base)])) ((BUFFER_B thread base)[!(FRONT thread base)]) ((BUFFER_C thread base)[!(FRONT thread base)]));;
    (FRONT thread base) ::= modulo (plus (!(FRONT thread base)) ONE) (num buf_size) ;;
    (SIZE thread base) ::= minus (!(SIZE thread base)) ONE
  ESAC.

Definition write_code (thread : bool) (base : nat) (buf_size : nat) (location : term) (offset : term) (value : term) : term :=
  CASE (!(SIZE thread base) == (num buf_size)) THEN (flush thread buf_size base) ELSE yunit ESAC ;;
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

Definition nd_flush1 (thread : bool) (base : nat) (buf_size : nat): term :=
  WHILE (and (!(SPECIAL base) == ONE) (not (!(SIZE thread base) == ZERO))) DO
    flush thread base buf_size
  DONE.


Fixpoint translate (s : term) (thread : bool) (base : nat) (buf_size : nat) : term :=
match s with
  | var k =>  var k
  | num n => num n
  | tru =>  tru
  | fls => fls
  | yunit => yunit
  | plus e1 e2 => (nd_flush thread base buf_size) ;; plus (translate e1 thread base buf_size) (translate e2 thread base buf_size))

  | not tru => (nd_flush thread base buf_size) ;; (not tru)
  | not fls => (nd_flush thread base buf_size) ;; (not fls)
  | not e => not (translate e thread base buf_size)
  | and fls e => (nd_flush thread base buf_size) ;; (and fls e)
  | and tru tru => (nd_flush thread base buf_size) ;; (and tru tru)
  | and tru fls => (nd_flush thread base buf_size) ;; (and tru fls)
  | and e1 e2 => and (translate e1 thread base buf_size) (translate e2 thread base buf_size)
  | seq yunit e2 => (nd_flush thread base buf_size) ;; (seq yunit (translate e2 thread base buf_size))
  | seq e1 e2 => seq (translate e1 thread base buf_size) (translate e2 thread base buf_size)
  | case tru e2 e3 => (nd_flush thread base buf_size) ;; (case tru (translate e2 thread base buf_size) e3)
  | case fls e2 e3 => (nd_flush thread base buf_size) ;; (case fls e2 (translate e3 thread base buf_size))
  | case e1 e2 e3 => case (translate e1 thread base buf_size) (translate e2 thread base buf_size) (translate e3 thread base buf_size)
  | reference (var n) => (nd_flush thread base buf_size) ;; (reference (var n))
  | reference e => reference (translate e thread base buf_size)
  | cast (num n) => (nd_flush thread base buf_size) ;; (cast (num n))
  | cast e => cast (translate e thread base buf_size)
  | while e1 e2 => (nd_flush thread base buf_size) ;; (while (translate e1 thread base buf_size) (translate e2 thread base buf_size))
  | read (var x) e => (nd_flush thread base buf_size) ;; (read (var x) (translate e thread base buf_size))
  | read (var x) (num n) => (nd_flush thread base buf_size) ;; (read_code thread base buf_size (var x) (num n))
  | read e1 e2 => read (translate e1 thread base buf_size) (translate e2 thread base buf_size)
  | write (var x) e1 e2 => (nd_flush thread base buf_size) ;; (write (var x) (translate e2 thread base buf_size) (translate e3 thread base buf_size))
  | write (var x) (num m) e2 => (nd_flush thread base buf_size) ;; (write (translate e2 thread base buf_size) (translate e3 thread base buf_size))
  | write (var x) (num m) (num n) => (nd_flush thread base buf_size) ;; (write_code thread base buf_size (var x) (num m) (num n))
  | write e1 e2 e3 => write (translate e1 thread base buf_size) (translate e2 thread base buf_size) (translate e3 thread base buf_size)
end.


Definition translate_program (p : TSO.program) : SC.program :=  
 let buf_size := fst (fst (fst p)) in
  let init := snd (fst (fst p))  in
  let s1 := snd (fst p) in
  let s2 := snd p in
  let base := length init in
  (translate_vars init buf_size,
  translate s1 true base buf_size,
  translate s2 false base buf_size,
  while tru ((SPECIAL base) ::= ZERO)).
