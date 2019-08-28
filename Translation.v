Require Import Strings.String.
Require Import List.
Require Import IMP.
Require Import TSO.
Require Import SC.
Require Import ZArith.
Require Import Util.

Definition BUFFER_1A (base : nat) : term := var (base + 1).
Definition BUFFER_1B (base : nat) : term := var (base + 2).
Definition SIZE_1 (base : nat) : term := var (base + 3).
Definition FRONT_1 (base : nat) : term := var (base + 4).
Definition REAR_1 (base : nat) : term := var (base + 5).
Definition LOOP_1 (base : nat) : term := var (base + 6).
Definition FOUND_1 (base : nat) : term := var (base + 7).
Definition RESULT_1 (base : nat) : term := var (base + 8).
Definition BUFFER_2A (base : nat) : term := var (base + 9).
Definition BUFFER_2B (base : nat) : term := var (base + 10).
Definition SIZE_2 (base : nat) : term := var (base + 11).
Definition FRONT_2 (base : nat) : term := var (base + 12).
Definition REAR_2 (base : nat) : term := var (base + 13).
Definition LOOP_2 (base : nat) : term := var (base + 14).
Definition FOUND_2 (base : nat) : term := var (base + 15).
Definition RESULT_2 (base : nat) : term := var (base + 16).
Definition SPECIAL (base : nat) : term := var (base + 17).
Definition SIZES (base : nat) : term := var (base + 18).

Definition ZERO : term := num (0%Z).
Definition ONE : term  := num (1%Z).

Definition BUFFER_A (thread : bool) (base : nat) := 
  if thread then BUFFER_1A base else BUFFER_2A base.
Definition BUFFER_B (thread : bool) (base : nat) :=
  if thread then BUFFER_1B base else BUFFER_2B base.
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

Definition read_code (thread : bool) (real : term) (offset : term) (base : nat) (buf_size : nat) : term :=
  LOOP thread base ::= ZERO ;;
  FOUND thread base ::= ZERO ;;
  (WHILE !(LOOP thread base) << (num (Z.of_nat buf_size)) DO
    (CASE ((BUFFER_A thread base) [!(LOOP thread base)] == (plus (reference real) offset) ) THEN
      RESULT thread base ::= (BUFFER_B thread base)[!(LOOP thread base)] ;;
      FOUND thread base ::= ONE
    ELSE
      yunit
    END)
  DONE);;
  CASE (!(FOUND thread base) == ONE) THEN !(RESULT thread base) ELSE (!real) END.

Fixpoint flush_write (thread : bool) (address : term) (value : term) (base : nat) (sizes_sum : term) (sizes_length : term): term :=
  (LOOP thread base) ::= minus sizes_length ONE;;
  (RESULT thread base) ::= sizes_sum;;
  WHILE (address << !(RESULT thread base)) DO 
    (RESULT thread base) ::= minus (!(RESULT thread base)) ((SIZES base)[!(LOOP thread base)]);;
    (LOOP thread base) ::= minus (!(LOOP thread base)) ONE
  DONE ;;
  write (cast (!(RESULT thread base))) (minus address (!(RESULT thread base))) value.


Definition flush (thread : bool) (base : nat) (buf_size : nat) (sizes_sum : term) (sizes_length : term) : term :=
  CASE (!(SIZE thread base) == ZERO) THEN yunit
  ELSE
    (flush_write thread ((BUFFER_A thread base)[!(FRONT thread base)]) ((BUFFER_B thread base)[!(FRONT thread base)]) base sizes_sum sizes_length);;
    (FRONT thread base) ::= modulo (plus (!(FRONT thread base)) ONE) (num (Z.of_nat buf_size)) ;;
    (SIZE thread base) ::= minus (!(SIZE thread base)) ONE
  END.

Definition write_code (address : term) (offset : term) (value : term) (thread : bool) (base : nat) (buf_size : nat) (sizes_sum : term) (sizes_length : term) : term :=
  CASE ((SIZE thread base) == (num (Z.of_nat buf_size))) THEN (flush thread base buf_size sizes_sum sizes_length) ELSE yunit END ;;
  (REAR thread base) ::= modulo (plus (!(REAR thread base)) ONE) (num (Z.of_nat buf_size));;
  (BUFFER_A thread base)[!(REAR thread base)] ::= plus (reference address) offset;;
  (BUFFER_B thread base)[!(REAR thread base)] ::= value;;
  (SIZE thread base) ::= plus (!(SIZE thread base)) ONE.

Definition nd_flush (thread : bool) (base : nat) (buf_size : nat) (sizes_sum : term) (sizes_length : term) : term :=
  (SPECIAL base) ::= ONE ;;
  WHILE (and (!(SPECIAL base) == ONE) (not (!(SIZE thread base) == ZERO))) DO 
    flush thread base buf_size sizes_sum sizes_length
  DONE.

Definition flush_all (thread : bool) (base : nat) (buf_size : nat) (sizes_sum : term) (sizes_length : term) : term :=
  WHILE (not (!(SIZE thread base) == ZERO)) DO
    flush thread base buf_size sizes_sum sizes_length
  DONE.

Fixpoint translate (s : term) (base : nat) (buf_size : nat) (thread : bool) (sizes_sum : term) (sizes_length : term) : term :=
match s with
  | var k => var k
  | ref n => ref n
  | num n => num n
  | plus e1 e2 => (nd_flush thread base buf_size sizes_sum sizes_length) ;; (plus (translate e1 base buf_size thread sizes_sum sizes_length) (translate e2 base buf_size thread sizes_sum sizes_length))
  | minus e1 e2 => (nd_flush thread base buf_size sizes_sum sizes_length) ;; (minus (translate e1 base buf_size thread sizes_sum sizes_length) (translate e2 base buf_size thread sizes_sum sizes_length))
  | modulo e1 e2 => (nd_flush thread base buf_size sizes_sum sizes_length) ;; (modulo (translate e1 base buf_size thread sizes_sum sizes_length) (translate e2 base buf_size thread sizes_sum sizes_length))
  | tru => tru
  | fls => fls
  | less_than e1 e2 => (nd_flush thread base buf_size sizes_sum sizes_length) ;; (less_than (translate e1 base buf_size thread sizes_sum sizes_length) (translate e2 base buf_size thread sizes_sum sizes_length))
  | not e => (nd_flush thread base buf_size sizes_sum sizes_length) ;; (not (translate e base buf_size thread sizes_sum sizes_length))
  | and e1 e2 => (nd_flush thread base buf_size sizes_sum sizes_length) ;; (and (translate e1 base buf_size thread sizes_sum sizes_length) (translate e2 base buf_size thread sizes_sum sizes_length))
  | yunit => yunit
  | seq e1 e2 => (nd_flush thread base buf_size sizes_sum sizes_length) ;; ((translate e1 base buf_size thread sizes_sum sizes_length) ;; (translate e2 base buf_size thread sizes_sum sizes_length))
  | ifterm e1 e2 e3 => (nd_flush thread base buf_size sizes_sum sizes_length) ;; (ifterm (translate e1 base buf_size thread sizes_sum sizes_length) (translate e2 base buf_size thread sizes_sum sizes_length) (translate e3 base buf_size thread sizes_sum sizes_length))
  | reference e => (nd_flush thread base buf_size sizes_sum sizes_length) ;; (reference (translate e base buf_size thread sizes_sum sizes_length))
  | cast e => (nd_flush thread base buf_size sizes_sum sizes_length) ;; (cast (translate e base buf_size thread sizes_sum sizes_length))
  | while e1 e2 => (nd_flush thread base buf_size sizes_sum sizes_length) ;; (while (translate e1 base buf_size thread sizes_sum sizes_length) (translate e2 base buf_size thread sizes_sum sizes_length))
  | read e1 e2 => (nd_flush thread base buf_size sizes_sum sizes_length) ;; (read_code thread (translate e1 base buf_size thread sizes_sum sizes_length) (translate e2 base buf_size thread sizes_sum sizes_length) base buf_size)
  | write e1 e2 e3 => (nd_flush thread base buf_size sizes_sum sizes_length) ;; (write_code (translate e1 base buf_size thread sizes_sum sizes_length) (translate e2 base buf_size thread sizes_sum sizes_length) (translate e3 base buf_size thread sizes_sum sizes_length) thread base buf_size sizes_sum sizes_length)
end.

Definition translate_vars (init : list (nat * (list Z))) (buf_size : nat) : list (nat * (list Z)) :=
  init ++
  (buf_size,nil) :: (* BUFFER_1A *)
  (buf_size,nil) :: (* BUFFER_1B *)
  (1,nil) :: (* SIZE_1 *)
  (1,nil) :: (* FRONT_1 *)
  (1, (Z.of_nat (buf_size - 1)) :: nil) :: (* REAR_1 *)
  (1,nil) :: (* LOOP_1 *)
  (1,nil) :: (* FOUND_1 *)
  (1,nil) :: (* RESULT_1 *)
  (buf_size,nil) :: (* BUFFER_2A *)
  (buf_size,nil) :: (* BUFFER_2B *)
  (1,nil) :: (* SIZE_2 *)
  (1,nil) :: (* FRONT_2 *)
  (1, (Z.of_nat (buf_size - 1)) :: nil) :: (* REAR_2 *)
  (1,nil) :: (* LOOP_2 *)
  (1,nil) :: (* FOUND_2 *)
  (1,nil) :: (* RESULT_2 *)
  (1,nil) :: (* SPECIAL *)
  (length init, map Z.of_nat (fst_list init)) :: nil. (* SIZES *)

Definition translate_program (p : TSO.program) : SC.program :=
  let buf_size := fst (fst (fst p)) in
  let init := snd (fst (fst p))  in
  let s1 := snd (fst p) in
  let s2 := snd p in
  let sizes := fst_list init in
  let base := length sizes in
  let sizes_sum := num (Z.of_nat (sum sizes)) in
  let sizes_length := num (Z.of_nat base) in 
  match init with
    | nil => (nil, s1, s2, yunit)
    | _ => (translate_vars init buf_size,
           seq (translate s1 base buf_size true sizes_sum sizes_length) (flush_all true base buf_size sizes_sum sizes_length),
           seq (translate s1 base buf_size false sizes_sum sizes_length) (flush_all false base buf_size sizes_sum sizes_length),
           while tru ((SPECIAL base) ::= ZERO))
  end.

Definition psteps (p : SC_machine) (q : SC_machine) :=
  exists l,
  (length l >= 2 /\ hd_error l = Some p /\ hd_error (rev l) = Some q /\
  (forall n a b, nth_error l n = Some a /\ nth_error l (S n) = Some b -> pstep a b)).

Definition bisimilar (p : TSO_machine) (q : SC_machine) : Prop :=
  let TSO_term := fst p in
  let TSO_memory := snd p in
  let SC_term := fst q in
  let SCGS := snd (snd q) in
  let buf_size := fst (fst (fst TSO_term)) in
  let local := snd (fst TSO_memory) in
  let TSOGS := snd TSO_memory in
  let init' := fst (fst (fst SC_term)) in
  (translate_program TSO_term = SC_term) /\
  (forall n m, TSOGS n = Some m -> SCGS n = Some m) /\
  (init' = nil -> 
      (exists BUFFER_1A BUFFER_1B FRONT_1 REAR_1 SIZE_1 BUFFER_2A BUFFER_2B FRONT_2 REAR_2 SIZE_2,
          (forall add val n, (nth_error (local true) n = Some (add, val)) ->
              exists keys values front rear size,
                  (SCGS BUFFER_1A = Some keys /\
                   SCGS BUFFER_1B = Some values /\
                   SCGS FRONT_1 = Some front /\
                   SCGS REAR_1 = Some rear /\
                   SCGS SIZE_1 = Some size /\
                   (Z.to_nat (Z.sub front rear)) = length (local true) /\
                   (Z.to_nat (Z.sub front rear)) = (Z.to_nat size) /\
                   SCGS ((Z.to_nat keys) + (((Z.to_nat front) + n) mod buf_size)) = Some (Z.of_nat add) /\
                   SCGS ((Z.to_nat values) + (((Z.to_nat front) + n) mod buf_size)) = Some val
                  )
          ) /\
          (forall add val n, (nth_error (local true) n = Some (add, val)) ->
              exists keys values front rear size,
                  (SCGS BUFFER_2A = Some keys /\
                   SCGS BUFFER_2B = Some values /\
                   SCGS FRONT_2 = Some front /\
                   SCGS REAR_2 = Some rear /\
                   SCGS SIZE_2 = Some size /\
                   (Z.to_nat (Z.sub front rear)) = length (local true) /\
                   (Z.to_nat (Z.sub front rear)) = (Z.to_nat size) /\
                   SCGS ((Z.to_nat keys) + (((Z.to_nat front) + n) mod buf_size)) = Some (Z.of_nat add) /\
                   SCGS ((Z.to_nat values) + (((Z.to_nat front) + n) mod buf_size)) = Some val
                  )
          )
      )
  ).


