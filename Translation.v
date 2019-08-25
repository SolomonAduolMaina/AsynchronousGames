Require Import Strings.String.
Require Import List.
Require Import IMP.
Require Import TSO.
Require Import SC.
Require Import ZArith.

Fixpoint take {A} (n : nat) (l : list A)  :=
  match l, n with
    | _, 0 => nil
    | nil, _ => nil
    | x :: xs, S n => x :: (take n xs)
  end.

Fixpoint sum (l : list nat) :=
  match l with
    | nil => 0
    | x :: xs => x + (sum xs)
  end.

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
Definition ZERO : term := num (0%Z).
Definition ONE : term  := num (1%Z).
Definition MINUS_ONE : term := num (-1%Z).

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

Fixpoint virtual_to_real (index : nat) (virtual : nat) (sizes : list nat) : (nat * nat) :=
  match index with
    | 0 => (0, virtual)
    | S n => let base := sum (take n sizes) in
             if base <=? virtual then (base, virtual - base) else virtual_to_real n virtual sizes
  end.

Definition real_to_virtual (real : term) (sizes : list nat) : term := 
  match real with
    | var real => num (Z.of_nat (sum (take (real - 1) sizes)))
    | _ => num (0%Z)
  end.

Definition read_code (thread : bool) (real : term) (offset : term) (sizes : list nat) (buf_size : nat) : term :=
  let base := length sizes in
  LOOP thread base ::= ZERO ;;
  FOUND thread base ::= ZERO ;;
  (WHILE !(LOOP thread base) << (num (Z.of_nat buf_size)) DO
    (CASE ((BUFFER_A thread base) [!(LOOP thread base)] == (plus (real_to_virtual real sizes) offset) ) THEN
      RESULT thread base ::= (BUFFER_B thread base)[!(LOOP thread base)] ;;
      FOUND thread base ::= ONE
    ELSE
      yunit
    END)
  DONE);;
  CASE (!(FOUND thread base) == ONE) THEN !(RESULT thread base) ELSE (!real) END.

Definition flush_write (virtual : term) (value : term) (sizes : list nat) : term :=
  match virtual with
    | num m  => let (base, offset) := virtual_to_real (length sizes) (Z.to_nat m) sizes in
                     write (var base) (num (Z.of_nat offset)) value
    | _ => yunit
  end.

Definition flush (thread : bool) (sizes : list nat) (buf_size : nat) : term :=
  let base := length sizes in
  CASE (!(SIZE thread base) == ZERO) THEN yunit
  ELSE
    (flush_write ((BUFFER_A thread base)[!(FRONT thread base)]) ((BUFFER_B thread base)[!(FRONT thread base)]) sizes);;
    (FRONT thread base) ::= modulo (plus (!(FRONT thread base)) ONE) (num (Z.of_nat buf_size)) ;;
    (SIZE thread base) ::= plus (!(SIZE thread base)) MINUS_ONE
  END.

Definition write_code (virtual : term) (offset : term) (value : term) (thread : bool) (sizes : list nat) (buf_size : nat) : term :=
  let base := length sizes in
  CASE ((SIZE thread base) == (num (Z.of_nat buf_size))) THEN (flush thread sizes buf_size) ELSE yunit END ;;
  (REAR thread base) ::= modulo (plus (!(REAR thread base)) ONE) (num (Z.of_nat buf_size));;
  (BUFFER_A thread base)[!(REAR thread base)] ::= plus virtual offset;;
  (BUFFER_B thread base)[!(REAR thread base)] ::= value;;
  (SIZE thread base) ::= plus (!(SIZE thread base)) ONE.

Definition nd_flush (thread : bool) (sizes : list nat) (buf_size : nat) : term :=
  let base := length sizes in
  (SPECIAL base) ::= ONE ;;
  WHILE (!(SPECIAL base) == ONE) DO (flush thread sizes buf_size) DONE.

Fixpoint translate (s : term) (sizes : list nat) (buf_size : nat) (thread : bool) (f : nat -> nat): term :=
match s with
  | var k => (paire (var k) (real_to_virtual (var k) sizes))
  | ref n m => (ref (f n) m)
  | num n => (num n)
  | plus e1 e2 => (nd_flush thread sizes buf_size) ;; (plus (translate e1 sizes buf_size thread f) (translate e2 sizes buf_size thread f))
  | modulo e1 e2 => (nd_flush thread sizes buf_size) ;; (modulo (translate e1 sizes buf_size thread f) (translate e2 sizes buf_size thread f))
  | tru => tru
  | fls => fls
  | less_than e1 e2 => (nd_flush thread sizes buf_size) ;; (less_than (translate e1 sizes buf_size thread f) (translate e2 sizes buf_size thread f))
  | not e => (nd_flush thread sizes buf_size) ;; (not (translate e sizes buf_size thread f))
  | and e1 e2 => (nd_flush thread sizes buf_size) ;; (and (translate e1 sizes buf_size thread f) (translate e2 sizes buf_size thread f))
  | yunit => (nd_flush thread sizes buf_size) ;; yunit
  | seq e1 e2 => (nd_flush thread sizes buf_size) ;; ((translate e1 sizes buf_size thread f) ;; (translate e2 sizes buf_size thread f))
  | ifterm e1 e2 e3 => (nd_flush thread sizes buf_size) ;; (ifterm (translate e1 sizes buf_size thread f) (translate e2 sizes buf_size thread f) (translate e3 sizes buf_size thread f))
  | while e1 e2 => (nd_flush thread sizes buf_size) ;; (while (translate e1 sizes buf_size thread f) (translate e2 sizes buf_size thread f))
  | paire e1 e2 => (nd_flush thread sizes buf_size) ;; (paire (translate e1 sizes buf_size thread f) (translate e2 sizes buf_size thread f))
  | first e => (nd_flush thread sizes buf_size) ;; (first (translate e sizes buf_size thread f))
  | second e => (nd_flush thread sizes buf_size) ;; (second (translate e sizes buf_size thread f))
  | read e1 e2 => (nd_flush thread sizes buf_size) ;; (read_code thread (first e1) (translate e2 sizes buf_size thread f) sizes buf_size)
  | write e1 e2 e3 => (nd_flush thread sizes buf_size) ;; (write_code (second e1) (translate e2 sizes buf_size thread f) (translate e3 sizes buf_size thread f) thread sizes buf_size)
end.

Fixpoint fst_list {A B} (l : list (A * B)) : list A :=
  match l with
    | nil => nil
    | (a, _) :: xs => a :: (fst_list xs)
  end.

Definition translate_vars (init : list (nat * (list Z))) (buf_size : nat) : list (nat * (list Z)) :=
  (1,nil) :: (* SPECIAL *)
  (1,nil) :: (* RESULT_2 *)
  (1,nil) :: (* FOUND_2 *)
  (1,nil) :: (* LOOP_2 *)
  (1, (Z.of_nat (buf_size - 1)) :: nil) :: (* REAR_2 *)
  (1,nil) :: (* FRONT_2 *)
  (1,nil) :: (* SIZE_2 *)
  (buf_size,nil) :: (* BUFFER_2B *)
  (buf_size,nil) :: (* BUFFER_2A *)
  (1,nil) :: (* RESULT_1 *)
  (1,nil) :: (* FOUND_1 *)
  (1,nil) :: (* LOOP_1 *)
  (1, (Z.of_nat (buf_size - 1)) :: nil) :: (* REAR_1 *)
  (1,nil) :: (* FRONT_1 *)
  (1,nil) :: (* SIZE_1 *)
  (buf_size,nil) :: (* BUFFER_1B *)
  (buf_size,nil) :: (* BUFFER_1A *)
  init.

Definition translate_program (p : TSO.program) (f : nat -> nat) : SC.program :=
  let buf_size := fst (fst (fst p)) in
  let init := snd (fst (fst p))  in
  let s1 := snd (fst p) in
  let s2 := snd p in
  let sizes := fst_list (rev init) in
  let base := length sizes in
  (translate_vars init buf_size,
   translate s1 sizes buf_size true f,
   translate s1 sizes buf_size false f,
   while tru ((SPECIAL base) ::= ZERO)).


