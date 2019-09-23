Require Import Strings.String.
Require Import List.
Require Import Util.
Require Import Lambda.
Require Import TSO.
Require Import SC.


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

Definition BUFFER_1A (base : nat) : term := array (base + BUFFER_1A_CONST).
Definition BUFFER_1B (base : nat) : term := array (base + BUFFER_1B_CONST).
Definition BUFFER_1C (base : nat) : term := array (base + BUFFER_1C_CONST).
Definition SIZE_1 (base : nat) : term := array (base + SIZE_1_CONST).
Definition FRONT_1 (base : nat) : term := array (base + FRONT_1_CONST).
Definition REAR_1 (base : nat) : term := array (base + REAR_1_CONST).
Definition LOOP_1 (base : nat) : term := array (base + LOOP_1_CONST).
Definition FOUND_1 (base : nat) : term := array (base + FOUND_1_CONST).
Definition RESULT_1 (base : nat) : term := array (base + RESULT_1_CONST).
Definition BUFFER_2A (base : nat) : term := array (base + BUFFER_2A_CONST).
Definition BUFFER_2B (base : nat) : term := array (base + BUFFER_2B_CONST).
Definition BUFFER_2C (base : nat) : term := array (base + BUFFER_2C_CONST).
Definition SIZE_2 (base : nat) : term := array (base + SIZE_2_CONST).
Definition FRONT_2 (base : nat) : term := array (base + FRONT_2_CONST).
Definition REAR_2 (base : nat) : term := array (base + REAR_2_CONST).
Definition LOOP_2 (base : nat) : term := array (base + LOOP_2_CONST).
Definition FOUND_2 (base : nat) : term := array (base + FOUND_2_CONST).
Definition RESULT_2 (base : nat) : term := array (base + RESULT_2_CONST).
Definition SPECIAL (base : nat) : term := array (base + SPECIAL_CONST).

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

Definition translate_arrays (init : list (nat * (list nat))) (buf_size : nat) : list (nat * (list nat)) :=
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

Definition translate_read (thread : bool) (base : nat) (buf_size : nat) (location : term) (offset : term)  : term :=
  let read_code :=
  LOOP thread base ::= ZERO ;;
  FOUND thread base ::= ZERO ;;
  (WHILE !(LOOP thread base ) << (num buf_size) DO
    (CASE (and ( (BUFFER_A thread base ) [!(LOOP thread base)] == (var "location") ) ( (BUFFER_B thread base) [!(LOOP thread base)] == (var "offset") )) THEN
      RESULT thread base ::= (BUFFER_C thread base)[!(LOOP thread base)] ;;
      FOUND thread base ::= ONE
    ELSE
      yunit
    ESAC)
  DONE);;
  CASE (!(FOUND thread base) == ONE) THEN !(RESULT thread base) ELSE (!(cast (var "location"))) ESAC in
app (app (lam "location" (lam "offset" read_code)) location) offset.

Definition flush (thread : bool) (base : nat) (buf_size : nat) : term :=
  CASE (!(SIZE thread base ) == ZERO) THEN yunit
  ELSE
    (write (cast ((BUFFER_A thread base )[!(FRONT thread base)])) ((BUFFER_B thread base)[!(FRONT thread base)]) ((BUFFER_C thread base)[!(FRONT thread base)]));;
    (FRONT thread base) ::= modulo (plus (!(FRONT thread base)) ONE) (num buf_size) ;;
    (SIZE thread base) ::= minus (!(SIZE thread base)) ONE
  ESAC.


Definition translate_write (thread : bool) (base : nat) (buf_size : nat) (array : term) (offset : term) (value : term) : term :=
  let write_code :=
  CASE (!(SIZE thread base) == (num buf_size)) THEN (flush thread buf_size base) ELSE yunit ESAC ;;
  (REAR thread base) ::= modulo (plus (!(REAR thread base)) ONE) (num buf_size);;
  (BUFFER_A thread base)[!(REAR thread base)] ::= (& (var "array"));;
  (BUFFER_B thread base)[!(REAR thread base)] ::= (var "offset");;
  (BUFFER_C thread base)[!(REAR thread base)] ::= (var "value");;
  (SIZE thread base) ::= plus (!(SIZE thread base)) ONE
in app (app (app (lam "array" (lam "offset" (lam "value" write_code))) array) offset) value.


Definition flush_star (thread : bool) (base : nat) (buf_size : nat): term :=
  (SPECIAL base) ::= ONE ;;
  WHILE (and (!(SPECIAL base) == ONE) (not (!(SIZE thread base) == ZERO))) DO
    flush thread base buf_size
  DONE.


Fixpoint translate (s : term) (thread : bool) (base : nat) (buf_size : nat) : term :=
  match s with
    | array k => array k
    | num n => num n
    | tru => tru
    | fls => fls
    | yunit => yunit
    | var x => var x
    | lam x e => lam x (translate e thread base buf_size)
    | app e1 e2 => 
      let x := translate e1 thread base buf_size in
      let y := translate e2 thread base buf_size in
      app (lam "x" (seq (flush_star thread base buf_size) (var "x"))) (app x y)
    | plus e1 e2 => 
      let x := translate e1 thread base buf_size in
      let y := translate e2 thread base buf_size in
      app (lam "x" (seq (flush_star thread base buf_size) (var "x"))) (plus x y)
    | minus e1 e2 =>
      let x := translate e1 thread base buf_size in
      let y := translate e2 thread base buf_size in
      let z := flush_star thread base buf_size in
      app (lam "x" (seq (flush_star thread base buf_size) (var "x"))) (minus x y)
    | modulo e1 e2 =>
      let x := translate e1 thread base buf_size in
      let y := translate e2 thread base buf_size in
      let z := flush_star thread base buf_size in
      app (lam "x" (seq (flush_star thread base buf_size) (var "x"))) (modulo x y)
    | less_than e1 e2 =>
      let x := translate e1 thread base buf_size in
      let y := translate e2 thread base buf_size in
      let z := flush_star thread base buf_size in
      app (lam "x" (seq (flush_star thread base buf_size) (var "x"))) (less_than x y)
    | and e1 e2 =>
      let x := translate e1 thread base buf_size in
      let y := translate e2 thread base buf_size in
      let z := flush_star thread base buf_size in
      app (lam "x" (seq (flush_star thread base buf_size) (var "x"))) (and x y)
    | not e =>
      let x := translate e thread base buf_size in
      app (lam "x" (seq (flush_star thread base buf_size) (var "x"))) (not x)
    | reference e =>
      let x := translate e thread base buf_size in
      app (lam "x" (seq (flush_star thread base buf_size) (var "x"))) (reference x)
    | cast e =>
      let x := translate e thread base buf_size in
      app (lam "x" (seq (flush_star thread base buf_size) (var "x"))) (cast x)
    | case e1 e2 e3 =>
      let x := translate e1 thread base buf_size in
      let y := translate e2 thread base buf_size in
      let z := translate e3 thread base buf_size in
      app (lam "x" (seq (flush_star thread base buf_size) (var "x"))) (case x y z)
    | read e1 e2 =>
      let x := translate e1 thread base buf_size in
      let y := translate e2 thread base buf_size in
      app (lam "x" (seq (flush_star thread base buf_size) (var "x"))) (translate_read thread base buf_size x y)
    | write e1 e2 e3 =>
      let x := translate e1 thread base buf_size in
      let y := translate e2 thread base buf_size in
      let z := translate e3 thread base buf_size in
      app (lam "x" (seq (flush_star thread base buf_size) (var "x"))) (translate_write thread base buf_size x y z)
  end.

Fact subst_flush_star : forall x v thread base buf_size,
  subst x v (lam "x" (flush_star thread base buf_size;; var "x")) =
  (lam "x" (flush_star thread base buf_size;; var "x")).
Proof. intros. simpl. assert (subst x v (FRONT thread base) = (FRONT thread base)). unfold FRONT. destruct thread. unfold FRONT_1. simpl. reflexivity. unfold FRONT_2. simpl. reflexivity. assert (subst x v (SIZE thread base) = (SIZE thread base)). unfold SIZE. destruct thread. unfold SIZE_1. simpl. reflexivity. unfold SIZE_2. simpl. reflexivity. assert (subst x v (BUFFER_A thread base) = (BUFFER_A thread base)). unfold BUFFER_A. destruct thread. unfold BUFFER_1A. simpl. reflexivity. unfold BUFFER_2A. simpl. reflexivity. assert (subst x v (BUFFER_B thread base) = (BUFFER_B thread base)). unfold BUFFER_B. destruct thread. unfold BUFFER_1B. simpl. reflexivity. unfold BUFFER_2B. simpl. reflexivity. assert (subst x v (BUFFER_C thread base) = (BUFFER_C thread base)). unfold BUFFER_C. destruct thread. unfold BUFFER_1C. simpl. reflexivity. unfold BUFFER_2C. simpl. reflexivity.
destruct (string_dec x "x") eqn:ORIG; destruct (string_dec x "y") eqn:ORIG1; destruct (string_dec x "g") eqn:ORIG2; destruct (string_dec x "while") eqn:ORIG3; destruct (string_dec x "b") eqn:ORIG4; destruct (string_dec x "c") eqn:ORIG5; try (rewrite H); try (rewrite H0); try (rewrite H1); try (rewrite H1); try (rewrite H2); try (rewrite H3); auto; simpl. Qed.

Fact subst_array : forall n x v, subst x v (array n) = array n.
Proof. intros. simpl. reflexivity. Qed.

Fact subst_num : forall n x v, subst x v (num n) = num n.
Proof. intros. simpl. reflexivity. Qed.

Fact subst_tru : forall x v, subst x v tru = tru.
Proof. intros. simpl. reflexivity. Qed.

Fact subst_fls : forall x v, subst x v fls = fls.
Proof. intros. simpl. reflexivity. Qed.

Fact subst_yunit : forall x v, subst x v yunit = yunit.
Proof. intros. simpl. reflexivity. Qed.

Fact subst_app : forall e1 e2 x v, subst x v (app e1 e2) = app (subst x v e1) (subst x v e2).
Proof. intros. simpl. reflexivity. Qed.


Fact subst_plus : forall e1 e2 x v, subst x v (plus e1 e2) = plus (subst x v e1) (subst x v e2).
Proof. intros. simpl. reflexivity. Qed.

Fact subst_minus : forall e1 e2 x v, subst x v (minus e1 e2) = minus (subst x v e1) (subst x v e2).
Proof. intros. simpl. reflexivity. Qed.

Fact subst_modulo : forall e1 e2 x v, subst x v (modulo e1 e2) = modulo (subst x v e1) (subst x v e2).
Proof. intros. simpl. reflexivity. Qed.

Fact subst_less_than : forall e1 e2 x v, subst x v (less_than e1 e2) = less_than (subst x v e1) (subst x v e2).
Proof. intros. simpl. reflexivity. Qed.

Fact subst_and : forall e1 e2 x v, subst x v (and e1 e2) = and (subst x v e1) (subst x v e2).
Proof. intros. simpl. reflexivity. Qed.

Fact subst_not : forall e1  x v, subst x v (not e1) = not (subst x v e1).
Proof. intros. simpl. reflexivity. Qed.

Fact subst_cast : forall e1 x v, subst x v (cast e1) = cast (subst x v e1).
Proof. intros. simpl. reflexivity. Qed.

Fact subst_reference : forall e1 x v, subst x v (reference e1) = reference (subst x v e1).
Proof. intros. simpl. reflexivity. Qed.

Fact subst_read : forall e1 e2 x v, subst x v (read e1 e2) = read (subst x v e1) (subst x v e2).
Proof. intros. simpl. reflexivity. Qed.

Fact subst_write : forall e1 e2 e3 x v, subst x v (write e1 e2 e3) = write (subst x v e1) (subst x v e2) (subst x v e3).
Proof. intros. simpl. reflexivity. Qed.

Fact subst_case : forall e1 e2 e3 x v, subst x v (case e1 e2 e3) = case (subst x v e1) (subst x v e2) (subst x v e3).
Proof. intros. simpl. reflexivity. Qed.

Fact subst_var : forall x y v, subst x v (var y) = if (string_dec x y) then v else (var y).
Proof. intros. simpl. reflexivity. Qed.

Fact subst_lam : forall x y v e, subst x v (lam y e) = lam y (if (string_dec x y) then e else (subst x v e)).
Proof. intros. simpl. reflexivity. Qed.



Definition translate_program (p : TSO.program) : SC.program :=  
  let buf_size := fst (fst (fst p)) in
  let init := snd (fst (fst p))  in
  let s1 := snd (fst p) in
  let s2 := snd p in
  let base := length init in
  (translate_arrays init buf_size,
  translate s1 true base buf_size,
  translate s2 false base buf_size,
  while tru ((SPECIAL base) ::= ZERO)).
