Require Import List.
Require Import Util.
Require Import Lambda.
Require Import TSO.
Require Import SC.
Require Import ZArith.

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
Definition DONE_COUNTER_CONST := 19.

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
Definition DONE_COUNTER (base : nat) : term := array (base + DONE_COUNTER_CONST).

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
  (1,nil) :: (* SPECIAL *)
  (1, 2 :: nil) :: nil. (* DONE_COUNTER *)


Definition or (s : term) (t : term) := not (and (not s) (not t)).

Definition equals (s : term) (t : term) := not (or (less_than s t) (less_than t s)).

(* NEEDS TO BE CAPTURE-AVOIDING *)
Definition seq (s : term) (t : term) := app (lam (shift_up 0 t)) s.

Definition y_combinator := 
  lam (app (lam (app (var 1) (app (var 0) (var 0)))) (lam (app (var 1) (app (var 0) (var 0)))) ).

Definition while_fun := 
  lam (lam (lam (case (var 1) (seq (var 0) (app (app (var 2) (var 1)) (var 0))) yunit))).

Definition while_fics := app y_combinator while_fun.

Definition while (s : term) (t : term) := app (app while_fics s) t.

Notation "x == y" := (equals x y) (at level 60).

Notation "c1 ;; c2" :=
  (seq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'DONE'" :=
  (while b c) (at level 80, right associativity).

Definition read_code (thread : bool) (base : nat) (buf_size : nat) := 
  LOOP thread base ::= ZERO ;;
  FOUND thread base ::= ZERO ;;
  (WHILE !(LOOP thread base ) << (num buf_size) DO
    (CASE (and ( (BUFFER_A thread base)[!(LOOP thread base)] == (& (first (var 0))) ) ( (BUFFER_B thread base)[!(LOOP thread base)] == (second (var 0)) )) THEN
      RESULT thread base ::= (BUFFER_C thread base)[!(LOOP thread base)] ;;
      FOUND thread base ::= ONE
    ELSE
      yunit
    ESAC)
  DONE) ;;
  CASE (!(FOUND thread base) == ONE) THEN !(RESULT thread base) ELSE (read (first (var 0)) (second (var 0))) ESAC.

Definition new_read (thread : bool) (base : nat) (buf_size : nat) (array : term) (offset : term)  : term :=
app (lam (read_code thread base buf_size)) (paire array offset).

Definition flush (thread : bool) (base : nat) (buf_size : nat) : term :=
  CASE (!(SIZE thread base ) == ZERO) THEN yunit
  ELSE
    (write (cast ((BUFFER_A thread base )[!(FRONT thread base)])) ((BUFFER_B thread base)[!(FRONT thread base)]) ((BUFFER_C thread base)[!(FRONT thread base)]));;
    (FRONT thread base) ::= modulo (plus (!(FRONT thread base)) ONE) (num buf_size) ;;
    (SIZE thread base) ::= minus (!(SIZE thread base)) ONE
  ESAC.

Definition write_code  (thread : bool) (base : nat) (buf_size : nat) :=
CASE (!(SIZE thread base) == (num buf_size)) THEN (flush thread buf_size base) ELSE yunit ESAC ;;
  (REAR thread base) ::= modulo (plus (!(REAR thread base)) ONE) (num buf_size);;
  (BUFFER_A thread base)[!(REAR thread base)] ::= (& (first (var 0)));;
  (BUFFER_B thread base)[!(REAR thread base)] ::= (first (second (var 0)));;
  (BUFFER_C thread base)[!(REAR thread base)] ::= (second (second (var 0)));;
  (SIZE thread base) ::= plus (!(SIZE thread base)) ONE.

Definition new_write (thread : bool) (base : nat) (buf_size : nat) (array : term) (offset : term) (value : term) : term :=
app (lam (write_code thread base buf_size)) (paire array (paire offset value)).


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
    | lam e => lam (seq (flush_star thread base buf_size) (translate e thread base buf_size))
    | app e1 e2 => 
      app (translate e1 thread base buf_size) (translate e2 thread base buf_size)
    | plus e1 e2 => 
      let x := translate e1 thread base buf_size in
      let y := translate e2 thread base buf_size in
      app (lam (seq (flush_star thread base buf_size) (var 0))) (plus x y)
    | minus e1 e2 =>
      let x := translate e1 thread base buf_size in
      let y := translate e2 thread base buf_size in
      let z := flush_star thread base buf_size in
      app (lam (seq (flush_star thread base buf_size) (var 0))) (minus x y)
    | modulo e1 e2 =>
      let x := translate e1 thread base buf_size in
      let y := translate e2 thread base buf_size in
      let z := flush_star thread base buf_size in
      app (lam (seq (flush_star thread base buf_size) (var 0))) (modulo x y)
    | less_than e1 e2 =>
      let x := translate e1 thread base buf_size in
      let y := translate e2 thread base buf_size in
      let z := flush_star thread base buf_size in
      app (lam (seq (flush_star thread base buf_size) (var 0))) (less_than x y)
    | and e1 e2 =>
      let x := translate e1 thread base buf_size in
      let y := translate e2 thread base buf_size in
      let z := flush_star thread base buf_size in
      app (lam (seq (flush_star thread base buf_size) (var 0))) (and x y)
    | not e =>
      let x := translate e thread base buf_size in
      app (lam (seq (flush_star thread base buf_size) (var 0))) (not x)
    | reference e =>
      let x := translate e thread base buf_size in
      app (lam (seq (flush_star thread base buf_size) (var 0))) (reference x)
    | cast e =>
      let x := translate e thread base buf_size in
      app (lam (seq (flush_star thread base buf_size) (var 0))) (cast x)
    | case e1 e2 e3 =>
      let x := translate e1 thread base buf_size in
      let y := translate e2 thread base buf_size in
      let z := translate e3 thread base buf_size in
      case x (seq (flush_star thread base buf_size) y) (seq (flush_star thread base buf_size) z)
    | read e1 e2 =>
      let x := translate e1 thread base buf_size in
      let y := translate e2 thread base buf_size in
      app (lam (seq (flush_star thread base buf_size) (var 0))) (new_read thread base buf_size x y)
    | write e1 e2 e3 =>
      let x := translate e1 thread base buf_size in
      let y := translate e2 thread base buf_size in
      let z := translate e3 thread base buf_size in
      app (lam (seq (flush_star thread base buf_size) (var 0))) (new_write thread base buf_size x y z)
    | paire e1 e2 =>
      paire (translate e1 thread base buf_size) (translate e2 thread base buf_size)
    | first e =>
      let x := translate e thread base buf_size in
      app (lam (seq (flush_star thread base buf_size) (var 0))) (first x)
    | second e =>
      let x := translate e thread base buf_size in
      app (lam (seq (flush_star thread base buf_size) (var 0))) (second x)
  end.

Fact translate_var : forall x thread base buf_size, translate (var x) thread base buf_size = var x.
Proof. intros. simpl. reflexivity. Qed.

Fact translate_array : forall n thread base buf_size, translate (array n) thread base buf_size = array n.
Proof. intros. simpl. reflexivity. Qed.

Fact translate_num : forall n thread base buf_size, translate (num n) thread base buf_size = num n.
Proof. intros. simpl. reflexivity. Qed.

Fact translate_tru : forall thread base buf_size, translate tru thread base buf_size = tru.
Proof. intros. simpl. reflexivity. Qed.

Fact translate_fls : forall thread base buf_size, translate fls thread base buf_size = fls.
Proof. intros. simpl. reflexivity. Qed.

Fact translate_yunit : forall thread base buf_size, translate yunit thread base buf_size = yunit.
Proof. intros. simpl. reflexivity. Qed.

Fact translate_lam : forall e thread base buf_size, translate (lam e) thread base buf_size = lam (seq (flush_star thread base buf_size) (translate e thread base buf_size)).
Proof. intros. simpl. reflexivity. Qed.

Fact translate_plus : forall thread base buf_size e1 e2, translate (plus e1 e2) thread base buf_size = app (lam (seq (flush_star thread base buf_size) (var 0))) (plus (translate e1 thread base buf_size) (translate e2 thread base buf_size)).
Proof. intros. simpl. reflexivity. Qed.

Fact translate_app : forall thread base buf_size e1 e2, translate (app e1 e2) thread base buf_size = app (translate e1 thread base buf_size) (translate e2 thread base buf_size).
Proof. intros. simpl. reflexivity. Qed.

Fact translate_paire : forall thread base buf_size e1 e2, translate (paire e1 e2) thread base buf_size = paire (translate e1 thread base buf_size) (translate e2 thread base buf_size).
Proof. intros. simpl. reflexivity. Qed.

Fact translate_minus : forall thread base buf_size e1 e2, translate (minus e1 e2) thread base buf_size = app (lam (seq (flush_star thread base buf_size) (var 0))) (minus (translate e1 thread base buf_size) (translate e2 thread base buf_size)).
Proof. intros. simpl. reflexivity. Qed.

Fact translate_modulo : forall thread base buf_size e1 e2, translate (modulo e1 e2) thread base buf_size = app (lam (seq (flush_star thread base buf_size) (var 0))) (modulo (translate e1 thread base buf_size) (translate e2 thread base buf_size)).
Proof. intros. simpl. reflexivity. Qed.

Fact translate_less_than : forall thread base buf_size e1 e2, translate (less_than e1 e2) thread base buf_size = app (lam (seq (flush_star thread base buf_size) (var 0))) (less_than (translate e1 thread base buf_size) (translate e2 thread base buf_size)).
Proof. intros. simpl. reflexivity. Qed.

Fact translate_and : forall thread base buf_size e1 e2, translate (and e1 e2) thread base buf_size = app (lam (seq (flush_star thread base buf_size) (var 0))) (and (translate e1 thread base buf_size) (translate e2 thread base buf_size)).
Proof. intros. simpl. reflexivity. Qed.

Fact translate_not : forall thread base buf_size e, translate (not e) thread base buf_size = app (lam (seq (flush_star thread base buf_size) (var 0))) (not (translate e thread base buf_size)).
Proof. intros. simpl. reflexivity. Qed.

Fact translate_cast : forall thread base buf_size e, translate (cast e) thread base buf_size = app (lam (seq (flush_star thread base buf_size) (var 0))) (cast (translate e thread base buf_size)).
Proof. intros. simpl. reflexivity. Qed.

Fact translate_reference : forall thread base buf_size e, translate (reference e) thread base buf_size = app (lam (seq (flush_star thread base buf_size) (var 0))) (reference (translate e thread base buf_size)).
Proof. intros. simpl. reflexivity. Qed.

Fact translate_first : forall thread base buf_size e, translate (first e) thread base buf_size = app (lam (seq (flush_star thread base buf_size) (var 0))) (first (translate e thread base buf_size)).
Proof. intros. simpl. reflexivity. Qed.

Fact translate_second : forall thread base buf_size e, translate (second e) thread base buf_size = app (lam (seq (flush_star thread base buf_size) (var 0))) (second (translate e thread base buf_size)).
Proof. intros. simpl. reflexivity. Qed.

Fact translate_case : forall thread base buf_size e1 e2 e3, translate (case e1 e2 e3) thread base buf_size = case (translate e1 thread base buf_size) (seq (flush_star thread base buf_size) (translate e2 thread base buf_size)) (seq (flush_star thread base buf_size) (translate e3 thread base buf_size)).
Proof. intros. simpl. reflexivity. Qed.

Fact translate_read : forall thread base buf_size e1 e2, translate (read e1 e2) thread base buf_size = app (lam (seq (flush_star thread base buf_size) (var 0))) (new_read thread base buf_size (translate e1 thread base buf_size)  (translate e2 thread base buf_size)).
Proof. intros. simpl. reflexivity. Qed.

Fact translate_write : forall thread base buf_size e1 e2 e3, translate (write e1 e2 e3) thread base buf_size = app (lam (seq (flush_star thread base buf_size) (var 0))) (new_write thread base buf_size (translate e1 thread base buf_size)  (translate e2 thread base buf_size) (translate e3 thread base buf_size)).
Proof. intros. simpl. reflexivity. Qed.

Fact subst_flush_star1 : forall x v thread base buf_size,
  subst x v (flush_star thread base buf_size) = flush_star thread base buf_size.
Proof. intros. simpl. assert (forall x, (x + 1 = S x)). intros. omega. repeat (rewrite H). destruct thread. simpl. auto. auto. Qed.

Fact subst_flush_star : forall x v thread base buf_size,
  subst x v (lam (flush_star thread base buf_size;; var 0)) = (lam (flush_star thread base buf_size;; var 0)).
Proof. intros. simpl. assert (forall x, (x + 1 = S x)). intros. omega. repeat (rewrite H). destruct thread. simpl. auto. auto. Qed.

Fact new_read_subst_helper : forall x v thread base buf_size, subst x v (lam (read_code thread base buf_size)) = lam (read_code thread base buf_size).
Proof. intros. rewrite subst_lam. unfold read_code. unfold seq. assert (forall x, (x + 1 = S x)). intros. omega. simpl. repeat (rewrite H). destruct thread. simpl. auto. auto. Qed.

Fact new_read_subst : forall x v e1 e2 thread base buf_size,
  new_read thread base buf_size (subst x v e1) (subst x v e2) = subst x v (new_read thread base buf_size e1 e2).
Proof. intros. simpl. assert (forall x, (x + 1 = S x)). intros. omega. repeat (rewrite H). destruct thread. simpl. auto. auto. Qed.

Fact new_write_subst : forall x v e1 e2 e3 thread base buf_size,
  new_write thread base buf_size (subst x v e1) (subst x v e2) (subst x v e3) = subst x v (new_write thread base buf_size e1 e2 e3).
Proof. intros. simpl. assert (forall x, (x + 1 = S x)). intros. omega. repeat (rewrite H). destruct thread. simpl. auto. auto. Qed.

Fixpoint shift_up_n_c n c e  :=
  match n with
    | 0 => e
    | S n => shift_up_n_c n c (shift_up c e)
  end.

Definition shift_up_n n e := shift_up_n_c n 0 e.

Fact shift_up_n_c_array : forall n c k, shift_up_n_c n c (array k) = array k.
Proof. intros. generalize dependent k. generalize dependent c. induction n ; intros.
  + simpl. auto.
  + simpl. rewrite IHn. auto. Qed.

Fact shift_up_n_c_num : forall n c k, shift_up_n_c n c (num k) = num k.
Proof. intros. generalize dependent k. generalize dependent c. induction n ; intros.
  + simpl. auto.
  + simpl. rewrite IHn. auto. Qed.

Fact shift_up_n_c_tru : forall n c, shift_up_n_c n c tru = tru.
Proof. intros. generalize dependent c. induction n ; intros.
  + simpl. auto.
  + simpl. rewrite IHn. auto. Qed.

Fact shift_up_n_c_fls : forall n c, shift_up_n_c n c fls = fls.
Proof. intros. generalize dependent c. induction n ; intros.
  + simpl. auto.
  + simpl. rewrite IHn. auto. Qed.

Fact shift_up_n_c_yunit : forall n c, shift_up_n_c n c yunit = yunit.
Proof. intros. generalize dependent c. induction n ; intros.
  + simpl. auto.
  + simpl. rewrite IHn. auto. Qed.

Fact shift_up_n_c_plus : forall n c e1 e2, shift_up_n_c n c (plus e1 e2) = plus (shift_up_n_c n c e1) (shift_up_n_c n c e2).
Proof. intros. generalize dependent c. generalize dependent e1. generalize dependent e2. induction n ; intros.
  + simpl. auto.
  + simpl. rewrite IHn. auto. Qed.

Fact shift_up_n_c_minus : forall n c e1 e2, shift_up_n_c n c (minus e1 e2) = minus (shift_up_n_c n c e1) (shift_up_n_c n c e2).
Proof. intros. generalize dependent c. generalize dependent e1. generalize dependent e2. induction n ; intros.
  + simpl. auto.
  + simpl. rewrite IHn. auto. Qed.

Fact shift_up_n_c_modulo : forall n c e1 e2, shift_up_n_c n c (modulo e1 e2) = modulo (shift_up_n_c n c e1) (shift_up_n_c n c e2).
Proof. intros. generalize dependent c. generalize dependent e1. generalize dependent e2. induction n ; intros.
  + simpl. auto.
  + simpl. rewrite IHn. auto. Qed.

Fact shift_up_n_c_less_than : forall n c e1 e2, shift_up_n_c n c (less_than e1 e2) = less_than (shift_up_n_c n c e1) (shift_up_n_c n c e2).
Proof. intros. generalize dependent c. generalize dependent e1. generalize dependent e2. induction n ; intros.
  + simpl. auto.
  + simpl. rewrite IHn. auto. Qed.

Fact shift_up_n_c_and : forall n c e1 e2, shift_up_n_c n c (and e1 e2) = and (shift_up_n_c n c e1) (shift_up_n_c n c e2).
Proof. intros. generalize dependent c. generalize dependent e1. generalize dependent e2. induction n ; intros.
  + simpl. auto.
  + simpl. rewrite IHn. auto. Qed.

Fact shift_up_n_c_read : forall n c e1 e2, shift_up_n_c n c (read e1 e2) = read (shift_up_n_c n c e1) (shift_up_n_c n c e2).
Proof. intros. generalize dependent c. generalize dependent e1. generalize dependent e2. induction n ; intros.
  + simpl. auto.
  + simpl. rewrite IHn. auto. Qed.

Fact shift_up_n_c_app : forall n c e1 e2, shift_up_n_c n c (app e1 e2) = app (shift_up_n_c n c e1) (shift_up_n_c n c e2).
Proof. intros. generalize dependent c. generalize dependent e1. generalize dependent e2. induction n ; intros.
  + simpl. auto.
  + simpl. rewrite IHn. auto. Qed.

Fact shift_up_n_c_write : forall n c e1 e2 e3, shift_up_n_c n c (write e1 e2 e3) = write (shift_up_n_c n c e1) (shift_up_n_c n c e2) (shift_up_n_c n c e3).
Proof. intros. generalize dependent c. generalize dependent e1. generalize dependent e2. generalize dependent e3. induction n ; intros.
  + simpl. auto.
  + simpl. rewrite IHn. auto. Qed.

Fact shift_up_n_c_case : forall n c e1 e2 e3, shift_up_n_c n c (case e1 e2 e3) = case (shift_up_n_c n c e1) (shift_up_n_c n c e2) (shift_up_n_c n c e3).
Proof. intros. generalize dependent c. generalize dependent e1. generalize dependent e2. generalize dependent e3. induction n ; intros.
  + simpl. auto.
  + simpl. rewrite IHn. auto. Qed.

Fact shift_up_n_c_paire : forall n c e1 e2, shift_up_n_c n c (paire e1 e2) = paire (shift_up_n_c n c e1) (shift_up_n_c n c e2).
Proof. intros. generalize dependent c. generalize dependent e1. generalize dependent e2. induction n ; intros.
  + simpl. auto.
  + simpl. rewrite IHn. auto. Qed.

Fact shift_up_n_c_cast : forall n c e, shift_up_n_c n c (cast e) = cast (shift_up_n_c n c e).
Proof. intros. generalize dependent c. generalize dependent e. induction n ; intros.
  + simpl. auto.
  + simpl. rewrite IHn. auto. Qed.

Fact shift_up_n_c_not : forall n c e, shift_up_n_c n c (not e) = not (shift_up_n_c n c e).
Proof. intros. generalize dependent c. generalize dependent e. induction n ; intros.
  + simpl. auto.
  + simpl. rewrite IHn. auto. Qed.

Fact shift_up_n_c_reference : forall n c e, shift_up_n_c n c (reference e) = reference (shift_up_n_c n c e).
Proof. intros. generalize dependent c. generalize dependent e. induction n ; intros.
  + simpl. auto.
  + simpl. rewrite IHn. auto. Qed.

Fact shift_up_n_c_first : forall n c e, shift_up_n_c n c (first e) = first (shift_up_n_c n c e).
Proof. intros. generalize dependent c. generalize dependent e. induction n ; intros.
  + simpl. auto.
  + simpl. rewrite IHn. auto. Qed.

Fact shift_up_n_c_second : forall n c e, shift_up_n_c n c (second e) = second (shift_up_n_c n c e).
Proof. intros. generalize dependent c. generalize dependent e. induction n ; intros.
  + simpl. auto.
  + simpl. rewrite IHn. auto. Qed.


Fact shift_up_n_c_lam : forall n c e, shift_up_n_c n c (lam e) = lam (shift_up_n_c n (c+1) e).
Proof. intros. generalize dependent e. generalize dependent c. induction n ; intros.
  + simpl. auto.
  + simpl. rewrite IHn. auto. Qed.

Fact shift_up_n_c_var1 : forall n c k, k < c -> shift_up_n_c n c (var k) = var k.
Proof. intros. generalize dependent k. generalize dependent c. induction n ; intros.
  + simpl. auto.
  + simpl. destruct (k <? c) eqn:ORIG.
    ++ apply Nat.ltb_lt in ORIG. apply IHn. auto.
    ++ apply Nat.ltb_lt in H. rewrite H in ORIG. inversion ORIG. Qed.

Fact shift_up_n_c_var2 : forall n c k, k >= c -> shift_up_n_c n c (var k) = var (n+k).
Proof. intros. generalize dependent k. generalize dependent c. induction n ; intros.
  + simpl. auto.
  + simpl. destruct (k <? c) eqn:ORIG.
    ++ apply Nat.ltb_lt in ORIG. omega.
    ++ rewrite IHn. assert (n+(k+1) = S(n+k)). omega. rewrite H0. auto. omega. Qed.


Fact shift_up_n_eq : forall n c e, shift_up_n_c (n + 1) c e = shift_up (n+c) (shift_up_n_c n c e).
Proof. intros. generalize dependent c. generalize dependent n. induction e ; intros.
  + rewrite shift_up_n_c_array. rewrite shift_up_n_c_array. simpl. auto.
  + rewrite shift_up_n_c_num. rewrite shift_up_n_c_num. simpl. auto.
  + rewrite shift_up_n_c_plus. rewrite shift_up_n_c_plus. rewrite IHe1. rewrite IHe2. simpl. auto.
  + rewrite shift_up_n_c_minus. rewrite shift_up_n_c_minus. rewrite IHe1. rewrite IHe2. simpl. auto.
  + rewrite shift_up_n_c_modulo. rewrite shift_up_n_c_modulo. rewrite IHe1. rewrite IHe2. simpl. auto.
  + rewrite shift_up_n_c_tru. rewrite shift_up_n_c_tru. simpl. auto.
  + rewrite shift_up_n_c_fls. rewrite shift_up_n_c_fls. simpl. auto.
  + rewrite shift_up_n_c_less_than. rewrite shift_up_n_c_less_than. rewrite IHe1. rewrite IHe2. simpl. auto. 
  + rewrite shift_up_n_c_not. rewrite shift_up_n_c_not. rewrite IHe. simpl. auto.
  + rewrite shift_up_n_c_and. rewrite shift_up_n_c_and. rewrite IHe1. rewrite IHe2. simpl. auto.
  + rewrite shift_up_n_c_yunit. rewrite shift_up_n_c_yunit. simpl. auto.
  + rewrite shift_up_n_c_read. rewrite shift_up_n_c_read. rewrite IHe1. rewrite IHe2. simpl. auto.
  + rewrite shift_up_n_c_write. rewrite shift_up_n_c_write. rewrite IHe1. rewrite IHe2. rewrite IHe3. simpl. auto.
  + rewrite shift_up_n_c_reference. rewrite shift_up_n_c_reference. rewrite IHe. simpl. auto.
  + rewrite shift_up_n_c_cast. rewrite shift_up_n_c_cast. rewrite IHe. simpl. auto.
  + rewrite shift_up_n_c_case. rewrite shift_up_n_c_case. rewrite IHe1. rewrite IHe2. rewrite IHe3. simpl. auto.
  + destruct (n <? c) eqn:ORIG. apply Nat.ltb_lt in ORIG. rewrite shift_up_n_c_var1. rewrite shift_up_n_c_var1. simpl. destruct (n <? n0 + c) eqn:ORIG1. apply Nat.ltb_lt in ORIG1. auto. assert (n < n0 + c -> False). intros. apply Nat.ltb_lt in H. rewrite H in ORIG1. inversion ORIG1. contradiction H. omega. auto. auto. assert (n <  c -> False). intros. apply Nat.ltb_lt in H. rewrite ORIG in H. inversion H. assert (n >= c). omega. rewrite shift_up_n_c_var2. rewrite shift_up_n_c_var2. simpl. destruct (n0 + n <? n0 + c) eqn:ORIG1. rewrite Nat.ltb_lt in ORIG1. omega. assert (n0+1+n=n0+n+1). omega. rewrite H1. auto. auto. auto.
  + rewrite shift_up_n_c_app. rewrite shift_up_n_c_app. rewrite IHe1. rewrite IHe2. simpl. auto.
  + rewrite shift_up_n_c_lam. rewrite shift_up_n_c_lam. assert (n+1=S n). omega. repeat (rewrite H in *). simpl. assert (shift_up_n_c (n + 1) (c+1) e =
shift_up (n + (c + 1)) (shift_up_n_c n (c + 1) e)). apply IHe. assert (n+c+1=n+(c+1)). omega. rewrite H1 in *. rewrite <- H0. assert (n+1=S n). omega. rewrite H2 in *. simpl. auto.
  + rewrite shift_up_n_c_paire. rewrite shift_up_n_c_paire. rewrite IHe1. rewrite IHe2. simpl. auto.
  + rewrite shift_up_n_c_first. rewrite shift_up_n_c_first. rewrite IHe. simpl. auto.
  + rewrite shift_up_n_c_second. rewrite shift_up_n_c_second. rewrite IHe. simpl. auto.
Qed.

Fact foo : forall n e, shift_up_n_c (S n) 0 e = shift_up 0 (shift_up_n_c n 0 e).
Proof. intros. generalize dependent e. induction n ; intros ; simpl.
  + auto.
  + rewrite <- IHn. simpl. auto. Qed.

Fact blah : forall x v e c, subst (x + (c+1)) (shift_up_n (c+1) v) (shift_up c e) =
shift_up c (subst (x + c) (shift_up_n c v) e).
Proof. intros. generalize dependent x. generalize dependent v. generalize dependent c. induction e ; intros ; simpl ; try auto ; try (rewrite IHe1 ; rewrite IHe2 ; auto); try (rewrite IHe3 ; auto) ; try (rewrite IHe ; auto). destruct (n =? x + c) eqn:ORIG. apply beq_nat_true in ORIG. subst. destruct (x + c <? c) eqn:ORIG. rewrite Nat.ltb_lt in ORIG. omega. simpl. destruct (x + c + 1 =? x + (c + 1)) eqn:ORIG1. apply beq_nat_true in ORIG1. unfold shift_up_n. rewrite shift_up_n_eq. assert (c+0=c). omega. rewrite H. auto. apply beq_nat_false in ORIG1. contradiction ORIG1. omega. destruct (n <? c) eqn:ORIG1. apply Nat.ltb_lt in ORIG1. simpl. destruct ( n =? x + (c + 1)) eqn:ORIG2. apply beq_nat_true in ORIG2. subst. omega. destruct (n <? c) eqn:ORIG3. auto. assert ((n <? c) = true -> False). intros. rewrite ORIG3 in H. inversion H. assert ((n <? c) = true). apply Nat.ltb_lt. auto. apply H in H0. contradiction. simpl. destruct (n + 1 =? x + (c + 1)) eqn:ORIG2. apply beq_nat_true in ORIG2. assert (n=x+c). omega. subst. apply beq_nat_false in ORIG. contradiction ORIG. auto. destruct (n <? c) eqn:ORIG3. inversion ORIG1. auto. unfold shift_up_n in *. rewrite <- foo. rewrite <- foo. assert (x+(c+1)+1=x+((c+1)+1)). omega. rewrite H. clear H. assert (S (c+1) = (c+1)+1). omega. rewrite H. clear H. rewrite IHe. assert (x+(c+1)=x+c+1). omega. rewrite H. auto. clear H. assert (c+1=S c). omega. rewrite H. auto. Qed.


Fact helper : forall x v e, subst (x + 1) (shift_up 0 v) (shift_up 0 e) = shift_up 0 (subst x v e).
Proof. intros. intros. generalize dependent x. generalize dependent v. induction e ; intros ; simpl ; auto ; try (rewrite IHe1 ; rewrite IHe2 ; auto) ; try (rewrite IHe3 ; auto) ; try (rewrite IHe ; auto).
  + destruct (n + 1 =? x + 1) eqn:ORIG.
    ++ apply beq_nat_true in ORIG. assert (n=x). omega. subst. destruct (x =? x) eqn:ORIG1. auto. apply beq_nat_false in ORIG1. contradiction ORIG1. auto.
    ++ apply beq_nat_false in ORIG. assert (n <> x). omega. destruct (n =? x) eqn:ORIG1. apply beq_nat_true in ORIG1. subst. contradiction H. auto. simpl. auto.
  + assert (shift_up 0 (shift_up 0 v) = shift_up_n_c (1+1) 0 v). rewrite foo. rewrite foo. simpl. auto. rewrite H. clear H. assert (shift_up_n_c (1 + 1) 0 v = shift_up_n (1+1) v). unfold shift_up_n. auto. rewrite H. clear H. assert (x+1+1=x+(1+1)). omega. rewrite H. rewrite blah.
simpl. unfold shift_up_n. simpl. auto. Qed.

Fact seq_subst : forall x v e e', subst x v (e;;e') = ((subst x v e) ;; (subst x v e')).
Proof. intros. unfold seq. rewrite subst_app. rewrite subst_lam. rewrite helper. auto. Qed.

Fact shift_up_flush_star1 : forall c thread base buf_size,
  shift_up c(flush_star thread base buf_size) = flush_star thread base buf_size.
Proof. intros. simpl. assert (forall x, (x + 1 = S x)). intros. omega. repeat (rewrite H). destruct thread. simpl. auto. auto. Qed.

Fact shift_up_new_read_star1 : forall c thread base buf_size e1 e2,
  shift_up c (new_read thread base buf_size e1 e2) = new_read thread base buf_size  (shift_up c e1) (shift_up c e2).
Proof. intros. unfold new_read. unfold read_code. simpl. assert (forall x, (x + 1 = S x)). intros. omega. repeat (rewrite H). destruct thread. simpl. auto. auto. Qed.

Fact shift_up_new_write_star1 : forall c thread base buf_size e1 e2 e3,
  shift_up c (new_write thread base buf_size e1 e2 e3) = new_write thread base buf_size  (shift_up c e1) (shift_up c e2) (shift_up c e3).
Proof. intros. unfold new_write. unfold write_code. simpl. assert (forall x, (x + 1 = S x)). intros. omega. repeat (rewrite H). destruct thread. simpl. auto. auto. Qed.

Fact foo1 : forall c k e, shift_up (c + k + 1) (shift_up k e) = shift_up k (shift_up (c + k) e).
Proof. intros. generalize dependent c. generalize dependent k. induction e ; intros ; simpl ; auto ; try (rewrite IHe1 ; rewrite IHe2 ; auto) ; try (rewrite IHe3 ; auto) ; try (rewrite IHe ; auto). 
  + destruct (n <? k) eqn:ORIG.
    ++ assert (COPY:=ORIG). apply Nat.ltb_lt in ORIG. assert (n  <? c + k = true). apply Nat.ltb_lt. omega. rewrite H. apply Nat.ltb_lt in H. simpl. rewrite COPY. assert (n <? c+k+1 = true). apply Nat.ltb_lt. omega. rewrite H0. auto.
    ++ simpl. destruct (n + 1 <? c + k + 1) eqn:ORIG1. apply Nat.ltb_lt in ORIG1. assert (n <? c+k = true). apply Nat.ltb_lt. omega. rewrite H. simpl. destruct (n <? k) eqn:ORIG2. inversion ORIG. auto. assert (n + 1 <? c + k + 1 = true -> False). intros. rewrite ORIG1 in H. inversion H. destruct (n <? c + k) eqn:ORIG2. contradiction H. apply Nat.ltb_lt. apply Nat.ltb_lt in ORIG2. omega. simpl. destruct (n + 1 <? k) eqn:ORIG3. apply Nat.ltb_lt in ORIG3. assert (n<k -> False). intros. apply Nat.ltb_lt in H0. rewrite ORIG in H0. inversion H0. clear ORIG1. contradiction H0. omega. auto.
  + assert (c+k+1+1=c+(k+1)+1). omega. rewrite H. rewrite IHe. assert (c+(k+1)=c+k+1). omega. rewrite H0. auto. Qed.

Fact shift_up_seq : forall c e1 e2 , shift_up c (e1;;e2) = ((shift_up c e1);;(shift_up c e2)).
Proof. intros. unfold seq. rewrite shift_up_app. rewrite shift_up_lam. assert (shift_up (c + 1) (shift_up 0 e2) = shift_up 0 (shift_up c e2)). assert (c+0+1=c+1). omega. rewrite <- H. rewrite foo1. assert (c+0=c). omega. rewrite H0. auto. rewrite H. auto. Qed.

Fact shift_commutes_with_translate : forall c e thread base buf_size, translate (shift_up c e) thread base buf_size = shift_up c (translate e thread base buf_size).
Proof. intros. generalize dependent c; induction e ; intros.
  + simpl. auto.
  + simpl. auto.
  + rewrite shift_up_plus. rewrite translate_plus. rewrite translate_plus. rewrite shift_up_app. rewrite shift_up_plus. rewrite shift_up_lam. rewrite shift_up_seq. rewrite shift_up_flush_star1. rewrite IHe1. rewrite IHe2. destruct c; simpl ; auto.
  + rewrite shift_up_minus. rewrite translate_minus. rewrite translate_minus. rewrite shift_up_app. rewrite shift_up_minus. rewrite shift_up_lam. rewrite shift_up_seq. rewrite shift_up_flush_star1. rewrite IHe1. rewrite IHe2. simpl. destruct c; simpl ; auto.
  + rewrite shift_up_modulo. rewrite translate_modulo. rewrite translate_modulo. rewrite shift_up_app. rewrite shift_up_modulo. rewrite shift_up_lam. rewrite shift_up_seq. rewrite shift_up_flush_star1. rewrite IHe1. rewrite IHe2. destruct c; simpl ; auto.
  + simpl. auto.
  + simpl. auto.
  + rewrite shift_up_less_than. rewrite translate_less_than. rewrite translate_less_than. rewrite shift_up_app. rewrite shift_up_less_than. rewrite shift_up_lam. rewrite shift_up_seq. rewrite shift_up_flush_star1. rewrite IHe1. rewrite IHe2. destruct c; simpl ; auto.
  + rewrite shift_up_not. rewrite translate_not. rewrite translate_not. rewrite shift_up_app. rewrite shift_up_not. rewrite shift_up_lam. rewrite shift_up_seq. rewrite shift_up_flush_star1. rewrite IHe. destruct c; simpl ; auto.
  + rewrite shift_up_and. rewrite translate_and. rewrite translate_and. rewrite shift_up_app. rewrite shift_up_and. rewrite shift_up_lam. rewrite shift_up_seq. rewrite shift_up_flush_star1. rewrite IHe1. rewrite IHe2. simpl. destruct c; simpl ; auto.
  + simpl. auto.
  + rewrite shift_up_read. rewrite translate_read. rewrite translate_read. rewrite shift_up_app. rewrite IHe1. rewrite IHe2. rewrite shift_up_new_read_star1. rewrite shift_up_lam. rewrite shift_up_seq. rewrite shift_up_flush_star1. destruct c; simpl ; auto.
  + rewrite shift_up_write. rewrite translate_write. rewrite translate_write. rewrite shift_up_app. rewrite IHe1. rewrite IHe2. rewrite IHe3. rewrite shift_up_new_write_star1. rewrite shift_up_lam. rewrite shift_up_seq. rewrite shift_up_flush_star1. simpl (shift_up (0 + 1) (var 0)). destruct c; simpl ; auto.
  + rewrite shift_up_reference. rewrite translate_reference. rewrite translate_reference. rewrite shift_up_app. rewrite shift_up_reference. rewrite shift_up_lam. rewrite shift_up_seq. rewrite shift_up_flush_star1. rewrite IHe. destruct c; simpl ; auto.
  + rewrite shift_up_cast. rewrite translate_cast. rewrite translate_cast. rewrite shift_up_app. rewrite shift_up_cast. rewrite shift_up_lam. rewrite shift_up_seq. rewrite shift_up_flush_star1. rewrite IHe. destruct c; simpl ; auto.
  + rewrite shift_up_case. rewrite translate_case. rewrite translate_case. rewrite shift_up_case. rewrite shift_up_seq. rewrite shift_up_flush_star1. rewrite shift_up_seq. rewrite shift_up_flush_star1. rewrite IHe1. rewrite IHe2. rewrite IHe3. destruct c; simpl ; auto.
  + simpl. destruct (n <? c); simpl ; auto.
  + rewrite shift_up_app. rewrite translate_app. rewrite translate_app. rewrite shift_up_app. rewrite IHe1. rewrite IHe2. destruct c; simpl ; auto.
  + rewrite shift_up_lam. rewrite translate_lam. rewrite translate_lam. rewrite shift_up_lam. rewrite shift_up_seq. rewrite shift_up_flush_star1. rewrite IHe. auto.
  + rewrite shift_up_paire. rewrite translate_paire. rewrite translate_paire. rewrite shift_up_paire. rewrite IHe1. rewrite IHe2. destruct c; simpl ; auto.
  + rewrite shift_up_first. rewrite translate_first. rewrite translate_first. rewrite shift_up_app. rewrite shift_up_first. rewrite shift_up_lam. rewrite shift_up_seq. rewrite shift_up_flush_star1. rewrite IHe. destruct c; simpl ; auto.
  + rewrite shift_up_second. rewrite translate_second. rewrite translate_second. rewrite shift_up_app. rewrite shift_up_second. rewrite shift_up_lam. rewrite shift_up_seq. rewrite shift_up_flush_star1. rewrite IHe. destruct c; simpl ; auto. Qed.

Fact seq_flush_subst : forall x v thread base buf_size e, subst x v (flush_star thread base buf_size;; e) =  (flush_star thread base buf_size;; (subst x v e)).
Proof. intros. rewrite seq_subst. rewrite subst_flush_star1. auto. Qed.

Fact trans_subst : forall x v e thread base buf_size, 
  translate (subst x v e) thread base buf_size = subst x (translate v thread base buf_size) (translate e thread base buf_size).
Proof. intros. generalize dependent v. generalize dependent x. induction e ; intros.
  + rewrite subst_array. simpl. reflexivity.
  + rewrite subst_num. simpl. reflexivity.
  + rewrite subst_plus. rewrite translate_plus. rewrite translate_plus. rewrite subst_app. rewrite subst_plus. rewrite IHe1. rewrite IHe2. rewrite subst_flush_star. reflexivity.
  + rewrite subst_minus. rewrite translate_minus. rewrite translate_minus. rewrite subst_app. rewrite subst_minus. rewrite IHe1. rewrite IHe2. rewrite subst_flush_star. reflexivity.
  + rewrite subst_modulo. rewrite translate_modulo. rewrite translate_modulo. rewrite subst_app. rewrite subst_modulo. rewrite IHe1. rewrite IHe2. rewrite subst_flush_star. reflexivity.
  + rewrite subst_tru. simpl. reflexivity.
  + rewrite subst_fls. simpl. reflexivity.
  + rewrite subst_less_than. rewrite translate_less_than. rewrite translate_less_than. rewrite subst_app. rewrite subst_less_than. rewrite IHe1. rewrite IHe2. rewrite subst_flush_star. reflexivity.
  + rewrite subst_not. rewrite translate_not. rewrite translate_not. rewrite subst_app. rewrite subst_not. rewrite IHe. rewrite subst_flush_star. reflexivity.
  + rewrite subst_and. rewrite translate_and. rewrite translate_and. rewrite subst_app. rewrite subst_and. rewrite IHe1. rewrite IHe2. rewrite subst_flush_star. reflexivity.
  + rewrite subst_yunit. simpl. reflexivity.
  + rewrite subst_read. rewrite translate_read. rewrite translate_read. rewrite subst_app. rewrite IHe1. rewrite IHe2. rewrite subst_flush_star. rewrite new_read_subst. auto.
  + rewrite subst_write. rewrite translate_write. rewrite translate_write. rewrite subst_app. rewrite IHe1. rewrite IHe2. rewrite IHe3. rewrite subst_flush_star. rewrite new_write_subst. auto.
  + rewrite subst_reference. rewrite translate_reference. rewrite translate_reference. rewrite subst_app. rewrite subst_reference. rewrite IHe. rewrite subst_flush_star. reflexivity.
  + rewrite subst_cast. rewrite translate_cast. rewrite translate_cast. rewrite subst_app. rewrite subst_cast. rewrite IHe. rewrite subst_flush_star. reflexivity.
  + rewrite subst_case. rewrite translate_case. rewrite translate_case. rewrite subst_case. rewrite IHe1. rewrite IHe2. rewrite IHe3. rewrite seq_flush_subst. rewrite seq_flush_subst. auto.
  + rewrite subst_var. simpl. destruct (n =? x). auto. simpl. auto.
  + rewrite subst_app. rewrite translate_app. rewrite IHe1. rewrite IHe2. reflexivity.
  + rewrite subst_lam. rewrite translate_lam. rewrite translate_lam. rewrite subst_lam. rewrite seq_subst. rewrite subst_flush_star1. rewrite IHe. rewrite shift_commutes_with_translate. auto.
  + rewrite subst_paire. rewrite translate_paire. rewrite translate_paire. rewrite subst_paire. rewrite IHe1. rewrite IHe2. reflexivity.
  + rewrite subst_first. rewrite translate_first. rewrite translate_first. rewrite subst_app. rewrite subst_first. rewrite IHe. rewrite subst_flush_star. reflexivity.
  + rewrite subst_second. rewrite translate_second. rewrite translate_second. rewrite subst_app. rewrite subst_second. rewrite IHe. rewrite subst_flush_star. reflexivity.
Qed.

Fact translation_of_value_is_value : forall v thread base buf_size,
    value v -> value (translate v thread base buf_size).
Proof. intros. induction H; simpl.
  + apply value_array.
  + apply value_num.
  + apply value_yunit.
  + apply value_tru.
  + apply value_fls.
  + apply value_lam.
  + apply value_paire. auto. auto. Qed.


Fact translation_of_context_steps : forall e e' b B buf_size f m' m'0 l l' thread E u v u' v',
(forall t, u t = if thread_equals t thread then translate e b B buf_size else f t) ->
(forall t, v t = if thread_equals t thread then translate e' b B buf_size else f t) ->
(forall t, u' t = if thread_equals t thread then translate (con_subst E e) b B buf_size else f t) ->
(forall t, v' t = if thread_equals t thread then translate (con_subst E e') b B buf_size else f t) ->
SC_program_steps (l, u, m') (l', v, m'0) ->
SC_program_steps (l, u', m') (l', v', m'0).
Proof. intros. generalize dependent l. generalize dependent l'. generalize dependent u. generalize dependent u'. generalize dependent v. generalize dependent v'. induction E; intros; try (remember (fun t => if thread_equals t thread then translate (con_subst E e) b B buf_size else f t) as threads; remember (fun t => if thread_equals t thread then translate (con_subst E e') b B buf_size else f t) as threads'); simpl in *.
  + apply program_steps_same with (u:=u) (v:=v). auto. intros. rewrite H. rewrite H1. auto. intros. rewrite H0. rewrite H2. auto.
  + apply steps_app_left with (threads:=threads) (threads':=threads') (thread:=thread) (e2:=translate t b B buf_size).
    ++ apply IHE with (u:=u) (v:=v). rewrite Heqthreads'. auto. auto. rewrite Heqthreads. auto. auto. auto.
    ++ intros. destruct (thread_equals t0 thread) eqn:ORIG.
       +++ rewrite Heqthreads. rewrite ORIG. rewrite H1. rewrite ORIG. auto.
       +++ rewrite Heqthreads. rewrite ORIG. rewrite H1. rewrite ORIG. auto.
    ++ intros. destruct (thread_equals t0 thread) eqn:ORIG.
       +++ rewrite Heqthreads'. rewrite ORIG. rewrite H2. rewrite ORIG. auto.
       +++ rewrite Heqthreads'. rewrite ORIG. rewrite H2. rewrite ORIG. auto.
  + destruct s. destruct e0. subst x. rewrite translate_app in *. rewrite translate_lam in *. apply steps_app_right with (threads:=threads) (threads':=threads') (thread:=thread) (e2:=flush_star b B buf_size;; translate x0 b B buf_size).
    ++ apply IHE with (u:=u) (v:=v). rewrite Heqthreads'. auto. auto. rewrite Heqthreads. auto. auto. auto.
    ++ intros. destruct (thread_equals t thread) eqn:ORIG.
       +++ rewrite Heqthreads. rewrite ORIG. rewrite H1. rewrite ORIG. auto.
       +++ rewrite Heqthreads. rewrite ORIG. rewrite H1. rewrite ORIG. auto.
    ++ intros. destruct (thread_equals t thread) eqn:ORIG.
       +++ rewrite Heqthreads'. rewrite ORIG. rewrite H2. rewrite ORIG. auto.
       +++ rewrite Heqthreads'. rewrite ORIG. rewrite H2. rewrite ORIG. auto.
  + remember (fun t0 => if thread_equals t0 thread then plus (translate (con_subst E e) b B buf_size) (translate t b B buf_size) else f t0) as threads''; remember (fun t0 => if thread_equals t0 thread then plus (translate (con_subst E e') b B buf_size) (translate t b B buf_size) else f t0) as threads'''. apply steps_app_right with (threads:=threads'') (threads':=threads''') (thread:=thread) (e2:=flush_star b B buf_size;; var 0).
    ++ apply steps_plus_left with (threads:=threads) (threads':=threads') (thread:=thread) (e2:=translate t b B buf_size). apply IHE with (u:=u) (v:=v). rewrite Heqthreads'. auto. auto. rewrite Heqthreads. auto. auto. auto. rewrite Heqthreads''. rewrite Heqthreads. intros. destruct (thread_equals t0 thread). auto. auto. rewrite Heqthreads'''. rewrite Heqthreads'. intros. destruct (thread_equals t0 thread). auto. auto.
    ++ intros. destruct (thread_equals t0 thread) eqn:ORIG.
       +++ rewrite Heqthreads''. rewrite ORIG. rewrite H1. rewrite ORIG. auto.
       +++ rewrite Heqthreads''. rewrite ORIG. rewrite H1. rewrite ORIG. auto.
    ++ intros. destruct (thread_equals t0 thread) eqn:ORIG.
       +++ rewrite Heqthreads'''. rewrite ORIG. rewrite H2. rewrite ORIG. auto.
       +++ rewrite Heqthreads'''. rewrite ORIG. rewrite H2. rewrite ORIG. auto.
  + destruct s. destruct e0. subst x. rewrite translate_plus in *. rewrite translate_num in *. remember (fun t0 => if thread_equals t0 thread then plus (num x0) (translate (con_subst E e) b B buf_size) else f t0) as threads''; remember (fun t0 => if thread_equals t0 thread then plus (num x0) (translate (con_subst E e') b B buf_size)else f t0) as threads'''. apply steps_app_right with (threads:=threads'') (threads':=threads''') (thread:=thread) (e2:=flush_star b B buf_size;; var 0).
    ++ apply steps_plus_right with (threads:=threads) (threads':=threads') (thread:=thread) (e2:=x0). apply IHE with (u:=u) (v:=v). rewrite Heqthreads'. auto. auto. rewrite Heqthreads. auto. auto. auto. rewrite Heqthreads''. rewrite Heqthreads. intros. destruct (thread_equals t thread). auto. auto. rewrite Heqthreads'''. rewrite Heqthreads'. intros. destruct (thread_equals t thread). auto. auto.
    ++ intros. destruct (thread_equals t thread) eqn:ORIG.
       +++ rewrite Heqthreads''. rewrite ORIG. rewrite H1. rewrite ORIG. auto.
       +++ rewrite Heqthreads''. rewrite ORIG. rewrite H1. rewrite ORIG. auto.
    ++ intros. destruct (thread_equals t thread) eqn:ORIG.
       +++ rewrite Heqthreads'''. rewrite ORIG. rewrite H2. rewrite ORIG. auto.
       +++ rewrite Heqthreads'''. rewrite ORIG. rewrite H2. rewrite ORIG. auto.
  + remember (fun t0 => if thread_equals t0 thread then minus (translate (con_subst E e) b B buf_size) (translate t b B buf_size) else f t0) as threads''; remember (fun t0 => if thread_equals t0 thread then minus (translate (con_subst E e') b B buf_size) (translate t b B buf_size) else f t0) as threads'''. apply steps_app_right with (threads:=threads'') (threads':=threads''') (thread:=thread) (e2:=flush_star b B buf_size;; var 0).
    ++ apply steps_minus_left with (threads:=threads) (threads':=threads') (thread:=thread) (e2:=translate t b B buf_size). apply IHE with (u:=u) (v:=v). rewrite Heqthreads'. auto. auto. rewrite Heqthreads. auto. auto. auto. rewrite Heqthreads''. rewrite Heqthreads. intros. destruct (thread_equals t0 thread). auto. auto. rewrite Heqthreads'''. rewrite Heqthreads'. intros. destruct (thread_equals t0 thread). auto. auto.
    ++ intros. destruct (thread_equals t0 thread) eqn:ORIG.
       +++ rewrite Heqthreads''. rewrite ORIG. rewrite H1. rewrite ORIG. auto.
       +++ rewrite Heqthreads''. rewrite ORIG. rewrite H1. rewrite ORIG. auto.
    ++ intros. destruct (thread_equals t0 thread) eqn:ORIG.
       +++ rewrite Heqthreads'''. rewrite ORIG. rewrite H2. rewrite ORIG. auto.
       +++ rewrite Heqthreads'''. rewrite ORIG. rewrite H2. rewrite ORIG. auto.
  + destruct s. destruct e0. subst x. rewrite translate_minus in *. rewrite translate_num in *. remember (fun t0 => if thread_equals t0 thread then minus (num x0) (translate (con_subst E e) b B buf_size) else f t0) as threads''; remember (fun t0 => if thread_equals t0 thread then minus (num x0) (translate (con_subst E e') b B buf_size)else f t0) as threads'''. apply steps_app_right with (threads:=threads'') (threads':=threads''') (thread:=thread) (e2:=flush_star b B buf_size;; var 0).
    ++ apply steps_minus_right with (threads:=threads) (threads':=threads') (thread:=thread) (e2:=x0). apply IHE with (u:=u) (v:=v). rewrite Heqthreads'. auto. auto. rewrite Heqthreads. auto. auto. auto. rewrite Heqthreads''. rewrite Heqthreads. intros. destruct (thread_equals t thread). auto. auto. rewrite Heqthreads'''. rewrite Heqthreads'. intros. destruct (thread_equals t thread). auto. auto.
    ++ intros. destruct (thread_equals t thread) eqn:ORIG.
       +++ rewrite Heqthreads''. rewrite ORIG. rewrite H1. rewrite ORIG. auto.
       +++ rewrite Heqthreads''. rewrite ORIG. rewrite H1. rewrite ORIG. auto.
    ++ intros. destruct (thread_equals t thread) eqn:ORIG.
       +++ rewrite Heqthreads'''. rewrite ORIG. rewrite H2. rewrite ORIG. auto.
       +++ rewrite Heqthreads'''. rewrite ORIG. rewrite H2. rewrite ORIG. auto.
  + remember (fun t0 => if thread_equals t0 thread then modulo (translate (con_subst E e) b B buf_size) (translate t b B buf_size) else f t0) as threads''; remember (fun t0 => if thread_equals t0 thread then modulo (translate (con_subst E e') b B buf_size) (translate t b B buf_size) else f t0) as threads'''. apply steps_app_right with (threads:=threads'') (threads':=threads''') (thread:=thread) (e2:=flush_star b B buf_size;; var 0).
    ++ apply steps_modulo_left with (threads:=threads) (threads':=threads') (thread:=thread) (e2:=translate t b B buf_size). apply IHE with (u:=u) (v:=v). rewrite Heqthreads'. auto. auto. rewrite Heqthreads. auto. auto. auto. rewrite Heqthreads''. rewrite Heqthreads. intros. destruct (thread_equals t0 thread). auto. auto. rewrite Heqthreads'''. rewrite Heqthreads'. intros. destruct (thread_equals t0 thread). auto. auto.
    ++ intros. destruct (thread_equals t0 thread) eqn:ORIG.
       +++ rewrite Heqthreads''. rewrite ORIG. rewrite H1. rewrite ORIG. auto.
       +++ rewrite Heqthreads''. rewrite ORIG. rewrite H1. rewrite ORIG. auto.
    ++ intros. destruct (thread_equals t0 thread) eqn:ORIG.
       +++ rewrite Heqthreads'''. rewrite ORIG. rewrite H2. rewrite ORIG. auto.
       +++ rewrite Heqthreads'''. rewrite ORIG. rewrite H2. rewrite ORIG. auto.
  + destruct s. destruct e0. subst x. rewrite translate_modulo in *. rewrite translate_num in *. remember (fun t0 => if thread_equals t0 thread then modulo (num x0) (translate (con_subst E e) b B buf_size) else f t0) as threads''; remember (fun t0 => if thread_equals t0 thread then modulo (num x0) (translate (con_subst E e') b B buf_size)else f t0) as threads'''. apply steps_app_right with (threads:=threads'') (threads':=threads''') (thread:=thread) (e2:=flush_star b B buf_size;; var 0).
    ++ apply steps_modulo_right with (threads:=threads) (threads':=threads') (thread:=thread) (e2:=x0). apply IHE with (u:=u) (v:=v). rewrite Heqthreads'. auto. auto. rewrite Heqthreads. auto. auto. auto. rewrite Heqthreads''. rewrite Heqthreads. intros. destruct (thread_equals t thread). auto. auto. rewrite Heqthreads'''. rewrite Heqthreads'. intros. destruct (thread_equals t thread). auto. auto.
    ++ intros. destruct (thread_equals t thread) eqn:ORIG.
       +++ rewrite Heqthreads''. rewrite ORIG. rewrite H1. rewrite ORIG. auto.
       +++ rewrite Heqthreads''. rewrite ORIG. rewrite H1. rewrite ORIG. auto.
    ++ intros. destruct (thread_equals t thread) eqn:ORIG.
       +++ rewrite Heqthreads'''. rewrite ORIG. rewrite H2. rewrite ORIG. auto.
       +++ rewrite Heqthreads'''. rewrite ORIG. rewrite H2. rewrite ORIG. auto.
  + remember (fun t0 => if thread_equals t0 thread then less_than (translate (con_subst E e) b B buf_size) (translate t b B buf_size) else f t0) as threads''; remember (fun t0 => if thread_equals t0 thread then less_than (translate (con_subst E e') b B buf_size) (translate t b B buf_size) else f t0) as threads'''. apply steps_app_right with (threads:=threads'') (threads':=threads''') (thread:=thread) (e2:=flush_star b B buf_size;; var 0).
    ++ apply steps_less_than_left with (threads:=threads) (threads':=threads') (thread:=thread) (e2:=translate t b B buf_size). apply IHE with (u:=u) (v:=v). rewrite Heqthreads'. auto. auto. rewrite Heqthreads. auto. auto. auto. rewrite Heqthreads''. rewrite Heqthreads. intros. destruct (thread_equals t0 thread). auto. auto. rewrite Heqthreads'''. rewrite Heqthreads'. intros. destruct (thread_equals t0 thread). auto. auto.
    ++ intros. destruct (thread_equals t0 thread) eqn:ORIG.
       +++ rewrite Heqthreads''. rewrite ORIG. rewrite H1. rewrite ORIG. auto.
       +++ rewrite Heqthreads''. rewrite ORIG. rewrite H1. rewrite ORIG. auto.
    ++ intros. destruct (thread_equals t0 thread) eqn:ORIG.
       +++ rewrite Heqthreads'''. rewrite ORIG. rewrite H2. rewrite ORIG. auto.
       +++ rewrite Heqthreads'''. rewrite ORIG. rewrite H2. rewrite ORIG. auto.
  + destruct s. destruct e0. subst x. rewrite translate_less_than in *. rewrite translate_num in *. remember (fun t0 => if thread_equals t0 thread then less_than (num x0) (translate (con_subst E e) b B buf_size) else f t0) as threads''; remember (fun t0 => if thread_equals t0 thread then less_than (num x0) (translate (con_subst E e') b B buf_size)else f t0) as threads'''. apply steps_app_right with (threads:=threads'') (threads':=threads''') (thread:=thread) (e2:=flush_star b B buf_size;; var 0).
    ++ apply steps_less_than_right with (threads:=threads) (threads':=threads') (thread:=thread) (e2:=x0). apply IHE with (u:=u) (v:=v). rewrite Heqthreads'. auto. auto. rewrite Heqthreads. auto. auto. auto. rewrite Heqthreads''. rewrite Heqthreads. intros. destruct (thread_equals t thread). auto. auto. rewrite Heqthreads'''. rewrite Heqthreads'. intros. destruct (thread_equals t thread). auto. auto.
    ++ intros. destruct (thread_equals t thread) eqn:ORIG.
       +++ rewrite Heqthreads''. rewrite ORIG. rewrite H1. rewrite ORIG. auto.
       +++ rewrite Heqthreads''. rewrite ORIG. rewrite H1. rewrite ORIG. auto.
    ++ intros. destruct (thread_equals t thread) eqn:ORIG.
       +++ rewrite Heqthreads'''. rewrite ORIG. rewrite H2. rewrite ORIG. auto.
       +++ rewrite Heqthreads'''. rewrite ORIG. rewrite H2. rewrite ORIG. auto.
  + remember (fun t0 => if thread_equals t0 thread then and (translate (con_subst E e) b B buf_size) (translate t b B buf_size) else f t0) as threads''; remember (fun t0 => if thread_equals t0 thread then and (translate (con_subst E e') b B buf_size) (translate t b B buf_size) else f t0) as threads'''. apply steps_app_right with (threads:=threads'') (threads':=threads''') (thread:=thread) (e2:=flush_star b B buf_size;; var 0).
    ++ apply steps_and_left with (threads:=threads) (threads':=threads') (thread:=thread) (e2:=translate t b B buf_size). apply IHE with (u:=u) (v:=v). rewrite Heqthreads'. auto. auto. rewrite Heqthreads. auto. auto. auto. rewrite Heqthreads''. rewrite Heqthreads. intros. destruct (thread_equals t0 thread). auto. auto. rewrite Heqthreads'''. rewrite Heqthreads'. intros. destruct (thread_equals t0 thread). auto. auto.
    ++ intros. destruct (thread_equals t0 thread) eqn:ORIG.
       +++ rewrite Heqthreads''. rewrite ORIG. rewrite H1. rewrite ORIG. auto.
       +++ rewrite Heqthreads''. rewrite ORIG. rewrite H1. rewrite ORIG. auto.
    ++ intros. destruct (thread_equals t0 thread) eqn:ORIG.
       +++ rewrite Heqthreads'''. rewrite ORIG. rewrite H2. rewrite ORIG. auto.
       +++ rewrite Heqthreads'''. rewrite ORIG. rewrite H2. rewrite ORIG. auto.
  + destruct s. subst x. rewrite translate_and in *. rewrite translate_tru in *. remember (fun t0 => if thread_equals t0 thread then and tru (translate (con_subst E e) b B buf_size) else f t0) as threads''; remember (fun t0 => if thread_equals t0 thread then and tru (translate (con_subst E e')  b B buf_size) else f t0) as threads'''. apply steps_app_right with (threads:=threads'') (threads':=threads''') (thread:=thread) (e2:=flush_star b B buf_size;; var 0).
    ++ apply steps_and_right with (threads:=threads) (threads':=threads') (thread:=thread). apply IHE with (u:=u) (v:=v). rewrite Heqthreads'. auto. auto. rewrite Heqthreads. auto. auto. auto. rewrite Heqthreads''. rewrite Heqthreads. intros. destruct (thread_equals t thread). auto. auto. rewrite Heqthreads'''. rewrite Heqthreads'. intros. destruct (thread_equals t thread). auto. auto.
    ++ intros. destruct (thread_equals t thread) eqn:ORIG.
       +++ rewrite Heqthreads''. rewrite ORIG. rewrite H1. rewrite ORIG. auto.
       +++ rewrite Heqthreads''. rewrite ORIG. rewrite H1. rewrite ORIG. auto.
    ++ intros. destruct (thread_equals t thread) eqn:ORIG.
       +++ rewrite Heqthreads'''. rewrite ORIG. rewrite H2. rewrite ORIG. auto.
       +++ rewrite Heqthreads'''. rewrite ORIG. rewrite H2. rewrite ORIG. auto.
  + unfold new_read in *. remember (fun t0 => if thread_equals t0 thread then app (lam (read_code b B buf_size))  (paire (translate (con_subst E e) b B buf_size) (translate t b B buf_size)) else f t0) as threads''. remember (fun t0 => if thread_equals t0 thread then app (lam (read_code b B buf_size))  (paire (translate (con_subst E e') b B buf_size) (translate t b B buf_size)) else f t0) as threads'''. apply steps_app_right with (threads:=threads'') (threads':=threads''') (thread:=thread) (e2:=flush_star b B buf_size;; var 0).
    ++ remember (fun t0 => if thread_equals t0 thread then (paire (translate (con_subst E e) b B buf_size) (translate t b B buf_size)) else f t0) as threads''''. remember (fun t0 => if thread_equals t0 thread then (paire (translate (con_subst E e') b B buf_size) (translate t b B buf_size)) else f t0) as threads'''''. apply steps_app_right with (threads:=threads'''') (threads':=threads''''') (thread:=thread) (e2:=read_code b B buf_size).
       +++ apply steps_paire_left with (threads:=threads) (threads':=threads') (thread:=thread) (e2:=translate t b B buf_size). apply IHE with (u:=u) (v:=v). rewrite Heqthreads'. auto. auto. rewrite Heqthreads. auto. auto. auto. rewrite Heqthreads''''. rewrite Heqthreads. intros. destruct (thread_equals t0 thread). auto. auto. rewrite Heqthreads'''''. rewrite Heqthreads'. intros. destruct (thread_equals t0 thread). auto. auto.
       +++ rewrite Heqthreads''''. rewrite Heqthreads''. intros. destruct (thread_equals t0 thread). auto. auto.
       +++ rewrite Heqthreads'''''. rewrite Heqthreads'''. intros. destruct (thread_equals t0 thread). auto. auto.
    ++ intros. rewrite H1. rewrite Heqthreads''. destruct (thread_equals t0 thread). auto. auto.
    ++ intros. rewrite H2. rewrite Heqthreads'''. destruct (thread_equals t0 thread). auto. auto.
  + destruct s. destruct e0. subst x. rewrite translate_read in *. unfold new_read in *. rewrite translate_array in *. remember (fun t0 => if thread_equals t0 thread then app (lam (read_code b B buf_size))  (paire (array x0) (translate (con_subst E e) b B buf_size) ) else f t0) as threads''. remember (fun t0 => if thread_equals t0 thread then app (lam (read_code b B buf_size))  (paire (array x0) (translate (con_subst E e') b B buf_size)) else f t0) as threads'''. apply steps_app_right with (threads:=threads'') (threads':=threads''') (thread:=thread) (e2:=flush_star b B buf_size;; var 0).
    ++ remember (fun t0 => if thread_equals t0 thread then (paire (array x0) (translate (con_subst E e) b B buf_size)) else f t0) as threads''''. remember (fun t0 => if thread_equals t0 thread then (paire (array x0) (translate (con_subst E e') b B buf_size)) else f t0) as threads'''''. apply steps_app_right with (threads:=threads'''') (threads':=threads''''') (thread:=thread) (e2:=read_code b B buf_size).
       +++ apply steps_paire_right with (threads:=threads) (threads':=threads') (thread:=thread) (e2:=array x0). apply IHE with (u:=u) (v:=v). rewrite Heqthreads'. auto. auto. rewrite Heqthreads. auto. auto. auto. apply value_array. rewrite Heqthreads''''. rewrite Heqthreads. intros. destruct (thread_equals t thread). auto. auto. rewrite Heqthreads'''''. rewrite Heqthreads'. intros. destruct (thread_equals t thread). auto. auto.
       +++ rewrite Heqthreads''''. rewrite Heqthreads''. intros. destruct (thread_equals t thread). auto. auto.
       +++ rewrite Heqthreads'''''. rewrite Heqthreads'''. intros. destruct (thread_equals t thread). auto. auto.
    ++ intros. rewrite H1. rewrite Heqthreads''. destruct (thread_equals t thread). auto. auto.
    ++ intros. rewrite H2. rewrite Heqthreads'''. destruct (thread_equals t thread). auto. auto.
  + unfold new_write in *. remember (fun q => if thread_equals q thread then app (lam (write_code b B buf_size)) (paire (translate (con_subst E e) b B buf_size) (paire (translate t b B buf_size) (translate t0 b B buf_size))) else f q) as threads''. remember (fun q => if thread_equals q thread then app (lam (write_code b B buf_size)) (paire (translate (con_subst E e') b B buf_size) (paire (translate t b B buf_size) (translate t0 b B buf_size))) else f q) as threads'''. apply steps_app_right with (threads:=threads'') (threads':=threads''') (thread:=thread) (e2:=flush_star b B buf_size;; var 0).
    ++ remember (fun q => if thread_equals q thread then paire (translate (con_subst E e) b B buf_size)
                        (paire (translate t b B buf_size) (translate t0 b B buf_size)) else f q) as threads''''. remember (fun q => if thread_equals q thread then paire (translate (con_subst E e') b B buf_size) (paire (translate t b B buf_size) (translate t0 b B buf_size)) else f q) as threads'''''. apply steps_app_right with (threads:=threads'''') (threads':=threads''''') (thread:=thread) (e2:=write_code b B buf_size).
       +++ apply steps_paire_left with (threads:=threads) (threads':=threads') (thread:=thread) (e2:=paire (translate t b B buf_size) (translate t0 b B buf_size)). apply IHE with (u:=u) (v:=v). rewrite Heqthreads'. auto. auto. rewrite Heqthreads. auto. auto. auto. rewrite Heqthreads''''. rewrite Heqthreads. intros. destruct (thread_equals t1 thread) eqn:ORIG. auto. auto. rewrite Heqthreads'''''. intros. destruct (thread_equals t1 thread) eqn:ORIG. rewrite Heqthreads'. rewrite ORIG. auto. rewrite Heqthreads'. rewrite ORIG. auto.
       +++ rewrite Heqthreads''''. intros. rewrite Heqthreads''. destruct (thread_equals t1 thread) eqn:ORIG. auto. auto.
       +++ rewrite Heqthreads'''''. rewrite Heqthreads'''. intros. destruct (thread_equals t1 thread). auto. auto.
    ++ intros. rewrite H1. rewrite Heqthreads''. destruct (thread_equals t1 thread). auto. auto.
    ++ intros. rewrite H2. rewrite Heqthreads'''. destruct (thread_equals t1 thread). auto. auto.
  + destruct s. destruct e0. subst x. rewrite translate_write in *. unfold new_write in *. rewrite translate_array in *. remember (fun q => if thread_equals q thread then app (lam (write_code b B buf_size)) (paire (array x0) (paire (translate (con_subst E e) b B buf_size) (translate t b B buf_size))) else f q) as threads''. remember (fun q => if thread_equals q thread then app (lam (write_code b B buf_size)) (paire (array x0) (paire (translate (con_subst E e') b B buf_size) (translate t b B buf_size))) else f q) as threads'''. apply steps_app_right with (threads:=threads'') (threads':=threads''') (thread:=thread) (e2:=flush_star b B buf_size;; var 0).
    ++ remember (fun q => if thread_equals q thread then (paire (array x0)
                        (paire (translate (con_subst E e) b B buf_size)
                           (translate t b B buf_size))) else f q) as threads''''. remember (fun q => if thread_equals q thread then (paire (array x0)
                        (paire (translate (con_subst E e') b B buf_size)
                           (translate t b B buf_size))) else f q) as threads'''''. apply steps_app_right with (threads:=threads'''') (threads':=threads''''') (thread:=thread) (e2:=write_code b B buf_size).
       +++ remember (fun q => if thread_equals q thread then (
                        (paire (translate (con_subst E e) b B buf_size)
                           (translate t b B buf_size))) else f q) as threads''''''. remember (fun q => if thread_equals q thread then (
                        (paire (translate (con_subst E e') b B buf_size)
                           (translate t b B buf_size))) else f q) as threads'''''''. apply steps_paire_right with (threads:=threads'''''') (threads':=threads''''''') (thread:=thread) (e2:=array x0).
           ++++ apply steps_paire_left with (threads:=threads) (threads':=threads') (thread:=thread) (e2:=translate t b B buf_size). apply IHE with (u:=u) (v:=v). rewrite Heqthreads'. auto. auto. rewrite Heqthreads. auto. auto. auto. rewrite Heqthreads''''''. rewrite Heqthreads. intros. destruct (thread_equals t0 thread) eqn:ORIG. auto. auto. rewrite Heqthreads'''''''. intros. destruct (thread_equals t0 thread) eqn:ORIG. rewrite Heqthreads'. rewrite ORIG. auto. rewrite Heqthreads'. rewrite ORIG. auto.
           ++++ apply value_array. 
           ++++ rewrite Heqthreads''''. intros. rewrite Heqthreads''''''. destruct (thread_equals t0 thread) eqn:ORIG. auto. auto.
           ++++ rewrite Heqthreads'''''. rewrite Heqthreads'''''''. intros. destruct (thread_equals t0 thread). auto. auto.
       +++ rewrite Heqthreads''. rewrite Heqthreads''''. intros. destruct (thread_equals t0 thread). auto. auto.
       +++ rewrite Heqthreads'''. rewrite Heqthreads'''''. intros. destruct (thread_equals t0 thread). auto. auto.
    ++ intros. rewrite H1. rewrite Heqthreads''. destruct (thread_equals t0 thread). auto. auto.
    ++ intros. rewrite H2. rewrite Heqthreads'''. destruct (thread_equals t0 thread). auto. auto.
  + destruct s. destruct e0. destruct s0. destruct e0. subst x. subst x1. rewrite translate_write in *. unfold new_write in *. rewrite translate_array in *. rewrite translate_num in *. remember (fun q => if thread_equals q thread then app (lam (write_code b B buf_size)) (paire (array x0) (paire (num x2) (translate (con_subst E e) b B buf_size))) else f q) as threads''. remember (fun q => if thread_equals q thread then app (lam (write_code b B buf_size)) (paire (array x0) (paire (num x2) (translate (con_subst E e') b B buf_size))) else f q) as threads'''. apply steps_app_right with (threads:=threads'') (threads':=threads''') (thread:=thread) (e2:=flush_star b B buf_size;; var 0).
    ++ remember (fun q => if thread_equals q thread then (paire (array x0)
                        (paire (num x2) (translate (con_subst E e) b B buf_size))) else f q) as threads''''. remember (fun q => if thread_equals q thread then (paire (array x0)
                        (paire (num x2) (translate (con_subst E e') b B buf_size))) else f q) as threads'''''. apply steps_app_right with (threads:=threads'''') (threads':=threads''''') (thread:=thread) (e2:=write_code b B buf_size).
       +++ remember (fun q => if thread_equals q thread then (
                        (paire (num x2) (translate (con_subst E e) b B buf_size))) else f q) as threads''''''. remember (fun q => if thread_equals q thread then (
                        (paire (num x2) (translate (con_subst E e') b B buf_size))) else f q) as threads'''''''. apply steps_paire_right with (threads:=threads'''''') (threads':=threads''''''') (thread:=thread) (e2:=array x0).
           ++++ apply steps_paire_right with (threads:=threads) (threads':=threads') (thread:=thread) (e2:=num x2). apply IHE with (u:=u) (v:=v). rewrite Heqthreads'. auto. auto. rewrite Heqthreads. auto. auto. auto. apply value_num. rewrite Heqthreads''''''. rewrite Heqthreads. intros. destruct (thread_equals t thread) eqn:ORIG. auto. auto. rewrite Heqthreads'''''''. intros. destruct (thread_equals t thread) eqn:ORIG. rewrite Heqthreads'. rewrite ORIG. auto. rewrite Heqthreads'. rewrite ORIG. auto.
           ++++ apply value_array. 
           ++++ rewrite Heqthreads''''. intros. rewrite Heqthreads''''''. destruct (thread_equals t thread) eqn:ORIG. auto. auto.
           ++++ rewrite Heqthreads'''''. rewrite Heqthreads'''''''. intros. destruct (thread_equals t thread). auto. auto.
       +++ rewrite Heqthreads''. rewrite Heqthreads''''. intros. destruct (thread_equals t thread). auto. auto.
       +++ rewrite Heqthreads'''. rewrite Heqthreads'''''. intros. destruct (thread_equals t thread). auto. auto.
    ++ intros. rewrite H1. rewrite Heqthreads''. destruct (thread_equals t thread). auto. auto.
    ++ intros. rewrite H2. rewrite Heqthreads'''. destruct (thread_equals t thread). auto. auto.
  + apply steps_case_left with (threads:=threads) (threads':=threads') (thread:=thread) (e2:=flush_star b B buf_size;; translate t b B buf_size) (e3:=flush_star b B buf_size;; translate t0 b B buf_size). apply IHE with (u:=u) (v:=v). rewrite Heqthreads'. auto. auto. rewrite Heqthreads. auto. auto. auto. intros. destruct (thread_equals t1 thread) eqn:ORIG.
       +++ rewrite Heqthreads. rewrite ORIG. rewrite H1. rewrite ORIG. auto.
       +++ rewrite Heqthreads. rewrite ORIG. rewrite H1. rewrite ORIG. auto.
       +++ intros. destruct (thread_equals t1 thread) eqn:ORIG.
           ++++ rewrite Heqthreads'. rewrite ORIG. rewrite H2. rewrite ORIG. auto.
           ++++ rewrite Heqthreads'. rewrite ORIG. rewrite H2. rewrite ORIG. auto.
  + remember (fun t0 => if thread_equals t0 thread then not (translate (con_subst E e) b B buf_size) else f t0) as threads''; remember (fun t0 => if thread_equals t0 thread then not (translate (con_subst E e') b B buf_size)else f t0) as threads'''. apply steps_app_right with (threads:=threads'') (threads':=threads''') (thread:=thread) (e2:=flush_star b B buf_size;; var 0).
    ++ apply steps_not_left with (threads:=threads) (threads':=threads') (thread:=thread). apply IHE with (u:=u) (v:=v). rewrite Heqthreads'. auto. auto. rewrite Heqthreads. auto. auto. auto. rewrite Heqthreads''. rewrite Heqthreads. intros. destruct (thread_equals t thread). auto. auto. rewrite Heqthreads'''. rewrite Heqthreads'. intros. destruct (thread_equals t thread). auto. auto.
    ++ intros. destruct (thread_equals t thread) eqn:ORIG.
       +++ rewrite Heqthreads''. rewrite ORIG. rewrite H1. rewrite ORIG. auto.
       +++ rewrite Heqthreads''. rewrite ORIG. rewrite H1. rewrite ORIG. auto.
    ++ intros. destruct (thread_equals t thread) eqn:ORIG.
       +++ rewrite Heqthreads'''. rewrite ORIG. rewrite H2. rewrite ORIG. auto.
       +++ rewrite Heqthreads'''. rewrite ORIG. rewrite H2. rewrite ORIG. auto.
  + remember (fun t0 => if thread_equals t0 thread then reference (translate (con_subst E e) b B buf_size) else f t0) as threads''; remember (fun t0 => if thread_equals t0 thread then reference (translate (con_subst E e') b B buf_size)else f t0) as threads'''. apply steps_app_right with (threads:=threads'') (threads':=threads''') (thread:=thread) (e2:=flush_star b B buf_size;; var 0).
    ++ apply steps_reference_left with (threads:=threads) (threads':=threads') (thread:=thread). apply IHE with (u:=u) (v:=v). rewrite Heqthreads'. auto. auto. rewrite Heqthreads. auto. auto. auto. rewrite Heqthreads''. rewrite Heqthreads. intros. destruct (thread_equals t thread). auto. auto. rewrite Heqthreads'''. rewrite Heqthreads'. intros. destruct (thread_equals t thread). auto. auto.
    ++ intros. destruct (thread_equals t thread) eqn:ORIG.
       +++ rewrite Heqthreads''. rewrite ORIG. rewrite H1. rewrite ORIG. auto.
       +++ rewrite Heqthreads''. rewrite ORIG. rewrite H1. rewrite ORIG. auto.
    ++ intros. destruct (thread_equals t thread) eqn:ORIG.
       +++ rewrite Heqthreads'''. rewrite ORIG. rewrite H2. rewrite ORIG. auto.
       +++ rewrite Heqthreads'''. rewrite ORIG. rewrite H2. rewrite ORIG. auto.
  + remember (fun t0 => if thread_equals t0 thread then cast (translate (con_subst E e) b B buf_size) else f t0) as threads''; remember (fun t0 => if thread_equals t0 thread then cast (translate (con_subst E e') b B buf_size)else f t0) as threads'''. apply steps_app_right with (threads:=threads'') (threads':=threads''') (thread:=thread) (e2:=flush_star b B buf_size;; var 0).
    ++ apply steps_cast_left with (threads:=threads) (threads':=threads') (thread:=thread). apply IHE with (u:=u) (v:=v). rewrite Heqthreads'. auto. auto. rewrite Heqthreads. auto. auto. auto. rewrite Heqthreads''. rewrite Heqthreads. intros. destruct (thread_equals t thread). auto. auto. rewrite Heqthreads'''. rewrite Heqthreads'. intros. destruct (thread_equals t thread). auto. auto.
    ++ intros. destruct (thread_equals t thread) eqn:ORIG.
       +++ rewrite Heqthreads''. rewrite ORIG. rewrite H1. rewrite ORIG. auto.
       +++ rewrite Heqthreads''. rewrite ORIG. rewrite H1. rewrite ORIG. auto.
    ++ intros. destruct (thread_equals t thread) eqn:ORIG.
       +++ rewrite Heqthreads'''. rewrite ORIG. rewrite H2. rewrite ORIG. auto.
       +++ rewrite Heqthreads'''. rewrite ORIG. rewrite H2. rewrite ORIG. auto.
  + apply steps_paire_left with (threads:=threads) (threads':=threads') (thread:=thread) (e2:=translate t b B buf_size). apply IHE with (u:=u) (v:=v). rewrite Heqthreads'. auto. auto. rewrite Heqthreads. intros. destruct (thread_equals t0 thread) eqn:ORIG. auto. auto. intros. rewrite H. auto. auto. intros. rewrite H1. destruct (thread_equals t0 thread) eqn:ORIG. rewrite Heqthreads. rewrite ORIG. auto. rewrite Heqthreads. rewrite ORIG. auto. intros. destruct (thread_equals t0 thread) eqn:ORIG. rewrite H2. rewrite ORIG. rewrite Heqthreads'. rewrite ORIG. auto. rewrite Heqthreads'. rewrite ORIG. rewrite H2. rewrite ORIG. auto.
  + destruct s. apply steps_paire_right with (threads:=threads) (threads':=threads') (thread:=thread) (e2:=translate x b B buf_size). apply IHE with (u:=u) (v:=v). rewrite Heqthreads'. auto. auto. rewrite Heqthreads. intros. auto. intros. rewrite H. auto. auto. apply translation_of_value_is_value. auto. intros. destruct (thread_equals t thread) eqn:ORIG. rewrite H1. rewrite ORIG. rewrite Heqthreads. rewrite ORIG. rewrite translate_paire. auto. rewrite Heqthreads. rewrite ORIG. rewrite H1. rewrite ORIG. auto. intros. destruct (thread_equals t thread) eqn:ORIG. rewrite H2. rewrite ORIG. rewrite Heqthreads'. rewrite ORIG. rewrite translate_paire. auto. rewrite Heqthreads'. rewrite ORIG. rewrite H2. rewrite ORIG. auto.
  + remember (fun t0 => if thread_equals t0 thread then first (translate (con_subst E e) b B buf_size) else f t0) as threads''; remember (fun t0 => if thread_equals t0 thread then first (translate (con_subst E e') b B buf_size)else f t0) as threads'''. apply steps_app_right with (threads:=threads'') (threads':=threads''') (thread:=thread) (e2:=flush_star b B buf_size;; var 0).
    ++ apply steps_first_left with (threads:=threads) (threads':=threads') (thread:=thread). apply IHE with (u:=u) (v:=v). rewrite Heqthreads'. auto. auto. rewrite Heqthreads. auto. auto. auto. rewrite Heqthreads''. rewrite Heqthreads. intros. destruct (thread_equals t thread). auto. auto. rewrite Heqthreads'''. rewrite Heqthreads'. intros. destruct (thread_equals t thread). auto. auto.
    ++ intros. destruct (thread_equals t thread) eqn:ORIG.
       +++ rewrite Heqthreads''. rewrite ORIG. rewrite H1. rewrite ORIG. auto.
       +++ rewrite Heqthreads''. rewrite ORIG. rewrite H1. rewrite ORIG. auto.
    ++ intros. destruct (thread_equals t thread) eqn:ORIG.
       +++ rewrite Heqthreads'''. rewrite ORIG. rewrite H2. rewrite ORIG. auto.
       +++ rewrite Heqthreads'''. rewrite ORIG. rewrite H2. rewrite ORIG. auto.
  + remember (fun t0 => if thread_equals t0 thread then second (translate (con_subst E e) b B buf_size) else f t0) as threads''; remember (fun t0 => if thread_equals t0 thread then second (translate (con_subst E e') b B buf_size)else f t0) as threads'''. apply steps_app_right with (threads:=threads'') (threads':=threads''') (thread:=thread) (e2:=flush_star b B buf_size;; var 0).
    ++ apply steps_second_left with (threads:=threads) (threads':=threads') (thread:=thread). apply IHE with (u:=u) (v:=v). rewrite Heqthreads'. auto. auto. rewrite Heqthreads. auto. auto. auto. rewrite Heqthreads''. rewrite Heqthreads. intros. destruct (thread_equals t thread). auto. auto. rewrite Heqthreads'''. rewrite Heqthreads'. intros. destruct (thread_equals t thread). auto. auto.
    ++ intros. destruct (thread_equals t thread) eqn:ORIG.
       +++ rewrite Heqthreads''. rewrite ORIG. rewrite H1. rewrite ORIG. auto.
       +++ rewrite Heqthreads''. rewrite ORIG. rewrite H1. rewrite ORIG. auto.
    ++ intros. destruct (thread_equals t thread) eqn:ORIG.
       +++ rewrite Heqthreads'''. rewrite ORIG. rewrite H2. rewrite ORIG. auto.
       +++ rewrite Heqthreads'''. rewrite ORIG. rewrite H2. rewrite ORIG. auto.
Qed.
