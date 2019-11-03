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
Definition seq (s : term) (t : term) := app (lam (Lambda.shift true 0 t)) s.

Notation "x == y" := (equals x y) (at level 60).

Notation "c1 ;; c2" :=
  (seq c1 c2) (at level 80, right associativity).


Definition y_combinator := 
  lam (app (lam (app (var 1) (app (var 0) (var 0)))) (lam (app (var 1) (app (var 0) (var 0)))) ).

Definition while_fun := 
  lam (lam (lam (case (var 1) (seq (var 0) (app (app (var 2) (var 1)) (var 0))) yunit))).

Definition while_fics := app y_combinator while_fun.

Definition while (s : term) (t : term) := app (app while_fics s) t.

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

Fixpoint shift_n_c b n c e  :=
  match n with
    | 0 => e
    | S n => shift_n_c b n c (Lambda.shift b c e)
  end.

Definition shift_n b n e := shift_n_c b n 0 e.

Fact shift_n_c_array : forall n c k b, shift_n_c b n c (array k) = array k.
Proof. intros. generalize dependent k. generalize dependent c. induction n ; intros.
  + simpl. auto.
  + simpl. rewrite IHn. auto. Qed.

Fact shift_n_c_num : forall n c k b, shift_n_c b n c (num k) = num k.
Proof. intros. generalize dependent k. generalize dependent c. induction n ; intros.
  + simpl. auto.
  + simpl. rewrite IHn. auto. Qed.

Fact shift_n_c_tru : forall n c b, shift_n_c b n c tru = tru.
Proof. intros. generalize dependent c. induction n ; intros.
  + simpl. auto.
  + simpl. rewrite IHn. auto. Qed.

Fact shift_n_c_fls : forall n c b, shift_n_c b n c fls = fls.
Proof. intros. generalize dependent c. induction n ; intros.
  + simpl. auto.
  + simpl. rewrite IHn. auto. Qed.

Fact shift_n_c_yunit : forall n c b, shift_n_c b n c yunit = yunit.
Proof. intros. generalize dependent c. induction n ; intros.
  + simpl. auto.
  + simpl. rewrite IHn. auto. Qed.

Fact shift_n_c_plus : forall n c e1 e2 b, shift_n_c b n c (plus e1 e2) = plus (shift_n_c b n c e1) (shift_n_c b n c e2).
Proof. intros. generalize dependent c. generalize dependent e1. generalize dependent e2. induction n ; intros.
  + simpl. auto.
  + simpl. rewrite IHn. auto. Qed.

Fact shift_n_c_minus : forall n c e1 e2 b, shift_n_c b n c (minus e1 e2) = minus (shift_n_c b n c e1) (shift_n_c b n c e2).
Proof. intros. generalize dependent c. generalize dependent e1. generalize dependent e2. induction n ; intros.
  + simpl. auto.
  + simpl. rewrite IHn. auto. Qed.

Fact shift_n_c_modulo : forall n c e1 e2 b, shift_n_c b n c (modulo e1 e2) = modulo (shift_n_c b n c e1) (shift_n_c b n c e2).
Proof. intros. generalize dependent c. generalize dependent e1. generalize dependent e2. induction n ; intros.
  + simpl. auto.
  + simpl. rewrite IHn. auto. Qed.

Fact shift_n_c_less_than : forall n c e1 e2 b, shift_n_c b n c (less_than e1 e2) = less_than (shift_n_c b n c e1) (shift_n_c b n c e2).
Proof. intros. generalize dependent c. generalize dependent e1. generalize dependent e2. induction n ; intros.
  + simpl. auto.
  + simpl. rewrite IHn. auto. Qed.

Fact shift_n_c_and : forall n c e1 e2 b, shift_n_c b n c (and e1 e2) = and (shift_n_c b n c e1) (shift_n_c b n c e2).
Proof. intros. generalize dependent c. generalize dependent e1. generalize dependent e2. induction n ; intros.
  + simpl. auto.
  + simpl. rewrite IHn. auto. Qed.

Fact shift_n_c_read : forall n c e1 e2 b, shift_n_c b n c (read e1 e2) = read (shift_n_c b n c e1) (shift_n_c b n c e2).
Proof. intros. generalize dependent c. generalize dependent e1. generalize dependent e2. induction n ; intros.
  + simpl. auto.
  + simpl. rewrite IHn. auto. Qed.

Fact shift_n_c_app : forall n c e1 e2 b, shift_n_c b n c (app e1 e2) = app (shift_n_c b n c e1) (shift_n_c b n c e2).
Proof. intros. generalize dependent c. generalize dependent e1. generalize dependent e2. induction n ; intros.
  + simpl. auto.
  + simpl. rewrite IHn. auto. Qed.

Fact shift_n_c_write : forall n c e1 e2 e3 b, shift_n_c b n c (write e1 e2 e3) = write (shift_n_c b n c e1) (shift_n_c b n c e2) (shift_n_c b n c e3).
Proof. intros. generalize dependent c. generalize dependent e1. generalize dependent e2. generalize dependent e3. induction n ; intros.
  + simpl. auto.
  + simpl. rewrite IHn. auto. Qed.

Fact shift_n_c_case : forall n c e1 e2 e3 b, shift_n_c b n c (case e1 e2 e3) = case (shift_n_c b n c e1) (shift_n_c b n c e2) (shift_n_c b n c e3).
Proof. intros. generalize dependent c. generalize dependent e1. generalize dependent e2. generalize dependent e3. induction n ; intros.
  + simpl. auto.
  + simpl. rewrite IHn. auto. Qed.

Fact shift_n_c_paire : forall n c e1 e2 b, shift_n_c b n c (paire e1 e2) = paire (shift_n_c b n c e1) (shift_n_c b n c e2).
Proof. intros. generalize dependent c. generalize dependent e1. generalize dependent e2. induction n ; intros.
  + simpl. auto.
  + simpl. rewrite IHn. auto. Qed.

Fact shift_n_c_cast : forall n c e b, shift_n_c b n c (cast e) = cast (shift_n_c b n c e).
Proof. intros. generalize dependent c. generalize dependent e. induction n ; intros.
  + simpl. auto.
  + simpl. rewrite IHn. auto. Qed.

Fact shift_n_c_not : forall n c e b, shift_n_c b n c (not e) = not (shift_n_c b n c e).
Proof. intros. generalize dependent c. generalize dependent e. induction n ; intros.
  + simpl. auto.
  + simpl. rewrite IHn. auto. Qed.

Fact shift_n_c_reference : forall n c e b, shift_n_c b n c (reference e) = reference (shift_n_c b n c e).
Proof. intros. generalize dependent c. generalize dependent e. induction n ; intros.
  + simpl. auto.
  + simpl. rewrite IHn. auto. Qed.

Fact shift_n_c_first : forall n c e b, shift_n_c b n c (first e) = first (shift_n_c b n c e).
Proof. intros. generalize dependent c. generalize dependent e. induction n ; intros.
  + simpl. auto.
  + simpl. rewrite IHn. auto. Qed.

Fact shift_n_c_second : forall n c e b, shift_n_c b n c (second e) = second (shift_n_c b n c e).
Proof. intros. generalize dependent c. generalize dependent e. induction n ; intros.
  + simpl. auto.
  + simpl. rewrite IHn. auto. Qed.


Fact shift_n_c_lam : forall n c e b, shift_n_c b n c (lam e) = lam (shift_n_c b n (c+1) e).
Proof. intros. generalize dependent e. generalize dependent c. induction n ; intros.
  + simpl. auto.
  + simpl. rewrite IHn. auto. Qed.

Fact shift_n_c_var1 : forall n c k b, k < c -> shift_n_c b n c (var k) = var k.
Proof. intros. generalize dependent k. generalize dependent c. induction n ; intros.
  + simpl. auto.
  + simpl. destruct (k <? c) eqn:ORIG.
    ++ apply Nat.ltb_lt in ORIG. apply IHn. auto.
    ++ apply Nat.ltb_lt in H. rewrite H in ORIG. inversion ORIG. Qed.

Fact shift_n_c_var2 : forall n c k , k >= c -> shift_n_c true n c (var k) = var (n+k).
Proof. intros. generalize dependent k. generalize dependent c. induction n ; intros.
  + simpl. auto.
  + simpl. destruct (k <? c) eqn:ORIG.
    ++ apply Nat.ltb_lt in ORIG. omega.
    ++ rewrite IHn. assert (n+(k+1) = S(n+k)). omega. rewrite H0. auto. omega. Qed.


Fact shift_n_c_var3 : forall n c k , k >= c -> shift_n_c false (S n) c (var k) = var (max (k-(S n)) (c-1)).
Proof. intros. generalize dependent k. generalize dependent c. induction n ; intros.
  + simpl. replace (max (k-1) (c-1)) with (k-1). destruct (k <? c) eqn:ORIG. apply Nat.ltb_lt in ORIG. omega. auto. symmetry. apply max_l. omega.
  + replace (shift_n_c false (S (S n)) c (var k)) with (shift_n_c false (S n) c (Lambda.shift false c (var k))). simpl (Lambda.shift false c (var k)).
destruct (k <? c) eqn:ORIG.
    ++ apply Nat.ltb_lt in ORIG. omega.
    ++ destruct (k =? c) eqn:ORIG2.
       +++ apply beq_nat_true in ORIG2. subst. assert (forall n c, shift_n_c false n c (var (c-1)) = var (c-1)). intros. induction n0. simpl. auto. simpl. destruct (c0 - 1 <? c0) eqn:ORIG1. apply Nat.ltb_lt in ORIG1. auto. destruct c0. simpl in *. auto.
assert (S c0 - 1 < S c0). omega. apply Nat.ltb_lt in H0. rewrite ORIG1 in H0.  inversion H0. rewrite H0. replace (max (c - S (S n)) (c-1)) with (c-1). auto. symmetry. apply max_r. omega.
       +++ apply beq_nat_false in ORIG2. assert (k > c). omega. rewrite IHn. replace (k-1-S n) with (k-S(S n)). auto. omega. omega.
    ++ simpl. auto. Qed.


Fact shift_up_n_eq : forall n c e, shift_n_c true (n + 1) c e = Lambda.shift true (n+c) (shift_n_c true n c e).
Proof. intros. generalize dependent c. generalize dependent n. induction e ; intros.
  + rewrite shift_n_c_array. rewrite shift_n_c_array. simpl. auto.
  + rewrite shift_n_c_num. rewrite shift_n_c_num. simpl. auto.
  + rewrite shift_n_c_plus. rewrite shift_n_c_plus. rewrite IHe1. rewrite IHe2. simpl. auto.
  + rewrite shift_n_c_minus. rewrite shift_n_c_minus. rewrite IHe1. rewrite IHe2. simpl. auto.
  + rewrite shift_n_c_modulo. rewrite shift_n_c_modulo. rewrite IHe1. rewrite IHe2. simpl. auto.
  + rewrite shift_n_c_tru. rewrite shift_n_c_tru. simpl. auto.
  + rewrite shift_n_c_fls. rewrite shift_n_c_fls. simpl. auto.
  + rewrite shift_n_c_less_than. rewrite shift_n_c_less_than. rewrite IHe1. rewrite IHe2. simpl. auto. 
  + rewrite shift_n_c_not. rewrite shift_n_c_not. rewrite IHe. simpl. auto.
  + rewrite shift_n_c_and. rewrite shift_n_c_and. rewrite IHe1. rewrite IHe2. simpl. auto.
  + rewrite shift_n_c_yunit. rewrite shift_n_c_yunit. simpl. auto.
  + rewrite shift_n_c_read. rewrite shift_n_c_read. rewrite IHe1. rewrite IHe2. simpl. auto.
  + rewrite shift_n_c_write. rewrite shift_n_c_write. rewrite IHe1. rewrite IHe2. rewrite IHe3. simpl. auto.
  + rewrite shift_n_c_reference. rewrite shift_n_c_reference. rewrite IHe. simpl. auto.
  + rewrite shift_n_c_cast. rewrite shift_n_c_cast. rewrite IHe. simpl. auto.
  + rewrite shift_n_c_case. rewrite shift_n_c_case. rewrite IHe1. rewrite IHe2. rewrite IHe3. simpl. auto.
  + destruct (n <? c) eqn:ORIG. apply Nat.ltb_lt in ORIG. rewrite shift_n_c_var1. rewrite shift_n_c_var1. simpl. destruct (n <? n0 + c) eqn:ORIG1. apply Nat.ltb_lt in ORIG1. auto. assert (n < n0 + c -> False). intros. apply Nat.ltb_lt in H. rewrite H in ORIG1. inversion ORIG1. contradiction H. omega. auto. auto. assert (n <  c -> False). intros. apply Nat.ltb_lt in H. rewrite ORIG in H. inversion H. assert (n >= c). omega. rewrite shift_n_c_var2. rewrite shift_n_c_var2. simpl. destruct (n0 + n <? n0 + c) eqn:ORIG1. rewrite Nat.ltb_lt in ORIG1. omega. assert (n0+1+n=n0+n+1). omega. rewrite H1. auto. auto. auto.
  + rewrite shift_n_c_app. rewrite shift_n_c_app. rewrite IHe1. rewrite IHe2. simpl. auto.
  + rewrite shift_n_c_lam. rewrite shift_n_c_lam. assert (n+1=S n). omega. repeat (rewrite H in *). simpl. assert (shift_n_c true (n + 1) (c+1) e =
Lambda.shift true (n + (c + 1)) (shift_n_c true n (c + 1) e)). apply IHe. assert (n+c+1=n+(c+1)). omega. rewrite H1 in *. rewrite <- H0. assert (n+1=S n). omega. rewrite H2 in *. simpl. auto.
  + rewrite shift_n_c_paire. rewrite shift_n_c_paire. rewrite IHe1. rewrite IHe2. simpl. auto.
  + rewrite shift_n_c_first. rewrite shift_n_c_first. rewrite IHe. simpl. auto.
  + rewrite shift_n_c_second. rewrite shift_n_c_second. rewrite IHe. simpl. auto.
Qed.

Fact foo : forall n e b, shift_n_c b (S n) 0 e = Lambda.shift b 0 (shift_n_c b n 0 e).
Proof. intros. generalize dependent e. induction n ; intros ; simpl.
  + auto.
  + rewrite <- IHn. simpl. auto. Qed.

Fact blah : forall x v e c, subst (x + (c+1)) (shift_n true (c+1) v) (Lambda.shift true c e) =
Lambda.shift true c (subst (x + c) (shift_n true c v) e).
Proof. intros. generalize dependent x. generalize dependent v. generalize dependent c. induction e ; intros ; simpl ; try auto ; try (rewrite IHe1 ; rewrite IHe2 ; auto); try (rewrite IHe3 ; auto) ; try (rewrite IHe ; auto). destruct (n =? x + c) eqn:ORIG. apply beq_nat_true in ORIG. subst. destruct (x + c <? c) eqn:ORIG. rewrite Nat.ltb_lt in ORIG. omega. simpl. destruct (x + c + 1 =? x + (c + 1)) eqn:ORIG1. apply beq_nat_true in ORIG1. unfold shift_n. rewrite shift_up_n_eq. assert (c+0=c). omega. rewrite H. auto. apply beq_nat_false in ORIG1. contradiction ORIG1. omega. destruct (n <? c) eqn:ORIG1. apply Nat.ltb_lt in ORIG1. simpl. destruct ( n =? x + (c + 1)) eqn:ORIG2. apply beq_nat_true in ORIG2. subst. omega. destruct (n <? c) eqn:ORIG3. auto. assert ((n <? c) = true -> False). intros. rewrite ORIG3 in H. inversion H. assert ((n <? c) = true). apply Nat.ltb_lt. auto. apply H in H0. contradiction. simpl. destruct (n + 1 =? x + (c + 1)) eqn:ORIG2. apply beq_nat_true in ORIG2. assert (n=x+c). omega. subst. apply beq_nat_false in ORIG. contradiction ORIG. auto. destruct (n <? c) eqn:ORIG3. inversion ORIG1. auto. unfold shift_n in *. rewrite <- foo. rewrite <- foo. assert (x+(c+1)+1=x+((c+1)+1)). omega. rewrite H. clear H. assert (S (c+1) = (c+1)+1). omega. rewrite H. clear H. rewrite IHe. assert (x+(c+1)=x+c+1). omega. rewrite H. auto. clear H. assert (c+1=S c). omega. rewrite H. auto. Qed.


Fact helper : forall x v e, subst (x + 1) (Lambda.shift true 0 v) (Lambda.shift true 0 e) = Lambda.shift true 0 (subst x v e).
Proof. intros. intros. generalize dependent x. generalize dependent v. induction e ; intros ; simpl ; auto ; try (rewrite IHe1 ; rewrite IHe2 ; auto) ; try (rewrite IHe3 ; auto) ; try (rewrite IHe ; auto).
  + destruct (n + 1 =? x + 1) eqn:ORIG.
    ++ apply beq_nat_true in ORIG. assert (n=x). omega. subst. destruct (x =? x) eqn:ORIG1. auto. apply beq_nat_false in ORIG1. contradiction ORIG1. auto.
    ++ apply beq_nat_false in ORIG. assert (n <> x). omega. destruct (n =? x) eqn:ORIG1. apply beq_nat_true in ORIG1. subst. contradiction H. auto. simpl. auto.
  + assert (Lambda.shift true 0 (Lambda.shift true 0 v) = shift_n_c true (1+1) 0 v). rewrite foo. rewrite foo. simpl. auto. rewrite H. clear H. assert (shift_n_c true (1 + 1) 0 v = shift_n true (1+1) v). unfold shift_n. auto. rewrite H. clear H. assert (x+1+1=x+(1+1)). omega. rewrite H. rewrite blah.
simpl. unfold shift_n. simpl. auto. Qed.

Fact seq_subst : forall x v e e', subst x v (e;;e') = ((subst x v e) ;; (subst x v e')).
Proof. intros. unfold seq. rewrite subst_app. rewrite subst_lam. rewrite helper. auto. Qed.

Fact shift_flush_star1 : forall c b thread base buf_size,
  Lambda.shift b c (flush_star thread base buf_size) = flush_star thread base buf_size.
Proof. intros. destruct b.
  + simpl. assert (forall x, (x + 1 = S x)). intros. omega. repeat (rewrite H). destruct thread. simpl. auto. auto.
  + simpl. assert (forall x, (x + 1 = S x)). intros. omega. repeat (rewrite H). destruct thread. simpl. auto. auto. Qed.

Fact shift_new_read_star1 : forall c b thread base buf_size e1 e2,
  Lambda.shift b c (new_read thread base buf_size e1 e2) = new_read thread base buf_size  (Lambda.shift b c e1) (Lambda.shift b c e2).
Proof. intros. destruct b.
  + unfold new_read. unfold read_code. simpl. assert (forall x, (x + 1 = S x)). intros. omega. repeat (rewrite H). destruct thread. simpl. auto. auto.
  + unfold new_read. unfold read_code. simpl. assert (forall x, (x + 1 = S x)). intros. omega. repeat (rewrite H). destruct thread. simpl. auto. auto. Qed.

Fact shift_new_write_star1 : forall c b thread base buf_size e1 e2 e3,
  Lambda.shift b c (new_write thread base buf_size e1 e2 e3) = new_write thread base buf_size  (Lambda.shift b c e1) (Lambda.shift b c e2) (Lambda.shift b c e3).
Proof. intros. destruct b.
  + unfold new_write. unfold write_code. simpl. assert (forall x, (x + 1 = S x)). intros. omega. repeat (rewrite H). destruct thread. simpl. auto. auto.
  + unfold new_write. unfold write_code. simpl. assert (forall x, (x + 1 = S x)). intros. omega. repeat (rewrite H). destruct thread. simpl. auto. auto. Qed.

Fact foo1 : forall c k e, Lambda.shift true (c + k + 1) (Lambda.shift true k e) = Lambda.shift true k (Lambda.shift true (c + k) e).
Proof. intros. generalize dependent c. generalize dependent k. induction e ; intros ; simpl ; auto ; try (rewrite IHe1 ; rewrite IHe2 ; auto) ; try (rewrite IHe3 ; auto) ; try (rewrite IHe ; auto). 
  + destruct (n <? k) eqn:ORIG.
    ++ assert (COPY:=ORIG). apply Nat.ltb_lt in ORIG. assert (n  <? c + k = true). apply Nat.ltb_lt. omega. rewrite H. apply Nat.ltb_lt in H. simpl. rewrite COPY. assert (n <? c+k+1 = true). apply Nat.ltb_lt. omega. rewrite H0. auto.
    ++ simpl. destruct (n + 1 <? c + k + 1) eqn:ORIG1. apply Nat.ltb_lt in ORIG1. assert (n <? c+k = true). apply Nat.ltb_lt. omega. rewrite H. simpl. destruct (n <? k) eqn:ORIG2. inversion ORIG. auto. assert (n + 1 <? c + k + 1 = true -> False). intros. rewrite ORIG1 in H. inversion H. destruct (n <? c + k) eqn:ORIG2. contradiction H. apply Nat.ltb_lt. apply Nat.ltb_lt in ORIG2. omega. simpl. destruct (n + 1 <? k) eqn:ORIG3. apply Nat.ltb_lt in ORIG3. assert (n<k -> False). intros. apply Nat.ltb_lt in H0. rewrite ORIG in H0. inversion H0. clear ORIG1. contradiction H0. omega. auto.
  + assert (c+k+1+1=c+(k+1)+1). omega. rewrite H. rewrite IHe. assert (c+(k+1)=c+k+1). omega. rewrite H0. auto. Qed.

Fact shift_up_seq : forall c e1 e2 , Lambda.shift true c (e1;;e2) = ((Lambda.shift true c e1);;(Lambda.shift true c e2)).
Proof. intros. unfold seq. rewrite shift_app. rewrite shift_lam. assert (Lambda.shift true (c + 1) (Lambda.shift true 0 e2) = Lambda.shift true 0 (Lambda.shift true c e2)). assert (c+0+1=c+1). omega. rewrite <- H. rewrite foo1. assert (c+0=c). omega. rewrite H0. auto. rewrite H. auto. Qed.

Fact shift_up_commutes_with_translate : forall c e thread base buf_size, translate (Lambda.shift true c e) thread base buf_size = Lambda.shift true c (translate e thread base buf_size).
Proof. intros. generalize dependent c; induction e ; intros.
  + simpl. auto.
  + simpl. auto.
  + rewrite shift_plus. rewrite translate_plus. rewrite translate_plus. rewrite shift_app. rewrite shift_plus. rewrite shift_lam. rewrite shift_up_seq. rewrite shift_flush_star1. rewrite IHe1. rewrite IHe2. destruct c; simpl ; auto.
  + rewrite shift_minus. rewrite translate_minus. rewrite translate_minus. rewrite shift_app. rewrite shift_minus. rewrite shift_lam. rewrite shift_up_seq. rewrite shift_flush_star1. rewrite IHe1. rewrite IHe2. simpl. destruct c; simpl ; auto.
  + rewrite shift_modulo. rewrite translate_modulo. rewrite translate_modulo. rewrite shift_app. rewrite shift_modulo. rewrite shift_lam. rewrite shift_up_seq. rewrite shift_flush_star1. rewrite IHe1. rewrite IHe2. destruct c; simpl ; auto.
  + simpl. auto.
  + simpl. auto.
  + rewrite shift_less_than. rewrite translate_less_than. rewrite translate_less_than. rewrite shift_app. rewrite shift_less_than. rewrite shift_lam. rewrite shift_up_seq. rewrite shift_flush_star1. rewrite IHe1. rewrite IHe2. destruct c; simpl ; auto.
  + rewrite shift_not. rewrite translate_not. rewrite translate_not. rewrite shift_app. rewrite shift_not. rewrite shift_lam. rewrite shift_up_seq. rewrite shift_flush_star1. rewrite IHe. destruct c; simpl ; auto.
  + rewrite shift_and. rewrite translate_and. rewrite translate_and. rewrite shift_app. rewrite shift_and. rewrite shift_lam. rewrite shift_up_seq. rewrite shift_flush_star1. rewrite IHe1. rewrite IHe2. simpl. destruct c; simpl ; auto.
  + simpl. auto.
  + rewrite shift_read. rewrite translate_read. rewrite translate_read. rewrite shift_app. rewrite IHe1. rewrite IHe2. rewrite shift_new_read_star1. rewrite shift_lam. rewrite shift_up_seq. rewrite shift_flush_star1. destruct c; simpl ; auto.
  + rewrite shift_write. rewrite translate_write. rewrite translate_write. rewrite shift_app. rewrite IHe1. rewrite IHe2. rewrite IHe3. rewrite shift_new_write_star1. rewrite shift_lam. rewrite shift_up_seq. rewrite shift_flush_star1. simpl (Lambda.shift true (0 + 1) (var 0)). destruct c; simpl ; auto.
  + rewrite shift_reference. rewrite translate_reference. rewrite translate_reference. rewrite shift_app. rewrite shift_reference. rewrite shift_lam. rewrite shift_up_seq. rewrite shift_flush_star1. rewrite IHe. destruct c; simpl ; auto.
  + rewrite shift_cast. rewrite translate_cast. rewrite translate_cast. rewrite shift_app. rewrite shift_cast. rewrite shift_lam. rewrite shift_up_seq. rewrite shift_flush_star1. rewrite IHe. destruct c; simpl ; auto.
  + rewrite shift_case. rewrite translate_case. rewrite translate_case. rewrite shift_case. rewrite shift_up_seq. rewrite shift_flush_star1. rewrite shift_up_seq. rewrite shift_flush_star1. rewrite IHe1. rewrite IHe2. rewrite IHe3. destruct c; simpl ; auto.
  + simpl. destruct (n <? c); simpl ; auto.
  + rewrite shift_app. rewrite translate_app. rewrite translate_app. rewrite shift_app. rewrite IHe1. rewrite IHe2. destruct c; simpl ; auto.
  + rewrite shift_lam. rewrite translate_lam. rewrite translate_lam. rewrite shift_lam. rewrite shift_up_seq. rewrite shift_flush_star1. rewrite IHe. auto.
  + rewrite shift_paire. rewrite translate_paire. rewrite translate_paire. rewrite shift_paire. rewrite IHe1. rewrite IHe2. destruct c; simpl ; auto.
  + rewrite shift_first. rewrite translate_first. rewrite translate_first. rewrite shift_app. rewrite shift_first. rewrite shift_lam. rewrite shift_up_seq. rewrite shift_flush_star1. rewrite IHe. destruct c; simpl ; auto.
  + rewrite shift_second. rewrite translate_second. rewrite translate_second. rewrite shift_app. rewrite shift_second. rewrite shift_lam. rewrite shift_up_seq. rewrite shift_flush_star1. rewrite IHe. destruct c; simpl ; auto. Qed.

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
  + rewrite subst_lam. rewrite translate_lam. rewrite translate_lam. rewrite subst_lam. rewrite seq_subst. rewrite subst_flush_star1. rewrite IHe. rewrite shift_up_commutes_with_translate. auto.
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

Fixpoint remove x l :=
  match l with
    | nil => nil
    | y :: l => if (x =? y) then remove x l else y :: (remove x l)
end.

Fact remove_id1 : forall y l x, In y l -> y <> x -> In y (remove x l).
Proof. intros. induction l.
  + inversion H.
  + simpl. destruct (x =? a) eqn:ORIG.
    ++ apply beq_nat_true in ORIG. subst. apply IHl. destruct H. contradiction H0. auto. auto.
    ++ simpl. destruct H. subst. left. reflexivity. right. apply IHl. auto. Qed.


Fact remove_id2 : forall x l, remove x l = nil -> (l = nil \/ (forall y, In y l -> y = x)).
Proof. intros. induction l.
  + left. auto.
  + right. intros. simpl in H. simpl in H0. destruct (x =? a) eqn:ORIG.
    ++ apply beq_nat_true in ORIG. subst. destruct H0. auto. apply IHl in H. destruct H. subst. inversion H0. apply H. auto.
    ++ inversion H. Qed.

Fact remove_in_iff : forall x y l, In y (remove x l) <-> ((x=y -> False) /\ (In y l)).
Proof. intros. unfold iff. split.
  + intros. generalize dependent x. generalize dependent y. induction l ; intros.
    ++ inversion H.
    ++ simpl in H. destruct (x =? a) eqn:ORIG.
       +++ apply beq_nat_true in ORIG. subst. apply IHl in H. destruct H. split. auto. right. auto.
       +++ simpl in H. apply beq_nat_false in ORIG. destruct H.
           ++++ subst. split. auto. left. auto.
           ++++ apply IHl in H. destruct H. split. auto. right. auto.
  + intros. apply remove_id1. destruct H. auto. destruct H. auto.
Qed.

Fixpoint fvs (e : term) : (list nat) :=
  match e with
    | array _ => nil
    | num _ => nil
    | plus e1 e2 => (fvs e1) ++ (fvs e2)
    | minus e1 e2 =>  (fvs e1) ++ (fvs e2)
    | modulo e1 e2 =>  (fvs e1) ++ (fvs e2)
    | tru => nil
    | fls => nil
    | less_than e1 e2 =>  (fvs e1) ++ (fvs e2)
    | not e => fvs e
    | and e1 e2 =>  (fvs e1) ++ (fvs e2)
    | yunit => nil
    | write e1 e2 e3 => (fvs e1) ++ (fvs e2) ++ (fvs e3)
    | read e1 e2 =>  (fvs e1) ++ (fvs e2)
    | reference e => fvs e
    | cast e => fvs e
    | case e1 e2 e3 => (fvs e1) ++ (fvs e2) ++ (fvs e3)
    | var y => y :: nil
    | app e1 e2 =>  (fvs e1) ++ (fvs e2)
    | lam e => map (fun x => x - 1) (remove 0 (fvs e))
    | paire e1 e2 => (fvs e1) ++ (fvs e2)
    | first e => fvs e
    | second e => fvs e
  end.

Fact foo2 : forall n e b, (forall k, In k (fvs e) -> k < n) -> Lambda.shift b n e = e.
Proof. intros. generalize dependent n. generalize dependent b. induction e ; intros ; simpl in * ; try auto.
  + rewrite IHe1. rewrite IHe2. auto. intros. apply H. apply in_app_iff. right. auto. intros. apply H. apply in_app_iff. left. auto.
  + rewrite IHe1. rewrite IHe2. auto. intros. apply H. apply in_app_iff. right. auto. intros. apply H. apply in_app_iff. left. auto.
  + rewrite IHe1. rewrite IHe2. auto. intros. apply H. apply in_app_iff. right. auto. intros. apply H. apply in_app_iff. left. auto.
  + rewrite IHe1. rewrite IHe2. auto. intros. apply H. apply in_app_iff. right. auto. intros. apply H. apply in_app_iff. left. auto.
  + rewrite IHe. auto. auto.
  + rewrite IHe1. rewrite IHe2. auto. intros. apply H. apply in_app_iff. right. auto. intros. apply H. apply in_app_iff. left. auto.
  + rewrite IHe1. rewrite IHe2. auto. intros. apply H. apply in_app_iff. right. auto. intros. apply H. apply in_app_iff. left. auto.
  + rewrite IHe1. rewrite IHe2. rewrite IHe3. auto. intros. apply H. rewrite in_app_iff. rewrite in_app_iff. right. right. auto. intros. apply H. rewrite in_app_iff. rewrite in_app_iff. right. left. auto. intros. apply H. rewrite in_app_iff. left. auto.
  + rewrite IHe. auto. auto.
  + rewrite IHe. auto. auto.
  + rewrite IHe1. rewrite IHe2. rewrite IHe3. auto. intros. apply H. rewrite in_app_iff. rewrite in_app_iff. right. right. auto. intros. apply H. rewrite in_app_iff. rewrite in_app_iff. right. left. auto. intros. apply H. rewrite in_app_iff. left. auto.
  + destruct (n <? n0) eqn:ORIG.
    ++ auto.
    ++ assert (n < n0). apply H. left. auto. apply Nat.ltb_ge in ORIG. omega.
  + rewrite IHe1. rewrite IHe2. auto. intros. apply H. apply in_app_iff. right. auto. intros. apply H. apply in_app_iff. left. auto.
  + rewrite IHe. auto. intros. destruct k.
    ++ omega.
    ++ assert (k < n). apply H. apply in_map_iff. refine (ex_intro _ (S k) _). split. omega. apply remove_in_iff. split. omega. auto. omega.
  + rewrite IHe1. rewrite IHe2. auto. intros. apply H. apply in_app_iff. right. auto. intros. apply H. apply in_app_iff. left. auto.
  + rewrite IHe. auto. auto.
  + rewrite IHe. auto. auto.
Qed.

Fact foo3 : forall c k e, c > 0 -> Lambda.shift true k (Lambda.shift false (c+k) e) = Lambda.shift false (c+k+1) (Lambda.shift true k e).
Proof. intros. generalize dependent c. generalize dependent k. induction e ; intros ; simpl in * ; try auto ; try (rewrite IHe1; try (rewrite IHe2); auto ; auto) ; try (rewrite IHe3 ; auto ; auto) ; try (rewrite IHe ; auto ; auto). destruct (n <? c + k) eqn:ORIG; destruct (n <? k) eqn:ORIG1. replace (n <? c + k + 1) with true. auto. symmetry. apply Nat.ltb_lt. apply Nat.ltb_lt in ORIG. omega. replace (n + 1 <? c+k + 1) with true. auto. symmetry. apply Nat.ltb_lt. apply Nat.ltb_lt in ORIG. omega. destruct (n - 1 <? k) eqn:ORIG2. apply Nat.ltb_ge in ORIG. apply Nat.ltb_lt in ORIG1. omega. replace (n <? c+k+1) with true. apply Nat.ltb_ge in ORIG. assert (n >0). omega. destruct n. omega. simpl. replace (n-0+1) with (S n). auto. omega. symmetry. apply Nat.ltb_lt. apply Nat.ltb_lt in ORIG1. apply Nat.ltb_ge in ORIG. apply Nat.ltb_ge in ORIG2. omega. replace (n+1 <? c+k+1) with false. replace (n - 1 <? k) with false. apply Nat.ltb_ge in ORIG. destruct n. omega. simpl. replace (n-0+1) with (n+1-0). auto. omega. symmetry. apply Nat.ltb_ge. apply Nat.ltb_ge in ORIG. apply Nat.ltb_ge in ORIG1. omega. symmetry. apply Nat.ltb_ge. apply Nat.ltb_ge in ORIG. omega. replace (c+k+1) with (c+(k+1)). rewrite IHe. auto. auto. omega. Qed.


Fact foo4 : forall e b k m, k <= m -> ((fvs e = nil) \/ (forall p, In p (fvs e) -> ((p < k) \/ (p >= m)))) -> Lambda.shift b k e = Lambda.shift b m e.
Proof. intros. generalize dependent k. generalize dependent b.  generalize dependent m. induction e ; intros ; simpl in * ; try auto.
  + rewrite IHe1 with (m:=m). rewrite IHe2 with (m:=m). auto. auto. 
    ++ destruct H0.
       +++ apply app_eq_nil in H0. destruct H0. left. auto.
       +++ right. intros. apply H0. apply in_or_app. right. auto.
    ++ auto.
    ++ destruct H0.
       +++ apply app_eq_nil in H0. destruct H0. left. auto.
       +++  right. intros. apply H0. apply in_or_app. left. auto.
  + rewrite IHe1 with (m:=m). rewrite IHe2 with (m:=m). auto. auto. 
    ++ destruct H0.
       +++ apply app_eq_nil in H0. destruct H0. left. auto.
       +++ right. intros. apply H0. apply in_or_app. right. auto.
    ++ auto.
    ++ destruct H0.
       +++ apply app_eq_nil in H0. destruct H0. left. auto.
       +++  right. intros. apply H0. apply in_or_app. left. auto.
  + rewrite IHe1 with (m:=m). rewrite IHe2 with (m:=m). auto. auto. 
    ++ destruct H0.
       +++ apply app_eq_nil in H0. destruct H0. left. auto.
       +++ right. intros. apply H0. apply in_or_app. right. auto.
    ++ auto.
    ++ destruct H0.
       +++ apply app_eq_nil in H0. destruct H0. left. auto.
       +++  right. intros. apply H0. apply in_or_app. left. auto.
  + rewrite IHe1 with (m:=m). rewrite IHe2 with (m:=m). auto. auto. 
    ++ destruct H0.
       +++ apply app_eq_nil in H0. destruct H0. left. auto.
       +++ right. intros. apply H0. apply in_or_app. right. auto.
    ++ auto.
    ++ destruct H0.
       +++ apply app_eq_nil in H0. destruct H0. left. auto.
       +++  right. intros. apply H0. apply in_or_app. left. auto.
  + rewrite IHe with (m:=m). auto. auto. auto.
  + rewrite IHe1 with (m:=m). rewrite IHe2 with (m:=m). auto. auto. 
    ++ destruct H0.
       +++ apply app_eq_nil in H0. destruct H0. left. auto.
       +++ right. intros. apply H0. apply in_or_app. right. auto.
    ++ auto.
    ++ destruct H0.
       +++ apply app_eq_nil in H0. destruct H0. left. auto.
       +++  right. intros. apply H0. apply in_or_app. left. auto.
  + rewrite IHe1 with (m:=m). rewrite IHe2 with (m:=m). auto. auto. 
    ++ destruct H0.
       +++ apply app_eq_nil in H0. destruct H0. left. auto.
       +++ right. intros. apply H0. apply in_or_app. right. auto.
    ++ auto.
    ++ destruct H0.
       +++ apply app_eq_nil in H0. destruct H0. left. auto.
       +++  right. intros. apply H0. apply in_or_app. left. auto.
  + rewrite IHe1 with (m:=m). rewrite IHe2 with (m:=m). rewrite IHe3 with (m:=m). auto. auto. 
    ++ destruct H0.
       +++ apply app_eq_nil in H0. destruct H0. apply app_eq_nil in H1. destruct H1. left. auto.
       +++ right. intros. apply H0. apply in_or_app. right.  apply in_or_app. right. auto.
    ++ auto.
    ++ destruct H0.
       +++ apply app_eq_nil in H0. destruct H0. apply app_eq_nil in H1. destruct H1. left. auto.
       +++  right. intros. apply H0. apply in_or_app. right. apply in_or_app. left. auto.
    ++ auto.
    ++ destruct H0.
       +++ apply app_eq_nil in H0. destruct H0. left. auto.
       +++ right. intros. apply H0. apply in_or_app. left. auto.
  + rewrite IHe with (m:=m). auto. auto. auto.
  + rewrite IHe with (m:=m). auto. auto. auto.
  + rewrite IHe1 with (m:=m). rewrite IHe2 with (m:=m). rewrite IHe3 with (m:=m). auto. auto. 
    ++ destruct H0.
       +++ apply app_eq_nil in H0. destruct H0. apply app_eq_nil in H1. destruct H1. left. auto.
       +++ right. intros. apply H0. apply in_or_app. right.  apply in_or_app. right. auto.
    ++ auto.
    ++ destruct H0.
       +++ apply app_eq_nil in H0. destruct H0. apply app_eq_nil in H1. destruct H1. left. auto.
       +++  right. intros. apply H0. apply in_or_app. right. apply in_or_app. left. auto.
    ++ auto.
    ++ destruct H0.
       +++ apply app_eq_nil in H0. destruct H0. left. auto.
       +++ right. intros. apply H0. apply in_or_app. left. auto.
  +  destruct H0.
    ++ inversion H0.
    ++ assert (n < k \/ n >= m). apply H0. left. auto. destruct H1.
       +++ replace (n <? k) with true. replace (n <? m) with true. auto. symmetry. apply Nat.ltb_lt. omega. symmetry. apply Nat.ltb_lt. auto.
       +++ replace (n <? k) with false. replace (n <? m) with false. auto. symmetry. apply Nat.ltb_ge. omega. symmetry. apply Nat.ltb_ge. omega.
  + rewrite IHe1 with (m:=m). rewrite IHe2 with (m:=m). auto. auto. 
    ++ destruct H0.
       +++ apply app_eq_nil in H0. destruct H0. left. auto.
       +++ right. intros. apply H0. apply in_or_app. right. auto.
    ++ auto.
    ++ destruct H0.
       +++ apply app_eq_nil in H0. destruct H0. left. auto.
       +++  right. intros. apply H0. apply in_or_app. left. auto.
  + rewrite IHe with (m:=m+1). auto. omega. destruct H0. apply map_eq_nil in H0. apply remove_id2 in H0. destruct H0. left. auto. right. intros. assert (p=0). apply H0. auto. subst. left. omega. right. intros. destruct p. left. omega. assert (In p (map (fun x : nat => x - 1) (remove 0 (fvs e)))). apply in_map_iff. refine (ex_intro _ (S p) _). split. omega. apply remove_in_iff. split. omega. auto. apply H0 in H2. destruct H2. left. omega. right. omega.
  + rewrite IHe1 with (m:=m). rewrite IHe2 with (m:=m). auto. auto. 
    ++ destruct H0.
       +++ apply app_eq_nil in H0. destruct H0. left. auto.
       +++ right. intros. apply H0. apply in_or_app. right. auto.
    ++ auto.
    ++ destruct H0.
       +++ apply app_eq_nil in H0. destruct H0. left. auto.
       +++  right. intros. apply H0. apply in_or_app. left. auto.
  + rewrite IHe with (m:=m). auto. auto. auto.
  + rewrite IHe with (m:=m). auto. auto. auto.
Qed.

Fact foo5 : forall k e, (In k (fvs e) -> False) -> Lambda.shift true k (Lambda.shift false k e) = Lambda.shift false (k+1) (Lambda.shift true k e).
Proof. intros. generalize dependent k. induction e ; intros ; simpl in * ; try auto.
  + rewrite IHe1. rewrite IHe2. auto. intros. contradiction H. apply in_app_iff. right. auto. intros. contradiction H. apply in_app_iff. left. auto.
  + rewrite IHe1. rewrite IHe2. auto. intros. contradiction H. apply in_app_iff. right. auto. intros. contradiction H. apply in_app_iff. left. auto.
  + rewrite IHe1. rewrite IHe2. auto. intros. contradiction H. apply in_app_iff. right. auto. intros. contradiction H. apply in_app_iff. left. auto.
  + rewrite IHe1. rewrite IHe2. auto. intros. contradiction H. apply in_app_iff. right. auto. intros. contradiction H. apply in_app_iff. left. auto.
  + rewrite IHe. auto. auto.
  + rewrite IHe1. rewrite IHe2. auto. intros. contradiction H. apply in_app_iff. right. auto. intros. contradiction H. apply in_app_iff. left. auto.
  + rewrite IHe1. rewrite IHe2. auto. intros. contradiction H. apply in_app_iff. right. auto. intros. contradiction H. apply in_app_iff. left. auto.
  + rewrite IHe1. rewrite IHe2. rewrite IHe3. auto. intros. apply H. apply in_app_iff. right. apply in_app_iff. right. auto. intros. apply H. apply in_app_iff. right. apply in_app_iff. left. auto. intros. apply H. apply in_app_iff. left. auto.
  + rewrite IHe. auto. auto.
  + rewrite IHe. auto. auto.
  + rewrite IHe1. rewrite IHe2. rewrite IHe3. auto. intros. apply H. apply in_app_iff. right. apply in_app_iff. right. auto. intros. apply H. apply in_app_iff. right. apply in_app_iff. left. auto. intros. apply H. apply in_app_iff. left. auto.
  + destruct (n <? k) eqn:ORIG.
    ++ rewrite ORIG. replace (n <? k + 1) with true. auto. symmetry. apply Nat.ltb_lt. apply Nat.ltb_lt in ORIG. omega.
    ++ replace (n+1 <? k+1) with false. destruct (n-1 <? k) eqn:ORIG2.
       +++ apply Nat.ltb_lt in ORIG2. apply Nat.ltb_ge in ORIG. assert (n=k). omega. subst. contradiction H. left. auto.
       +++ destruct n.
           ++++ simpl in *. apply Nat.ltb_ge in ORIG. assert (k=0). omega. subst. contradiction H. left. auto.
           ++++ replace (S n-1+1) with (S n + 1 -1). auto. omega.
       +++ symmetry. apply Nat.ltb_ge. apply Nat.ltb_ge in ORIG. omega.
  + rewrite IHe1. rewrite IHe2. auto. intros. contradiction H. apply in_app_iff. right. auto. intros. contradiction H. apply in_app_iff. left. auto.
  + rewrite IHe. auto. intros. rewrite in_map_iff in H. apply H. refine (ex_intro _ (S k) _). split. omega. apply remove_in_iff. split. omega. replace (S k) with (k+1). auto. omega.
  + rewrite IHe1. rewrite IHe2. auto. intros. contradiction H. apply in_app_iff. right. auto. intros. contradiction H. apply in_app_iff. left. auto.
  + rewrite IHe. auto. auto.
  + rewrite IHe. auto. auto.
Qed.


Fact shift_down_seq : forall c e1 e2 , (c = 0 -> (In 0 (fvs e2) -> False)) -> Lambda.shift false c (e1;;e2) = ((Lambda.shift false c e1);;(Lambda.shift false c e2)).
Proof. intros. unfold seq. rewrite shift_app. rewrite shift_lam. destruct c ; simpl.
  + assert (In 0 (fvs e2) -> False). apply H. auto. rewrite foo5. auto. auto.
  + replace (S c) with (c+1+0). rewrite foo3. replace (S (c+1)) with (c+1+0+1). auto. omega. omega. omega. 
Qed.

Fact fvs_array : forall n, fvs (array n) = nil.
Proof. intros. simpl. auto. Qed.

Fact fvs_num : forall n, fvs (num n) = nil.
Proof. intros. simpl. auto. Qed.

Fact fvs_tru : fvs tru = nil.
Proof. intros. simpl. auto. Qed.

Fact fvs_fls : fvs fls = nil.
Proof. intros. simpl. auto. Qed.

Fact fvs_plus : forall e1 e2, fvs (plus e1 e2) = (fvs e1) ++ (fvs e2).
Proof. intros. simpl. auto. Qed.

Fact fvs_minus : forall e1 e2, fvs (minus e1 e2) = (fvs e1) ++ (fvs e2).
Proof. intros. simpl. auto. Qed.


Fact fvs_app : forall e1 e2, fvs (app e1 e2) = (fvs e1) ++ (fvs e2).
Proof. intros. simpl. auto. Qed.
Fact fvs_modulo : forall e1 e2, fvs (modulo e1 e2) = (fvs e1) ++ (fvs e2).
Proof. intros. simpl. auto. Qed.
Fact fvs_and : forall e1 e2, fvs (and e1 e2) = (fvs e1) ++ (fvs e2).
Proof. intros. simpl. auto. Qed.
Fact fvs_less_than : forall e1 e2, fvs (less_than e1 e2) = (fvs e1) ++ (fvs e2).
Proof. intros. simpl. auto. Qed.
Fact fvs_paire : forall e1 e2, fvs (paire e1 e2) = (fvs e1) ++ (fvs e2).
Proof. intros. simpl. auto. Qed.
Fact fvs_read : forall e1 e2, fvs (read e1 e2) = (fvs e1) ++ (fvs e2).
Proof. intros. simpl. auto. Qed.
Fact fvs_case : forall e1 e2 e3, fvs (case e1 e2 e3) = (fvs e1) ++ (fvs e2) ++ (fvs e3).
Proof. intros. simpl. auto. Qed.
Fact fvs_write : forall e1 e2 e3, fvs (write e1 e2 e3) = (fvs e1) ++ (fvs e2) ++ (fvs e3).
Proof. intros. simpl. auto. Qed.
Fact fvs_not : forall e, fvs (not e) = fvs e.
Proof. intros. simpl. auto. Qed.
Fact fvs_reference : forall e, fvs (reference e) = fvs e.
Proof. intros. simpl. auto. Qed.
Fact fvs_first : forall e, fvs (first e) = fvs e.
Proof. intros. simpl. auto. Qed.
Fact fvs_second : forall e, fvs (second e) = fvs e.
Proof. intros. simpl. auto. Qed.
Fact fvs_cast : forall e, fvs (cast e) = fvs e.
Proof. intros. simpl. auto. Qed.
Fact fvs_lam : forall e, fvs (lam e) = map (fun x => x - 1) (remove 0 (fvs e)).
Proof. intros. simpl. auto.
Qed.

Fact fvs_shift_up : forall c x e, c <= x -> (In (S x) (fvs (Lambda.shift true c e)) <-> In x (fvs e)).
Proof. intros. generalize dependent c. generalize dependent x. induction e ; intros ; simpl.
  + intuition.
  + intuition.
  + unfold iff. split.
    ++ intros. apply in_app_iff. apply in_app_iff in H0. destruct H0.
       +++ left. apply IHe1 in H. apply H. auto.
       +++ right. apply IHe2 in H. apply H. auto.
    ++ intros. apply in_app_iff. apply in_app_iff in H0. destruct H0.
       +++ left. apply IHe1 in H. apply H. auto.
       +++ right. apply IHe2 in H. apply H. auto.
  + unfold iff. split.
    ++ intros. apply in_app_iff. apply in_app_iff in H0. destruct H0.
       +++ left. apply IHe1 in H. apply H. auto.
       +++ right. apply IHe2 in H. apply H. auto.
    ++ intros. apply in_app_iff. apply in_app_iff in H0. destruct H0.
       +++ left. apply IHe1 in H. apply H. auto.
       +++ right. apply IHe2 in H. apply H. auto.  + unfold iff. split.
    ++ intros. apply in_app_iff. apply in_app_iff in H0. destruct H0.
       +++ left. apply IHe1 in H. apply H. auto.
       +++ right. apply IHe2 in H. apply H. auto.
    ++ intros. apply in_app_iff. apply in_app_iff in H0. destruct H0.
       +++ left. apply IHe1 in H. apply H. auto.
       +++ right. apply IHe2 in H. apply H. auto.
  + intuition.
  + intuition.
  + unfold iff. split.
    ++ intros. apply in_app_iff. apply in_app_iff in H0. destruct H0.
       +++ left. apply IHe1 in H. apply H. auto.
       +++ right. apply IHe2 in H. apply H. auto.
    ++ intros. apply in_app_iff. apply in_app_iff in H0. destruct H0.
       +++ left. apply IHe1 in H. apply H. auto.
       +++ right. apply IHe2 in H. apply H. auto.
  + apply IHe in H. auto.
  + unfold iff. split.
    ++ intros. apply in_app_iff. apply in_app_iff in H0. destruct H0.
       +++ left. apply IHe1 in H. apply H. auto.
       +++ right. apply IHe2 in H. apply H. auto.
    ++ intros. apply in_app_iff. apply in_app_iff in H0. destruct H0.
       +++ left. apply IHe1 in H. apply H. auto.
       +++ right. apply IHe2 in H. apply H. auto.
  + intuition.
  + unfold iff. split.
    ++ intros. apply in_app_iff. apply in_app_iff in H0. destruct H0.
       +++ left. apply IHe1 in H. apply H. auto.
       +++ right. apply IHe2 in H. apply H. auto.
    ++ intros. apply in_app_iff. apply in_app_iff in H0. destruct H0.
       +++ left. apply IHe1 in H. apply H. auto.
       +++ right. apply IHe2 in H. apply H. auto.
  + unfold iff. split.
    ++ intros. apply in_app_iff. apply in_app_iff in H0. destruct H0.
       +++ left. apply IHe1 in H. apply H. auto.
       +++ apply in_app_iff in H0. destruct H0. right. apply IHe2 in H. apply in_app_iff. left. apply H. auto. apply IHe3 in H. right. apply in_app_iff. right. apply H. auto.
    ++ intros. apply in_app_iff. apply in_app_iff in H0. destruct H0.
       +++ left. apply IHe1 in H. apply H. auto.
       +++ apply in_app_iff in H0. destruct H0. right. apply IHe2 in H. apply in_app_iff. left. apply H. auto. apply IHe3 in H. right. apply in_app_iff. right. apply H. auto.
  + apply IHe in H. auto.
  + apply IHe in H. auto.
  +  unfold iff. split.
    ++ intros. apply in_app_iff. apply in_app_iff in H0. destruct H0.
       +++ left. apply IHe1 in H. apply H. auto.
       +++ right. apply in_app_iff in H0. destruct H0.
           ++++ apply IHe2 in H. apply in_app_iff. left. apply H. auto.
           ++++ apply IHe3 in H. apply in_app_iff. right. apply H. auto.
    ++ intros. apply in_app_iff. apply in_app_iff in H0. destruct H0.
       +++ left. apply IHe1 in H. apply H. auto.
       +++ right. apply in_app_iff in H0. destruct H0.
           ++++ apply IHe2 in H. apply in_app_iff. left. apply H. auto.
           ++++ apply IHe3 in H. apply in_app_iff. right. apply H. auto.
  + unfold iff. split. 
    ++ intros. destruct (n <? c) eqn:ORIG.
       +++ apply Nat.ltb_lt in ORIG. destruct H0.
           ++++ subst. omega.
           ++++ contradiction H0.
       +++ destruct H0.
           ++++ left. omega.
           ++++ contradiction H0.
    ++ intros. destruct (n <? c) eqn:ORIG.
       +++ apply Nat.ltb_lt in ORIG. destruct H0.
           ++++ subst. omega.
           ++++ contradiction H0.
       +++ destruct H0.
           ++++ left. omega.
           ++++ contradiction H0.
  + unfold iff. split.
    ++ intros. apply in_app_iff. apply in_app_iff in H0. destruct H0.
       +++ left. apply IHe1 in H. apply H. auto.
       +++ right. apply IHe2 in H. apply H. auto.
    ++ intros. apply in_app_iff. apply in_app_iff in H0. destruct H0.
       +++ left. apply IHe1 in H. apply H. auto.
       +++ right. apply IHe2 in H. apply H. auto.
  + unfold iff. split.
    ++ intros. apply in_map_iff. apply in_map_iff in H0. destruct H0. destruct H0. apply remove_in_iff in H1. destruct H1. replace x0 with (S (S x)) in *. apply IHe in H2. refine (ex_intro _ (S x) _). split. omega. apply remove_in_iff. split. omega. auto. omega. omega.
    ++ intros. intros. apply in_map_iff. apply in_map_iff in H0. destruct H0. destruct H0. apply remove_in_iff in H1. destruct H1. replace x0 with ((S x)) in *. assert (S c <= S x). omega. apply IHe in H3. refine (ex_intro _ (S (S x)) _ ). split. omega. apply remove_in_iff. split. omega. replace (S c) with (c+1) in *. apply H3. auto. omega. omega.
  + unfold iff. split.
    ++ intros. apply in_app_iff. apply in_app_iff in H0. destruct H0.
       +++ left. apply IHe1 in H. apply H. auto.
       +++ right. apply IHe2 in H. apply H. auto.
    ++ intros. apply in_app_iff. apply in_app_iff in H0. destruct H0.
       +++ left. apply IHe1 in H. apply H. auto.
       +++ right. apply IHe2 in H. apply H. auto.
  + apply IHe in H. auto.
  + apply IHe in H. auto.
Qed.

Fact fvs_translate : forall e thread base buf_size, (forall x, In x (fvs e) <-> In x (fvs (translate e thread base buf_size))).
Proof. intros. generalize dependent x. induction e ; intros.
  + simpl. intuition.
  + simpl. intuition.
  + rewrite translate_plus. rewrite fvs_plus. rewrite fvs_app. unfold iff. split.
    ++ intros. destruct thread.
       +++ simpl. apply in_app_iff in H. destruct H. apply in_app_iff. left. apply IHe1. auto. apply in_app_iff. right. apply IHe2. auto.
       +++ simpl. apply in_app_iff in H. destruct H. apply in_app_iff. left. apply IHe1. auto. apply in_app_iff. right. apply IHe2. auto.
    ++ intros. destruct thread.
       +++ simpl in *. apply in_app_iff. apply in_app_iff in H. destruct H.
           ++++ left. apply IHe1. auto.
           ++++ right. apply IHe2. auto.
       +++ simpl in *. apply in_app_iff. apply in_app_iff in H. destruct H.
           ++++ left. apply IHe1. auto.
           ++++ right. apply IHe2. auto.
  + rewrite translate_minus. rewrite fvs_minus. rewrite fvs_app. unfold iff. split.
    ++ intros. destruct thread.
       +++ simpl. apply in_app_iff in H. destruct H. apply in_app_iff. left. apply IHe1. auto. apply in_app_iff. right. apply IHe2. auto.
       +++ simpl. apply in_app_iff in H. destruct H. apply in_app_iff. left. apply IHe1. auto. apply in_app_iff. right. apply IHe2. auto.
    ++ intros. destruct thread.
       +++ simpl in *. apply in_app_iff. apply in_app_iff in H. destruct H.
           ++++ left. apply IHe1. auto.
           ++++ right. apply IHe2. auto.
       +++ simpl in *. apply in_app_iff. apply in_app_iff in H. destruct H.
           ++++ left. apply IHe1. auto.
           ++++ right. apply IHe2. auto.
  + rewrite translate_modulo. rewrite fvs_modulo. rewrite fvs_app. unfold iff. split.
    ++ intros. destruct thread.
       +++ simpl. apply in_app_iff in H. destruct H. apply in_app_iff. left. apply IHe1. auto. apply in_app_iff. right. apply IHe2. auto.
       +++ simpl. apply in_app_iff in H. destruct H. apply in_app_iff. left. apply IHe1. auto. apply in_app_iff. right. apply IHe2. auto.
    ++ intros. destruct thread.
       +++ simpl in *. apply in_app_iff. apply in_app_iff in H. destruct H.
           ++++ left. apply IHe1. auto.
           ++++ right. apply IHe2. auto.
       +++ simpl in *. apply in_app_iff. apply in_app_iff in H. destruct H.
           ++++ left. apply IHe1. auto.
           ++++ right. apply IHe2. auto.
  + simpl. intuition.
  + simpl. intuition.
  + rewrite translate_less_than. rewrite fvs_less_than. rewrite fvs_app. unfold iff. split.
    ++ intros. destruct thread.
       +++ simpl. apply in_app_iff in H. destruct H. apply in_app_iff. left. apply IHe1. auto. apply in_app_iff. right. apply IHe2. auto.
       +++ simpl. apply in_app_iff in H. destruct H. apply in_app_iff. left. apply IHe1. auto. apply in_app_iff. right. apply IHe2. auto.
    ++ intros. destruct thread.
       +++ simpl in *. apply in_app_iff. apply in_app_iff in H. destruct H.
           ++++ left. apply IHe1. auto.
           ++++ right. apply IHe2. auto.
       +++ simpl in *. apply in_app_iff. apply in_app_iff in H. destruct H.
           ++++ left. apply IHe1. auto.
           ++++ right. apply IHe2. auto.
  + rewrite translate_not. rewrite fvs_not. rewrite fvs_app. unfold iff. split.
    ++ intros. destruct thread.
       +++ simpl. apply IHe. auto.
       +++ simpl. apply IHe. auto.
    ++ intros. destruct thread.
       +++ simpl in H. apply IHe. auto.
       +++ simpl in H. apply IHe. auto.
  + rewrite translate_and. rewrite fvs_and. rewrite fvs_app. unfold iff. split.
    ++ intros. destruct thread.
       +++ simpl. apply in_app_iff in H. destruct H. apply in_app_iff. left. apply IHe1. auto. apply in_app_iff. right. apply IHe2. auto.
       +++ simpl. apply in_app_iff in H. destruct H. apply in_app_iff. left. apply IHe1. auto. apply in_app_iff. right. apply IHe2. auto.
    ++ intros. destruct thread.
       +++ simpl in *. apply in_app_iff. apply in_app_iff in H. destruct H.
           ++++ left. apply IHe1. auto.
           ++++ right. apply IHe2. auto.
       +++ simpl in *. apply in_app_iff. apply in_app_iff in H. destruct H.
           ++++ left. apply IHe1. auto.
           ++++ right. apply IHe2. auto.
  + simpl. intuition.
  + rewrite translate_read. rewrite fvs_read. rewrite fvs_app. unfold new_read. rewrite fvs_app. unfold iff. split.
    ++ intros. destruct thread.
       +++ simpl. apply in_app_iff in H. destruct H. apply in_app_iff. left. apply IHe1. auto. apply in_app_iff. right. apply IHe2. auto.
       +++ simpl. apply in_app_iff in H. destruct H. apply in_app_iff. left. apply IHe1. auto. apply in_app_iff. right. apply IHe2. auto.
    ++ intros. destruct thread.
       +++ simpl in *. apply in_app_iff. apply in_app_iff in H. destruct H.
           ++++ left. apply IHe1. auto.
           ++++ right. apply IHe2. auto.
       +++ simpl in *. apply in_app_iff. apply in_app_iff in H. destruct H.
           ++++ left. apply IHe1. auto.
           ++++ right. apply IHe2. auto.
  + rewrite translate_write. rewrite fvs_write. rewrite fvs_app. unfold new_write. rewrite fvs_app. rewrite fvs_paire. rewrite fvs_paire. unfold iff. split.
    ++ intros. destruct thread.
       +++ simpl. apply in_app_iff in H. destruct H. apply in_app_iff. left. apply IHe1. auto. apply in_app_iff. right. apply in_app_iff in H. destruct H. apply in_app_iff. left. apply IHe2. auto. apply in_app_iff. right. apply IHe3. auto.
       +++ simpl. simpl. apply in_app_iff in H. destruct H. apply in_app_iff. left. apply IHe1. auto. apply in_app_iff. right. apply in_app_iff in H. destruct H. apply in_app_iff. left. apply IHe2. auto. apply in_app_iff. right. apply IHe3. auto.
    ++ intros. destruct thread.
       +++ simpl in *. apply in_app_iff. apply in_app_iff in H. destruct H.
           ++++ left. apply IHe1. auto.
           ++++ apply in_app_iff in H. destruct H. right. apply in_app_iff. left. apply IHe2. auto. right. apply in_app_iff. right. apply IHe3. auto.
       +++ simpl in *. apply in_app_iff. apply in_app_iff in H. destruct H.
           ++++ left. apply IHe1. auto.
           ++++ apply in_app_iff in H. destruct H. right. apply in_app_iff. left. apply IHe2. auto. right. apply in_app_iff. right. apply IHe3. auto.
  + rewrite translate_reference. rewrite fvs_reference. rewrite fvs_app. unfold iff. split.
    ++ intros. destruct thread.
       +++ simpl. apply IHe. auto.
       +++ simpl. apply IHe. auto.
    ++ intros. destruct thread.
       +++ simpl in H. apply IHe. auto.
       +++ simpl in H. apply IHe. auto.
  + rewrite translate_cast. rewrite fvs_cast. rewrite fvs_app. unfold iff. split.
    ++ intros. destruct thread.
       +++ simpl. apply IHe. auto.
       +++ simpl. apply IHe. auto.
    ++ intros. destruct thread.
       +++ simpl in H. apply IHe. auto.
       +++ simpl in H. apply IHe. auto.
  + rewrite translate_case. rewrite fvs_case. unfold iff. split.
    ++ intros. destruct thread.
       +++ simpl. apply in_app_iff in H. destruct H. apply in_app_iff. left. apply IHe1. auto. apply in_app_iff. right. apply in_app_iff in H. destruct H. apply in_app_iff. left. apply in_app_iff. left. apply in_map_iff. refine (ex_intro _ (S x) _). split. omega. apply remove_in_iff. split. omega. apply fvs_shift_up. omega. apply IHe2. auto. apply in_app_iff. right. apply in_app_iff. left. apply in_map_iff. refine (ex_intro _ (S x) _). split. omega. apply remove_in_iff. split. omega. apply fvs_shift_up. omega. apply IHe3. auto.
        +++ simpl. apply in_app_iff in H. destruct H. apply in_app_iff. left. apply IHe1. auto. apply in_app_iff. right. apply in_app_iff in H. destruct H. apply in_app_iff. left. apply in_app_iff. left. apply in_map_iff. refine (ex_intro _ (S x) _). split. omega. apply remove_in_iff. split. omega. apply fvs_shift_up. omega. apply IHe2. auto. apply in_app_iff. right. apply in_app_iff. left. apply in_map_iff. refine (ex_intro _ (S x) _). split. omega. apply remove_in_iff. split. omega. apply fvs_shift_up. omega. apply IHe3. auto.
     ++ intros. destruct thread.
        +++ simpl in H. apply in_app_iff in H. destruct H.
            ++++ apply in_app_iff. left. apply IHe1. auto.
            ++++ apply in_app_iff in H. destruct H.
                 +++++ apply in_app_iff in H. destruct H. apply in_map_iff in H. destruct H. destruct H. subst. apply remove_in_iff in H0. destruct H0. assert (exists x, x0 = S x). destruct x0. omega. refine (ex_intro _ x0 _). auto. destruct H1. subst. replace (S x - 1) with x. apply in_app_iff. right. apply in_app_iff. left. apply fvs_shift_up in H0. apply IHe2. auto. omega. omega. inversion H.
                 +++++ apply in_app_iff in H. destruct H. apply in_map_iff in H. destruct H. destruct H. subst. apply remove_in_iff in H0. destruct H0. assert (exists x, x0 = S x). destruct x0. omega. refine (ex_intro _ x0 _). auto. destruct H1. subst. replace (S x - 1) with x. apply in_app_iff. right. apply in_app_iff. right. apply fvs_shift_up in H0. apply IHe3. auto. omega. omega. inversion H.
+++ simpl in H. apply in_app_iff in H. destruct H.
            ++++ apply in_app_iff. left. apply IHe1. auto.
            ++++ apply in_app_iff in H. destruct H.
                 +++++ apply in_app_iff in H. destruct H. apply in_map_iff in H. destruct H. destruct H. subst. apply remove_in_iff in H0. destruct H0. assert (exists x, x0 = S x). destruct x0. omega. refine (ex_intro _ x0 _). auto. destruct H1. subst. replace (S x - 1) with x. apply in_app_iff. right. apply in_app_iff. left. apply fvs_shift_up in H0. apply IHe2. auto. omega. omega. inversion H.
                 +++++ apply in_app_iff in H. destruct H. apply in_map_iff in H. destruct H. destruct H. subst. apply remove_in_iff in H0. destruct H0. assert (exists x, x0 = S x). destruct x0. omega. refine (ex_intro _ x0 _). auto. destruct H1. subst. replace (S x - 1) with x. apply in_app_iff. right. apply in_app_iff. right. apply fvs_shift_up in H0. apply IHe3. auto. omega. omega. inversion H.
  + simpl. intuition.
  + rewrite translate_app. rewrite fvs_app. rewrite fvs_app. unfold iff. split.
    ++ intros. destruct thread.
       +++ simpl. apply in_app_iff in H. destruct H. apply in_app_iff. left. apply IHe1. auto. apply in_app_iff. right. apply IHe2. auto.
       +++ simpl. apply in_app_iff in H. destruct H. apply in_app_iff. left. apply IHe1. auto. apply in_app_iff. right. apply IHe2. auto.
    ++ intros. destruct thread.
       +++ simpl in *. apply in_app_iff. apply in_app_iff in H. destruct H.
           ++++ left. apply IHe1. auto.
           ++++ right. apply IHe2. auto.
       +++ simpl in *. apply in_app_iff. apply in_app_iff in H. destruct H.
           ++++ left. apply IHe1. auto.
           ++++ right. apply IHe2. auto.
  + rewrite translate_lam. rewrite fvs_lam. rewrite fvs_lam. rewrite in_map_iff. rewrite in_map_iff. unfold iff. split.
    ++ intros. destruct thread.
       +++ simpl. destruct H. destruct H. subst. apply remove_in_iff in H0. destruct H0. destruct x0. omega. refine (ex_intro _ (S x0) _). split. auto. apply remove_in_iff. split. omega. apply in_app_iff. left. apply in_map_iff. refine (ex_intro _ (S (S x0)) _ ). split. omega. apply remove_in_iff. split. omega. admit.
       +++ simpl. destruct H. destruct H. subst. apply remove_in_iff in H0. destruct H0. destruct x0. omega. refine (ex_intro _ (S x0) _). split. auto. apply remove_in_iff. split. omega. apply in_app_iff. left. apply in_map_iff. refine (ex_intro _ (S (S x0)) _ ). split. omega. apply remove_in_iff. split. omega. admit.
    ++ intros. destruct thread.
       +++ simpl in H. destruct H. destruct H. subst. apply remove_in_iff in H0. destruct H0. destruct x0. omega. refine (ex_intro _ (S x0) _). split. auto. apply remove_in_iff. split. omega. apply in_app_iff in H0. destruct H0.
           ++++ apply in_map_iff in H0. destruct H0. destruct H0. assert (x=S (S x0)). omega. subst. apply remove_in_iff in H1. destruct H1. admit.
           ++++ inversion H0.
       +++ simpl in H. destruct H. destruct H. subst. apply remove_in_iff in H0. destruct H0. destruct x0. omega. refine (ex_intro _ (S x0) _). split. auto. apply remove_in_iff. split. omega. apply in_app_iff in H0. destruct H0.
           ++++ apply in_map_iff in H0. destruct H0. destruct H0. assert (x=S (S x0)). omega. subst. apply remove_in_iff in H1. destruct H1. admit.
           ++++ inversion H0.
  + rewrite translate_paire. rewrite fvs_paire. rewrite fvs_paire. unfold iff. split.
    ++ intros. destruct thread.
       +++ simpl. apply in_app_iff in H. destruct H. apply in_app_iff. left. apply IHe1. auto. apply in_app_iff. right. apply IHe2. auto.
       +++ simpl. apply in_app_iff in H. destruct H. apply in_app_iff. left. apply IHe1. auto. apply in_app_iff. right. apply IHe2. auto.
    ++ intros. destruct thread.
       +++ simpl in *. apply in_app_iff. apply in_app_iff in H. destruct H.
           ++++ left. apply IHe1. auto.
           ++++ right. apply IHe2. auto.
       +++ simpl in *. apply in_app_iff. apply in_app_iff in H. destruct H.
           ++++ left. apply IHe1. auto.
           ++++ right. apply IHe2. auto.
  + rewrite translate_first. rewrite fvs_first. rewrite fvs_app. unfold iff. split.
    ++ intros. destruct thread.
       +++ simpl. apply IHe. auto.
       +++ simpl. apply IHe. auto.
    ++ intros. destruct thread.
       +++ simpl in H. apply IHe. auto.
       +++ simpl in H. apply IHe. auto.
  + rewrite translate_second. rewrite fvs_second. rewrite fvs_app. unfold iff. split.
    ++ intros. destruct thread.
       +++ simpl. apply IHe. auto.
       +++ simpl. apply IHe. auto.
    ++ intros. destruct thread.
       +++ simpl in H. apply IHe. auto.
       +++ simpl in H. apply IHe. auto.
Admitted.




Fact shift_down_commutes_with_translate : forall c e thread base buf_size, (c = 0 -> (In 0 (fvs e) -> False)) -> translate (Lambda.shift false c e) thread base buf_size = Lambda.shift false c (translate e thread base buf_size).
Proof. intros. generalize dependent c; induction e ; intros.
  + simpl. auto.
  + simpl. auto.
  + rewrite shift_plus. rewrite translate_plus. rewrite translate_plus. rewrite shift_app. rewrite shift_plus. rewrite shift_lam. rewrite shift_down_seq. rewrite shift_flush_star1. rewrite IHe1. rewrite IHe2. destruct c; simpl ; auto. intros. apply H. auto. simpl. apply in_app_iff. right. auto. intros. apply H. auto. simpl. apply in_app_iff. left. auto. intros. omega.
  + rewrite shift_minus. rewrite translate_minus. rewrite translate_minus. rewrite shift_app. rewrite shift_minus. rewrite shift_lam. rewrite shift_down_seq. rewrite shift_flush_star1. rewrite IHe1. rewrite IHe2. simpl. destruct c; simpl ; auto. intros. apply H. auto. simpl. apply in_app_iff. right. auto. intros. apply H. auto. simpl. apply in_app_iff. left. auto. intros. omega.
  + rewrite shift_modulo. rewrite translate_modulo. rewrite translate_modulo. rewrite shift_app. rewrite shift_modulo. rewrite shift_lam. rewrite shift_down_seq. rewrite shift_flush_star1. rewrite IHe1. rewrite IHe2. destruct c; simpl ; auto. intros. apply H. auto. simpl. apply in_app_iff. right. auto. intros. apply H. auto. simpl. apply in_app_iff. left. auto. intros. omega.
  + simpl. auto.
  + simpl. auto.
  + rewrite shift_less_than. rewrite translate_less_than. rewrite translate_less_than. rewrite shift_app. rewrite shift_less_than. rewrite shift_lam. rewrite shift_down_seq. rewrite shift_flush_star1. rewrite IHe1. rewrite IHe2. destruct c; simpl ; auto. intros. apply H. auto. simpl. apply in_app_iff. right. auto. intros. apply H. auto. simpl. apply in_app_iff. left. auto. intros. omega.
  + rewrite shift_not. rewrite translate_not. rewrite translate_not. rewrite shift_app. rewrite shift_not. rewrite shift_lam. rewrite shift_down_seq. rewrite shift_flush_star1. rewrite IHe. destruct c; simpl ; auto. simpl in H. auto. intros. omega.
  + rewrite shift_and. rewrite translate_and. rewrite translate_and. rewrite shift_app. rewrite shift_and. rewrite shift_lam. rewrite shift_down_seq. rewrite shift_flush_star1. rewrite IHe1. rewrite IHe2. simpl. destruct c; simpl ; auto. intros. apply H. auto. simpl. apply in_app_iff. right. auto. intros. apply H. auto. simpl. apply in_app_iff. left. auto. intros. omega.
  + simpl. auto.
  + rewrite shift_read. rewrite translate_read. rewrite translate_read. rewrite shift_app. rewrite IHe1. rewrite IHe2. rewrite shift_new_read_star1. rewrite shift_lam. rewrite shift_down_seq. rewrite shift_flush_star1. destruct c; simpl ; auto. intros. omega. intros. apply H. auto. simpl. apply in_app_iff. right. auto. intros. apply H. auto. simpl. apply in_app_iff. left. auto.
  + rewrite shift_write. rewrite translate_write. rewrite translate_write. rewrite shift_app. rewrite IHe1. rewrite IHe2. rewrite IHe3. rewrite shift_new_write_star1. rewrite shift_lam. rewrite shift_down_seq. rewrite shift_flush_star1. simpl (Lambda.shift true (0 + 1) (var 0)). destruct c; simpl ; auto. intros. omega. intros. apply H. auto. simpl. apply in_app_iff. right. apply in_app_iff. right. auto. intros. auto. apply H. auto. simpl. apply in_app_iff. right. apply in_app_iff. left. auto. intros. apply H. auto. simpl. apply in_app_iff. left. auto.
  + rewrite shift_reference. rewrite translate_reference. rewrite translate_reference. rewrite shift_app. rewrite shift_reference. rewrite shift_lam. rewrite shift_down_seq. rewrite shift_flush_star1. rewrite IHe. destruct c; simpl ; auto. simpl in H. auto. intros. omega.
  + rewrite shift_cast. rewrite translate_cast. rewrite translate_cast. rewrite shift_app. rewrite shift_cast. rewrite shift_lam. rewrite shift_down_seq. rewrite shift_flush_star1. rewrite IHe. destruct c; simpl ; auto. simpl in H. auto. intros. omega.
  + rewrite shift_case. rewrite translate_case. rewrite translate_case. rewrite shift_case. rewrite IHe1. rewrite IHe2. rewrite IHe3. rewrite shift_down_seq. rewrite shift_flush_star1. rewrite shift_down_seq. rewrite shift_flush_star1. destruct c; simpl ; auto. admit. admit. intros. apply H. auto. simpl. apply in_app_iff. right. apply in_app_iff. right. auto. intros. auto. apply H. auto. simpl. apply in_app_iff. right. apply in_app_iff. left. auto. intros. apply H. auto. simpl. apply in_app_iff. left. auto.
  + simpl. auto.
  + rewrite shift_app. rewrite translate_app. rewrite translate_app. rewrite shift_app. rewrite IHe1. rewrite IHe2. destruct c; simpl ; auto. intros. apply H. auto. simpl. apply in_app_iff. right. auto. intros. apply H. auto. simpl. apply in_app_iff. left. auto.
  + rewrite shift_lam. rewrite translate_lam. rewrite translate_lam. rewrite shift_lam. rewrite shift_down_seq. rewrite shift_flush_star1. rewrite IHe. auto. intros. omega. intros. omega.
  + rewrite shift_paire. rewrite translate_paire. rewrite translate_paire. rewrite shift_paire. rewrite IHe1. rewrite IHe2. destruct c; simpl ; auto. intros. apply H. auto. simpl. apply in_app_iff. right. auto. intros. apply H. auto. simpl. apply in_app_iff. left. auto.
  + rewrite shift_first. rewrite translate_first. rewrite translate_first. rewrite shift_app. rewrite shift_first. rewrite shift_lam. rewrite shift_down_seq. rewrite shift_flush_star1. rewrite IHe. destruct c; simpl ; auto. simpl in H. auto. intros. omega.
  + rewrite shift_second. rewrite translate_second. rewrite translate_second. rewrite shift_app. rewrite shift_second. rewrite shift_lam. rewrite shift_down_seq. rewrite shift_flush_star1. rewrite IHe. destruct c; simpl ; auto.  simpl in H. auto. intros. omega. Admitted.

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
