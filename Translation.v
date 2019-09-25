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

Definition new_read (thread : bool) (base : nat) (buf_size : nat) (location : term) (offset : term)  : term :=
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


Definition new_write (thread : bool) (base : nat) (buf_size : nat) (array : term) (offset : term) (value : term) : term :=
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
    | lam x e => lam x (seq (flush_star thread base buf_size) (translate e thread base buf_size))
    | app e1 e2 => 
      app (translate e1 thread base buf_size) (translate e2 thread base buf_size)
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
      app (lam "x" (seq (flush_star thread base buf_size) (var "x"))) (new_read thread base buf_size x y)
    | write e1 e2 e3 =>
      let x := translate e1 thread base buf_size in
      let y := translate e2 thread base buf_size in
      let z := translate e3 thread base buf_size in
      app (lam "x" (seq (flush_star thread base buf_size) (var "x"))) (new_write thread base buf_size x y z)
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

Fact translate_lam : forall x e thread base buf_size, translate (lam x e) thread base buf_size = lam x (seq (flush_star thread base buf_size) (translate e thread base buf_size)).
Proof. intros. simpl. reflexivity. Qed.

Fact translate_plus : forall thread base buf_size e1 e2, translate (plus e1 e2) thread base buf_size = app (lam "x" (seq (flush_star thread base buf_size) (var "x"))) (plus (translate e1 thread base buf_size) (translate e2 thread base buf_size)).
Proof. intros. simpl. reflexivity. Qed.

Fact translate_app : forall thread base buf_size e1 e2, translate (app e1 e2) thread base buf_size = app (translate e1 thread base buf_size) (translate e2 thread base buf_size).
Proof. intros. simpl. reflexivity. Qed.

Fact translate_minus : forall thread base buf_size e1 e2, translate (minus e1 e2) thread base buf_size = app (lam "x" (seq (flush_star thread base buf_size) (var "x"))) (minus (translate e1 thread base buf_size) (translate e2 thread base buf_size)).
Proof. intros. simpl. reflexivity. Qed.

Fact translate_modulo : forall thread base buf_size e1 e2, translate (modulo e1 e2) thread base buf_size = app (lam "x" (seq (flush_star thread base buf_size) (var "x"))) (modulo (translate e1 thread base buf_size) (translate e2 thread base buf_size)).
Proof. intros. simpl. reflexivity. Qed.

Fact translate_less_than : forall thread base buf_size e1 e2, translate (less_than e1 e2) thread base buf_size = app (lam "x" (seq (flush_star thread base buf_size) (var "x"))) (less_than (translate e1 thread base buf_size) (translate e2 thread base buf_size)).
Proof. intros. simpl. reflexivity. Qed.

Fact translate_and : forall thread base buf_size e1 e2, translate (and e1 e2) thread base buf_size = app (lam "x" (seq (flush_star thread base buf_size) (var "x"))) (and (translate e1 thread base buf_size) (translate e2 thread base buf_size)).
Proof. intros. simpl. reflexivity. Qed.

Fact translate_case : forall thread base buf_size e1 e2 e3, translate (case e1 e2 e3) thread base buf_size = app (lam "x" (seq (flush_star thread base buf_size) (var "x"))) (case (translate e1 thread base buf_size) (translate e2 thread base buf_size) (translate e3 thread base buf_size)).
Proof. intros. simpl. reflexivity. Qed.

Fact translate_not : forall thread base buf_size e, translate (not e) thread base buf_size = app (lam "x" (seq (flush_star thread base buf_size) (var "x"))) (not (translate e thread base buf_size)).
Proof. intros. simpl. reflexivity. Qed.

Fact translate_cast : forall thread base buf_size e, translate (cast e) thread base buf_size = app (lam "x" (seq (flush_star thread base buf_size) (var "x"))) (cast (translate e thread base buf_size)).
Proof. intros. simpl. reflexivity. Qed.

Fact translate_reference : forall thread base buf_size e, translate (reference e) thread base buf_size = app (lam "x" (seq (flush_star thread base buf_size) (var "x"))) (reference (translate e thread base buf_size)).
Proof. intros. simpl. reflexivity. Qed.

Fact translate_read : forall thread base buf_size e1 e2, translate (read e1 e2) thread base buf_size = app (lam "x" (seq (flush_star thread base buf_size) (var "x"))) (new_read thread base buf_size (translate e1 thread base buf_size) (translate e2 thread base buf_size)).
Proof. intros. simpl. reflexivity. Qed.

Fact translate_write : forall thread base buf_size e1 e2 e3, translate (write e1 e2 e3) thread base buf_size = app (lam "x" (seq (flush_star thread base buf_size) (var "x"))) (new_write thread base buf_size (translate e1 thread base buf_size) (translate e2 thread base buf_size) (translate e3 thread base buf_size)).
Proof. intros. simpl. reflexivity. Qed.

Fact subst_flush_star : forall x v thread base buf_size,
  subst x v (lam "x" (flush_star thread base buf_size;; var "x")) =
  (lam "x" (flush_star thread base buf_size;; var "x")).
Proof. intros. apply subst_idempotent. intros C. simpl in C. destruct thread; simpl in C; auto. Qed.


Fact new_read_subst : forall x v e1 e2 thread base buf_size,
  new_read thread base buf_size (subst x v e1) (subst x v e2) = subst x v (new_read thread base buf_size e1 e2).
Proof. intros. unfold new_read. rewrite subst_app. rewrite subst_app. rewrite subst_lam. rewrite subst_lam. destruct (string_dec x "location"); destruct (string_dec x "offset"); auto.
assert (subst x v
                (LOOP thread base [num 0]::= ZERO;;
                 FOUND thread base [num 0]::= ZERO;;
                 (WHILE (LOOP thread base [num 0]) << num buf_size
                  DO CASE and
                            ((BUFFER_A thread base [LOOP thread base [num 0]]) ==
                             var "location")
                            ((BUFFER_B thread base [LOOP thread base [num 0]]) ==
                             var "offset")
                     THEN (RESULT thread base [num 0]::= BUFFER_C thread base)
                          [LOOP thread base [num 0]];;
                          FOUND thread base [num 0]::= ONE ELSE yunit ESAC DONE);;
                 CASE (FOUND thread base [num 0]) == ONE
                 THEN RESULT thread base [num 0] ELSE cast (var "location") [num 0]
                 ESAC) = 
                (LOOP thread base [num 0]::= ZERO;;
                 FOUND thread base [num 0]::= ZERO;;
                 (WHILE (LOOP thread base [num 0]) << num buf_size
                  DO CASE and
                            ((BUFFER_A thread base [LOOP thread base [num 0]]) ==
                             var "location")
                            ((BUFFER_B thread base [LOOP thread base [num 0]]) ==
                             var "offset")
                     THEN (RESULT thread base [num 0]::= BUFFER_C thread base)
                          [LOOP thread base [num 0]];;
                          FOUND thread base [num 0]::= ONE ELSE yunit ESAC DONE);;
                 CASE (FOUND thread base [num 0]) == ONE
                 THEN RESULT thread base [num 0] ELSE cast (var "location") [num 0]
                 ESAC)). apply subst_idempotent. simpl. destruct thread. simpl. intros C. destruct C. contradiction n. auto. destruct H. contradiction n. auto. destruct H. contradiction n0. auto. destruct H. contradiction n0. auto. destruct H. contradiction n. auto. auto. simpl. intros C. destruct C. contradiction n. auto. destruct H. contradiction n. auto. destruct H. contradiction n0. auto. destruct H. contradiction n0. auto. destruct H. contradiction n. auto. auto. rewrite H. auto. Qed.

Fact new_write_subst : forall x v e1 e2 e3 thread base buf_size,
  new_write thread base buf_size (subst x v e1) (subst x v e2) (subst x v e3) = subst x v (new_write thread base buf_size e1 e2 e3).
intros. unfold new_write. rewrite subst_app. rewrite subst_app. rewrite subst_app. rewrite subst_lam. rewrite subst_lam. rewrite subst_lam. destruct (string_dec x "array"); destruct (string_dec x "offset"); destruct (string_dec x "value"); auto.
assert (subst x v
                      ((CASE (SIZE thread base [num 0]) == num buf_size
                        THEN flush thread buf_size base ELSE yunit ESAC);;
                       REAR thread base [num 0]
                       ::= modulo (plus (REAR thread base [num 0]) ONE)
                             (num buf_size);;
                       BUFFER_A thread base [REAR thread base [num 0]]
                       ::= (& var "array");;
                       BUFFER_B thread base [REAR thread base [num 0]]
                       ::= var "offset";;
                       BUFFER_C thread base [REAR thread base [num 0]]::= var "value";;
                       SIZE thread base [num 0]
                       ::= plus (SIZE thread base [num 0]) ONE) = 
                      ((CASE (SIZE thread base [num 0]) == num buf_size
                        THEN flush thread buf_size base ELSE yunit ESAC);;
                       REAR thread base [num 0]
                       ::= modulo (plus (REAR thread base [num 0]) ONE)
                             (num buf_size);;
                       BUFFER_A thread base [REAR thread base [num 0]]
                       ::= (& var "array");;
                       BUFFER_B thread base [REAR thread base [num 0]]
                       ::= var "offset";;
                       BUFFER_C thread base [REAR thread base [num 0]]::= var "value";;
                       SIZE thread base [num 0]
                       ::= plus (SIZE thread base [num 0]) ONE)). apply subst_idempotent. destruct thread. simpl. intros C. destruct C. contradiction n. auto. destruct H. contradiction n0. auto. destruct H. contradiction n1. auto. auto. simpl. intros C. destruct C. contradiction n. auto. destruct H. contradiction n0. auto. destruct H. contradiction n1. auto. auto. rewrite H. auto. Qed.

Fact seq_flush_subst : forall x v thread base buf_size e, subst x v (flush_star thread base buf_size;; e) =  (flush_star thread base buf_size;; (subst x v e)).
Proof. intros. unfold flush_star. unfold flush. unfold seq. rewrite subst_app. rewrite subst_app. rewrite subst_app. rewrite subst_lam. rewrite subst_lam. rewrite subst_app. rewrite subst_lam. rewrite subst_lam. rewrite subst_var. assert (subst x v (SPECIAL base [num 0]::= ONE) = (SPECIAL base [num 0]::= ONE)). apply subst_idempotent. intros C. simpl in C. auto. rewrite H. assert (subst x v
             (WHILE and ((SPECIAL base [num 0]) == ONE) (not ((SIZE thread base [num 0]) == ZERO))
              DO CASE (SIZE thread base [num 0]) == ZERO THEN yunit
                 ELSE app
                        (app (lam "x" (lam "y" (var "y")))
                           (cast (BUFFER_A thread base [FRONT thread base [num 0]])
                            [BUFFER_B thread base [FRONT thread base [num 0]]]
                            ::= (BUFFER_C thread base [FRONT thread base [num 0]])))
                        (app
                           (app (lam "x" (lam "y" (var "y")))
                              (FRONT thread base [num 0]
                               ::= modulo (plus (FRONT thread base [num 0]) ONE) (num buf_size)))
                           (SIZE thread base [num 0]::= minus (SIZE thread base [num 0]) ONE)) ESAC DONE) =
             (WHILE and ((SPECIAL base [num 0]) == ONE) (not ((SIZE thread base [num 0]) == ZERO))
              DO CASE (SIZE thread base [num 0]) == ZERO THEN yunit
                 ELSE app
                        (app (lam "x" (lam "y" (var "y")))
                           (cast (BUFFER_A thread base [FRONT thread base [num 0]])
                            [BUFFER_B thread base [FRONT thread base [num 0]]]
                            ::= (BUFFER_C thread base [FRONT thread base [num 0]])))
                        (app
                           (app (lam "x" (lam "y" (var "y")))
                              (FRONT thread base [num 0]
                               ::= modulo (plus (FRONT thread base [num 0]) ONE) (num buf_size)))
                           (SIZE thread base [num 0]::= minus (SIZE thread base [num 0]) ONE)) ESAC DONE)). apply subst_idempotent. simpl. destruct thread; simpl; auto. rewrite H0. clear H0. destruct (string_dec x "x"); destruct (string_dec x "y"); auto.
Qed.


Fact trans_subst : forall x v e thread base buf_size, 
  translate (subst x v e) thread base buf_size = subst x (translate v thread base buf_size) (translate e thread base buf_size).
Proof. intros. induction e.
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
  + rewrite subst_case. rewrite translate_case. rewrite translate_case. rewrite subst_app. rewrite subst_case. rewrite IHe1. rewrite IHe2. rewrite IHe3. rewrite subst_flush_star. reflexivity.
  + rewrite subst_var. rewrite translate_var. simpl. destruct (string_dec x s).
    ++ subst. reflexivity.
    ++ simpl. reflexivity.
  + rewrite subst_app. rewrite translate_app. rewrite translate_app. rewrite subst_app. rewrite IHe1. rewrite IHe2. reflexivity.
  + rewrite subst_lam. rewrite translate_lam. rewrite translate_lam. rewrite subst_lam.
destruct (string_dec x s).
    ++ subst. reflexivity.
    ++ rewrite IHe. rewrite seq_flush_subst. auto. Qed.

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
