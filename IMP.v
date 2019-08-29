Require Import List.
Require Import ZArith.
Require Import Util.

(* IMP with fixed width arrays *)
Inductive term : Type :=
  | var : nat -> term
  | num : Z -> term
  | plus : term -> term -> term
  | minus : term -> term -> term
  | modulo : term -> term -> term
  | tru : term
  | fls : term
  | less_than : term -> term -> term
  | not : term -> term
  | and : term -> term -> term
  | yunit : term
  | read : term -> term -> term (* p[offset] *)
  | write : term -> term -> term -> term (* p[offset] := n *)
  | reference : term -> term (* &p *)
  | cast : term -> term (* ( int* ) n*)
  | seq : term -> term -> term
  | ifterm : term -> term -> term -> term
  | while : term -> term -> term.

Definition or (s : term) (t : term) := not (and (not s) (not t)).

Definition equals (s : term) (t : term) := not (or (less_than s t) (less_than t s)).

Bind Scope imp_scope with term.
Notation "x == y" :=
  (equals x y) (at level 60) : imp_scope.
Notation "x << y" :=
  (less_than x y) (at level 60) : imp_scope.
Notation "'!' x" :=
  (read x (num (0%Z))) (at level 60) : imp_scope.
Notation "'&' x" :=
  (reference x) (at level 60) : imp_scope.
Notation "p '[' offset ']'" :=
  (read p offset) (at level 60) : imp_scope.
Notation "x '::=' a" :=
  (write x (num (0%Z)) a) (at level 60) : imp_scope.
Notation "x '[' offset ']' '::=' a" :=
  (write x offset a) (at level 60) : imp_scope.
Notation "c1 ;; c2" :=
  (seq c1 c2) (at level 80, right associativity) : imp_scope.
Notation "'WHILE' b 'DO' c 'DONE'" :=
  (while b c) (at level 80, right associativity) : imp_scope.
Notation "'CASE' c1 'THEN' c2 'ELSE' c3 'END'" :=
  (ifterm c1 c2 c3) (at level 80, right associativity) : imp_scope.

Inductive value : term -> Prop :=
  | val_unit : value yunit
  | val_num : forall n, value (num n).

Inductive mem_event : Type :=
    | Read (loc : nat) (offset : nat) (value : Z)
    | Write (loc : nat) (offset : nat) (value : Z)
    | Allocate (loc : nat) (size : nat) (init : list Z)
    | Reference (loc : nat) (value : nat)
    | Cast (n : nat) (loc : nat)
    | Tau.

Inductive step : term -> mem_event -> term -> Prop :=
  | step_reference1 : forall e e' event,
                  step e event e' ->
                  step (reference e) event (reference e')
  | step_reference2 : forall x n,
                    step (reference (var x)) (Reference x n) (num (Z.of_nat n))
  | step_cast1 : forall e e' event,
                  step e event e' ->
                  step (cast e) event (cast e')
  | step_cast2 : forall x n,
                    step (cast (num n)) (Cast (Z.to_nat n) x) (var x)
  | step_read1 : forall e1 e1' e2 event,
                  step e1 event e1' ->
                  step (read e1 e2) event (read e1' e2)
  | step_read2 : forall e1 e1' event n,
                  step e1 event e1' ->
                  step (read (var n) e1) event (read (var n) e1')
  | step_read3 : forall offset value n,
                step (read (var n) (num offset))
                     (Read n (Z.to_nat offset) value)
                     (num value)
  | step_write1 : forall e1 e1' e2 e3 event ,
                  step e1 event e1' ->
                  step (write e1 e2 e3) event (write e1' e2 e3)
  | step_write2 : forall e1 e1' e2 event n,
                  step e1 event e1' ->
                  step (write (var n) e1 e2) event (write (var n) e1' e2)
  | step_write3 : forall e1 e1' event n offset,
                  step e1 event e1' ->
                  step (write (var n) (num offset) e1)
                       event
                       (write (var n) (num offset) e1')
  | step_write4 : forall val n offset,
                  step (write (var n) (num offset) (num val)) 
                       (Write n (Z.to_nat offset) val)
                        yunit
  | step_plus1 : forall e1 e1' event e2,
                  step e1 event e1' ->
                  step (plus e1 e2) event (plus e1' e2)
  | step_plus2 : forall e1 e1' n event,
                  step e1 event e1' ->
                  step (plus (num n) e1) event (plus (num n) e1')
  | step_plus3 : forall m n,
                  step (plus (num m) (num n)) Tau (num (m + n))
  | step_minus1 : forall e1 e1' event e2,
                  step e1 event e1' ->
                  step (minus e1 e2) event (minus e1' e2)
  | step_minus2 : forall e1 e1' n event,
                  step e1 event e1' ->
                  step (minus (num n) e1) event (minus (num n) e1')
  | step_minus3 : forall m n,
                  step (minus (num m) (num n)) Tau (num (m - n))
  | step_mod1 : forall e1 e1' e2 event,
                  step e1 event e1' ->
                  step (modulo e1 e2) event (modulo e1' e2)
  | step_mod2 : forall e1 e1' n event,
                  step e1 event e1' ->
                  step (modulo (num n) e1) event (modulo (num n) e1')
  | step_mod3 : forall m n,
                  step (modulo (num m) (num n)) Tau (num (Z.modulo m n))
  | step_lt1 : forall e1 e1' e2 event,
                  step e1 event e1' ->
                  step (less_than e1 e2) event (less_than e1' e2)
  | step_lt2 : forall e1 e1' n event,
                  step e1 event e1' ->
                  step (less_than (num n) e1) event (less_than (num n) e1')
  | step_lt3 : forall m n,
                  (Z.ltb m n = true) ->
                  step (less_than (num m) (num n)) Tau tru
  | step_and1 : forall e1 e1' event e2,
                  step e1 event e1' ->
                  step (and e1 e2) event (and e1' e2)
  | step_and21 : forall e1 e1' event,
                  step e1 event e1' ->
                  step (and tru e1) event (and tru e1')
  | step_and22 : forall e1 e1' event,
                  step e1 event e1' ->
                  step (and fls e1) event (and fls e1')
  | step_and31 : step (and tru tru) Tau tru
  | step_and32 : step (and tru fls) Tau tru
  | step_and33 : step (and fls tru) Tau tru
  | step_and34 : step (and fls fls) Tau tru
  | step_lt4 : forall m n,
                  (Z.ltb m n = false) ->
                  step (less_than (num m) (num n)) Tau fls
  | step_not1 : forall e1 e1' event,
                  step e1 event e1' ->
                  step (not e1) event (not e1')
  | step_not2 : step (not tru) Tau fls
  | step_not3 : step (not fls) Tau tru
  | step_seq1 : forall e1 e1' e2 event,
                  step e1 event e1' ->
                  step (seq e1 e2) event (seq e1' e2)
  | step_seq2 : forall e2, step (seq yunit e2) Tau e2
  | step_ifterm1 : forall e1 e1' e2 e3 event,
                  step e1 event e1' ->
                  step (ifterm e1 e2 e3) event (ifterm e1' e2 e3)
  | step_ifterm2 : forall e2 e3,
                  step (ifterm tru e2 e3) Tau e2
  | step_ifterm3 : forall e2 e3,
                  step (ifterm fls e2 e3) Tau e3
  | step_while : forall b c,
                  step (while b c)
                        Tau
                        (ifterm b (seq c (while b c)) yunit).

