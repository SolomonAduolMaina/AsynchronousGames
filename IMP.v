Require Import List.
Require Import Util.

(* IMP with fixed width arrays *)
Inductive term : Type :=
  | var : nat -> term
  | num : nat -> term
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
  (read x (num 0)) (at level 60) : imp_scope.
Notation "'&' x" :=
  (reference x) (at level 60) : imp_scope.
Notation "p '[' offset ']'" :=
  (read p offset) (at level 60) : imp_scope.
Notation "x '::=' a" :=
  (write x (num 0) a) (at level 60) : imp_scope.
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

(* IMP with fixed width arrays *)
Inductive context : Type :=
  | Hole : context
  | Cplus1 : context -> term -> context
  | Cplus2 : {x : term | value x} -> context -> context
  | Cminus1 : context -> term -> context
  | Cminus2 : {x : term | value x} -> context -> context
  | Cmodulo1 : context -> term -> context
  | Cmodulo2 : {x : term | value x} -> context -> context
  | Cless_than1 : context -> term -> context
  | Cless_than2 : {x : term | value x} -> context -> context
  | Cand1 : context -> term -> context
  | Cand2 : {x : term | value x} -> context -> context
  | Cread1 : context -> term -> context
  | Cread2 : {x : term | value x} -> context -> context
  | Cwrite1 : context -> term -> term -> context
  | Cwrite2 : {x : term | value x} -> context -> term -> context
  | Cwrite3 : {x : term | value x} -> {x : term | value x} -> context -> context
  | Cif : context -> term -> term -> context
  | Cseq : context -> term -> context
  | Cnot : context -> context
  | Creference : context -> context
  | Ccast : context -> context.


Fixpoint subst (E : context) (s : term) : term :=
  match E with
    | Hole => s
    | Cplus1 E t => plus (subst E s) t
    | Cplus2 (exist _ x _) E => plus x (subst E s)
    | Cminus1 E t => minus (subst E s) t
    | Cminus2 (exist _ x _) E => minus x (subst E s)
    | Cmodulo1 E t => modulo (subst E s) t
    | Cmodulo2 (exist _ x _) E => modulo x (subst E s)
    | Cless_than1 E t => less_than (subst E s) t
    | Cless_than2 (exist _ x _) E => less_than x (subst E s)
    | Cand1 E t => and (subst E s) t
    | Cand2 (exist _ x _) E => and x (subst E s)
    | Cread1 E t => read (subst E s) t
    | Cread2 (exist _ x _) E => read x (subst E s)
    | Cwrite1 E t t' => write (subst E s) t t'
    | Cwrite2 (exist _ x _) E t => write x (subst E s) t
    | Cwrite3 (exist _ x _) (exist _ y _) E => write x y (subst E s)
    | Cif E t t' => ifterm (subst E s) t t'
    | Cseq E t => read (subst E s) t
    | Cnot E => not (subst E s)
    | Creference E => reference (subst E s)
    | Ccast E => cast (subst E s)
  end.

Inductive mem_event : Type :=
    | Read (loc : nat) (offset : nat) (value : nat)
    | Write (loc : nat) (offset : nat) (value : nat)
    | Allocate (loc : nat) (size : nat) (init : list nat)
    | Reference (loc : nat) (value : nat)
    | Cast (n : nat) (loc : nat)
    | Tau.

Inductive step : term -> mem_event -> term -> Prop :=
  | step_context : forall e e' E event,
                   step e event e' ->
                   step (subst E e) event (subst E e')
  | step_reference : forall x n, step (reference (var x)) (Reference x n) (num n)
  | step_cast : forall x n,  step (cast (num n)) (Cast n x) (var x)
  | step_read : forall offset value n,
                step (read (var n) (num offset))
                     (Read n offset value)
                     (num value)
  | step_write : forall val n offset,
                  step (write (var n) (num offset) (num val)) 
                       (Write n offset val)
                        yunit
  | step_plus : forall m n, step (plus (num m) (num n)) Tau (num (m + n))
  | step_minus : forall m n, step (minus (num m) (num n)) Tau (num (m - n))
  | step_mod : forall m n, step (modulo (num m) (num n)) Tau (num (Nat.modulo m n))
  | step_lt1 : forall m n, m < n -> step (less_than (num m) (num n)) Tau tru
  | step_lt2 : forall m n, m >= n -> step (less_than (num m) (num n)) Tau fls
  | step_and1 : step (and tru tru) Tau tru
  | step_and2 : step (and tru fls) Tau fls
  | step_and3 : step (and fls tru) Tau fls
  | step_and4 : step (and fls fls) Tau fls
  | step_not1 : step (not tru) Tau fls
  | step_not2 : step (not fls) Tau tru
  | step_seq : forall e2, step (seq yunit e2) Tau e2
  | step_ifterm1 : forall e2 e3, step (ifterm tru e2 e3) Tau e2
  | step_ifterm2 : forall e2 e3, step (ifterm fls e2 e3) Tau e3
  | step_while : forall b c, step (while b c) Tau (ifterm b (seq c (while b c)) yunit).
