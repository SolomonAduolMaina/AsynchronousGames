Require Import List.
Require Import ZArith.
Require Import Util.

(* IMP with fixed width arrays *)
Inductive term : Type :=
  | var : nat -> term
  | ref : nat -> nat -> term (* second number indicates size of allocation *)
  | num : Z -> term
  | plus : term -> term -> term
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
  | val_ref : forall n m, value (ref n m)
  | val_num : forall n, value (num n).

Notation "x * y" := (prod x y).
Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z).

Reserved Notation "'[' x ':=' s ']' t" (at level 20).

Fixpoint subst (x : nat) (s : term) (t : term) : term :=
  match t with
  | var x' =>
      if Nat.eqb x x' then s else t
  | ref n m =>
      ref n m
  | num n =>
      num n
  | read e1 e2 =>
    read ([x:=s] e1) ([x:=s] e2)
  | plus e1 e2 =>
    plus ([x:=s] e1) ([x:=s] e2)
  | modulo e1 e2 =>
    modulo ([x:=s] e1) ([x:=s] e2)
  | tru =>
    tru
  | fls =>
    fls
  | less_than e1 e2 =>
    less_than ([x:=s] e1) ([x:=s] e2)
  | not e =>
    not ([x:=s] e)
  | and e1 e2 =>
    and ([x:=s] e1) ([x:=s] e2)
  | yunit =>
    yunit
  | write e1 e2 e3 =>
    write ([x:=s] e1) ([x:=s] e2) ([x:=s] e3)
  | seq e1 e2 =>
    seq ([x:=s] e1) ([x:=s] e2)
  | ifterm e1 e2 e3 =>
    ifterm ([x:=s] e1) ([x:=s] e2) ([x:=s] e3)
  | while e1 e2 =>
    while ([x:=s] e1) ([x:=s] e2)
  | reference e =>
    reference ([x:=s] e)
  end

where "'[' x ':=' s ']' t" := (subst x s t).

Inductive mem_event : Type :=
    | Read (loc : nat) (offset : nat) (value : Z)
    | Write (loc : nat) (offset : nat) (value : Z)
    | Allocate (loc : nat) (size : nat) (init : list Z)
    | Tau.

Inductive step : term -> mem_event -> term -> Prop :=
  | step_reference1 : forall e e' event,
                  step e event e' ->
                  step (reference e) event (reference e')
  | step_reference2 : forall n m,
                    step (reference (ref n m)) Tau (num (Z.of_nat n))
  | step_read1 : forall e1 e1' event n size,
                  step e1 event e1' ->
                  step (read (ref n size) e1) event (read (ref n size) e1')
  | step_read2 : forall offset value n size,
                ((Z.leb 0 offset) = true /\ (Z.ltb offset (Z.of_nat size)) = true) ->
                step (read (ref n size) (num offset))
                     (Read n (Z.to_nat offset) value)
                     (num value)
  | step_write1 : forall e1 e1' e2 event n m,
                  step e1 event e1' ->
                  step (write (ref n m) e1 e2) event (write (ref n m) e1' e2)
  | step_write2 : forall e1 e1' event n offset size,
                  ((Z.leb 0 offset) = true /\ (Z.ltb offset (Z.of_nat size)) = true) ->
                  step e1 event e1' ->
                  step (write (ref n size) (num offset) e1)
                       event
                       (write (ref n size) (num offset) e1')
  | step_write3 : forall val n offset size,
                  (Z.ltb offset (Z.of_nat size) = true )->
                  step (write (ref n size) (num offset) (num val)) 
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

