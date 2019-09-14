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
  | case : term -> term -> term -> term
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
Notation "'CASE' c1 'THEN' c2 'ELSE' c3 'ESAC'" :=
  (case c1 c2 c3) (at level 80, right associativity) : imp_scope.

Inductive value : term -> Prop :=
  | val_unit : value yunit
  | val_num : forall n, value (num n).

Inductive mem_event : Type :=
    | Read (loc : nat) (offset : nat) (value : nat)
    | Write (loc : nat) (offset : nat) (value : nat)
    | Allocate (loc : nat) (size : nat) (init : list nat)
    | Reference (loc : nat) (value : nat)
    | Cast (n : nat) (loc : nat)
    | Tau.

Inductive step : term -> mem_event -> term -> Prop :=
  | step_reference1 : forall e e' event,
                  step e event e' ->
                  step (reference e) event (reference e')
  | step_reference2 : forall x n,
                    step (reference (var x)) (Reference x n) (num n)
  | step_cast1 : forall e e' event,
                  step e event e' ->
                  step (cast e) event (cast e')
  | step_cast2 : forall x n,
                    step (cast (num n)) (Cast n x) (var x)
  | step_read1 : forall e1 e1' e2 event,
                  step e1 event e1' ->
                  step (read e1 e2) event (read e1' e2)
  | step_read2 : forall e1 e1' event n,
                  step e1 event e1' ->
                  step (read (var n) e1) event (read (var n) e1')
  | step_read3 : forall offset value n,
                step (read (var n) (num offset))
                     (Read n offset value)
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
                       (Write n offset val)
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
                  step (modulo (num m) (num n)) Tau (num (Nat.modulo m n))
  | step_lt1 : forall e1 e1' e2 event,
                  step e1 event e1' ->
                  step (less_than e1 e2) event (less_than e1' e2)
  | step_lt2 : forall e1 e1' n event,
                  step e1 event e1' ->
                  step (less_than (num n) e1) event (less_than (num n) e1')
  | step_lt3 : forall m n,
                  m < n ->
                  step (less_than (num m) (num n)) Tau tru
  | step_lt4 : forall m n,
                  m >= n ->
                  step (less_than (num m) (num n)) Tau fls
  | step_and1 : forall e1 e1' event e2,
                  step e1 event e1' ->
                  step (and e1 e2) event (and e1' e2)
  | step_and2 : forall e, step (and fls e) Tau fls
  | step_and3 : forall e1 e1' event,
                  step e1 event e1' ->
                  step (and tru e1) event (and tru e1')
  | step_and4 : step (and tru tru) Tau tru
  | step_and5 : step (and tru fls) Tau fls
  | step_not1 : forall e1 e1' event,
                  step e1 event e1' ->
                  step (not e1) event (not e1')
  | step_not2 : step (not tru) Tau fls
  | step_not3 : step (not fls) Tau tru
  | step_seq1 : forall e1 e1' e2 event,
                  step e1 event e1' ->
                  step (seq e1 e2) event (seq e1' e2)
  | step_seq2 : forall e2, step (seq yunit e2) Tau e2
  | step_case1 : forall e1 e1' e2 e3 event,
                  step e1 event e1' ->
                  step (case e1 e2 e3) event (case e1' e2 e3)
  | step_case2 : forall e2 e3,
                  step (case tru e2 e3) Tau e2
  | step_case3 : forall e2 e3,
                  step (case fls e2 e3) Tau e3
  | step_while : forall b c,
                  step (while b c)
                        Tau
                        (case b (seq c (while b c)) yunit).

Inductive steps : term -> term -> Prop :=
  | steps_reflexive : forall p, steps p p
  | steps_transitive : forall p q r event, step p event q -> steps q r -> steps p r.

Fact var_does_not_step : forall n event e e', step e event e' -> e = var n -> False.
  Proof. intros; induction H; inversion H0. Qed.

Fact num_does_not_step : forall n event e e', step e event e' -> e = num n -> False.
  Proof. intros; induction H; inversion H0. Qed.

Fact unit_does_not_step : forall event e e', step e event e' -> e = yunit -> False.
  Proof. intros; induction H; inversion H0. Qed.

(* Inductive context : Type :=
  | Hole : context
  | Cplus1 : context -> term -> context
  | Cplus2 : {x : term | exists n, x = num n} -> context -> context
  | Cminus1 : context -> term -> context
  | Cminus2 : {x : term | exists n, x = num n} -> context -> context
  | Cmodulo1 : context -> term -> context
  | Cmodulo2 : {x : term | exists n, x = num n} -> context -> context
  | Cless_than1 : context -> term -> context
  | Cless_than2 : {x : term | x = tru \/ x = fls} -> context -> context
  | Cand1 : context -> term -> context
  | Cand2 : {x : term | x = tru \/ x = fls} -> context -> context
  | Cread1 : context -> term -> context
  | Cread2 : {x : term | exists s, x = var s} -> context -> context
  | Cwrite1 : context -> term -> term -> context
  | Cwrite2 : {x : term | exists s, x = var s} -> context -> term -> context
  | Cwrite3 : {x : term | exists s, x = var s} -> {x : term | exists n, x = num n} -> context -> context
  | Ccase : context -> term -> term -> context
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
    | Ccase E t t' => case (subst E s) t t'
    | Cseq E t => seq (subst E s) t
    | Cnot E => not (subst E s)
    | Creference E => reference (subst E s)
    | Ccast E => cast (subst E s)
  end.

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
  | step_case1 : forall e2 e3, step (case tru e2 e3) Tau e2
  | step_case2 : forall e2 e3, step (case fls e2 e3) Tau e3
  | step_while : forall b c, step (while b c) Tau (case b (seq c (while b c)) yunit).

Fact steps_context : forall e e' E, steps e e' -> steps (subst E e) (subst E e').
  Proof. intros. induction E; simpl; auto; induction IHE; try (apply steps_reflexive).
  + apply steps_transitive with (event:=event) (q:=plus q t).
      ++ assert (subst (Cplus1 Hole t) p = plus p t). simpl. auto.
          assert (subst (Cplus1 Hole t) q = plus q t). simpl. auto. rewrite <- H1. rewrite <- H2.
          apply step_context. auto.
      ++ auto.
  + destruct s eqn:ORIG. apply steps_transitive with (event:=event) (q:=plus x q).
      ++ assert (subst (Cplus2 s Hole) p = plus x p /\ subst (Cplus2 s Hole) q = plus x q). split.
        +++ simpl. destruct s. inversion ORIG. auto.
        +++ simpl. destruct s. inversion ORIG. auto.
        +++ destruct H1. rewrite <- H1. rewrite <- H2. apply step_context. auto.
      ++ auto.
  + apply steps_transitive with (event:=event) (q:=minus q t).
      ++ assert (subst (Cminus1 Hole t) p = minus p t). simpl. auto.
          assert (subst (Cminus1 Hole t) q = minus q t). simpl. auto. rewrite <- H1. rewrite <- H2.
          apply step_context. auto.
      ++ auto.
  + destruct s eqn:ORIG. apply steps_transitive with (event:=event) (q:=minus x q).
      ++ assert (subst (Cminus2 s Hole) p = minus x p /\ subst (Cminus2 s Hole) q = minus x q). split.
        +++ simpl. destruct s. inversion ORIG. auto.
        +++ simpl. destruct s. inversion ORIG. auto.
        +++ destruct H1. rewrite <- H1. rewrite <- H2. apply step_context. auto.
      ++ auto.
  + apply steps_transitive with (event:=event) (q:=modulo q t).
      ++ assert (subst (Cmodulo1 Hole t) p = modulo p t). simpl. auto.
          assert (subst (Cmodulo1 Hole t) q = modulo q t). simpl. auto. rewrite <- H1. rewrite <- H2.
          apply step_context. auto.
      ++ auto.
  + destruct s eqn:ORIG. apply steps_transitive with (event:=event) (q:=modulo x q).
      ++ assert (subst (Cmodulo2 s Hole) p = modulo x p /\ subst (Cmodulo2 s Hole) q = modulo x q). split.
        +++ simpl. destruct s. inversion ORIG. auto.
        +++ simpl. destruct s. inversion ORIG. auto.
        +++ destruct H1. rewrite <- H1. rewrite <- H2. apply step_context. auto.
      ++ auto.
  + apply steps_transitive with (event:=event) (q:=less_than q t).
      ++ assert (subst (Cless_than1 Hole t) p = less_than p t). simpl. auto.
          assert (subst (Cless_than1 Hole t) q = less_than q t). simpl. auto. rewrite <- H1. rewrite <- H2.
          apply step_context. auto.
      ++ auto.
  + destruct s eqn:ORIG. apply steps_transitive with (event:=event) (q:=less_than x q).
      ++ assert (subst (Cless_than2 s Hole) p = less_than x p /\ subst (Cless_than2 s Hole) q = less_than x q). split.
        +++ simpl. destruct s. inversion ORIG. auto.
        +++ simpl. destruct s. inversion ORIG. auto.
        +++ destruct H1. rewrite <- H1. rewrite <- H2. apply step_context. auto.
      ++ auto.
  + apply steps_transitive with (event:=event) (q:=and q t).
      ++ assert (subst (Cand1 Hole t) p = and p t). simpl. auto.
          assert (subst (Cand1 Hole t) q = and q t). simpl. auto. rewrite <- H1. rewrite <- H2.
          apply step_context. auto.
      ++ auto.
  + destruct s eqn:ORIG. apply steps_transitive with (event:=event) (q:=and x q).
      ++ assert (subst (Cand2 s Hole) p = and x p /\ subst (Cand2 s Hole) q = and x q). split.
        +++ simpl. destruct s. inversion ORIG. auto.
        +++ simpl. destruct s. inversion ORIG. auto.
        +++ destruct H1. rewrite <- H1. rewrite <- H2. apply step_context. auto.
      ++ auto.
  + apply steps_transitive with (event:=event) (q:=read q t).
      ++ assert (subst (Cread1 Hole t) p = read p t). simpl. auto.
          assert (subst (Cread1 Hole t) q = read q t). simpl. auto. rewrite <- H1. rewrite <- H2.
          apply step_context. auto.
      ++ auto.
  + destruct s eqn:ORIG. apply steps_transitive with (event:=event) (q:=read x q).
      ++ assert (subst (Cread2 s Hole) p = read x p /\ subst (Cread2 s Hole) q = read x q). split.
        +++ simpl. destruct s. inversion ORIG. auto.
        +++ simpl. destruct s. inversion ORIG. auto.
        +++ destruct H1. rewrite <- H1. rewrite <- H2. apply step_context. auto.
      ++ auto.
  + apply steps_transitive with (event:=event) (q:=write q t t0).
      ++ assert (subst (Cwrite1 Hole t t0) p = write p t t0). simpl. auto.
          assert (subst (Cwrite1 Hole t t0) q = write q t t0). simpl. auto. rewrite <- H1. rewrite <- H2.
          apply step_context. auto.
      ++ auto.
  + destruct s eqn:ORIG. apply steps_transitive with (event:=event) (q:=write x q t).
      ++ assert (subst (Cwrite2 s Hole t) p = write x p t/\ subst (Cwrite2 s Hole t) q = write x q t). split.
        +++ simpl. destruct s. inversion ORIG. auto.
        +++ simpl. destruct s. inversion ORIG. auto.
        +++ destruct H1. rewrite <- H1. rewrite <- H2. apply step_context. auto.
      ++ auto.
  + destruct s eqn:ORIG. destruct s0 eqn:ORIG1. apply steps_transitive with (event:=event) (q:=write x x0 q).
      ++ assert (subst (Cwrite3 s s0 Hole) p = write x x0 p/\ subst (Cwrite3 s s0 Hole) q = write x x0 q). split.
        +++ simpl. destruct s. destruct s0. inversion ORIG. inversion ORIG1. auto.
        +++ simpl. destruct s. destruct s0. inversion ORIG. inversion ORIG1. auto.
        +++ destruct H1. rewrite <- H1. rewrite <- H2. apply step_context. auto.
      ++ auto.
  + apply steps_transitive with (event:=event) (q:=case q t t0).
      ++ assert (subst (Ccase Hole t t0) p = case p t t0). simpl. auto.
          assert (subst (Ccase Hole t t0) q = case q t t0). simpl. auto. rewrite <- H1. rewrite <- H2.
          apply step_context. auto.
      ++ auto.
  + apply steps_transitive with (event:=event) (q:=seq q t).
      ++ assert (subst (Cseq Hole t) p = seq p t). simpl. auto.
          assert (subst (Cseq Hole t) q = seq q t). simpl. auto. rewrite <- H1. rewrite <- H2.
          apply step_context. auto.
      ++ auto.
  + apply steps_transitive with (event:=event) (q:=not q).
      ++ assert (subst (Cnot Hole) p = not p). simpl. auto.
          assert (subst (Cnot Hole) q = not q). simpl. auto. rewrite <- H1. rewrite <- H2.
          apply step_context. auto.
      ++ auto.
  + apply steps_transitive with (event:=event) (q:=reference q).
      ++ assert (subst (Creference Hole) p = reference p). simpl. auto.
          assert (subst (Creference Hole) q = reference q). simpl. auto. rewrite <- H1. rewrite <- H2.
          apply step_context. auto.
      ++ auto.
  + apply steps_transitive with (event:=event) (q:=cast q).
      ++ assert (subst (Ccast Hole) p = cast p). simpl. auto.
          assert (subst (Ccast Hole) q = cast q). simpl. auto. rewrite <- H1. rewrite <- H2.
          apply step_context. auto.
      ++ auto.
Qed.


Fact subst_num : forall m E e, subst E e = num m -> E = Hole /\ e = num m.
  Proof. intros. induction E; simpl in *; subst; auto; try (destruct s); try (destruct s0); inversion H.
  Qed.

Fact subst_var : forall m E e, subst E e = var m -> E = Hole /\ e = var m.
  Proof. intros. induction E; simpl in *; subst; auto; try (destruct s); try (destruct s0); inversion H.
  Qed.

Fact subst_yunit : forall E e, subst E e = yunit -> E = Hole /\ e = yunit.
  Proof. intros. induction E; simpl in *; subst; auto; try (destruct s); try (destruct s0); inversion H.
  Qed.

Fact subst_tru : forall E e, subst E e = tru -> E = Hole /\ e = tru.
  Proof. intros. induction E; simpl in *; subst; auto; try (destruct s); try (destruct s0); inversion H.
  Qed.

Fact subst_fls : forall E e, subst E e = fls -> E = Hole /\ e = fls.
  Proof. intros. induction E; simpl in *; subst; auto; try (destruct s); try (destruct s0); inversion H.
  Qed.*)
