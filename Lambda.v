Require Import List.
Require Import Strings.String.
Require Import Util.

(* Untyped Lambda Calculus with 
   1. fixed width arrays, 
   2. unit, 
   3. nats,
   4. bools,
   6. case statements
 *)

Inductive term : Type :=
  | array : nat -> term
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
  | case : term -> term -> term -> term
  | var : string -> term
  | app : term -> term -> term
  | lam : string -> term -> term.

Definition or (s : term) (t : term) := not (and (not s) (not t)).

Definition equals (s : term) (t : term) := not (or (less_than s t) (less_than t s)).

Definition seq (s : term) (t : term) := app (app (lam "x" (lam "y" (var "y"))) s) t.

Definition y_combinator := 
  let g := lam "x" (app (var "g") (app (var "x") (var "x"))) in
  lam "g" (app g g).

Definition while_fun := 
  lam "while" (lam "b" (lam "c" (case (var "b") (seq (var "c") (app (app (var "while") (var "b")) (var "c"))) yunit))).

Definition while_fics := app y_combinator while_fun.

Definition while (s : term) (t : term) := app (app while_fics s) t.

Notation "x == y" :=
  (equals x y) (at level 60).
Notation "x << y" :=
  (less_than x y) (at level 60).
Notation "'!' x" :=
  (read x (num 0)) (at level 60).
Notation "'&' x" :=
  (reference x) (at level 60).
Notation "p '[' offset ']'" :=
  (read p offset) (at level 60).
Notation "x '::=' a" :=
  (write x (num 0) a) (at level 60).
Notation "x '[' offset ']' '::=' a" :=
  (write x offset a) (at level 60).
Notation "c1 ;; c2" :=
  (seq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'DONE'" :=
  (while b c) (at level 80, right associativity).
Notation "'CASE' c1 'THEN' c2 'ELSE' c3 'ESAC'" :=
  (case c1 c2 c3) (at level 80, right associativity).


Inductive mem_event : Type :=
  | Read (loc : nat) (offset : nat) (value : nat)
  | Write (loc : nat) (offset : nat) (value : nat)
  | Allocate (loc : nat) (size : nat) (init : list nat)
  | Reference (loc : nat) (value : nat)
  | Cast (n : nat) (loc : nat)
  | Tau.

Inductive value : term -> Prop :=
  | value_array : forall x, value (array x)
  | value_num : forall x, value (num x)
  | value_yunit : value yunit
  | value_tru : value tru
  | value_fls : value fls
  | value_lam : forall x y, value (lam x y).

Fixpoint subst (x : string) (v : term) (e : term) :=
  match e with
    | array _ => e
    | num _ => e
    | plus e1 e2 => plus (subst x v e1) (subst x v e2)
    | minus e1 e2 => minus (subst x v e1) (subst x v e2)
    | modulo e1 e2 => modulo (subst x v e1) (subst x v e2)
    | tru => tru
    | fls => fls
    | less_than e1 e2 => less_than (subst x v e1) (subst x v e2)
    | not e => not (subst x v e)
    | and e1 e2 => and (subst x v e1) (subst x v e2)
    | yunit => yunit
    | write e1 e2 e3 => write (subst x v e1) (subst x v e2) (subst x v e3)
    | read e1 e2 => read (subst x v e1) (subst x v e2)
    | reference e => reference (subst x v e)
    | cast e => cast (subst x v e)
    | case e1 e2 e3 => case (subst x v e1) (subst x v e2) (subst x v e3)
    | var y => if string_dec x y then v else var y
    | app e1 e2 => app (subst x v e1) (subst x v e2)
    | lam y e => lam y (if (string_dec x y) then e else (subst x v e))
  end.

Inductive context : Type :=
  | Hole : context
  | Capp1 : context -> term -> context
  | Capp2 : {t : term | exists x e', t = lam x e'} -> context -> context
  | Cplus1 : context -> term -> context
  | Cplus2 : {x : term | exists n, x = num n} -> context -> context
  | Cminus1 : context -> term -> context
  | Cminus2 : {x : term | exists n, x = num n} -> context -> context
  | Cmodulo1 : context -> term -> context
  | Cmodulo2 : {x : term | exists n, x = num n} -> context -> context
  | Cless_than1 : context -> term -> context
  | Cless_than2 : {x : term | x = tru \/ x = fls} -> context -> context
  | Cand1 : context -> term -> context
  | Cand2 : {x : term | x = tru} -> context -> context
  | Cread1 : context -> term -> context
  | Cread2 : {x : term | exists s, x = array s} -> context -> context
  | Cwrite1 : context -> term -> term -> context
  | Cwrite2 : {x : term | exists s, x = array s} -> context -> term -> context
  | Cwrite3 : {x : term | exists s, x = array s} -> {x : term | exists n, x = num n} -> context -> context
  | Ccase : context -> term -> term -> context
  | Cseq : context -> term -> context
  | Cnot : context -> context
  | Creference : context -> context
  | Ccast : context -> context.

Fixpoint con_subst (E : context) (s : term) : term :=
  match E with
    | Hole => s
    | Capp1 E t => app (con_subst E s) t
    | Capp2 (exist _ f _) E => app f (con_subst E s)
    | Cplus1 E t => plus (con_subst E s) t
    | Cplus2 (exist _ x _) E => plus x (con_subst E s)
    | Cminus1 E t => minus (con_subst E s) t
    | Cminus2 (exist _ x _) E => minus x (con_subst E s)
    | Cmodulo1 E t => modulo (con_subst E s) t
    | Cmodulo2 (exist _ x _) E => modulo x (con_subst E s)
    | Cless_than1 E t => less_than (con_subst E s) t
    | Cless_than2 (exist _ x _) E => less_than x (con_subst E s)
    | Cand1 E t => and (con_subst E s) t
    | Cand2 (exist _ x _) E => and x (con_subst E s)
    | Cread1 E t => read (con_subst E s) t
    | Cread2 (exist _ x _) E => read x (con_subst E s)
    | Cwrite1 E t t' => write (con_subst E s) t t'
    | Cwrite2 (exist _ x _) E t => write x (con_subst E s) t
    | Cwrite3 (exist _ x _) (exist _ y _) E => write x y (con_subst E s)
    | Ccase E t t' => case (con_subst E s) t t'
    | Cseq E t => seq (con_subst E s) t
    | Cnot E => not (con_subst E s)
    | Creference E => reference (con_subst E s)
    | Ccast E => cast (con_subst E s)
  end.

Inductive step : term -> mem_event -> term -> Prop :=
  | step_context : forall e e' E event,
                   step e event e' ->
                   step (con_subst E e) event (con_subst E e')
  | step_app : forall x e v, value v -> step (app (lam x e) v) Tau (subst x v e)
  | step_reference : forall x n, step (reference (array x)) (Reference x n) (num n)
  | step_cast : forall x n,  step (cast (num n)) (Cast n x) (array x)
  | step_read : forall offset value n,
                step (read (array n) (num offset))
                     (Read n offset value)
                     (num value)
  | step_write : forall val n offset,
                  step (write (array n) (num offset) (num val)) 
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

Fact subst_inversion : forall E e e', con_subst E e = con_subst E e' -> e = e'.
Proof. intros. induction E; simpl in *; auto; apply IHE; try (destruct s); try (destruct s0); inversion H;   auto.
Qed.


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
