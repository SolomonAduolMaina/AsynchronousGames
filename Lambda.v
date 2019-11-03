Require Import List.
Require Import Util.
Require Import Arith.PeanoNat.
Require Import ZArith.

(* Untyped Lambda Calculus with 
   1. fixed width arrays, 
   2. unit, 
   3. nats,
   4. bools,
   6. case statements
   7. pairs
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
  | var : nat -> term
  | app : term -> term -> term
  | lam : term -> term
  | paire : term -> term -> term
  | first : term -> term
  | second : term -> term.

(*********************** Notation ***********************************************)

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
Notation "'CASE' c1 'THEN' c2 'ELSE' c3 'ESAC'" :=
  (case c1 c2 c3) (at level 80, right associativity).

(****************************** Memory events ***********************************)

Inductive mem_event : Type :=
  | Read (loc : nat) (offset : nat) (value : nat)
  | Write (loc : nat) (offset : nat) (value : nat)
  | Allocate (loc : nat) (size : nat) (init : list nat)
  | Reference (loc : nat) (value : nat)
  | Cast (n : nat) (loc : nat)
  | Tau.

(******************************* Values *****************************************)

Inductive value : term -> Prop :=
  | value_array : forall x, value (array x)
  | value_num : forall x, value (num x)
  | value_yunit : value yunit
  | value_tru : value tru
  | value_fls : value fls
  | value_lam : forall e, value (lam e)
  | value_paire : forall v1 v2, value v1 -> value v2 -> value (paire v1 v2).

(*************************Shifting and Substitution ****************************)

Fixpoint shift (b : bool) (c : nat) (e : term) : term :=
  match e with
    | array _ => e
    | num _ => e
    | plus e1 e2 => plus (shift b c e1) (shift b c e2)
    | minus e1 e2 => minus (shift b c e1) (shift b c e2)
    | modulo e1 e2 => modulo (shift b c e1) (shift b c e2)
    | tru => tru
    | fls => fls
    | less_than e1 e2 => less_than (shift b c e1) (shift b c e2)
    | not e => not (shift b c e)
    | and e1 e2 => and (shift b c e1) (shift b c e2)
    | yunit => yunit
    | write e1 e2 e3 => write (shift b c e1) (shift b c e2) (shift b c e3)
    | read e1 e2 => read (shift b c e1) (shift b c e2)
    | reference e => reference (shift b c e)
    | cast e => cast (shift b c e)
    | case e1 e2 e3 => case (shift b c e1) (shift b c e2) (shift b c e3)
    | var k => var (if k <? c then k else (if b then k + 1 else k - 1))
    | app e1 e2 => app (shift b c e1) (shift b c e2)
    | lam e => lam (shift b (c+1) e)
    | paire e1 e2 => paire (shift b c e1) (shift b c e2)
    | first e => first (shift b c e)
    | second e => second (shift b c e)
  end.

Fact shift_array : forall n b c, shift b c (array n) = array n.
Proof. intros. simpl. reflexivity. Qed.

Fact shift_num : forall n c b, shift b c (num n) = num n.
Proof. intros. simpl. reflexivity. Qed.

Fact shift_tru : forall c b, shift b c tru = tru.
Proof. intros. simpl. reflexivity. Qed.

Fact shift_fls : forall c b, shift b c fls = fls.
Proof. intros. simpl. reflexivity. Qed.

Fact shift_yunit : forall c b, shift b c yunit = yunit.
Proof. intros. simpl. reflexivity. Qed.

Fact shift_app : forall e1 e2 c b, shift b c (app e1 e2) = app (shift b c e1) (shift b c e2).
Proof. intros. simpl. reflexivity. Qed.

Fact shift_plus : forall e1 e2 c b, shift b c (plus e1 e2) = plus (shift b c e1) (shift b c e2).
Proof. intros. simpl. reflexivity. Qed.

Fact shift_minus : forall e1 e2 c b, shift b c (minus e1 e2) = minus (shift b c e1) (shift b c e2).
Proof. intros. simpl. reflexivity. Qed.

Fact shift_modulo : forall e1 e2 c b, shift b c (modulo e1 e2) = modulo (shift b c e1) (shift b c e2).
Proof. intros. simpl. reflexivity. Qed.

Fact shift_less_than : forall e1 e2 c b, shift b c (less_than e1 e2) = less_than (shift b c e1) (shift b c e2).
Proof. intros. simpl. reflexivity. Qed.

Fact shift_and : forall e1 e2 c b, shift b c (and e1 e2) = and (shift b c e1) (shift b c e2).
Proof. intros. simpl. reflexivity. Qed.

Fact shift_not : forall e1  c b, shift b c (not e1) = not (shift b c e1).
Proof. intros. simpl. reflexivity. Qed.

Fact shift_cast : forall e1 c b, shift b c (cast e1) = cast (shift b c e1).
Proof. intros. simpl. reflexivity. Qed.

Fact shift_reference : forall e1 c b, shift b c (reference e1) = reference (shift b c e1).
Proof. intros. simpl. reflexivity. Qed.

Fact shift_read : forall e1 e2 c b, shift b c (read e1 e2) = read (shift b c e1) (shift b c e2).
Proof. intros. simpl. reflexivity. Qed.

Fact shift_write : forall e1 e2 e3 c b, shift b c (write e1 e2 e3) = write (shift b c e1) (shift b c e2) (shift b c e3).
Proof. intros. simpl. reflexivity. Qed.

Fact shift_case : forall e1 e2 e3 c b, shift b c (case e1 e2 e3) = case (shift b c e1) (shift b c e2) (shift b c e3).
Proof. intros. simpl. reflexivity. Qed.

Fact shift_paire : forall e1 e2 c b, shift b c (paire e1 e2) = paire (shift b c e1) (shift b c e2).
Proof. intros. simpl. reflexivity. Qed.

Fact shift_first : forall e1 c b, shift b c (first e1) = first (shift b c e1).
Proof. intros. simpl. reflexivity. Qed.

Fact shift_second : forall e1 c b, shift b c (second e1) = second (shift b c e1).
Proof. intros. simpl. reflexivity. Qed.
 
Fact shift_var : forall k c b, shift b c (var k) =  var (if k <? c then k else (if b then k+1 else k-1)).
Proof. intros. simpl. reflexivity. Qed.

Fact shift_lam : forall c e b, shift b c (lam e) = lam (shift b (c+1) e).
Proof. intros. simpl. reflexivity. Qed.


Fixpoint subst (j : nat) (s : term) (e : term) :=
  match e with
    | array _ => e
    | num _ => e
    | plus e1 e2 => plus (subst j s e1) (subst j s e2)
    | minus e1 e2 => minus (subst j s e1) (subst j s e2)
    | modulo e1 e2 => modulo (subst j s e1) (subst j s e2)
    | tru => tru
    | fls => fls
    | less_than e1 e2 => less_than (subst j s e1) (subst j s e2)
    | not e => not (subst j s e)
    | and e1 e2 => and (subst j s e1) (subst j s e2)
    | yunit => yunit
    | write e1 e2 e3 => write (subst j s e1) (subst j s e2) (subst j s e3)
    | read e1 e2 => read (subst j s e1) (subst j s e2)
    | reference e => reference (subst j s e)
    | cast e => cast (subst j s e)
    | case e1 e2 e3 => case (subst j s e1) (subst j s e2) (subst j s e3)
    | var k => if k =? j then s else var k
    | app e1 e2 => app (subst j s e1) (subst j s e2)
    | lam e => lam (subst (j+1) (shift true 0 s) e)
    | paire e1 e2 => paire (subst j s e1) (subst j s e2)
    | first e => first (subst j s e)
    | second e => second (subst j s e)
  end.

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

Fact subst_paire : forall e1 e2 x v, subst x v (paire e1 e2) = paire (subst x v e1) (subst x v e2).
Proof. intros. simpl. reflexivity. Qed.

Fact subst_first : forall e1 x v, subst x v (first e1) = first (subst x v e1).
Proof. intros. simpl. reflexivity. Qed.

Fact subst_second : forall e1 x v, subst x v (second e1) = second (subst x v e1).
Proof. intros. simpl. reflexivity. Qed.

Fact subst_var : forall x k v, subst x v (var k) = if k =? x then v else var k.
Proof. intros. simpl. reflexivity. Qed.

Fact subst_lam : forall x v e, subst x v (lam e) = lam (subst (x+1) (shift true 0 v) e).
Proof. intros. simpl. reflexivity. Qed.

(************************** Contexts ********************************************)

Inductive context : Type :=
  | Hole : context
  | Capp1 : context -> term -> context
  | Capp2 : {t : term | exists e', t = lam e'} -> context -> context
  | Cplus1 : context -> term -> context
  | Cplus2 : {x : term | exists n, x = num n} -> context -> context
  | Cminus1 : context -> term -> context
  | Cminus2 : {x : term | exists n, x = num n} -> context -> context
  | Cmodulo1 : context -> term -> context
  | Cmodulo2 : {x : term | exists n, x = num n} -> context -> context
  | Cless_than1 : context -> term -> context
  | Cless_than2 : {x : term | exists n, x = num n} -> context -> context
  | Cand1 : context -> term -> context
  | Cand2 : {x : term | x = tru} -> context -> context
  | Cread1 : context -> term -> context
  | Cread2 : {x : term | exists s, x = array s} -> context -> context
  | Cwrite1 : context -> term -> term -> context
  | Cwrite2 : {x : term | exists s, x = array s} -> context -> term -> context
  | Cwrite3 : {x : term | exists s, x = array s} -> {x : term | exists n, x = num n} -> context -> context
  | Ccase : context -> term -> term -> context
  | Cnot : context -> context
  | Creference : context -> context
  | Ccast : context -> context
  | Cpaire1 : context -> term -> context
  | Cpaire2 : {v : term | value v} -> context -> context
  | Cfirst : context -> context
  | Csecond : context -> context.

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
    | Cnot E => not (con_subst E s)
    | Creference E => reference (con_subst E s)
    | Ccast E => cast (con_subst E s)
    | Cpaire1 E t => paire (con_subst E s) t
    | Cpaire2 (exist _ x _) E => paire x (con_subst E s)
    | Cfirst E => first (con_subst E s)
    | Csecond E => second (con_subst E s)
  end.

(******************************** Stepping *************************************)

Inductive step : term -> mem_event -> term -> Prop :=
  | step_context : forall e e' E event,
                   step e event e' ->
                   step (con_subst E e) event (con_subst E e')
  | step_app : forall e v, value v -> step (app (lam e) v) Tau (shift false 0 (subst 0 (shift true 0 v) e))
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
  | step_and3 : forall e, step (and fls e) Tau fls
  | step_not1 : step (not tru) Tau fls
  | step_not2 : step (not fls) Tau tru
  | step_case1 : forall e1 e2, step (case tru e1 e2) Tau e1
  | step_case2 : forall e1 e2, step (case fls e1 e2) Tau e2
  | step_fst : forall v1 v2, value v1 -> value v2 -> step (first (paire v1 v2)) Tau v1
  | step_snd : forall v1 v2, value v1 -> value v2 -> step (second (paire v1 v2)) Tau v2.
