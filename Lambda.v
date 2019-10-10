Require Import List.
Require Import Strings.String.
Require Import Util.

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
  | var : string -> term
  | app : term -> term -> term
  | lam : string -> term -> term
  | paire : term -> term -> term
  | first : term -> term
  | second : term -> term.

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
  | value_lam : forall x y, value (lam x y)
  | value_paire : forall v1 v2, value v1 -> value v2 -> value (paire v1 v2).

Fixpoint remove (s : string) (l : list string) :=
  match l with
    | nil => nil
    | t :: l => if string_dec t s then (remove s l) else t :: (remove s l)
  end.

Fixpoint fvs (e : term) : list string :=
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
    | lam x e => remove x (fvs e)
    | paire e1 e2 => (fvs e1) ++ (fvs e2)
    | first e1 => fvs e1
    | second e1 => fvs e1
  end.


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
    | paire e1 e2 => paire (subst x v e1) (subst x v e2)
    | first e => first (subst x v e)
    | second e => second (subst x v e)
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

Fact subst_var : forall x y v, subst x v (var y) = if (string_dec x y) then v else (var y).
Proof. intros. simpl. reflexivity. Qed.

Fact subst_lam : forall x y v e, subst x v (lam y e) = lam y (if (string_dec x y) then e else (subst x v e)).
Proof. intros. simpl. reflexivity. Qed.

Fact subst_paire : forall e1 e2 x v, subst x v (paire e1 e2) = paire (subst x v e1) (subst x v e2).
Proof. intros. simpl. reflexivity. Qed.

Fact subst_first : forall e1 x v, subst x v (first e1) = first (subst x v e1).
Proof. intros. simpl. reflexivity. Qed.

Fact subst_second : forall e1 x v, subst x v (second e1) = second (subst x v e1).
Proof. intros. simpl. reflexivity. Qed.

Fact subst_closed_helper1 : forall y l x, In y l -> y <> x -> In y (remove x l).
Proof. intros. induction l.
  + inversion H.
  + simpl. destruct (string_dec a x).
    ++ subst. apply IHl. destruct H. contradiction H0. auto. auto.
    ++ simpl. destruct H. subst. left. reflexivity. right. apply IHl. auto. Qed.

Fact not_in_app : forall {A} (x: A) l l', (~ (In x (l ++ l'))) -> (~ (In x l)) /\ (~ (In x l')).
Proof. intros. induction l.
  + simpl in *. auto.
  + simpl in *. split.
    ++ intros C. apply H. destruct C.
      +++ left. auto.
      +++ right. apply in_or_app. left. auto.
    ++ apply IHl. intros C. apply H. right. auto.
Qed.

Fact subst_idempotent : forall x v e, (~ (In x (fvs e))) -> subst x v e = e.
Proof. intros. generalize dependent x. induction e; intros.
  + rewrite subst_array. reflexivity.
  + rewrite subst_num. reflexivity.
  + rewrite subst_plus. simpl in H. apply not_in_app in H. destruct H. rewrite IHe1. rewrite IHe2. auto. auto. auto.
  + rewrite subst_minus. simpl in H. apply not_in_app in H. destruct H. rewrite IHe1. rewrite IHe2. auto. auto. auto.
  + rewrite subst_modulo. simpl in H. apply not_in_app in H. destruct H. rewrite IHe1. rewrite IHe2. auto. auto. auto.
  + rewrite subst_tru. reflexivity.
  + rewrite subst_fls. reflexivity.
  + rewrite subst_less_than. simpl in H. apply not_in_app in H. destruct H. rewrite IHe1. rewrite IHe2. auto. auto. auto.
  + rewrite subst_not. simpl in H. rewrite IHe. auto. auto.
  + rewrite subst_and. simpl in H. apply not_in_app in H. destruct H. rewrite IHe1. rewrite IHe2. auto. auto. auto.
  + rewrite subst_yunit. auto.
  + rewrite subst_read. simpl in H. apply not_in_app in H. destruct H. rewrite IHe1. rewrite IHe2. auto. auto. auto.
  + rewrite subst_write. simpl in H. apply not_in_app in H. destruct H. apply not_in_app in H0. destruct H0. rewrite IHe1. rewrite IHe2. rewrite IHe3. auto. auto. auto. auto.
  + rewrite subst_reference. simpl in H. rewrite IHe. auto. auto.
  + rewrite subst_cast. simpl in H. rewrite IHe. auto. auto.
  + rewrite subst_case. simpl in H. apply not_in_app in H. destruct H. apply not_in_app in H0. destruct H0. rewrite IHe1. rewrite IHe2. rewrite IHe3. auto. auto. auto. auto.
  + rewrite subst_var. simpl in H. destruct (string_dec x s).
    ++ subst. contradiction H. left. reflexivity.
    ++ reflexivity.
  + rewrite subst_app. simpl in H. apply not_in_app in H. destruct H. rewrite IHe1. rewrite IHe2. auto. auto. auto.
  + rewrite subst_lam. destruct (string_dec x s).
    ++ reflexivity.
    ++ rewrite IHe. auto. simpl in H. intros C. destruct (string_dec x s).
      +++ contradiction n.
      +++ contradiction H. apply subst_closed_helper1. auto. auto.
  + rewrite subst_paire. simpl in H. apply not_in_app in H. destruct H. rewrite IHe1. rewrite IHe2. auto. auto. auto.
  + rewrite subst_first. simpl in H. rewrite IHe. auto. auto.
  + rewrite subst_second. simpl in H. rewrite IHe. auto. auto.
Qed.

Fact subst_closed : forall x v e, fvs e = nil -> subst x v e = e.
Proof. intros. apply subst_idempotent. rewrite H. auto. Qed.


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
  | step_and3 : forall e, step (and fls e) Tau fls
  | step_not1 : step (not tru) Tau fls
  | step_not2 : step (not fls) Tau tru
  | step_case1 : forall e1 e2, step (case tru e1 e2) Tau e1
  | step_case2 : forall e1 e2, step (case fls e1 e2) Tau e2
  | step_fst : forall v1 v2, value v1 -> value v2 -> step (first (paire v1 v2)) Tau v1
  | step_snd : forall v1 v2, value v1 -> value v2 -> step (second (paire v1 v2)) Tau v2.
