Require Import List.
Require Import Strings.String.
Require Import Util.

(* PCF with 
   1. fixed width arrays, 
   2. unit, 
   3. nats,
   4. bools,
   6. case statements
 *)
Inductive type : Type :=
  | Nat : type
  | Bool : type
  | Unit : type
  | Array : nat -> type
  | Arrow : type -> type -> type. 


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
  | lam : string -> type -> term -> term
  | fics : type -> term -> term.

Definition or (s : term) (t : term) := not (and (not s) (not t)).

Definition equals (s : term) (t : term) := not (or (less_than s t) (less_than t s)).

Definition seq (s : term) (t : term) := app (app (lam "x" Unit (lam "y" Unit (var "y"))) s) t.


Definition while_fun := 
  lam "while" (Arrow Bool (Arrow Unit Unit)) (lam "b" Bool (lam "c" Unit (case (var "b") (seq (var "c") (app (app (var "while") (var "b")) (var "c"))) yunit))).

Definition while_fics := fics (Arrow Bool (Arrow Unit Unit)) while_fun.

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
  | value_lam : forall x y tau, value (lam x tau y).

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
    | lam y tau e => lam y tau (if (string_dec x y) then e else (subst x v e))
    | fics tau e => fics tau (subst x v e)
  end.

Inductive context : Type :=
  | Hole : context
  | Capp1 : context -> term -> context
  | Capp2 : {t : term | exists x tau e', t = lam tau x e'} -> context -> context
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
  | step_tau : forall f tau, step (fics tau f) Tau (app f (fics tau f))
  | step_app : forall x tau e v, value v -> step (app (lam x tau e) v) Tau (subst x v e)
  | step_reference : forall x n, step (reference (array x)) (Reference x n) (num n)
  | step_cast : forall x n, step (cast (num n)) (Cast n x) (array x)
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

(* Fact subst_inversion : forall E e e', con_subst E e = con_subst E e' -> e = e'.
Proof. intros. induction E; simpl in *; auto; apply IHE; try (destruct s); try (destruct s0); inversion H;   auto.
Qed.


Fact steps_plus : forall e1 e2 e t event, step t event e ->
t = (plus e1 e2) ->
(exists e1', e = plus e1' e2 /\ step e1 event e1') \/ 
(exists n1 n2, e1 = num n1 /\ e2 = num n2  /\ e = num (n1 + n2)) \/ 
(exists n e2', e1 = num n /\ e = plus e1 e2' /\ step e2 event e2').
  Proof. intros. generalize dependent e1. generalize dependent e2. induction H; intros; try (inversion H0); subst.
  + destruct E; simpl in *; subst; try (destruct s); try (destruct s0); try (inversion H0); subst.
    ++ apply IHstep. reflexivity.
    ++ left. refine (ex_intro _ (con_subst E e') _). split. reflexivity. apply step_context. auto.
    ++ destruct e0; subst. right. right. refine (ex_intro _ x _). refine (ex_intro _ (con_subst E e') _). split. reflexivity. split. reflexivity. apply step_context. auto.
  + right. left. refine (ex_intro _ m _). refine (ex_intro _ n _). auto.
Qed.

Inductive steps : term -> term -> Prop :=
  | steps_reflexive : forall p, steps p p
  | steps_transitive : forall p q r event, step p event q -> steps q r -> steps p r.

Fact array_does_not_step : forall n event e e', step e event e' -> e = array n -> False.
  Proof. intros; induction H; inversion H0. Qed.

Fact num_does_not_step : forall n event e e', step e event e' -> e = num n -> False.
  Proof. intros; induction H; inversion H0. Qed.

Fact unit_does_not_step : forall event e e', step e event e' -> e = yunit -> False.
  Proof. intros; induction H; inversion H0. Qed.


Fact steps_context : forall e e' E, steps e e' -> steps (con_subst E e) (con_subst E e').
  Proof. intros. induction E; simpl; auto; induction IHE; try (apply steps_reflexive).
  + apply steps_transitive with (event:=event) (q:=plus q t).
      ++ assert (con_subst (Cplus1 Hole t) p = plus p t). simpl. auto.
          assert (con_subst (Cplus1 Hole t) q = plus q t). simpl. auto. rewrite <- H1. rewrite <- H2.
          apply step_context. auto.
      ++ auto.
  + destruct s eqn:ORIG. apply steps_transitive with (event:=event) (q:=plus x q).
      ++ assert (con_subst (Cplus2 s Hole) p = plus x p /\ con_subst (Cplus2 s Hole) q = plus x q). split.
        +++ simpl. destruct s. inversion ORIG. auto.
        +++ simpl. destruct s. inversion ORIG. auto.
        +++ destruct H1. rewrite <- H1. rewrite <- H2. apply step_context. auto.
      ++ auto.
  + apply steps_transitive with (event:=event) (q:=minus q t).
      ++ assert (con_subst (Cminus1 Hole t) p = minus p t). simpl. auto.
          assert (con_subst (Cminus1 Hole t) q = minus q t). simpl. auto. rewrite <- H1. rewrite <- H2.
          apply step_context. auto.
      ++ auto.
  + destruct s eqn:ORIG. apply steps_transitive with (event:=event) (q:=minus x q).
      ++ assert (con_subst (Cminus2 s Hole) p = minus x p /\ con_subst (Cminus2 s Hole) q = minus x q). split.
        +++ simpl. destruct s. inversion ORIG. auto.
        +++ simpl. destruct s. inversion ORIG. auto.
        +++ destruct H1. rewrite <- H1. rewrite <- H2. apply step_context. auto.
      ++ auto.
  + apply steps_transitive with (event:=event) (q:=modulo q t).
      ++ assert (con_subst (Cmodulo1 Hole t) p = modulo p t). simpl. auto.
          assert (con_subst (Cmodulo1 Hole t) q = modulo q t). simpl. auto. rewrite <- H1. rewrite <- H2.
          apply step_context. auto.
      ++ auto.
  + destruct s eqn:ORIG. apply steps_transitive with (event:=event) (q:=modulo x q).
      ++ assert (con_subst (Cmodulo2 s Hole) p = modulo x p /\ con_subst (Cmodulo2 s Hole) q = modulo x q). split.
        +++ simpl. destruct s. inversion ORIG. auto.
        +++ simpl. destruct s. inversion ORIG. auto.
        +++ destruct H1. rewrite <- H1. rewrite <- H2. apply step_context. auto.
      ++ auto.
  + apply steps_transitive with (event:=event) (q:=less_than q t).
      ++ assert (con_subst (Cless_than1 Hole t) p = less_than p t). simpl. auto.
          assert (con_subst (Cless_than1 Hole t) q = less_than q t). simpl. auto. rewrite <- H1. rewrite <- H2.
          apply step_context. auto.
      ++ auto.
  + destruct s eqn:ORIG. apply steps_transitive with (event:=event) (q:=less_than x q).
      ++ assert (con_subst (Cless_than2 s Hole) p = less_than x p /\ con_subst (Cless_than2 s Hole) q = less_than x q). split.
        +++ simpl. destruct s. inversion ORIG. auto.
        +++ simpl. destruct s. inversion ORIG. auto.
        +++ destruct H1. rewrite <- H1. rewrite <- H2. apply step_context. auto.
      ++ auto.
  + apply steps_transitive with (event:=event) (q:=and q t).
      ++ assert (con_subst (Cand1 Hole t) p = and p t). simpl. auto.
          assert (con_subst (Cand1 Hole t) q = and q t). simpl. auto. rewrite <- H1. rewrite <- H2.
          apply step_context. auto.
      ++ auto.
  + destruct s eqn:ORIG. apply steps_transitive with (event:=event) (q:=and x q).
      ++ assert (con_subst (Cand2 s Hole) p = and x p /\ con_subst (Cand2 s Hole) q = and x q). split.
        +++ simpl. destruct s. inversion ORIG. auto.
        +++ simpl. destruct s. inversion ORIG. auto.
        +++ destruct H1. rewrite <- H1. rewrite <- H2. apply step_context. auto.
      ++ auto.
  + apply steps_transitive with (event:=event) (q:=read q t).
      ++ assert (con_subst (Cread1 Hole t) p = read p t). simpl. auto.
          assert (con_subst (Cread1 Hole t) q = read q t). simpl. auto. rewrite <- H1. rewrite <- H2.
          apply step_context. auto.
      ++ auto.
  + destruct s eqn:ORIG. apply steps_transitive with (event:=event) (q:=read x q).
      ++ assert (con_subst (Cread2 s Hole) p = read x p /\ con_subst (Cread2 s Hole) q = read x q). split.
        +++ simpl. destruct s. inversion ORIG. auto.
        +++ simpl. destruct s. inversion ORIG. auto.
        +++ destruct H1. rewrite <- H1. rewrite <- H2. apply step_context. auto.
      ++ auto.
  + apply steps_transitive with (event:=event) (q:=write q t t0).
      ++ assert (con_subst (Cwrite1 Hole t t0) p = write p t t0). simpl. auto.
          assert (con_subst (Cwrite1 Hole t t0) q = write q t t0). simpl. auto. rewrite <- H1. rewrite <- H2.
          apply step_context. auto.
      ++ auto.
  + destruct s eqn:ORIG. apply steps_transitive with (event:=event) (q:=write x q t).
      ++ assert (con_subst (Cwrite2 s Hole t) p = write x p t/\ con_subst (Cwrite2 s Hole t) q = write x q t). split.
        +++ simpl. destruct s. inversion ORIG. auto.
        +++ simpl. destruct s. inversion ORIG. auto.
        +++ destruct H1. rewrite <- H1. rewrite <- H2. apply step_context. auto.
      ++ auto.
  + destruct s eqn:ORIG. destruct s0 eqn:ORIG1. apply steps_transitive with (event:=event) (q:=write x x0 q).
      ++ assert (con_subst (Cwrite3 s s0 Hole) p = write x x0 p/\ con_subst (Cwrite3 s s0 Hole) q = write x x0 q). split.
        +++ simpl. destruct s. destruct s0. inversion ORIG. inversion ORIG1. auto.
        +++ simpl. destruct s. destruct s0. inversion ORIG. inversion ORIG1. auto.
        +++ destruct H1. rewrite <- H1. rewrite <- H2. apply step_context. auto.
      ++ auto.
  + apply steps_transitive with (event:=event) (q:=case q t t0).
      ++ assert (con_subst (Ccase Hole t t0) p = case p t t0). simpl. auto.
          assert (con_subst (Ccase Hole t t0) q = case q t t0). simpl. auto. rewrite <- H1. rewrite <- H2.
          apply step_context. auto.
      ++ auto.
  + apply steps_transitive with (event:=event) (q:=seq q t).
      ++ assert (con_subst (Cseq Hole t) p = seq p t). simpl. auto.
          assert (con_subst (Cseq Hole t) q = seq q t). simpl. auto. rewrite <- H1. rewrite <- H2.
          apply step_context. auto.
      ++ auto.
  + apply steps_transitive with (event:=event) (q:=not q).
      ++ assert (con_subst (Cnot Hole) p = not p). simpl. auto.
          assert (con_subst (Cnot Hole) q = not q). simpl. auto. rewrite <- H1. rewrite <- H2.
          apply step_context. auto.
      ++ auto.
  + apply steps_transitive with (event:=event) (q:=reference q).
      ++ assert (con_subst (Creference Hole) p = reference p). simpl. auto.
          assert (con_subst (Creference Hole) q = reference q). simpl. auto. rewrite <- H1. rewrite <- H2.
          apply step_context. auto.
      ++ auto.
  + apply steps_transitive with (event:=event) (q:=cast q).
      ++ assert (con_subst (Ccast Hole) p = cast p). simpl. auto.
          assert (con_subst (Ccast Hole) q = cast q). simpl. auto. rewrite <- H1. rewrite <- H2.
          apply step_context. auto.
      ++ auto.
Qed.


Fact con_subst_num : forall m E e, con_subst E e = num m -> E = Hole /\ e = num m.
  Proof. intros. induction E; simpl in *; con_subst; auto; try (destruct s); try (destruct s0); inversion H.
  Qed.

Fact con_subst_array : forall m E e, con_subst E e = array m -> E = Hole /\ e = array m.
  Proof. intros. induction E; simpl in *; con_subst; auto; try (destruct s); try (destruct s0); inversion H.
  Qed.

Fact con_subst_yunit : forall E e, con_subst E e = yunit -> E = Hole /\ e = yunit.
  Proof. intros. induction E; simpl in *; con_subst; auto; try (destruct s); try (destruct s0); inversion H.
  Qed.

Fact con_subst_tru : forall E e, con_subst E e = tru -> E = Hole /\ e = tru.
  Proof. intros. induction E; simpl in *; con_subst; auto; try (destruct s); try (destruct s0); inversion H.
  Qed.

Fact con_subst_fls : forall E e, con_subst E e = fls -> E = Hole /\ e = fls.
  Proof. intros. induction E; simpl in *; con_subst; auto; try (destruct s); try (destruct s0); inversion H.
  Qed.*)
