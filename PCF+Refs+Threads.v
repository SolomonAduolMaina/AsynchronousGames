Require Import Strings.String.
Require Import List.

Inductive type : Type :=
  | Bool : type
  | Unit : type
  | NatRef : type
  | Arrow : type -> type -> type.

Inductive term : Type :=
(* PCF *)
  | var : string -> term
  | app : term -> term -> term
  | lam : string -> type -> term -> term
  | ifzero : term -> term -> term -> term
  | fics : type -> term -> term
  | num : nat -> term
  | yunit : term

(* (Nat) References. *)
  | ref : nat -> term
  | new_ref : term -> term
  | assign : term -> term -> term
  | deref : term -> term

(* Threads *)
  | fork : term -> term -> term
  | join : term -> term.

Inductive value : term -> Prop :=
  | v_lam : forall x tau e, value (lam x tau e)
  | v_num : forall n, value (num n)
  | v_yunit : value yunit
  | v_ref : forall n, value (ref n).

Reserved Notation "'[' x ':=' s ']' t" (at level 20).

Fixpoint subst (x : string) (s : term) (t : term) : term :=
  match t with
  | var x' =>
      if string_dec x x' then s else t
  | lam y T e =>
      lam y T (if string_dec x y then e else ([x:=s] e))
  | app t1 t2 =>
      app ([x:=s] t1) ([x:=s] t2)
  | num n =>
      num n
  | yunit =>
      yunit
  | ifzero e1 e2 e3 =>
      ifzero ([x:=s] e1) ([x:=s] e2) ([x:=s] e3)
  | fics T e =>
      fics T ([x:=s] e)
  | new_ref e =>
      new_ref ([x:=s] e)
  | ref n =>
      ref n
  | assign e1 e2 =>
      assign ([x:=s] e1) ([x:=s] e2)
  | deref e =>
      deref ([x:=s] e)
  | fork e e' =>
      fork ([x:=s] e) ([x:=s] e')
  | join e =>
      join ([x:=s] e) 
  end

where "'[' x ':=' s ']' t" := (subst x s t).

Notation "x * y" := (prod x y).
Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z).

(* A pool (thread_count, ref_count, l, l', e) is a 5-tuple where
    - thread_count : nat is used to generate thread ids
    - ref_count : nat is used to generate ref ids
    - l : (nat -> (option term)) is a function denoting running threads
    - l' : (nat -> (option nat)) is a function denoting the reference store
    - e : term is the reducing term *)

Definition pool :=
nat * nat * (nat -> (option term)) * (nat -> (option nat)) * term.

Inductive step : pool -> pool -> Prop :=
  | ST_thread : forall thread_count thread_count' ref_count ref_count' 
                threads threads' threads'' store store' id e1 e1' e,
        threads id = Some e1 ->
        step (thread_count, ref_count, threads, store, e1) 
             (thread_count', ref_count', threads', store', e1') ->
        threads'' = (fun n => if Nat.eqb n id then Some e1' else threads' n) ->
        step (thread_count, ref_count, threads, store, e)
             (thread_count', ref_count', threads'', store', e)
  | ST_fork : forall thread_count ref_count threads threads' store e e',
        threads' = (fun n => if Nat.eqb n thread_count then Some e else threads n) ->
        step (thread_count, ref_count, threads, store, fork e e')
             (thread_count + 1, ref_count, threads', store, e')
  | ST_join : forall thread_count ref_count threads store e,
        (forall n, (threads n = None) \/ (exists v, value v /\ threads n = Some v)) ->
        step (thread_count, ref_count, threads, store, join e)
             (thread_count, ref_count, threads, store, e)
  | ST_App1 : forall thread_count thread_count' 
                     ref_count ref_count' threads threads' store store' e1 e1' e,
        step (thread_count, ref_count, threads, store, e1)
             (thread_count', ref_count', threads', store', e1') ->
        step (thread_count, ref_count, threads, store, (app e1 e))
             (thread_count', ref_count', threads', store', (app e1' e))
  | ST_App2 : forall thread_count thread_count' 
                     ref_count ref_count' threads threads' store store' e1 e1' v,
        value v ->
        step (thread_count, ref_count, threads, store, e1)
             (thread_count', ref_count', threads', store', e1') ->
        step (thread_count, ref_count, threads, store, (app v e1))
             (thread_count', ref_count', threads', store', (app v e1'))
  | ST_App3 : forall thread_count ref_count threads store x T e v,
        value v ->
        step (thread_count, ref_count, threads, store, (app (lam x T e) v))
             (thread_count, ref_count, threads, store, ([x:=v]e))
  | ST_newref1 : forall thread_count thread_count' 
                        ref_count ref_count' threads threads' store store' e e',
        step (thread_count, ref_count, threads, store, e)
             (thread_count', ref_count', threads', store', e') ->
        step (thread_count, ref_count, threads, store, (new_ref e))
             (thread_count', ref_count', threads', store', (new_ref e'))
  | ST_newref2 : forall thread_count ref_count threads store store' n,
        store' = (fun x => if Nat.eqb ref_count x then Some n else store x) -> 
        step (thread_count, ref_count, threads, store, (new_ref (num n)))
             (thread_count, ref_count + 1, threads, store', (ref ref_count))
  | ST_assign1 : forall thread_count thread_count' 
                        ref_count ref_count' threads threads' store store' e1 e1' e,
        step (thread_count, ref_count, threads, store, e)
             (thread_count', ref_count', threads', store', e1') ->
        step (thread_count, ref_count, threads, store, (assign e1 e))
             (thread_count', ref_count', threads', store', (assign e1' e))
  | ST_assign2 : forall thread_count thread_count' 
                        ref_count ref_count' threads threads' store store' e1 e1' v,
        value v ->
        step (thread_count, ref_count, threads, store, e1)
             (thread_count', ref_count', threads', store', e1') ->
        step (thread_count, ref_count, threads, store, (assign v e1))
             (thread_count', ref_count', threads', store', (assign v e1'))
  | ST_assign3 : forall thread_count ref_count threads store store' x n,
        store' = (fun y => if Nat.eqb x y then Some n else store y) -> 
        step (thread_count, ref_count, threads, store, (assign (ref x) (num n)))
             (thread_count, ref_count, threads, store', yunit)
  | ST_deref1 : forall thread_count thread_count' 
                       ref_count ref_count' threads threads' store store' e e',
        step (thread_count, ref_count, threads, store, e)
             (thread_count', ref_count', threads', store', e') ->
        step (thread_count, ref_count, threads, store, (deref e))
             (thread_count', ref_count', threads', store', (deref e'))
  | ST_deref2 : forall thread_count ref_count threads store x n,
        store x = Some n ->
        step (thread_count, ref_count, threads, store, (deref (ref x)))
             (thread_count, ref_count, threads, store, (num n))
  | ST_ifzero1 : forall thread_count thread_count' 
                        ref_count ref_count' threads threads' store store' e1 e1' e2 e3,
        step (thread_count, ref_count, threads, store, e1)
             (thread_count', ref_count', threads', store', e1') ->
        step (thread_count, ref_count, threads, store, (ifzero e1 e2 e3))
             (thread_count', ref_count', threads', store', (ifzero e1' e2 e3))
  | ST_ifzero2 : forall thread_count ref_count threads store e2 e3,
        step (thread_count, ref_count, threads, store, (ifzero (num 0) e2 e3))
             (thread_count, ref_count, threads, store, e2)
  | ST_ifzero3 : forall thread_count ref_count threads store e2 e3 n,
        n <> 0 ->
        step (thread_count, ref_count, threads, store, (ifzero (num n) e2 e3))
             (thread_count, ref_count, threads, store, e3)
  | ST_fix : forall thread_count ref_count threads store T e,
        step (thread_count, ref_count, threads, store, (fics T e))
             (thread_count, ref_count, threads, store, app e (fics T e)).





