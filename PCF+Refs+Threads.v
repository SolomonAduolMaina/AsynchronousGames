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

(* A pool (l, ref_count, l', e) is a 4-tuple where
    - l : (list term) is the list of currently running child threads
    - ref_count : nat is used to generate ref ids
    - store : (nat -> (option nat)) is a function denoting the reference store
    - e : term is the parent thread *)

Definition pool := (list term) * nat * (nat -> (option nat)) * term.

Inductive step : pool -> pool -> Prop :=
  | ST_thread : forall ts ts' l ref_count ref_count' store store' e1 e1' e,
        step (ts ++ ts', ref_count, store, e1) (l, ref_count', store', e1') ->
        step (ts ++ (e1 :: nil) ++ ts', ref_count, store, e)
             (e1' :: l, ref_count', store', e)
  | ST_fork : forall threads ref_count store e e',
        step (threads, ref_count, store, fork e e')
             (e :: threads, ref_count, store, e')
  | ST_join : forall ref_count threads store e,
        (forall e, In e threads -> value e) ->
        step (threads, ref_count, store, join e) (threads, ref_count, store, e)
  | ST_App1 : forall threads threads' ref_count ref_count' store store' e1 e1' e,
        step (threads, ref_count, store, e1) (threads', ref_count', store', e1') ->
        step (threads, ref_count, store, app e1 e)
             (threads', ref_count', store', app e1' e)
  | ST_App2 : forall threads threads' ref_count ref_count' store store' e1 e1' v,
        value v ->
        step (threads, ref_count, store, e1) (threads', ref_count', store', e1') ->
        step (threads, ref_count, store, (app v e1))
             (threads', ref_count', store', (app v e1'))
  | ST_App3 : forall threads ref_count store x T e v,
        value v ->
        step (threads, ref_count, store, (app (lam x T e) v))
             (threads, ref_count, store, ([x:=v]e))
  | ST_newref1 : forall threads threads' ref_count ref_count' store store' e e',
        step (threads, ref_count, store, e) (threads', ref_count', store', e') ->
        step (threads, ref_count, store, (new_ref e))
             (threads', ref_count', store', (new_ref e'))
  | ST_newref2 : forall threads ref_count store store' n,
        store' = (fun x => if Nat.eqb ref_count x then Some n else store x) -> 
        step (threads, ref_count, store, (new_ref (num n)))
             (threads, ref_count + 1, store', (ref ref_count))
  | ST_assign1 : forall threads threads'  ref_count ref_count' store store' e1 e1' e,
        step (threads, ref_count, store, e) (threads', ref_count', store', e1') ->
        step (threads, ref_count, store, (assign e1 e))
             (threads', ref_count', store', (assign e1' e))
  | ST_assign2 : forall threads threads' ref_count ref_count' store store' e1 e1' v,
        value v ->
        step (threads, ref_count, store, e1) (threads', ref_count', store', e1') ->
        step (threads, ref_count, store, (assign v e1))
             (threads', ref_count', store', (assign v e1'))
  | ST_assign3 : forall threads ref_count store store' x n,
        store' = (fun y => if Nat.eqb x y then Some n else store y) -> 
        step (threads, ref_count, store, (assign (ref x) (num n)))
             (threads, ref_count, store', yunit)
  | ST_deref1 : forall threads threads' ref_count ref_count' store store' e e',
        step (threads, ref_count, store, e) (threads', ref_count', store', e') ->
        step (threads, ref_count, store, (deref e))
             (threads', ref_count', store', (deref e'))
  | ST_deref2 : forall ref_count threads store x n,
        store x = Some n ->
        step (threads, ref_count, store, (deref (ref x)))
             (threads, ref_count, store, (num n))
  | ST_ifzero1 : forall threads threads' ref_count ref_count' store store' e1 e1' e2 e3,
        step (threads, ref_count, store, e1) (threads', ref_count', store', e1') ->
        step (threads, ref_count, store, (ifzero e1 e2 e3))
             (threads', ref_count', store', (ifzero e1' e2 e3))
  | ST_ifzero2 : forall threads ref_count store e2 e3,
        step (threads, ref_count, store, (ifzero (num 0) e2 e3))
             (threads, ref_count, store, e2)
  | ST_ifzero3 : forall threads ref_count store e2 e3 n,
        n <> 0 ->
        step (threads, ref_count, store, (ifzero (num n) e2 e3))
             (threads, ref_count, store, e3)
  | ST_fix : forall threads ref_count store T e,
        step (threads, ref_count, store, (fics T e))
             (threads, ref_count, store, app e (fics T e)).

