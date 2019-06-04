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
  | fork_id : nat -> term
  | fork : (list term) -> term
  | join : term -> term -> term.

Inductive value : term -> Prop :=
  | v_lam : forall x tau e, value (lam x tau e)
  | v_num : forall n, value (num n)
  | v_yunit : value yunit
  | v_ref : forall n, value (ref n)
  | v_fork : forall n, value (fork_id n).

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
  | fork_id n =>
      fork_id n
  | join e1 e2 =>
      join ([x:=s] e1) ([x:=s] e2)
  | fork l =>
      fork (map (fun e => [x:=s] e) l)
  end

where "'[' x ':=' s ']' t" := (subst x s t).

Notation "x * y" := (prod x y).
Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z).

(* A pool (threads, fork_count, ref_count, local, global, e) is a 5-tuple where
    - threads : nat -> (list (term * nat * (list (nat * nat)) )) is a list
      of threads with respective fork_id and local stores
    - fork_count : nat is used to generate fork ids
    - ref_count : nat is used to generate ref ids
    - local : (list (nat * nat)) is the local store for the main thread
    - global : (nat -> (option nat)) is the global store
    - e : term is the main thread *)

Definition pool := (list (term * nat * (list (nat * nat))) )
* nat * nat * (list (nat * nat)) * (nat -> (option nat)) * term.

Inductive step : pool -> pool -> Prop :=
  | ST_switch : forall ts ts' l ref_count ref_count' fork_count fork_count'
                       local local' switched global global' e1 e1' n e,
        step (ts ++ ts', fork_count, ref_count, local, global, e1) 
             (l, fork_count', ref_count', local', global', e1') ->
        step (ts ++ ((e1, n, local) :: nil) ++ ts', fork_count, ref_count, switched, global, e)
             ((e1', n, local') :: l, fork_count', ref_count', switched, global', e)
  | ST_fork : forall threads threads' fork_count ref_count local global l,
        threads' = threads ++ (map (fun e => (e, fork_count, local)) l) ->
        step (threads, fork_count, ref_count, local, global, fork l)
             (threads', fork_count + 1, ref_count, local, global, fork_id fork_count)
  | ST_join1 : forall threads threads' fork_count local local'
                     fork_count' ref_count ref_count' global global' e1 e1' e,
        step (threads, fork_count, ref_count, local, global, e1) 
             (threads', fork_count', ref_count', local', global', e1') ->
        step (threads, fork_count, ref_count, local, global, join e1 e)
             (threads', fork_count', ref_count', local', global', join e1' e)
  | ST_join2 : forall fork_count ref_count threads local global n e,
        (forall e s, In (e, n, s) threads -> value e) ->
        step (threads, fork_count, ref_count, local, global, join (fork_id n) e)
             (threads, fork_count, ref_count, local, global, e)
  | ST_flush1 : forall fork_count ref_count threads local global global' e,
        (forall n k, (In (n, k) local -> global' n = Some k) /\
                     ((~ (In (n, k) local)) -> global' n = global n))  ->
        step (threads, fork_count, ref_count, local, global, e)
             (threads, fork_count, ref_count, nil, global', e)
  | ST_flush2 : forall ts ts' r f local local' global global' e e' n,
       (forall n k, (In (n, k) local -> global' n = Some k) /\
                    ((~ (In (n, k) local)) -> global' n = global n))  ->
        step (ts ++ ((e', n, local) :: nil) ++ ts', f, r, local', global, e)
             (ts ++ ((e', n, nil) :: nil) ++ ts', f, r, local', global', e)
  | ST_App1 : forall threads threads' fork_count local local'
                     fork_count' ref_count ref_count' global global' e1 e1' e,
        step (threads, fork_count, ref_count, local, global, e1) 
             (threads', fork_count', ref_count', local', global', e1') ->
        step (threads, fork_count, ref_count, local, global, app e1 e)
             (threads', fork_count', ref_count', local', global', app e1' e)
  | ST_App2 : forall threads threads' fork_count fork_count' local local'
              ref_count ref_count' global global' e1 e1' v,
        value v ->
        step (threads, fork_count, ref_count, local, global, e1) 
             (threads', fork_count', ref_count', local', global', e1') ->
        step (threads, fork_count, ref_count, local, global, (app v e1))
             (threads', fork_count', ref_count', local', global', (app v e1'))
  | ST_App3 : forall threads fork_count local ref_count global x T e v,
        value v ->
        step (threads, fork_count, ref_count, local, global, (app (lam x T e) v))
             (threads, fork_count, ref_count, local, global, ([x:=v]e))
  | ST_newref1 : forall threads threads' ref_count ref_count' local local'
                        fork_count fork_count' global global' e e',
        step (threads, fork_count, ref_count, local, global, e) 
             (threads', fork_count', ref_count', local', global', e') ->
        step (threads, fork_count, ref_count, local, global, (new_ref e))
             (threads', fork_count', ref_count', local', global', (new_ref e'))
  | ST_newref2 : forall threads fork_count ref_count local local' global n,
        In (ref_count, n) local' ->
        (forall a k, (In (a, k) local' /\ a = ref_count) -> k = n) ->
        (forall a k, (In (a, k) local' /\ a <> ref_count) -> In (a, k) local) ->
        step (threads, fork_count, ref_count, local, global, (new_ref (num n)))
             (threads, fork_count, ref_count + 1, local', global, (ref ref_count))
  | ST_assign1 : forall threads threads' ref_count ref_count' local local'
                        fork_count fork_count' global global' e1 e1' e,
        step (threads, fork_count, ref_count, local, global, e)
             (threads', fork_count', ref_count', local', global', e1') ->
        step (threads, fork_count, ref_count, local, global, (assign e1 e))
             (threads', fork_count', ref_count', local', global', (assign e1' e))
  | ST_assign2 : forall threads threads' ref_count ref_count' local local'
                 fork_count fork_count' global global' e1 e1' v,
        value v ->
        step (threads, fork_count, ref_count, local, global, e1) 
             (threads', fork_count', ref_count', local', global', e1') ->
        step (threads, fork_count, ref_count, local, global, (assign v e1))
             (threads', fork_count', ref_count', local', global', (assign v e1'))
  | ST_assign3 : forall threads fork_count ref_count local global local' x n,
        In (x, n) local' ->
        (forall a k, (In (a, k) local' /\ a = x) -> k = n) ->
        (forall a k, (In (a, k) local' /\ a <> x) -> In (a, k) local) ->
        step (threads, fork_count, ref_count, local, global, (assign (ref x) (num n)))
             (threads, fork_count, ref_count, local', global, yunit)
  | ST_deref1 : forall threads threads' ref_count ref_count' local local'
                fork_count fork_count' global global' e e',
        step (threads, fork_count, ref_count, local, global, e)
             (threads', fork_count', ref_count', local', global', e') ->
        step (threads, fork_count, ref_count, local, global, (deref e))
             (threads', fork_count', ref_count', local', global', (deref e'))
  | ST_deref2 : forall ref_count fork_count threads local global x n,
        In (x,n) local ->
        step (threads, fork_count, ref_count, local, global, (deref (ref x)))
             (threads, fork_count, ref_count, local, global, (num n))
  | ST_deref3 : forall ref_count fork_count threads local global x n,
        (forall k, ~ In (x, k) local) ->
        global x = Some n ->
        step (threads, fork_count, ref_count, local, global, (deref (ref x)))
             (threads, fork_count, ref_count, local, global, (num n))
  | ST_ifzero1 : forall threads threads' ref_count ref_count' local local'
                        fork_count fork_count' global global' e1 e1' e2 e3,
        step (threads, fork_count, ref_count, local, global, e1)
             (threads', fork_count', ref_count', local', global', e1') ->
        step (threads, fork_count, ref_count, local, global, (ifzero e1 e2 e3))
             (threads', fork_count, ref_count', local', global', (ifzero e1' e2 e3))
  | ST_ifzero2 : forall threads fork_count ref_count local global e2 e3,
        step (threads, fork_count, ref_count, local, global, (ifzero (num 0) e2 e3))
             (threads, fork_count, ref_count, local, global, e2)
  | ST_ifzero3 : forall threads fork_count ref_count local global e2 e3 n,
        n <> 0 ->
        step (threads, fork_count, ref_count, local, global, (ifzero (num n) e2 e3))
             (threads, fork_count, ref_count, local, global, e3)
  | ST_fix : forall threads fork_count ref_count local global T e,
        step (threads, fork_count, ref_count, local, global, (fics T e))
             (threads, fork_count, ref_count, local, global, app e (fics T e)).

