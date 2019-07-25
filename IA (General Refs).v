Require Import Strings.String.
Require Import List.

Inductive type : Type :=
  | Nat : type
  | Unit : type
  | Ref : type -> type
  | Arrow : type -> type -> type
  | Product : type -> type -> type.

Inductive term : Type :=
(* PCF *)
  | var : string -> term
  | app : term -> term -> term
  | lam : string -> type -> term -> term
  | ifzero : term -> term -> term -> term
  | fics : type -> term -> term
  | num : nat -> term
  | yunit : term
  | paire : term -> term -> term
  | first : term -> term
  | second : term -> term

(* (General) References. *)
  | ref : type -> nat -> term
  | new_ref : type -> term -> term
  | assign : term -> term -> term
  | deref : term -> term

(* Threads *)
  | fork : term -> term -> term.

Inductive value : term -> Prop :=
  | v_lam : forall x tau e, value (lam x tau e)
  | v_num : forall n, value (num n)
  | v_yunit : value yunit
  | v_ref : forall tau n, value (ref tau n)
  | V_pair : forall v1 v2,
             value v1 ->
             value v2 ->
             value (paire v1 v2).

Reserved Notation "'[' x ':=' s ']' t" (at level 20).

Fixpoint subst (x : string) (s : term) (t : term) : term :=
  match t with
  | var x' =>
      if string_dec x x' then s else t
  | lam y T e =>
      lam y T (if string_dec x y then e else [x:=s] e)
  | app t1 t2 =>
      app ([x:=s] t1) ([x:=s] t2)
  | num n =>
      num n
  | ref tau n =>
      ref tau n
  | yunit =>
      yunit
  | ifzero e1 e2 e3 =>
      ifzero ([x:=s] e1) ([x:=s] e2) ([x:=s] e3)
  | fics T e =>
      fics T ([x:=s] e)
  | new_ref tau e =>
      new_ref tau ([x:=s] e)
  | assign e1 e2 =>
      assign ([x:=s] e1) ([x:=s] e2)
  | deref e =>
      deref ([x:=s] e)
  | fork e e' =>
      fork ([x:=s] e) ([x:=s] e')
  | paire e e' =>
      paire ([x:=s] e) ([x:=s] e')
  | first e =>
      first ([x:=s] e)
  | second e =>
      second ([x:=s] e)
  end

where "'[' x ':=' s ']' t" := (subst x s t).

Notation "x * y" := (prod x y).
Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z).

Definition location  := nat.
Definition memory_model := (location -> (option (type * term))).

Definition update_store (store : memory_model) loc tau val :=
(fun m => if Nat.eqb m loc then Some (tau, val) else (store m)).

Inductive step : (term * memory_model) -> (term * memory_model) -> Prop :=
  | ST_Paire1 : forall e1 e1' e M M',
        step (e1, M) (e1', M') ->
        step (paire e1 e, M) (paire e1' e, M')
  | ST_Paire2 : forall e e' M M' v,
        value v ->
        step (e, M) (e', M') ->
        step (paire v e, M) (paire v e', M')
  | ST_first1 : forall e1 e1' M M',
        step (e1, M) (e1', M') ->
        step (first e1, M) (first e1', M')
  | ST_first2 : forall v1 v2 M,
        value v1 ->
        value v2 ->
        step (first (paire v1 v2), M) (v1, M)
  | ST_second1 : forall e1 e1' M M',
        step (e1, M) (e1', M') ->
        step (second e1, M) (second e1', M')
  | ST_second2 : forall v1 v2 M,
        value v1 ->
        value v2 ->
        step (second (paire v1 v2), M) (v2, M)
  | ST_App1 : forall e1 e1' e M M',
        step (e1, M) (e1', M') ->
        step (app e1 e, M) (app e1' e, M')
  | ST_App2 : forall e e' M M' v,
        value v ->
        step (e, M) (e', M') ->
        step (app v e, M) (app v e', M')
  | ST_App3a : forall e v x T M,
        value v ->
        step (app (lam x T e) v, M) ([x:=v]e, M)
  | ST_new1 : forall tau e e' M M',
        step (e, M) (e', M') ->
        step (new_ref tau e, M) (new_ref tau e', M')
  | ST_new2 : forall loc tau val M M' ,
        value val ->
        M loc = None ->
        M' = update_store M loc tau val ->
        step (new_ref tau val, M) (ref tau loc, M')
  | ST_assign1 : forall e1 e1' e M M',
        step (e1, M) (e1', M') ->
        step (assign e1 e, M) (assign e1' e, M')
  | ST_assign2 : forall e e' M M' v,
        value v ->
        step (e, M) (e', M') ->
        step (assign v e, M) (assign v e', M')
  | ST_assign3 : forall loc tau val M,
        step (assign (ref tau loc) val, M) 
             (yunit, update_store M loc tau val)
  | ST_fix : forall T e M,
        step (fics T e, M) (app e (fics T e), M)
  | ST_ifzero1 : forall e1 e1' e2 e3 M M',
        step (e1, M) (e1', M') ->
        step (ifzero e1 e2 e3, M) (ifzero e1' e2 e3, M')
  | ST_ifzero2 : forall e e' M,
        step (ifzero (num 0) e e', M) (e, M)
  | ST_ifzero3 : forall e e' n M,
        n <> 0 ->
        step (ifzero (num n) e e', M) (e', M)
  | ST_deref1 : forall e e' M M',
        step (e, M) (e', M') ->
        step (deref e, M) (deref e', M')
  | ST_deref2 : forall val tau loc M,
        M loc = Some (tau, val) ->
        step (deref (ref tau loc), M) (val, M)
  | ST_fork1 : forall e e' e1 M M',
        step (e, M) (e', M') ->
        step (fork e e1, M) (fork e' e1, M')
  | ST_fork2 : forall e e' e1 M M',
        step (e, M) (e', M') ->
        step (fork e1 e, M) (fork e1 e', M')
  | ST_fork3 : forall e val M,
        value val ->
        step (fork e val, M) (e, M).

