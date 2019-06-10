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
  | new_ref : term
  | assign : term -> term -> term
  | deref : term -> term

(* Threads *)
  | fork : term -> term -> term.

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
      lam y T (if string_dec x y then e else [x:=s] e)
  | app t1 t2 =>
      app ([x:=s] t1) ([x:=s] t2)
  | num n =>
      num n
  | ref n =>
      ref n
  | yunit =>
      yunit
  | ifzero e1 e2 e3 =>
      ifzero ([x:=s] e1) ([x:=s] e2) ([x:=s] e3)
  | fics T e =>
      fics T ([x:=s] e)
  | new_ref =>
      new_ref
  | assign e1 e2 =>
      assign ([x:=s] e1) ([x:=s] e2)
  | deref e =>
      deref ([x:=s] e)
  | fork e e' =>
      fork ([x:=s] e) ([x:=s] e')
  end

where "'[' x ':=' s ']' t" := (subst x s t).

Notation "x * y" := (prod x y).
Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z).

Inductive mem_event : Type :=
    | Read (loc : nat) (val : nat)
    | Write (loc : nat) (val : nat)
    | Allocate (loc : nat)
    | Tau.

Inductive step : term -> mem_event -> term -> Prop :=
  | ST_App1 : forall e1 e1' e event,
        step e1 event e1' ->
        step (app e1 e) event (app e1' e)
  | ST_App2 : forall e e' event v,
        value v ->
        step e event e' ->
        step (app v e) event (app v e')
  | ST_App3a : forall e v x T,
        value v ->
        step (app (lam x T e) v) Tau ([x:=v]e)
  | ST_new : forall n,
        step (new_ref) (Allocate n) (ref n)
  | ST_assign1 : forall e1 e1' e event,
        step e1 event e1' ->
        step (assign e1 e) event (assign e1' e)
  | ST_assign2 : forall e e' event v,
        value v ->
        step e event e' ->
        step (assign v e) event (assign v e')
  | ST_assign3 : forall loc n,
        step (assign (ref loc) (num n)) (Write loc n) yunit
  | ST_fix : forall T e,
        step (fics T e) Tau (app e (fics T e))
  | ST_ifzero1 : forall e1 e1' e2 e3 event,
        step e1 event e1' ->
        step (ifzero e1 e2 e3) event (ifzero e1' e2 e3)
  | ST_ifzero2 : forall e e',
        step (ifzero (num 0) e e') Tau e
  | ST_ifzero3 : forall e e' n,
        n <> 0 ->
        step (ifzero (num n) e e') Tau e'
  | ST_deref1 : forall e event e',
        step e event e' ->
        step (deref e) event (deref e')
  | ST_deref2 : forall val loc,
        step (deref (ref loc)) (Read loc val) (num val).

Definition thread_id := nat.
Definition location  := nat.
Definition local_store := (thread_id -> (location -> (option nat))).
Definition global_store := (location -> (option nat)).
Definition memory_model := local_store * global_store.

Definition update_local (local : local_store) thread loc val :=
(fun m k => if andb (Nat.eqb m thread) (Nat.eqb k loc) then val else local m k).

Definition update_global (global : global_store) loc val :=
(fun m => if Nat.eqb m loc then val else global m).

Inductive mem_step : memory_model -> (thread_id * mem_event) -> memory_model -> Prop := 
  | ST_read1 : forall thread val mem loc,
               (fst mem) thread loc = Some val ->
               mem_step mem (thread, Read loc val) mem
  | ST_read2 : forall thread val mem loc,
               (fst mem) thread loc = None ->
               (snd mem) loc = Some val ->
               mem_step mem (thread, Read loc val) mem
  | ST_write : forall thread val mem loc local',
               local' = update_local (fst mem) thread loc (Some val) ->
               mem_step mem (thread, (Write loc val)) (local', snd mem)
  | ST_allocate : forall thread mem loc local' global',
               (fst mem) thread loc = None ->
               (snd mem) loc = None ->
               local' = update_local (fst mem) thread loc (Some 0) ->
               global' = update_global (snd mem) loc (Some 0) ->
               mem_step mem (thread, (Allocate loc)) (local', global').

Inductive thread_tree :=
    | Leaf (a : (term * nat))
    | Node (a : (term * nat)) (l : list thread_tree).

Inductive thread_tree_value : (thread_tree -> Prop) :=
    | leaf_value : forall e n, value e -> thread_tree_value (Leaf (e, n))
    | node_value : forall e n l, 
                   value e -> 
                   (forall e', In e' l -> thread_tree_value e') ->
                   thread_tree_value (Node (e, n) l).

Fixpoint subtree_ids (t : thread_tree) : (list nat) :=
    match t with
      | Leaf (_, n) => (n :: nil)
      | Node _ l => fold_right (fun x y => x ++ y) nil (map subtree_ids l)
    end.

Definition TSO_machine := thread_tree * nat * memory_model.

Inductive STEP : TSO_machine -> TSO_machine -> Prop :=
  | ST_synchronize1 : forall e e' mem event mem' thread thread_count,
                step e event e' ->
                mem_step mem (thread, event) mem' ->
                STEP (Leaf (e, thread), thread_count, mem)
                     (Leaf (e', thread), thread_count, mem')
  | ST_synchronize2 : forall e e' mem event mem' thread l thread_count,
                step e event e' ->
                mem_step mem (thread, event) mem' ->
                STEP (Node (e, thread) l, thread_count, mem)
                     (Node (e', thread) l, thread_count, mem')
  | ST_flush : forall local' global' thread_count thread loc val thread_tree mem,
               (fst mem) thread loc = Some val ->
               local' = update_local (fst mem) thread loc None ->
               global' = update_global (snd mem) loc (Some val) ->
               STEP (thread_tree, thread_count, mem) (thread_tree, thread_count, (local', global'))
  | ST_child : forall mem mem' e n l l' t t' thread_count thread_count',
               STEP (t, thread_count, mem) (t', thread_count', mem') ->
               STEP (Node (e, n) (l ++ (t :: nil) ++ l'), thread_count, mem)
                    (Node (e, n) (l ++ (t' :: nil) ++ l'), thread_count', mem')
  | ST_fork1 : forall mem e e' thread thread_count,
               STEP (Leaf (fork e e', thread), thread_count, mem)
                    (Node (e', thread) ((Leaf (e, thread_count)) :: nil), S thread_count, mem)
  | ST_fork2 : forall mem e e' l thread thread_count,
               STEP (Node (fork e e', thread) l, thread_count, mem)
                    (Node (e', thread) ((Leaf (e, thread_count)) :: l), S thread_count, mem)
  | ST_reshape : forall thread_count mem e n,
                 STEP (Node (e, n) nil, thread_count, mem)
                      (Leaf (e, n), thread_count, mem)
  | ST_thread_done : forall thread_count mem e n l l' t,
              thread_tree_value t ->
              (forall thread loc, In thread (subtree_ids t) -> (fst mem) thread loc = None) ->
              STEP (Node (e, n) (l ++ (t :: nil) ++ l'), thread_count, mem)
                   (Node (e, n) (l ++ l'), thread_count, mem).
