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
  | fork : (list term) -> term -> term.

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
  | fork l e =>
      fork (map (fun e => [x:=s] e) l) ([x:=s] e)
  end

where "'[' x ':=' s ']' t" := (subst x s t).

Notation "x * y" := (prod x y).
Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z).

(* An tree is the tree of evaluating threads with respective thread ids *)
Inductive tree :=
    | Leaf (a : (term * nat))
    | Node (a : (term * nat)) (l : list tree).

Inductive tree_value : (tree -> Prop) :=
    | leaf_value : forall e n, value e -> tree_value (Leaf (e, n))
    | node_value : forall e n l, 
                   value e -> 
                   (forall e', In e' l -> tree_value e') ->
                   tree_value (Node (e, n) l).

Fixpoint subtree_ids (t : tree) : (list nat) :=
    match t with
      | Leaf (_, n) => (n :: nil)
      | Node _ l => fold_right (fun x y => x ++ y) nil (map subtree_ids l)
    end.

(* A single_thread_in is a 3-tuple (term, ref_count, read_res) where
    - term : tree is the evaluating term
    - ref_count : nat is used to generate ref ids
    - read_res : option (nat * nat) denotes a read response 

  A single_thread_out is a 6-tuple 
   (term, children, ref_count, write_req_req, read_req) where
    - term : tree is the evaluating term
    - children : list term is child threads created
    - ref_count : nat is used to generate ref ids
    - write_req : option (nat * nat) denotes a write request
    - read_req : option nat denotes a read request
    - read_res : option (nat * nat) denotes a read response
*)

Definition single_thread_in := term * nat * (option (nat * nat)).

Definition single_thread_out := 
term * (list term) * nat * (option (nat * nat)) * (option nat) * option (nat * nat).

Inductive step : single_thread_in -> single_thread_out -> Prop :=
  | ST_fork : forall ref_count read_res e children,
        step (fork children e, ref_count, read_res)
             (e, children, ref_count, None, None, read_res)
  | ST_App1 : forall ref_count ref_count' write_req read_req read_res read_res' e1 e1' e l,
        step (e1, ref_count, read_res)
             (e1', l, ref_count', write_req, read_req, read_res') ->
        step (app e1 e, ref_count, read_res)
             (app e1' e, l, ref_count', write_req, read_req, read_res')
  | ST_App2 : forall ref_count ref_count'
                      write_req  read_req  read_res  read_res' e e' l v,
        value v ->
        step (e, ref_count, read_res)
             (e', l, ref_count', write_req, read_req, read_res') ->
        step (app v e, ref_count, read_res)
             (app v e', l, ref_count', write_req, read_req, read_res')
  | ST_App3a : forall ref_count read_res e v x T,
        value v ->
        step (app (lam x T e) v, ref_count, read_res)
             ([x:=v]e, nil, ref_count, None, None, read_res)
  | ST_newref1 : forall ref_count ref_count'
                         write_req read_req read_res read_res' e e' l,
        step (e, ref_count, read_res)
             (e', l, ref_count', write_req, read_req, read_res') ->
        step (new_ref e, ref_count, read_res)
             (new_ref e', l, ref_count', write_req, read_req, read_res')
  | ST_newref2 : forall ref_count read_res n,
        step (new_ref (num n), ref_count, read_res)
             (ref ref_count, nil, ref_count + 1, Some (ref_count, n), None, read_res)
  | ST_assign1 : forall ref_count ref_count' write_req read_req read_res read_res'
                     e1 e1' e l ,
        step (e1, ref_count, read_res)
             (e1', l, ref_count', write_req, read_req, read_res') ->
        step (assign e1 e, ref_count, read_res)
             (assign e1' e, l, ref_count', write_req, read_req, read_res')
  | ST_assign2 : forall ref_count ref_count' write_req read_req read_res read_res'
                     e e' v l,
        value v ->
        step (e, ref_count, read_res)
             (e', l, ref_count', write_req, read_req, read_res') ->
        step (assign v e, ref_count, read_res)
             (assign v e', l, ref_count', write_req, read_req, read_res')
  | ST_assign3 : forall ref_count read_res x n,
        step (assign (ref x) (num n), ref_count, read_res)
             (yunit, nil, ref_count, Some (x, n), None, read_res)
  | ST_fix : forall ref_count read_res T e,
        step (fics T e, ref_count, read_res)
             (app e (fics T e), nil, ref_count, None, None, read_res)
  | ST_ifzero1 : forall ref_count ref_count' write_req read_req read_res read_res'
                     e1 e1' e2 e3 l,
        step (e1, ref_count, read_res)
             (e1', l, ref_count', write_req, read_req, read_res') ->
        step (ifzero e1 e2 e3, ref_count, read_res)
             (ifzero e1' e2 e3, l, ref_count', write_req, read_req, read_res')
  | ST_ifzero2 : forall ref_count read_res e e',
        step (ifzero (num 0) e e', ref_count, read_res)
             (e, nil, ref_count, None, None, read_res)
  | ST_ifzero3 : forall ref_count read_res e e' n,
        n <> 0 ->
        step (ifzero (num n) e e', ref_count, read_res)
             (e', nil, ref_count, None, None, read_res)
  | ST_deref1 : forall ref_count ref_count' write_req read_req read_res read_res'
                     e e' l,
        step (e, ref_count, read_res)
             (e', l, ref_count', write_req, read_req, read_res') ->
        step (deref e, ref_count, read_res)
             (deref e', l, ref_count', write_req, read_req, read_res')
  | ST_deref2a : forall ref_count loc,
        step (deref (ref loc), ref_count, None)
             (deref (ref loc), nil, ref_count, None, Some loc, None)
  | ST_deref3a : forall ref_count loc val,
        step (deref (ref loc), ref_count, Some (loc, val))
             (num val, nil, ref_count, None, None, None).


(* A TSO_machine is an 8 -tuple 
   (threads, thread_count, ref_count, local, write_req, read, global) where
    - threads : tree is the tree of evaluating threads
    - thread_count : nat is used to generate thread ids
    - ref_count : nat is used to generate ref ids
    - local : (nat -> (nat -> (option nat))) denotes local stores
    - write_req : list (nat * (nat * nat)) denotes the write_req buffer
    - read_req : list (nat * nat) denotes the read-request buffer
    - read_res : list (nat * (nat * nat)) denotes the read-response buffer
    - global : (nat -> (option nat)) denotes the global store *)
Definition TSO_machine := tree * nat * nat * (nat -> (nat -> (option nat))) * 
(list (nat * (nat * nat))) * (list (nat * nat)) * (list (nat * (nat * nat))) * (nat -> (option nat)).

Inductive step : TSO_machine -> TSO_machine -> Prop := 
  | ST_child : forall threads threads' thread_count thread_count' ref_count ref_count'
                      local local' write_req write_req' read_req read_req' read_res read_res' global global'
                      e n l l' t t',
               threads = Node (e, n) (l ++ (t :: nil) ++ l') ->
               threads' = Node (e, n) (l ++ (t' :: nil) ++ l') ->
               step (t, thread_count, ref_count, local, write_req, read_req, read_res, global)
                    (t', thread_count', ref_count', local', write_req', read_req', read_res', global') ->
               step (threads, thread_count, ref_count, local, write_req, read_req, read_res, global)
                    (threads', thread_count', ref_count', local', write_req', read_req', read_res', global')
  | ST_thread_done : forall threads threads' thread_count ref_count local write_req read_req read_res global
                      e n l l' t,
              threads = Node (e, n) (l ++ (t :: nil) ++ l') ->
              threads' = Node (e, n) (l ++ l') ->
              tree_value t ->
              (forall m, In m (subtree_ids t) -> 
                         ((forall k, (local m) k = None) /\ 
                          (forall a b, (In (a,b) write_req \/ In (a,b) read_res) -> a <> m) /\
                          (forall a b, In (a,b) read_req -> a <> m))) ->
              step (threads, thread_count, ref_count, local, write_req, read_req, read_res, global)
                   (threads', thread_count, ref_count, local, write_req, read_req, read_res, global)
  | ST_reshape : forall thread_count ref_count local write_req read_req read_res global e n,
                 step (Node (e, n) nil, thread_count, ref_count, local, write_req, read_req, read_res, global)
                      (Leaf (e, n), thread_count, ref_count, local, write_req, read_req, read_res, global)
(* Memory Model *)
  | ST_flush : forall threads thread_count ref_count local local' write_req read_req read_res global global' 
               thread loc val,
               local thread loc = Some val ->
               local' = (fun m k => 
                         if andb (Nat.eqb m thread) (Nat.eqb k loc) then None else local m k) ->
               global' = (fun m => if Nat.eqb m loc then Some val else global m) ->
               step (threads, thread_count, ref_count, local, write_req, read_req, read_res, global)
                    (threads, thread_count, ref_count, local', write_req, read_req, read_res, global')
  | ST_respond1 : forall thread threads thread_count ref_count local write_req read_req read_req'
                         read_res read_res' global loc val,
               read_req = read_req' ++ ((thread, loc) :: nil) ->
               local thread loc = Some val ->
               read_res' = (thread, (loc, val)) :: read_res ->
               step (threads, thread_count, ref_count, local, write_req, read_req, read_res, global)
                    (threads, thread_count, ref_count, local, write_req, read_req', read_res', global)
  | ST_respond2 : forall thread threads thread_count ref_count local write_req read_req read_req'
                         read_res read_res' global loc val,
               read_req = read_req' ++ ((thread, loc) :: nil) ->
               local thread loc = None ->
               global loc = Some val ->
               read_res' = (thread, (loc, val)) :: read_res ->
               step (threads, thread_count, ref_count, local, write_req, read_req, read_res, global)
                    (threads, thread_count, ref_count, local, write_req, read_req', read_res', global)
  | ST_write_req : forall thread threads thread_count ref_count local local'
                       write_req write_req' read_req read_res global loc val,
               write_req = write_req' ++ ((thread, (loc, val)) :: nil) ->
               local' = (fun m k => 
                         if andb (Nat.eqb m thread) (Nat.eqb k loc) then Some val else local m k) ->
               step (threads, thread_count, ref_count, local, write_req, read_req, read_res, global)
                    (threads, thread_count, ref_count, local', write_req', read_req, read_res, global)
(* Single step *)
  | ST_forka : forall threads threads' thread_count thread_count' ref_count local
                       write_req read_req read_res global l l' e n children f,
        threads = Node (fork children e, n) l ->
        f = (fun e' r => (S (fst r), ((Leaf (e', fst r)) :: (snd r)))) ->
        (thread_count', l') = fold_right f (thread_count, l) children ->
        threads' = Node (e, n) l' ->
        step (threads, thread_count, ref_count, local, write_req, read_req, read_res, global)
             (threads', thread_count', ref_count, local, write_req, read_req, read_res, global)
  | ST_forkb : forall threads threads' thread_count thread_count' ref_count local
                       write_req read_req read_res global l' e n children f,
        threads = Leaf (fork children e, n) ->
        f = (fun e' r => (S (fst r), ((Leaf (e', fst r)) :: (snd r)))) ->
        (thread_count', l') = fold_right f (thread_count, nil) children ->
        threads' = Node (e, n) l' ->
        step (threads, thread_count, ref_count, local, write_req, read_req, read_res, global)
             (threads', thread_count', ref_count, local, write_req, read_req, read_res, global)
  | ST_App1a : forall thread_count thread_count' ref_count ref_count'
                     local local' write_req write_req' read_req read_req' read_res read_res' global global'
                     e1 e1' e n,
        step (Leaf (e1, n), thread_count, ref_count, local, write_req, read_req, read_res, global)
             (Leaf (e1', n), thread_count', ref_count', local', write_req', read_req', read_res', global') ->
        step (Leaf (app e1 e, n), thread_count, ref_count, local, write_req, read_req, read_res, global)
             (Leaf (app e1' e, n), thread_count', ref_count', local', write_req', read_req', read_res', global')
  | ST_App1b : forall thread_count thread_count' ref_count ref_count'
                     local local' write_req write_req' read_req read_req' read_res read_res' global global'
                     e1 e1' e n l,
        step (Node (e1, n) l, thread_count, ref_count, local, write_req, read_req, read_res, global)
             (Node (e1', n) l, thread_count', ref_count', local', write_req', read_req', read_res', global') ->
        step (Node (app e1 e, n) l, thread_count, ref_count, local, write_req, read_req, read_res, global)
             (Node (app e1' e, n) l, thread_count', ref_count', local', write_req', read_req', read_res', global')
  | ST_App2a : forall thread_count thread_count' ref_count ref_count'
                     local local' write_req write_req' read_req read_req' read_res read_res' global global'
                     e e' n v,
        value v ->
        step (Leaf (e, n), thread_count, ref_count, local, write_req, read_req, read_res, global)
             (Leaf (e', n), thread_count', ref_count', local', write_req', read_req', read_res', global') ->
        step (Leaf (app v e, n), thread_count, ref_count, local, write_req, read_req, read_res, global)
             (Leaf (app v e', n), thread_count', ref_count', local', write_req', read_req', read_res', global')
  | ST_App2b : forall thread_count thread_count' ref_count ref_count'
                     local local' write_req write_req' read_req read_req' read_res read_res' global global'
                     e e' n v l,
        value v ->
        step (Node (e, n) l, thread_count, ref_count, local, write_req, read_req, read_res, global)
             (Node (e', n) l, thread_count', ref_count', local', write_req', read_req', read_res', global') ->
        step (Node (app v e, n) l, thread_count, ref_count, local, write_req, read_req, read_res, global)
             (Node (app v e', n) l, thread_count', ref_count', local', write_req', read_req', read_res', global')
  | ST_App3a : forall thread_count ref_count local write_req read_req read_res global e n v x T,
        value v ->
        step (Leaf (app (lam x T e) v, n), thread_count, ref_count, local, write_req, read_req, read_res, global)
             (Leaf ([x:=v]e, n), thread_count, ref_count, local, write_req, read_req, read_res, global)
  | ST_App3b : forall thread_count ref_count local write_req read_req read_res global e n v l x T,
        value v ->
        step (Node (app (lam x T e) v, n) l, thread_count, ref_count, local, write_req, read_req, read_res, global)
             (Node ([x:=v]e, n) l, thread_count, ref_count, local, write_req, read_req, read_res, global)
  | ST_newref1a : forall thread_count thread_count' ref_count ref_count'
                     local local' write_req write_req' read_req read_req' read_res read_res' global global'
                     e e' n,
        step (Leaf (e, n), thread_count, ref_count, local, write_req, read_req, read_res, global)
             (Leaf (e', n), thread_count', ref_count', local', write_req', read_req', read_res', global') ->
        step (Leaf (new_ref e, n), thread_count, ref_count, local, write_req, read_req, read_res, global)
             (Leaf (new_ref e', n), thread_count', ref_count', local', write_req', read_req', read_res', global')
  | ST_newref1b : forall thread_count thread_count' ref_count ref_count'
                     local local' write_req write_req' read_req read_req' read_res read_res' global global'
                     e e' n l,
        step (Node (e, n) l, thread_count, ref_count, local, write_req, read_req, read_res, global)
             (Node (e', n) l, thread_count', ref_count', local', write_req', read_req', read_res', global') ->
        step (Node (new_ref e, n) l, thread_count, ref_count, local, write_req, read_req, read_res, global)
             (Node (new_ref e', n) l, thread_count', ref_count', local', write_req', read_req', read_res', global')
  | ST_newref2a : forall thread thread_count ref_count local write_req write_req' read_req read_res global n,
        write_req' = (thread, (ref_count, n)) :: write_req ->
        step (Leaf (new_ref (num n), thread), thread_count, ref_count, local, write_req, read_req, read_res, global)
             (Leaf (ref ref_count, thread), thread_count, ref_count + 1, local, write_req', read_req, read_res, global)
  | ST_newref2b : forall thread thread_count ref_count local write_req write_req' read_req read_res global n l,
        write_req' = (thread, (ref_count, n)) :: write_req ->
        step (Node (new_ref (num n), thread) l, thread_count, ref_count, local, write_req, read_req, read_res, global)
             (Node (ref ref_count, thread) l, thread_count, ref_count + 1, local, write_req', read_req, read_res, global)
  | ST_assign1a : forall thread_count thread_count' ref_count ref_count'
                     local local' write_req write_req' read_req read_req' read_res read_res' global global'
                     e1 e1' e n,
        step (Leaf (e1, n), thread_count, ref_count, local, write_req, read_req, read_res, global)
             (Leaf (e1', n), thread_count', ref_count', local', write_req', read_req', read_res', global') ->
        step (Leaf (assign e1 e, n), thread_count, ref_count, local, write_req, read_req, read_res, global)
             (Leaf (assign e1' e, n), thread_count', ref_count', local', write_req', read_req', read_res', global')
  | ST_assign1b : forall thread_count thread_count' ref_count ref_count'
                     local local' write_req write_req' read_req read_req' read_res read_res' global global'
                     e1 e1' e n l,
        step (Leaf (e1, n), thread_count, ref_count, local, write_req, read_req, read_res, global)
             (Leaf (e1', n), thread_count', ref_count', local', write_req', read_req', read_res', global') ->
        step (Node (assign e1 e, n) l, thread_count, ref_count, local, write_req, read_req, read_res, global)
             (Node (assign e1' e, n) l, thread_count', ref_count', local', write_req', read_req', read_res', global')
  | ST_assign2a : forall thread_count thread_count' ref_count ref_count'
                     local local' write_req write_req' read_req read_req' read_res read_res' global global'
                     e e' n v,
        value v ->
        step (Leaf (e, n), thread_count, ref_count, local, write_req, read_req, read_res, global)
             (Leaf (e', n), thread_count', ref_count', local', write_req', read_req', read_res', global') ->
        step (Leaf (assign v e, n), thread_count, ref_count, local, write_req, read_req, read_res, global)
             (Leaf (assign v e', n), thread_count', ref_count', local', write_req', read_req', read_res', global')
  | ST_assign2b : forall thread_count thread_count' ref_count ref_count'
                     local local' write_req write_req' read_req read_req' read_res read_res' global global'
                     e e' n v l,
        value v ->
        step (Node (e, n) l, thread_count, ref_count, local, write_req, read_req, read_res, global)
             (Node (e', n) l, thread_count', ref_count', local', write_req', read_req', read_res', global') ->
        step (Node (assign v e, n) l, thread_count, ref_count, local, write_req, read_req, read_res, global)
             (Node (assign v e', n) l, thread_count', ref_count', local', write_req', read_req', read_res', global')
  | ST_assign3a : forall thread thread_count ref_count local write_req write_req' read_req read_res global x n,
        write_req' = (thread, (x, n)) :: write_req ->
        step (Leaf (assign (ref x) (num n), thread), thread_count, ref_count, local, write_req, read_req, read_res, global)
             (Leaf (yunit, thread), thread_count, ref_count, local, write_req', read_req, read_res, global)
  | ST_assign3b : forall thread thread_count ref_count local write_req write_req' read_req read_res global x n l,
        write_req' = (thread, (x, n)) :: write_req ->
        step (Node (assign (ref x) (num n), thread) l, thread_count, ref_count, local, write_req, read_req, read_res, global)
             (Node (yunit, thread) l, thread_count, ref_count, local, write_req', read_req, read_res, global)
  | ST_fixa : forall thread thread_count ref_count local write_req read_req read_res global T e,
        step (Leaf (fics T e, thread), thread_count, ref_count, local, write_req, read_req, read_res, global)
             (Leaf (app e (fics T e), thread), thread_count, ref_count, local, write_req, read_req, read_res, global)
  | ST_fixb : forall thread thread_count ref_count local write_req read_req read_res global T e l,
        step (Node (fics T e, thread) l, thread_count, ref_count, local, write_req, read_req, read_res, global)
             (Node (app e (fics T e), thread) l, thread_count, ref_count, local, write_req, read_req, read_res, global)
  | ST_deref1a : forall thread_count thread_count' ref_count ref_count'
                     local local' write_req write_req' read_req read_req' read_res read_res' global global'
                     e e' n,
        step (Leaf (e, n), thread_count, ref_count, local, write_req, read_req, read_res, global)
             (Leaf (e', n), thread_count', ref_count', local', write_req', read_req', read_res', global') ->
        step (Leaf (deref e, n), thread_count, ref_count, local, write_req, read_req, read_res, global)
             (Leaf (deref e', n), thread_count', ref_count', local', write_req', read_req', read_res', global')
  | ST_deref1b : forall thread_count thread_count' ref_count ref_count'
                     local local' write_req write_req' read_req read_req' read_res read_res' global global'
                     e e' n l,
        step (Node (e, n) l, thread_count, ref_count, local, write_req, read_req, read_res, global)
             (Node (e', n) l, thread_count', ref_count', local', write_req', read_req', read_res', global') ->
        step (Node (deref e, n) l, thread_count, ref_count, local, write_req, read_req, read_res, global)
             (Node (deref e', n) l, thread_count', ref_count', local', write_req', read_req', read_res', global')
  | ST_deref2a : forall thread thread_count ref_count local write_req read_req read_req' read_res global loc,
        read_req' = (thread, loc) :: read_req ->
        step (Leaf (deref (ref loc), thread), thread_count, ref_count, local, write_req, read_req, read_res, global)
             (Leaf (deref (ref loc), thread), thread_count, ref_count, local, write_req, read_req', read_res, global)
  | ST_deref2b : forall thread thread_count ref_count local write_req read_req read_req' read_res global loc l,
        read_req' = (thread, loc) :: read_req ->
        step (Node (deref (ref loc), thread) l, thread_count, ref_count, local, write_req, read_req, read_res, global)
             (Node (deref (ref loc), thread) l, thread_count, ref_count, local, write_req, read_req', read_res, global)
  | ST_deref3a : forall thread thread_count ref_count local write_req read_req read_res read_res' global loc val,
        read_res = read_res' ++ ((thread, (loc, val)) :: nil) ->
        step (Leaf (deref (ref loc), thread), thread_count, ref_count, local, write_req, read_req, read_res, global)
             (Leaf (num val, thread), thread_count, ref_count, local, write_req, read_req, read_res', global)
  | ST_deref3b : forall thread thread_count ref_count local write_req read_req read_res read_res' global loc val l,
        read_res = read_res' ++ ((thread, (loc, val)) :: nil) ->
        step (Node (deref (ref loc), thread) l, thread_count, ref_count, local, write_req, read_req, read_res, global)
             (Node (num val, thread) l, thread_count, ref_count, local, write_req, read_req, read_res', global)
  | ST_ifzero1a : forall thread_count thread_count' ref_count ref_count'
                     local local' write_req write_req' read_req read_req' read_res read_res' global global'
                     e1 e1' e2 e3 n,
        step (Leaf (e1, n), thread_count, ref_count, local, write_req, read_req, read_res, global)
             (Leaf (e1', n), thread_count', ref_count', local', write_req', read_req', read_res', global') ->
        step (Leaf (ifzero e1 e2 e3, n), thread_count, ref_count, local, write_req, read_req, read_res, global)
             (Leaf (ifzero e1' e2 e3, n), thread_count', ref_count', local', write_req', read_req', read_res', global')
 | ST_ifzero1b : forall thread_count thread_count' ref_count ref_count'
                     local local' write_req write_req' read_req read_req' read_res read_res' global global'
                     e1 e1' e2 e3 n l,
        step (Node (e1, n) l, thread_count, ref_count, local, write_req, read_req, read_res, global)
             (Node (e1', n) l, thread_count', ref_count', local', write_req', read_req', read_res', global') ->
        step (Node (ifzero e1 e2 e3, n) l, thread_count, ref_count, local, write_req, read_req, read_res, global)
             (Node (ifzero e1' e2 e3, n) l, thread_count', ref_count', local', write_req', read_req', read_res', global')
  | ST_ifzero2a : forall thread thread_count ref_count local write_req read_req read_res  global e e',
        step (Leaf (ifzero (num 0) e e', thread), thread_count, ref_count, local, write_req, read_req, read_res, global)
             (Leaf (e, thread), thread_count, ref_count, local, write_req, read_req, read_res, global)
  | ST_ifzero2b : forall thread thread_count ref_count local write_req read_req read_res  global e e' l,
        step (Node (ifzero (num 0) e e', thread) l, thread_count, ref_count, local, write_req, read_req, read_res, global)
             (Node (e, thread) l, thread_count, ref_count, local, write_req, read_req, read_res, global)
  | ST_ifzero3a : forall thread thread_count ref_count local write_req read_req read_res  global e e' n,
        n <> 0 ->
        step (Leaf (ifzero (num n) e e', thread), thread_count, ref_count, local, write_req, read_req, read_res, global)
             (Leaf (e', thread), thread_count, ref_count, local, write_req, read_req, read_res, global)
  | ST_ifzero3b : forall thread thread_count ref_count local write_req read_req read_res global e e' l n,
        n <> 0 ->
        step (Node (ifzero (num n) e e', thread) l, thread_count, ref_count, local, write_req, read_req, read_res, global)
             (Node (e', thread) l, thread_count, ref_count, local, write_req, read_req, read_res, global).

