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
  | new: string -> term -> term
  | assign : term -> term -> term
  | deref : term -> term

(* Threads *)
  | fork : (list term) -> term -> term.

Inductive value : term -> Prop :=
  | v_lam : forall x tau e, value (lam x tau e)
  | v_num : forall n, value (num n)
  | v_yunit : value yunit.

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
  | yunit =>
      yunit
  | ifzero e1 e2 e3 =>
      ifzero ([x:=s] e1) ([x:=s] e2) ([x:=s] e3)
  | fics T e =>
      fics T ([x:=s] e)
  | new y e =>
      new y (if string_dec x y then e else [x:=s] e)
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
    - ref_count : string is used to generate ref ids
    - read_res : option (string * nat) denotes a read response 

  A single_thread_out is a 5-tuple 
   (term, children, ref_count, write_req, read_req) where
    - term : tree is the evaluating term
    - children : list term is a list of newly spawned child threads
    - ref_count : string is used to generate ref ids
    - write_req : option (string * nat) denotes a write request
    - read_req : option string denotes a read request
*)

Definition single_thread_in := term * string * (option (string * nat)).

Definition single_thread_out := 
term * (list term) * string * (option (string * nat)) * (option string).

Inductive step : single_thread_in -> single_thread_out -> Prop :=
  | ST_fork : forall ref_count e children,
        step (fork children e, ref_count, None)
             (e, children, ref_count, None, None)
  | ST_App1 : forall ref_count ref_count' write_req read_req read_res e1 e1' e l,
        step (e1, ref_count, read_res)
             (e1', l, ref_count', write_req, read_req) ->
        step (app e1 e, ref_count, read_res)
             (app e1' e, l, ref_count', write_req, read_req)
  | ST_App2 : forall ref_count ref_count' write_req  read_req read_res e e' l v,
        value v ->
        step (e, ref_count, read_res)
             (e', l, ref_count', write_req, read_req) ->
        step (app v e, ref_count, read_res)
             (app v e', l, ref_count', write_req, read_req)
  | ST_App3a : forall ref_count e v x T,
        value v ->
        step (app (lam x T e) v, ref_count, None)
             ([x:=v]e, nil, ref_count, None, None)
  | ST_new : forall ref_count e x,
        step (new x e, ref_count, None)
             ([x:=var ref_count]e, nil, (append ref_count "x"), Some (ref_count, 0), None)
  | ST_assign1 : forall ref_count ref_count' write_req read_req read_res
                     e1 e1' e l ,
        step (e1, ref_count, read_res)
             (e1', l, ref_count', write_req, read_req) ->
        step (assign e1 e, ref_count, read_res)
             (assign e1' e, l, ref_count', write_req, read_req)
  | ST_assign2 : forall ref_count ref_count' write_req read_req read_res
                     e e' v l,
        value v ->
        step (e, ref_count, read_res)
             (e', l, ref_count', write_req, read_req) ->
        step (assign v e, ref_count, read_res)
             (assign v e', l, ref_count', write_req, read_req)
  | ST_assign3 : forall ref_count x n,
        step (assign (var x) (num n), ref_count, None)
             (yunit, nil, ref_count, Some (x, n), None)
  | ST_fix : forall ref_count T e,
        step (fics T e, ref_count, None)
             (app e (fics T e), nil, ref_count, None, None)
  | ST_ifzero1 : forall ref_count ref_count' write_req read_req read_res
                     e1 e1' e2 e3 l,
        step (e1, ref_count, read_res)
             (e1', l, ref_count', write_req, read_req) ->
        step (ifzero e1 e2 e3, ref_count, read_res)
             (ifzero e1' e2 e3, l, ref_count', write_req, read_req)
  | ST_ifzero2 : forall ref_count e e',
        step (ifzero (num 0) e e', ref_count, None)
             (e, nil, ref_count, None, None)
  | ST_ifzero3 : forall ref_count e e' n,
        n <> 0 ->
        step (ifzero (num n) e e', ref_count, None)
             (e', nil, ref_count, None, None)
  | ST_deref1 : forall ref_count ref_count' write_req read_req read_res
                     e e' l,
        step (e, ref_count, read_res)
             (e', l, ref_count', write_req, read_req) ->
        step (deref e, ref_count, read_res)
             (deref e', l, ref_count', write_req, read_req)
  | ST_deref2 : forall ref_count loc,
        step (deref (var loc), ref_count, None)
             (deref (var loc), nil, ref_count, None, Some loc)
  | ST_deref3 : forall ref_count loc val,
        step (deref (var loc), ref_count, Some (loc, val))
             (num val, nil, ref_count, None, None).

(*  A memory_model is a 5-tuple 
   (local, write_req, read_req, read_res, global) where
    - local : nat -> (string -> (option nat)) denotes the local stores
    - write_req : list (nat * (string * nat)) denotes the write-request buffer
    - read_req : list (nat * string) denotes the read-request buffer
    - read_res : list (nat * (string * nat)) denotes the read-response buffer
    - global : string -> (option nat)
*)

Definition memory_model := (nat -> (string -> (option nat))) * (list (nat * (string * nat))) * 
(list (nat * string)) * (list (nat * (string * nat))) * (string -> (option nat)).

Inductive mem_step : memory_model -> memory_model -> Prop := 
  | ST_flush : forall local local' write_req read_req read_res global global' 
               thread loc val,
               local thread loc = Some val ->
               local' = (fun m k => 
                         if negb (Nat.eqb m thread) then local m k else
                         (match (string_dec k loc) with
                               | left _ => None 
                               | right _ => local m k
                          end)) ->
               global' = (fun m => if string_dec m loc then Some val else global m) ->
               mem_step (local, write_req, read_req, read_res, global)
                        (local', write_req, read_req, read_res, global')
  | ST_respond1 : forall thread local write_req read_req read_req'
                         read_res read_res' global loc val,
               read_req = read_req' ++ ((thread, loc) :: nil) ->
               local thread loc = Some val ->
               read_res' = (thread, (loc, val)) :: read_res ->
               mem_step (local, write_req, read_req, read_res, global)
                        (local, write_req, read_req', read_res', global)
  | ST_respond2 : forall thread local write_req read_req read_req'
                         read_res read_res' global loc val,
               read_req = read_req' ++ ((thread, loc) :: nil) ->
               local thread loc = None ->
               global loc = Some val ->
               read_res' = (thread, (loc, val)) :: read_res ->
               mem_step (local, write_req, read_req, read_res, global)
                        (local, write_req, read_req', read_res', global)
  | ST_write_req : forall thread local local'
                       write_req write_req' read_req read_res global loc val,
               write_req = write_req' ++ ((thread, (loc, val)) :: nil) ->
               local' = (fun m k => 
                         if negb (Nat.eqb m thread) then local m k else
                         (match (string_dec k loc) with
                               | left _ => Some val 
                               | right _ => local m k
                          end)) ->
               mem_step (local, write_req, read_req, read_res, global)
                        (local', write_req', read_req, read_res, global).

(* A TSO_machine is a 4-tuple 
   (threads, thread_count, ref_count, mem) where
    - threads : tree is the tree of evaluating threads
    - thread_count : nat is used to generate thread ids
    - ref_count : string is used to generate ref ids
    - mem : memory_model is the memory_model *)

Definition TSO_machine := tree * nat * string * memory_model.

Inductive STEP : TSO_machine -> TSO_machine -> Prop := 
  | ST_child : forall thread_count thread_count' ref_count ref_count' mem mem'
                      e n l l' t t',
               STEP (t, thread_count, ref_count, mem)
                    (t', thread_count', ref_count', mem') ->
               STEP (Node (e, n) (l ++ (t :: nil) ++ l'), thread_count, ref_count, mem)
                    (Node (e, n) (l ++ (t' :: nil) ++ l'), thread_count', ref_count', mem')
  | ST_head1a : forall e ref_count e' l ref_count' write_request read_request write
                       thread read local local' res global l' mem mem' thread_count
                       thread_count' f write' read',
                step (e, ref_count, None) (e', l, ref_count', write_request, read_request) ->
                write' = (match write_request with
                                | None => write
                                | Some (loc, val) => (thread, (loc, val)) :: write
                          end) ->
                read' = (match read_request with
                               | None => read
                               | Some loc => (thread, loc) :: read
                         end) ->
                f = (fun e' r => (S (fst r), ((Leaf (e', fst r)) :: (snd r)))) ->
                (thread_count', l') = fold_right f (thread_count, nil) l ->
                local' = (fun k => 
                         if andb (Nat.ltb k thread_count') (Nat.leb thread_count k) then
                         local thread else local k) ->
                mem = (local, write, read, res, global) ->
                mem' = (local', write', read', res, global) ->
                STEP (Leaf (e, thread), thread_count, ref_count, mem)
                     (Node (e', thread) l', thread_count', ref_count', mem')
  | ST_head1b : forall e ref_count e' l ref_count' write_request read_request write
                       thread read local local' res global l' mem mem' thread_count
                       thread_count' f write' read' children,
                step (e, ref_count, None) (e', l, ref_count', write_request, read_request) ->
                write' = (match write_request with
                                | None => write
                                | Some (loc, val) => (thread, (loc, val)) :: write
                          end) ->
                read' = (match read_request with
                               | None => read
                               | Some loc => (thread, loc) :: read
                         end) ->
                f = (fun e' r => (S (fst r), ((Leaf (e', fst r)) :: (snd r)))) ->
                (thread_count', l') = fold_right f (thread_count, children) l ->
                local' = (fun k => 
                         if andb (Nat.ltb k thread_count') (Nat.leb thread_count k) then
                         local thread else local k) ->
                mem = (local, write, read, res, global) ->
                mem' = (local', write', read', res, global) ->
                STEP (Node (e, thread) children, thread_count, ref_count, mem)
                     (Node (e', thread) l', thread_count', ref_count', mem')
  | ST_head2a : forall e ref_count e' write loc val
                       thread read local res res' global mem mem' thread_count
                       thread_count',
                res = res' ++ ((thread, (loc, val)) :: nil) ->
                step (e, ref_count, Some (loc, val)) (e', nil, ref_count, None, None) ->
                mem = (local, write, read, res, global) ->
                mem' = (local, write, read, res', global) ->
                STEP (Leaf (e, thread), thread_count, ref_count, mem)
                     (Leaf (e', thread), thread_count', ref_count, mem')
  | ST_head2b : forall e ref_count e' l write loc val
                       thread read local res res' global mem mem' thread_count
                       thread_count',
                res = res' ++ ((thread, (loc, val)) :: nil) ->
                step (e, ref_count, Some (loc, val)) (e', nil, ref_count, None, None) ->
                mem = (local, write, read, res, global) ->
                mem' = (local, write, read, res', global) ->
                STEP (Node (e, thread) l, thread_count, ref_count, mem)
                     (Node (e', thread) l, thread_count', ref_count, mem')
  | ST_mem_step : forall threads thread_count ref_count mem mem',
                  mem_step mem mem' ->
                  STEP (threads, thread_count, ref_count, mem)
                       (threads, thread_count, ref_count, mem')
  | ST_thread_done : forall threads threads' thread_count ref_count mem local write read res global
                      e n l l' t,
              threads = Node (e, n) (l ++ (t :: nil) ++ l') ->
              threads' = Node (e, n) (l ++ l') ->
              tree_value t ->
              mem = (local, write, read, res, global) ->
              (forall m, In m (subtree_ids t) -> 
                         ((forall k, (local m) k = None) /\ 
                          (forall a b, (In (a,b) write \/ In (a,b) res) -> a <> m) /\
                          (forall a b, In (a,b) read -> a <> m))) ->
              STEP (threads, thread_count, ref_count, mem)
                   (threads', thread_count, ref_count, mem)
  | ST_reshape : forall thread_count ref_count mem e n,
                 STEP (Node (e, n) nil, thread_count, ref_count, mem)
                      (Leaf (e, n), thread_count, ref_count, mem).
