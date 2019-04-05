Set Implicit Arguments.
Set Contextual Implicit.
Set Primitive Projections.

Inductive void : Type := .

(* linear logic ------------------------------------------------------------- *)

(*
Init: 
-------------------------------
init A x y ⊢ {x ~ A} ⋅ {y ~ A^}


Cut:
C1 ⊢ G ⋅ {x ~ A}   C2 ⊢ D ⋅ {y ~ A^}
------------------------------------
cut A x y A C1 C2  ⊢ G, D

Tensor:
C1 ⊢ G ⋅ {x ~ A}   C2 ⊢ D ⋅ {x ~ B}
-------------------------------------
tensor x C1 C2  ⊢ G ⋅ D ⋅ {x ~ A ⊗ B}

One:
one x ⊢ {x ~ 1}

Par:
C ⊢ G ⋅ {x ~ A} ⋅ {y ~ B}
-----------------------------
par x y z C ⊢ G ⋅ {z ~ A # B}

Bot:
C ⊢ G
---------------------
bot x C ⊢ G ⋅ {x ~ ⊥}

With:
C1 ⊢ G ⋅ {x ~ A}     C2 ⊢ G ⋅ {x ~ B}
-------------------------------------
with x C1 C2 ⊢ G ⋅ {x ~ A & B}

Top:
top G x ⊢ G ⋅ {x ~ ⊤}

Plus:
C ⊢ G ⋅ {x ~ A}
---------------------------
plus1 x B C ⊢ G ⋅ {x ~ A ⊕ B}

C ⊢ G ⋅ {x ~ B}
---------------------------
plus2 x A C ⊢ G ⋅ {x ~ A ⊕ B}

Zero:
(no rule)

Exponentials:

Weaken:
C ⊢ G
--------------------------
weaken x A C ⊢ G, {x ~ ?A}

Contraction:
C ⊢ G ⋅ {x ~ ?A} ⋅ {y ~ ?A}
-------------------------------
contract x y z C ⊢ G ⋅ {z ~ ?A}

C ⊢ G ⋅ {x ~ A}
------------------------  forall B in G, B = ?C
bang x C ⊢ G ⋅ {x ~ !A}

C ⊢ G ⋅ {x ~ A}
----------------------
huh x C ⊢ G ⋅ {x ~ ?A}


Example equivalence

[[
C ⊢ G
---------------------   ---------------
bot x C ⊢ G ⋅ {x ~ ⊥}   one y ⊢ {y ~ 1}
--------------------------------------- (cut)
cut ⊥ x y (bot x C) (one y) ⊢ G
]]
==
[[ ⊢ G]]


(* ????? -------------------------------------------------------------------- *)
QUESTION:  In "two-sided" presenations of linear logic, there are the duality rules:

G ⋅ {x ~ A} ⊢ D
---------------------
G ⊢ {x ~ dual(A)} ⋅ D

Is this a sound one-sided rule?

⊢ G ⋅ {x ~ A}
-------------------
⊢ G ⋅ {x ~ dual(A)}
(* ?????? ------------------------------------------------------------------- *)

*)


Inductive ltype :=
| Atom (n:nat)
| AtomDual (n:nat)
| Zero
| Plus (A B:ltype)
| One
| Prod (A B:ltype)
| Top
| With (A B:ltype)
| Bot
| Par (A B:ltype)
| Bang (A:ltype)
| Ques (A:ltype).

Bind Scope ltype_scope with ltype.
Delimit Scope ltype_scope with ltype.
Local Open Scope ltype_scope.
  
Notation "0" := Zero : ltype_scope.
Notation "A ⊕ B" := (Plus A B) (at level 85, right associativity) : ltype_scope.
Notation "1" := One : ltype_scope.
Notation "A ⊗ B" := (Prod A B) (at level 80, right associativity) : ltype_scope.
Notation "⊤" := Top : ltype_scope.
Notation "A & B" := (With A B) (at level 85, right associativity) : ltype_scope.
Notation "⊥" := Bot : ltype_scope.
Notation "A # B" := (Par A B) (at level 80, right associativity) : ltype_scope.
Notation "! A" := (Bang A) (at level 90) : ltype_scope.
Notation "? A" := (Ques A) (at level 90) : ltype_scope.

Definition is_atomic (A:ltype) : bool :=
  match A with
  | Atom _
  | AtomDual _
  | One
  | Zero => true
  | _ => false (* what about [⊤] and [⊥] ? *)
  end.

Definition is_ques (A:ltype) : bool :=
  match A with
  | ? _ => true
  | _ => false
  end.

Definition is_pos (A:ltype) : bool :=
  match A with
  | Atom _
  | Zero
  | Plus _ _
  | One
  | Prod _ _
  | Bang _ => true
  | _ => false
  end.

Definition is_neg (A:ltype) : bool :=
  negb (is_pos A).

  
Fixpoint dual (A:ltype) : ltype :=
  match A with
  | Atom n => AtomDual n
  | AtomDual n => Atom n
  | 0 => ⊤
  | B ⊕ C => (dual B) & (dual C)
  | 1 => ⊥
  | B ⊗ C => (dual B) # (dual C)
  | ⊤ => 0
  | B & C => (dual B) ⊕ (dual C)
  | ⊥ => 1
  | B # C => (dual B) ⊗ (dual C)
  | !B => ?(dual B)
  | ? B => !(dual B)
  end.
Arguments dual !A.

Lemma dual_involutive : forall (A:ltype), dual (dual A) = A.
Proof.
  induction A; simpl; auto; try rewrite IHA1; try rewrite IHA2; try rewrite IHA; auto.
Qed.

(*
Notation "A -o B" := ((dual A) # B) (at level 99, right associativity) : ltype_scope.
Definition lequiv (A B:ltype) := (A -o B) & (B -o A).
*)


(* game semantics ----------------------------------------------------------- *)

(* A game defines a set of legal moves.

    - we can think of "Output" moves as "Player" or "Program" moves 
    - we can think of "Input" moves "Opponent" or "Environment moves

  HOWEVER: this is a bit misleading because of duality
    a single linear logic derivation will have some "subprocesses" that act
    like  Players and some that act like Opponents
*)

Section Game.

  Context { O : Type -> Type }
          { I : Type -> Type }.

  Inductive move (T:Type) : Type :=
  | OutputA : forall {Answer:Type} (output:O Answer) (k:Answer -> T), move T
  | InputA : forall (h: forall {Query:Type} (input:I Query), (Query * T)), move T
  .
  Arguments move _ : clear implicits.
  
  CoInductive game := go { observe : move game}.

End Game.

Arguments move _ _ _ : clear implicits.
Arguments game _ _ : clear implicits.
Notation Output x k := (go (OutputA x k)).
Notation Input  h := (go (InputA h)).


(* elementary events or "moves" --------------------------------------------- *)

(*
   emptyE 
      - Output: NO
      - Input : NO
*)
Variant emptyE : Type -> Type := .

(*
   doneE
      - Output: YES (halts)
      - Input : NO
*)
Variant doneE : Type -> Type :=
| Done : doneE void.  

(* voidPolyE
     - Output: NO
     - Input : YES (halts)
*)
Variant voidPolyE : Type -> Type :=
| VoidP : void -> forall X, voidPolyE X.



(* polyE  
    - Output: YES (continues)
    - Input : NO

   polyE's All constructor is basically Tau.
   It provides no extra information to the environment, but
   it's continuation has to be polymorphic in the input type,
*)
Variant polyE : Type -> Type :=
| All : forall X, polyE X.



(* voidUnitE
     - Output: NO
     - Input : YES (continues)
*)
Variant voidUnitE : Type -> Type :=
| VoidU : void -> voidUnitE unit.

(* unitE 
     - Output: YES (continues) 
     - Input : YES (continues)
*)
Variant unitE : Type -> Type :=
| oneE : unitE unit 
.



Lemma no_emptyE_output : forall T, not (exists (e:emptyE T), True).
Proof.
  intros T ex.
  destruct ex.
  inversion x.
Qed.  

Lemma no_emptyE_handler : forall T, not (exists (h:forall {Query:Type} (input:emptyE Query), (Query * T)), True).
Proof.
  (* Not sure if there is a constructive proof of this *)
Abort.  


Lemma doneE_output_exists : exists T (d:doneE T), True.
Proof.
  exists void. exists Done. auto.
Qed.  

Lemma no_doneE_handler : forall T, not (exists (h: forall {Query:Type} (input:doneE Query), (Query * T)), True).
Proof.
  intros T ex.
  destruct ex.
  destruct (x void Done).
  inversion v.
Qed.


Lemma polyE_output_exists : forall T, exists (e:polyE T), True.
Proof.
  intros T.
  exists All.
  auto.
Qed.
  
Lemma no_PolyE_handler: forall T, not (exists (h:forall {Query:Type} (input:polyE Query), (Query * T)), True).
Proof.
  intros T ex.
  destruct ex.
  destruct (x void All).
  inversion v.
Qed.  


Lemma no_voidPolyE_output : forall X, not (exists (x:voidPolyE X), True).
Proof.
  intros X ex.
  destruct ex.
  inversion x.
  inversion H0.
Qed.

Lemma only_voidPolyE_handler : forall T, exists (h:forall {Query:Type} (input:voidPolyE Query), (Query * T)), True.
Proof.
  intros t.
  exists (fun (Query:Type) => fun (e:voidPolyE Query) => match e with VoidP v => match v with end end).
  constructor.
Qed.  

Lemma no_voidUnitE_output : forall X, not (exists (x:voidUnitE X), True).
Proof.
  intros X ex.
  destruct ex.
  inversion x.
  inversion H0.
Qed.

Lemma voidUnitE_handler : forall T, T -> (forall X (input:voidUnitE X), (X * T)).
Proof.
  intros T t X i.
  inversion i.
  exact (tt, t).
Defined.


(* INTERPRETATION ----------------------------------------------------------- *)

(* interpretation of linear types *)

Record events := mk_events {
   output : Type -> Type ;
   input : Type -> Type ;
}.

Fixpoint ltype_events (A:ltype) : events :=
  match A with
  | 0 => mk_events voidUnitE polyE
  | ⊤ => mk_events polyE voidUnitE
  | 1 => mk_events doneE voidPolyE
  | ⊥ => mk_events voidPolyE doneE
  | _ => mk_events unitE unitE  (* TODO: Add others here *)
  end.

(* These lemmas should hold by construction *)
Lemma ltype_events_dual_in_out : forall A, (ltype_events A).(input) = (ltype_events (dual A)).(output).
Proof.
  induction A; simpl; auto.
Qed.  

Lemma ltype_events_dual_out_in : forall A, (ltype_events A).(output) = (ltype_events (dual A)).(input).
Proof.
  induction A; simpl; auto.
Qed.  

Definition gm_typ (e:events) := game (e.(output)) (e.(input)).

Notation "⟦ A ⟧" := (gm_typ (ltype_events A)).


(* ZERO : uninhabitable 

   (no rule for 0)
*)
Definition ZERO := ⟦0⟧.

Lemma ZERO_uninhabited : not (exists (g:ZERO), True).
Proof.
  intro H.
  destruct H.
  unfold ZERO in x.
  destruct x.
  simpl in *.
  inversion observe0.  inversion output0. inversion H0.
  destruct (h void All). inversion v.
Qed.

(* TOP : 

   --------
   ⊢ G ⋅ ⊤
*)         
Definition TOP := ⟦⊤⟧.

CoFixpoint top_strategy : TOP :=
  Input (voidUnitE_handler top_strategy).
CoFixpoint top_strategy2 (T:Type) : TOP :=
  Output All (fun (x:T) => top_strategy2 T).
Definition top_strategy3 (T:Type) : TOP :=
  Output All (fun (x:T) => top_strategy).
CoFixpoint top_strategy4 (T:Type) : TOP :=
  Input (voidUnitE_handler (Output All (fun (x:T) => top_strategy4 T))).



(* BOT is the type of immediately halting computations
   It is inhabited only by 

  ⊢ G
  ----------
  ⊢ G ⋅ ⊥
*)
Definition BOT := ⟦⊥⟧.

CoFixpoint bot_game : BOT :=
  Input (fun (Query:Type) => fun (e:voidPolyE Query) => match e with VoidP v => match v with end end).


(* ONE is the type of game that terminates with the [Done] event,
   (which carries no useful data).

   ⊢ 1
 *)
Definition ONE := strategy doneE polyE.

Definition one_strategy : ONE :=
  Output Done (fun (x:void) => match x with end).  





Lemma semantic_BOT : ⟦⊥⟧ = BOT.
Proof.
  reflexivity.
Qed.




Definition cut_type (A:ltype) := ⟦A⟧ -> ⟦dual A⟧ -> ⟦⊥⟧ -> Prop.



















Definition inl : {I1 O1 I2 O2} (g:game I1 O1) : SUM 







Variant sum1 (E1 E2 : Type -> Type) (X : Type) : Type :=
| inlE (_ : E1 X)
| inrE (_ : E2 X).
Notation "E1 +' E2" := (sum1 E1 E2)
(at level 50, left associativity) : type_scope.

Definition swap1 {A B : Type -> Type} {X : Type}
           (ab : sum1 A B X) : sum1 B A X :=
  match ab with
  | inlE a => inrE a
  | inrE b => inlE b
  end.

Definition bimap_sum1 {A B C D : Type -> Type} {X Y : Type}
           (f : A X -> C Y) (g : B X -> D Y)
           (ab : sum1 A B X) : sum1 C D Y :=
  match ab with
  | inlE a => inlE (f a)
  | inrE b => inrE (g b)
  end.

               
Variant pair1 (E1 E2 : Type -> Type) : Type -> Type :=
| bothE : forall {X Y:Type} (l : E1 X) (r : E2 Y), pair1 E1 E2 (X * Y)%type
.
Notation "E1 *' E2" := (pair1 E1 E2)
(at level 50, left associativity) : type_scope.




(*  ------------------------------------------------------------------------- *)
(* Below Here is old junk *)


(* Notation Tau t := (go (TauA t)). *)
(* Notation Fork t1 t2 := (go (ForkA t1 t2)). *)
(* Notation Choose t1 t2 := (go (ChooseA t1 t2)). *)


(* There's something funny about processes like the following:

   maybe [Fork] and [Choose] act like Tau steps for the purposes
   of observation
 *)
(*
CoFixpoint forky {O I} : game O I := Fork forky forky.
CoFixpoint choosey {O I} : game O I := Choose choosey choosey.
*)


(* strange: 
Variant swivel : Type -> Type :=
| swiv : forall I O (g:game I O), swivel (game O I).
*)








Section Process.

  Context { O : Type -> Type }
          { I : Type -> Type }.

  Inductive action (T:Type) :=
  | OutputA {Answer:Type} (output:O Answer) (k:option (Answer -> T))
  | InputA (h: forall {Query:Type} (input:I Query), (Query * option T))
  | ForkA (t1 t2 : T)
  | ChooseA (t1 t2 : T)
  | TauA (t:T)
  | StuckA
  | DoneA
  .
  Arguments action _ : clear implicits.
  
  CoInductive proc := go { observe : action proc }.

End Process.

Arguments action _ _ _ : clear implicits.
Arguments proc _ _ : clear implicits.

Notation Output x k := (go (OutputA x k)).
Notation Input  h := (go (InputA h)).
Notation Tau t := (go (TauA t)).
Notation Fork t1 t2 := (go (ForkA t1 t2)).
Notation Choose t1 t2 := (go (ChooseA t1 t2)).
Notation Stuck := (go StuckA).
Notation Done := (go DoneA).

(* There's something funny about processes like: *)
CoFixpoint forky {O I} : proc O I := Fork forky forky.
CoFixpoint choosey {O I} : proc O I := Choose choosey choosey.

Variant emptyE : Type -> Type := .


Variant sum1 (E1 E2 : Type -> Type) (X : Type) : Type :=
| inlE (_ : E1 X)
| inrE (_ : E2 X).
Notation "E1 +' E2" := (sum1 E1 E2)
(at level 50, left associativity) : type_scope.


Definition swap1 {A B : Type -> Type} {X : Type}
           (ab : sum1 A B X) : sum1 B A X :=
  match ab with
  | inlE a => inrE a
  | inrE b => inlE b
  end.

Definition bimap_sum1 {A B C D : Type -> Type} {X Y : Type}
           (f : A X -> C Y) (g : B X -> D Y)
           (ab : sum1 A B X) : sum1 C D Y :=
  match ab with
  | inlE a => inlE (f a)
  | inrE b => inrE (g b)
  end.

Variant unitE : Type -> Type :=
| oneE : unitE unit 
.
               
Variant pair1 (E1 E2 : Type -> Type) : Type -> Type :=
| bothE : forall {X Y:Type} (l : E1 X) (r : E2 Y), pair1 E1 E2 (X * Y)%type
.
Notation "E1 *' E2" := (pair1 E1 E2)
(at level 50, left associativity) : type_scope.



Section Hom.

  Context {O1 I1 O2 I2 : Type -> Type} .
  Context (F : (Type -> Type) -> (Type -> Type)) (homO : forall x, (O1 x) -> F O1 x).
  Context (G : (Type -> Type) -> (Type -> Type)) (homI : forall x, (I1 x) -> G I1 x).
  
  
  Definition mapO_match  (map : proc O1 I1 -> proc (F O1) I1) (p : proc O1 I1) : proc (F O1) I1 :=
    match p.(observe) with
    | OutputA o None => Output (homO o) None
    | OutputA o (Some k) => Output (homO o) (Some (fun x => map (k x)))
    | InputA h => Input (fun Q x =>
                          match h _ x with
                          | Some (a, q) => Some (a, map q)
                          | None => None
                          end)
    | ForkA t1 t2 => Fork (map t1) (map t2)
    | ChooseA t1 t2 => Choose (map t1) (map t2)
    | TauA t => Tau (map t)
    | StuckA => Stuck
    | DoneA => Done
    end.

  CoFixpoint mapO p := mapO_match mapO p. 

  Definition mapI_match  (map : proc O1 (G I1) -> proc O1 I1) (p : proc O1 (G I1)) : proc O1 I1 :=
    match p.(observe) with
    | OutputA o None => Output o None
    | OutputA o (Some k) => Output o (Some (fun x => map (k x)))
    | InputA h => Input (fun Q x =>
                          match h _ (homI x) with
                          | Some (a, q) => Some (a, map q)
                          | None => None
                          end)
    | ForkA t1 t2 => Fork (map t1) (map t2)
    | ChooseA t1 t2 => Choose (map t1) (map t2)
    | TauA t => Tau (map t)
    | StuckA => Stuck
    | DoneA => Done
    end.

  CoFixpoint mapI p := mapI_match mapI p. 

End Hom.

Definition injO1 {O1 O2 I} : proc O1 I -> proc (O1 +' O2) I := mapO (fun X => X +' O2) (@inlE O1 O2).
Definition injO2 {O1 O2 I} : proc O2 I -> proc (O1 +' O2) I := mapO (fun X => O1 +' X) (@inrE O1 O2).
Definition prjI1 {O I1 I2} : proc O (I1 +' I2) -> proc O I1 := mapI (fun X => X +' I2) (@inlE I1 I2).    
Definition prjI2 {O I1 I2} : proc O (I1 +' I2) -> proc O I2 := mapI (fun X => I1 +' X) (@inrE I1 I2).    



Section Hom2.

  Context {O1 I1 O2 I2 : Type -> Type} .
  Context (F : (Type -> Type) -> (Type -> Type)) (homO : forall x, F O1 x -> option (O1 x)).
  Context (G : (Type -> Type) -> (Type -> Type)) (homI : forall x, G I1 x -> option (I1 x)).
  
  
  Definition prjO_match  (map : proc (F O1) I1 -> proc O1 I1) (p : proc (F O1) I1) : proc O1 I1 :=
    match p.(observe) with
    | OutputA o None => match homO o with
                    | None => Stuck
                    | Some o => Output o None
                    end

    | OutputA o (Some k) => match homO o with
                           | None => Stuck
                           | Some o => Output o (Some (fun x => map (k x)))
                           end

    | InputA h => Input (fun Q x =>
                          match h _ x with
                          | Some (a, q) => Some (a, map q)
                          | None => None
                          end)
                             
    | ForkA t1 t2 => Fork (map t1) (map t2)
    | ChooseA t1 t2 => Choose (map t1) (map t2)
    | TauA t => Tau (map t)
    | StuckA => Stuck
    | DoneA => Done
    end.

  CoFixpoint prjO p := prjO_match prjO p. 


  Definition prjI_match  (map : proc O1 I1 -> proc O1 (G I1)) (p : proc O1 I1) : proc O1 (G I1) :=
    match p.(observe) with
    | OutputA o None => Output o None
    | OutputA o (Some k) => Output o (Some (fun x => map (k x)))
    | InputA h => Input (fun Q x =>
                          match (homI x) with
                          | Some y =>  match h _ y with
                                      | Some (a, q) => Some (a, map q)
                                      | None => None
                                      end
                          | None => None
                          end)
    | ForkA t1 t2 => Fork (map t1) (map t2)
    | ChooseA t1 t2 => Choose (map t1) (map t2)
    | TauA t => Tau (map t)
    | StuckA => Stuck
    | DoneA => Done
    end.

  CoFixpoint prjI p := prjI_match prjI p. 

End Hom2.

Definition prjO1 {O1 O2 I} : proc (O1 +' O2) I -> proc O1 I := prjO (fun X => X +' O2)
                                                                   (fun X e =>
                                                                      match e with
                                                                      | inlE o => Some o
                                                                      | inrE _ => None
                                                                      end).
                                                                   
Definition prjO2 {O1 O2 I} : proc (O1 +' O2) I -> proc O2 I := prjO (fun X => O1 +' X) 
                                                                   (fun X e =>
                                                                      match e with
                                                                      | inlE _ => None
                                                                      | inrE o => Some o
                                                                      end).

Definition injI1 {O I1 I2} : proc O I1 -> proc O (I1 +' I2) := prjI (fun X => X +' I2) (fun X e =>
                                                                      match e with
                                                                      | inlE o => Some o
                                                                      | inrE _ => None
                                                                      end).
Definition injI2 {O I1 I2} : proc O I2 -> proc O (I1 +' I2) := prjI  (fun X => I1 +' X) 
                                                                    (fun X e =>
                                                                       match e with
                                                                       | inlE _ => None
                                                                       | inrE o => Some o
                                                                       end).




Section ParO.

  Context {O1 O2 I : Type -> Type}.

  Definition parO (p1: proc O1 I) (p2 : proc O2 I) : proc (O1 +' O2) I :=
    Fork (injO1 p1) (injO2 p2).
  
End ParO.

Section ParI.
  Context {O I1 I2 : Type -> Type}.

  Definition parI (p1: proc O I1) (p2 : proc O I2) : proc O (I1 +' I2) :=
    Choose (injI1 p1) (injI2 p2).
  
End ParI.

























Section Linear.

  Definition Channel := Type -> Type.

  Inductive itree : (list Channel) -> Type -> Type :=
  | RetM : forall X, X -> itree [] X
  | VisM : forall R (l : list Channel) (E : Channel) n (pf: List.nth n l = Some E) X (o:E X) (k:X -> itree  R), itree l R.


  


  
  




Arguments move _ _ _ : clear implicits.
Arguments itree _ _ _ : clear implicits.

Bind Scope itree_scope with itree.
Delimit Scope itree_scope with itree.
Local Open Scope itree_scope.

Notation Ret x := (go (RetM x)).
Notation Tau t := (go (TauM t)).
Notation Output e k := (go (OutputM e k)).
Notation Input h := (go (InputM h)).
(* Notation Fork t1 t2 := (go (ForkM t1 t2)). *)
Notation Stuck := (go StuckM).

Module Bind.

  Section bind.

    Context {O I : Type -> Type} {T U : Type}.
    Variable k : T -> itree O I U.

    (* The [match] in the definition of bind. *)
    Definition bind_match
               (bind : itree O I T -> itree O I U)
               (t : itree O I T) : itree O I U :=
      match t.(observe) with
      | OutputM o k => Output o (fun x => bind (k x))
      | InputM h => Input (fun Q i => let (r, t) := h Q i in
                                  (r, bind t))
      | RetM r => k r
      | TauM t => Tau (bind t)
(*      | ForkM t1 t2 => Fork (bind t1) (bind t2) *)
      | StuckM => Stuck
      end.

  CoFixpoint bind' (t : itree O I T) : itree O I U :=
    bind_match bind' t.

End bind.

  Arguments bind_match _ _ _ /.


(* Monadic [>>=]: tree substitution, sequencing of computations. *)
Definition bind {O I T U}
           (c : itree O I T) (k : T -> itree O I U)
: itree O I U :=
  bind' k c.

(* note(gmm): There needs to be generic automation for monads to simplify
 * using the monad laws up to a setoid.
 * this would be *really* useful to a lot of projects.
 *
 * this will be especially important for this project because coinductives
 * don't simplify very nicely.
 *)

(** Functorial map ([fmap] in Haskell) *)
Definition map {O I R S} (f : R -> S)  (t : itree O I  R) : itree O I S :=
  bind t (fun x => Ret (f x)).  

Notation "t1 >>= k2" := (bind t1 k2)
  (at level 50, left associativity) : itree_scope.
Notation "x <- t1 ;; t2" := (bind t1 (fun x => t2))
  (at level 100, t1 at next level, right associativity) : itree_scope.
Notation "t1 ;; t2" := (bind t1 (fun _ => t2))
  (at level 100, right associativity) : itree_scope.
Notation "' p <- t1 ;; t2" :=
  (bind t1 (fun x_ => match x_ with p => t2 end))
  (at level 100, t1 at next level, p pattern, right associativity) : itree_scope.


(*
Section SynchronizeO.

  Context {O1 O2 I : Type -> Type} {T U : Type}.

  Definition synch_match
             (synch : itree O1 I T -> itree O2 I U -> itree (O1 *' O2) I (T * U))
             (t1 : itree O1 I T)
             (t2 : itree O2 I U)
    : itree (O1 *' O2) I (T * U)
    := 
      match t1.(observe) with
      | OutputM o1 k1 =>
        match t2.(observe) with
        | OutputM o2 k2 =>
          Output (bothE o1 o2) (fun '(x,y) => synch (k1 x) (k2 y))
        | 
        end
      | _ => Stuck
      end.
End Synchronize
*)


(*
Section SynchronizeI.

  Context {O I1 I2 : Type -> Type} {T U : Type}.

  (* This is unsatisfactory because it privileges t1 over t2 *)
  Definition synch_match
             (synch : itree O I1 T -> itree O I2 U -> itree O (I1 *' I2) (T * U) 
             (t1 : itree O I1 T)
             (t2 : itree O I2 U)
    : itree O (I1 *' I2) (T * U)
    := 
      match t1.(observe) with
      | OutputM o1 k1 => Output o1 (fun x => synch (k1 x) t2)
      | InputM h1 =>
        match t2.(observe) with
        | OutputM o2 k2 => Output o2 (fun x => synch t1 (k2 x))
        | InputM H2 =>
          InputM (fun X '(both e1 e2) => 
        

        


*)

Section Compose.

  Context {E F O1 I1 O2 I2 : Type -> Type} {T U : Type}.

  Definition compose_match
             (compose : itree (E +' O1) (F +' I1) T ->
                        itree (F +' O2) (E +' I2) U ->
                        itree (O1 +' O2) (I1 +' I2) (T * U))
             (t1 : itree (E +' O1) (F +' I1) T)
             (t2 : itree (F +' O2) (E +' I2) U)
    : itree (O1 +' O2) (I1 +' I2) (T * U)
    :=
      match t1.(observe) with
      | OutputM (inlE o1) k1 =>
        match t2.(observe) with
        | OutputM (inlE o2) k2 => Stuck
          
        | OutputM (inrE o2) k2 => Output (inrE o2) (fun x => compose t1 (k2 x))
        | InputM h2 => let '(ans1, t2') := h2 _ (inlE o1) in
                      Tau (compose (k1 ans1) t2')

        | TauM t2' => Tau (compose t1 t2')
        | _ => Stuck
        end

      | OutputM (inrE o1) k1 => Output (inlE o1) (fun x => compose (k1 x) t2)
        
      | InputM h1 =>
        match t2.(observe) with
        | OutputM (inlE o2) k2 => let '(ans2, t1') := h1 _ (inlE o2) in
                                 Tau (compose t1' (k2 ans2))

        | OutputM (inrE o2) k2 => Output (inrE o2) (fun x => compose t1 (k2 x))

        | TauM t2' => Tau (compose t1 t2')

        | _ => Stuck
        end

      | RetM v1 =>
        match t2.(observe) with
        | OutputM (inrE o2) k2 => Output (inrE o2) (fun x => compose t1 (k2 x))
        | RetM v2 => Ret (v1,v2)
        | _ => Stuck
        end
                                        
      | TauM t1' => Tau (compose t1' t2)
          

      | _ => Stuck
      end.

    CoFixpoint compose' t1 t2 :=
      compose_match compose' t1 t2.

End Compose.








Definition cmp_match {E F O I}
           (cm : proc (E +' O) (F +' I) -> proc (F +' O) (E +' I) -> proc O I)
           (p1 : proc (E +' O) (F +' I))
           (p2 : proc (F +' O) (E +' I)) :
  proc O I :=

  match p1.(observe) with
  | OutputA (inlE o) None =>

    match p2.(observe) with
    | OutputA (inlE o) None => Done
    | OutputA (inlE o) (Some k) => Stuck (* the process is deadlocked on F *)
    | OutputA (inrE o) None => Output o None  (* p1's message is just dropped *)
    | OutputA (inrE o) (Some k) => Output o (Some (fun x => cm p1 (k x)))

    | InputA h => match h _ (inlE o) with
                 | None => Done  (* the asynch message was received *)
                 | Some (a, p2') => Tau (cm Done p2')
                 end
    | TauA p2' => Tau (cm p1 p2')

    | ForkA p21 p22 => Choose (cm (lift (cm p1 p21))  p22)  (* message goes left *)
                             (cm (p)   (* message goes right *)
                     
                   
    | _ => Stuck
    end
    
    
  | _ => Stuck
  end
  .


CoFixpoint compose {E F O I} (p1 : proc (E +' O) (F +' I)) (p2 : proc (F +' O) (E +' I)) :
  proc O I := cmp_match compose p1 p2.
  
  


Definition new_match {E O I}
           (nm : proc (E +' O) (E +' I) -> proc O I) 
           (p : proc (E +' O) (E +' I)) : proc O I :=
  match p.(observe) with
  | OutputA (inlE o) None => Done
  | OutputA (inlE o) (Some k) => Stuck (* the process is deadlocked because it outputs an E but can't get a response *)
  | OutputA (inrE o) None => Output o None
  | OutputA (inrE o) (Some k) => Output o (Some (fun x => nm (k x)))
  | InputA h => Input (fun A x =>
                        match h _ (inrE x) with
                        | None => None
                        | Some (a, t) => Some (a, nm t)
                        end)
  | TauA t => Tau (nm t)

  | ForkA t1 t2 => compose t1 t2

  | ChooseA t1 t2 => Choose (nm t1) (nm t2)
                          
  | DoneA => Done
  | StuckA => Stuck
  end.


  

Section Compose2.

  Context {O1 O2 I1 I2 O I : Type -> Type}.

  Definition comp_match (cmp : proc (O +' O1) (I +' I1) -> proc (I +' O2) (O +' I2) -> proc (O1 +' O2) (I1 +' I2))
             (p1 : proc (O +' O1) (I +' I1))
             (p2 : proc (I +' O2) (O +' I2)) :
    proc (O1 +' O2) (I1 +' I2) :=

    match p1.(observe) with
    | OutputA (inlE o1) k1 =>

      match p2.(observe) with

      (* p1 wants to interact with p2 and vice versa *)
      | OutputA (inlE o2) k2 => Stuck  (* Deadlock *)

      (* p1 is waiting for p2, but p2 needs intput from the environment, so p2 must go first *)
      | OutputA (inrE o2) (Some k2) => Output (inrE o2) (Some (fun x => cmp p1 (k2 x)))

      (* p1 is waiting for p2, but p2 is doing an asynchronous output.
       *)
      | OutputA (inrE o2) None =>
        match k1 with
        | None => (Output (inrE o2) None)   (* p1's asynch output just gets dropped, but that's OK? *)
        | Some k => Fork Stuck (Output (inrE o2) None)
        end

      | InputA h2 => match h2 _ (inlE o1) with
                    | None => match k1 with
                             | None => Done  (* p1's output was asynchronous, so it's ok to drop it *)
                             | Some k =>
                               Input (fun _ x => match x with
                                               | inlE _ => None (* stuck because p1 would have to handle this input *)
                                               | inrE o => match h2 _ (inrE o) with
                                                          | None => None
                                                          | Some (a, p2') => Some (a, cmp p1 p2')
                                                          end
                                              end)
                             end
                    | Some (a, p2') => match k1 with
                                      | None => cmp Done p2'   (* p1 is Done, p2 continues as p2' *)
                                      | Some k => cmp (k a) p2'
                                      end
                    end

      | ForkA p21 p22 => (* p1's output could be handled by any combination of p21 or p22 as a race in both *)

        Stuck (* cmp (cmp p1 p21) p22 *)
        
                      
      | _ => Stuck
      end

    | ForkA p11 p12 => 

      match p2.(observe) with

      | ForkA p21 p22 => Stuck

        
        

      | _ => Stuck
      end
      

        
    | _ => Stuck
    end.
    



  
