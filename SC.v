Require Import List.
Require Import Lambda.
Require Import Util.

Definition mapping := nat -> (option (nat * nat)). (* base, size*)
Definition global_store := nat -> (option nat).
Definition memory_model := mapping * global_store.

Definition allocate (start : nat) (finish : nat) (init : list nat) (g : global_store) : global_store :=
(fun n => if andb (Nat.leb start n) (Nat.leb n finish) then Some (nth (n - start) init (0%nat)) else g 0).

Definition update_global (val : nat * nat) (g : global_store) : global_store :=
(fun n => if Nat.eqb n (fst val) then Some (snd val) else g n).

Definition update_mapping (location : nat) (base : nat) (size : nat) (g : mapping) : mapping :=
(fun n => if Nat.eqb n location then Some (base, size) else g n).

Inductive memory_step : memory_model -> mem_event -> memory_model -> Prop :=
  | ST_tau_step : forall mem, memory_step mem Tau mem
  | ST_read :  forall global value location offset mapping base size,
               mapping location = Some (base, size) ->
               offset < size ->
               global (base + offset) = Some value ->
               memory_step (mapping, global) (Read location offset value) (mapping, global)
  | ST_write : forall global global' offset value location mapping base size,
               mapping location = Some (base, size) ->
               offset < size ->
               global' = update_global (base + offset, value) global ->
               memory_step (mapping, global) (Write location offset value) (mapping, global')
  | ST_allocate_array : forall global global' init location size mapping base mapping',
               (forall n, base <= n < base + size -> global n = None) ->
               mapping location = None ->
               mapping' = update_mapping location base size mapping ->
               global' = allocate base (base + size - 1) init global ->
               memory_step (mapping, global) (Allocate location size init) (mapping', global')
  | ST_reference : forall global location base size mapping,
               mapping location = Some (base, size) ->
               memory_step (mapping, global) (Reference location base) (mapping, global)
  | ST_cast : forall global location mapping base size,
               mapping location = Some (base, size) ->
               memory_step (mapping, global) (Cast base location) (mapping, global).

(* A program is a 4-tuple (init, s1, s2, s3)
  2. init : (list (nat * (list nat))) denoting array variables with respective inital values,
  2. s1 : term denotes the program running on the first thread,
  3. s2 : term denotes the program running on the second thread.
  4. s3 : term denotes the program running on the third thread.
*)
Definition program := (list (nat * (list nat))) * term * term * term.

Definition SC_machine := program * memory_model.

Inductive pstep : SC_machine -> SC_machine -> Prop :=
  | ST_init_allocate_array : forall xs s1 s2 s3 mem mem' size init,
                      size > 0 ->
                      length init <= size ->
                      memory_step mem (Allocate (length xs) size init) mem' ->
                      pstep ((xs ++ ((size, init) :: nil), s1, s2, s3), mem)
                            ((xs, s1, s2, s3), mem')
  | ST_synchronize1 : forall s1 event s1' mem mem' s2 s3,
                      step s1 event s1' ->
                      memory_step mem event mem' ->
                      pstep ((nil, s1, s2, s3), mem)
                            ((nil, s1', s2, s3), mem')
  | ST_synchronize2 : forall s1 event s2' mem mem' s2 s3,
                      step s2 event s2' ->
                      memory_step mem event mem' ->
                      pstep ((nil, s1, s2, s3), mem)
                            ((nil, s1, s2', s3), mem')
  | ST_synchronize3 : forall s1 event s3' mem mem' s2 s3,
                      step s3 event s3' ->
                      memory_step mem event mem' ->
                      pstep ((nil, s1, s2, s3), mem)
                            ((nil, s1, s2, s3'), mem').

Inductive SC_program_steps : SC_machine -> SC_machine -> Prop :=
  | SC_program_steps_reflexive : forall p, SC_program_steps p p
  | SC_program_steps_transitive : forall p q r, pstep p q -> SC_program_steps q r -> SC_program_steps p r.

Fact steps_app_left : forall l l' e1 e1' e3 e3' e4 e4' m m' e2 t t',
t = (l, e1, e3, e4, m) ->
t' = (l', e1', e3', e4', m') ->
SC_program_steps t t' ->
SC_program_steps
(fst (fst (fst (fst t))), app (snd (fst (fst (fst t)))) e2, snd (fst (fst t)), snd (fst t), snd t) (fst (fst (fst (fst t'))), app (snd (fst (fst (fst t')))) e2, snd (fst (fst t')), snd (fst t'), snd t').
Proof. intros. generalize dependent l. generalize dependent e1. generalize dependent e3. generalize dependent e4. generalize dependent m.  generalize dependent l'. generalize dependent e1'. generalize dependent e3'. generalize dependent e4'. generalize dependent m'. generalize dependent e2. induction H1; intros.
  + apply SC_program_steps_reflexive.
  + subst. destruct q. destruct p. destruct p. destruct p. simpl in *. apply SC_program_steps_transitive with (q:=(l0, app t1 e2, t0, t, m0)).
    ++ inversion H; subst.
       +++ apply ST_init_allocate_array. auto. auto. auto.
       +++ apply ST_synchronize1 with (event:=event). apply step_context with (E:=Capp1 Hole e2). auto. auto.
       +++ apply ST_synchronize2 with (event:=event). auto. auto.
       +++ apply ST_synchronize3 with (event:=event). auto. auto.
    ++ apply IHSC_program_steps with (m'0:=m') (e4'0:=e4') (e3'0:=e3') (e1'0:=e1') (l'0:=l') (m:=m0) (e4:=t) (e3:=t0) (e1:=t1) (l:=l0). auto. auto. Qed.
    
Fact steps_app_right : forall l l' e1 e1' e3 e3' e4 e4' m m' e2 t t' x,
t = (l, e1, e3, e4, m) ->
t' = (l', e1', e3', e4', m') ->
SC_program_steps t t' ->
SC_program_steps
(fst (fst (fst (fst t))), app (lam x e2) (snd (fst (fst (fst t)))), snd (fst (fst t)), snd (fst t), snd t) (fst (fst (fst (fst t'))), app (lam x e2) (snd (fst (fst (fst t')))), snd (fst (fst t')), snd (fst t'), snd t').
Proof. intros. generalize dependent l. generalize dependent e1. generalize dependent e3. generalize dependent e4. generalize dependent m.  generalize dependent l'. generalize dependent e1'. generalize dependent e3'. generalize dependent e4'. generalize dependent m'. generalize dependent e2. generalize dependent x. induction H1; intros.
  + apply SC_program_steps_reflexive.
  + subst. destruct q. destruct p. destruct p. destruct p. simpl in *. apply SC_program_steps_transitive with (q:=(l0, app (lam x e2) t1, t0, t, m0)).
    ++ inversion H; subst.
       +++ apply ST_init_allocate_array. auto. auto. auto.
       +++ apply ST_synchronize1 with (event:=event). assert (exists y e', lam x e2 = lam y e'). refine (ex_intro _ x _). refine (ex_intro _ e2 _). auto. apply step_context with (E:=Capp2 (exist _ (lam x e2) H0) Hole). auto. auto.
       +++ apply ST_synchronize2 with (event:=event). auto. auto.
       +++ apply ST_synchronize3 with (event:=event). auto. auto.
    ++ apply IHSC_program_steps with (m'0:=m') (e4'0:=e4') (e3'0:=e3') (e1'0:=e1') (l'0:=l') (m:=m0) (e4:=t) (e3:=t0) (e1:=t1) (l:=l0). auto. auto. Qed.

Fact steps_plus_left : forall l l' e1 e1' e3 e3' e4 e4' m m' e2 t t',
t = (l, e1, e3, e4, m) ->
t' = (l', e1', e3', e4', m') ->
SC_program_steps t t' ->
SC_program_steps
(fst (fst (fst (fst t))), plus (snd (fst (fst (fst t)))) e2, snd (fst (fst t)), snd (fst t), snd t) (fst (fst (fst (fst t'))), plus (snd (fst (fst (fst t')))) e2, snd (fst (fst t')), snd (fst t'), snd t').
Proof. intros. generalize dependent l. generalize dependent e1. generalize dependent e3. generalize dependent e4. generalize dependent m.  generalize dependent l'. generalize dependent e1'. generalize dependent e3'. generalize dependent e4'. generalize dependent m'. generalize dependent e2. induction H1; intros.
  + apply SC_program_steps_reflexive.
  + subst. destruct q. destruct p. destruct p. destruct p. simpl in *. apply SC_program_steps_transitive with (q:=(l0, plus t1 e2, t0, t, m0)).
    ++ inversion H; subst.
       +++ apply ST_init_allocate_array. auto. auto. auto.
       +++ apply ST_synchronize1 with (event:=event). apply step_context with (E:=Cplus1 Hole e2). auto. auto.
       +++ apply ST_synchronize2 with (event:=event). auto. auto.
       +++ apply ST_synchronize3 with (event:=event). auto. auto.
    ++ apply IHSC_program_steps with (m'0:=m') (e4'0:=e4') (e3'0:=e3') (e1'0:=e1') (l'0:=l') (m:=m0) (e4:=t) (e3:=t0) (e1:=t1) (l:=l0). auto. auto. Qed.
    
Fact steps_plus_right : forall l l' e1 e1' e3 e3' e4 e4' m m' e2 t t',
t = (l, e1, e3, e4, m) ->
t' = (l', e1', e3', e4', m') ->
SC_program_steps t t' ->
SC_program_steps
(fst (fst (fst (fst t))), plus (num e2) (snd (fst (fst (fst t)))), snd (fst (fst t)), snd (fst t), snd t) (fst (fst (fst (fst t'))), plus (num e2) (snd (fst (fst (fst t')))), snd (fst (fst t')), snd (fst t'), snd t').
Proof. intros. generalize dependent l. generalize dependent e1. generalize dependent e3. generalize dependent e4. generalize dependent m.  generalize dependent l'. generalize dependent e1'. generalize dependent e3'. generalize dependent e4'. generalize dependent m'. generalize dependent e2. induction H1; intros.
  + apply SC_program_steps_reflexive.
  + subst. destruct q. destruct p. destruct p. destruct p. simpl in *. apply SC_program_steps_transitive with (q:=(l0, plus (num e2) t1, t0, t, m0)).
    ++ inversion H; subst.
       +++ apply ST_init_allocate_array. auto. auto. auto.
       +++ apply ST_synchronize1 with (event:=event). assert (exists n, num e2 = num n). refine (ex_intro _ e2 _). auto. apply step_context with (E:=Cplus2 (exist _ (num e2) H0) Hole). auto. auto.
       +++ apply ST_synchronize2 with (event:=event). auto. auto.
       +++ apply ST_synchronize3 with (event:=event). auto. auto.
    ++ apply IHSC_program_steps with (m'0:=m') (e4'0:=e4') (e3'0:=e3') (e1'0:=e1') (l'0:=l') (m:=m0) (e4:=t) (e3:=t0) (e1:=t1) (l:=l0). auto. auto. Qed.

Fact steps_minus_left : forall l l' e1 e1' e3 e3' e4 e4' m m' e2 t t',
t = (l, e1, e3, e4, m) ->
t' = (l', e1', e3', e4', m') ->
SC_program_steps t t' ->
SC_program_steps
(fst (fst (fst (fst t))), minus (snd (fst (fst (fst t)))) e2, snd (fst (fst t)), snd (fst t), snd t) (fst (fst (fst (fst t'))), minus (snd (fst (fst (fst t')))) e2, snd (fst (fst t')), snd (fst t'), snd t').
Proof. intros. generalize dependent l. generalize dependent e1. generalize dependent e3. generalize dependent e4. generalize dependent m.  generalize dependent l'. generalize dependent e1'. generalize dependent e3'. generalize dependent e4'. generalize dependent m'. generalize dependent e2. induction H1; intros.
  + apply SC_program_steps_reflexive.
  + subst. destruct q. destruct p. destruct p. destruct p. simpl in *. apply SC_program_steps_transitive with (q:=(l0, minus t1 e2, t0, t, m0)).
    ++ inversion H; subst.
       +++ apply ST_init_allocate_array. auto. auto. auto.
       +++ apply ST_synchronize1 with (event:=event). apply step_context with (E:=Cminus1 Hole e2). auto. auto.
       +++ apply ST_synchronize2 with (event:=event). auto. auto.
       +++ apply ST_synchronize3 with (event:=event). auto. auto.
    ++ apply IHSC_program_steps with (m'0:=m') (e4'0:=e4') (e3'0:=e3') (e1'0:=e1') (l'0:=l') (m:=m0) (e4:=t) (e3:=t0) (e1:=t1) (l:=l0). auto. auto. Qed.
    
Fact steps_minus_right : forall l l' e1 e1' e3 e3' e4 e4' m m' e2 t t',
t = (l, e1, e3, e4, m) ->
t' = (l', e1', e3', e4', m') ->
SC_program_steps t t' ->
SC_program_steps
(fst (fst (fst (fst t))), minus (num e2) (snd (fst (fst (fst t)))), snd (fst (fst t)), snd (fst t), snd t) (fst (fst (fst (fst t'))), minus (num e2) (snd (fst (fst (fst t')))), snd (fst (fst t')), snd (fst t'), snd t').
Proof. intros. generalize dependent l. generalize dependent e1. generalize dependent e3. generalize dependent e4. generalize dependent m.  generalize dependent l'. generalize dependent e1'. generalize dependent e3'. generalize dependent e4'. generalize dependent m'. generalize dependent e2. induction H1; intros.
  + apply SC_program_steps_reflexive.
  + subst. destruct q. destruct p. destruct p. destruct p. simpl in *. apply SC_program_steps_transitive with (q:=(l0, minus (num e2) t1, t0, t, m0)).
    ++ inversion H; subst.
       +++ apply ST_init_allocate_array. auto. auto. auto.
       +++ apply ST_synchronize1 with (event:=event). assert (exists n, num e2 = num n). refine (ex_intro _ e2 _). auto. apply step_context with (E:=Cminus2 (exist _ (num e2) H0) Hole). auto. auto.
       +++ apply ST_synchronize2 with (event:=event). auto. auto.
       +++ apply ST_synchronize3 with (event:=event). auto. auto.
    ++ apply IHSC_program_steps with (m'0:=m') (e4'0:=e4') (e3'0:=e3') (e1'0:=e1') (l'0:=l') (m:=m0) (e4:=t) (e3:=t0) (e1:=t1) (l:=l0). auto. auto. Qed.

Fact steps_modulo_left : forall l l' e1 e1' e3 e3' e4 e4' m m' e2 t t',
t = (l, e1, e3, e4, m) ->
t' = (l', e1', e3', e4', m') ->
SC_program_steps t t' ->
SC_program_steps
(fst (fst (fst (fst t))), modulo (snd (fst (fst (fst t)))) e2, snd (fst (fst t)), snd (fst t), snd t) (fst (fst (fst (fst t'))), modulo (snd (fst (fst (fst t')))) e2, snd (fst (fst t')), snd (fst t'), snd t').
Proof. intros. generalize dependent l. generalize dependent e1. generalize dependent e3. generalize dependent e4. generalize dependent m.  generalize dependent l'. generalize dependent e1'. generalize dependent e3'. generalize dependent e4'. generalize dependent m'. generalize dependent e2. induction H1; intros.
  + apply SC_program_steps_reflexive.
  + subst. destruct q. destruct p. destruct p. destruct p. simpl in *. apply SC_program_steps_transitive with (q:=(l0, modulo t1 e2, t0, t, m0)).
    ++ inversion H; subst.
       +++ apply ST_init_allocate_array. auto. auto. auto.
       +++ apply ST_synchronize1 with (event:=event). apply step_context with (E:=Cmodulo1 Hole e2). auto. auto.
       +++ apply ST_synchronize2 with (event:=event). auto. auto.
       +++ apply ST_synchronize3 with (event:=event). auto. auto.
    ++ apply IHSC_program_steps with (m'0:=m') (e4'0:=e4') (e3'0:=e3') (e1'0:=e1') (l'0:=l') (m:=m0) (e4:=t) (e3:=t0) (e1:=t1) (l:=l0). auto. auto. Qed.
    
Fact steps_modulo_right : forall l l' e1 e1' e3 e3' e4 e4' m m' e2 t t',
t = (l, e1, e3, e4, m) ->
t' = (l', e1', e3', e4', m') ->
SC_program_steps t t' ->
SC_program_steps
(fst (fst (fst (fst t))), modulo (num e2) (snd (fst (fst (fst t)))), snd (fst (fst t)), snd (fst t), snd t) (fst (fst (fst (fst t'))), modulo (num e2) (snd (fst (fst (fst t')))), snd (fst (fst t')), snd (fst t'), snd t').
Proof. intros. generalize dependent l. generalize dependent e1. generalize dependent e3. generalize dependent e4. generalize dependent m.  generalize dependent l'. generalize dependent e1'. generalize dependent e3'. generalize dependent e4'. generalize dependent m'. generalize dependent e2. induction H1; intros.
  + apply SC_program_steps_reflexive.
  + subst. destruct q. destruct p. destruct p. destruct p. simpl in *. apply SC_program_steps_transitive with (q:=(l0, modulo (num e2) t1, t0, t, m0)).
    ++ inversion H; subst.
       +++ apply ST_init_allocate_array. auto. auto. auto.
       +++ apply ST_synchronize1 with (event:=event). assert (exists n, num e2 = num n). refine (ex_intro _ e2 _). auto. apply step_context with (E:=Cmodulo2 (exist _ (num e2) H0) Hole). auto. auto.
       +++ apply ST_synchronize2 with (event:=event). auto. auto.
       +++ apply ST_synchronize3 with (event:=event). auto. auto.
    ++ apply IHSC_program_steps with (m'0:=m') (e4'0:=e4') (e3'0:=e3') (e1'0:=e1') (l'0:=l') (m:=m0) (e4:=t) (e3:=t0) (e1:=t1) (l:=l0). auto. auto. Qed.

Fact steps_less_than_left : forall l l' e1 e1' e3 e3' e4 e4' m m' e2 t t',
t = (l, e1, e3, e4, m) ->
t' = (l', e1', e3', e4', m') ->
SC_program_steps t t' ->
SC_program_steps
(fst (fst (fst (fst t))), less_than (snd (fst (fst (fst t)))) e2, snd (fst (fst t)), snd (fst t), snd t) (fst (fst (fst (fst t'))), less_than (snd (fst (fst (fst t')))) e2, snd (fst (fst t')), snd (fst t'), snd t').
Proof. intros. generalize dependent l. generalize dependent e1. generalize dependent e3. generalize dependent e4. generalize dependent m.  generalize dependent l'. generalize dependent e1'. generalize dependent e3'. generalize dependent e4'. generalize dependent m'. generalize dependent e2. induction H1; intros.
  + apply SC_program_steps_reflexive.
  + subst. destruct q. destruct p. destruct p. destruct p. simpl in *. apply SC_program_steps_transitive with (q:=(l0, less_than t1 e2, t0, t, m0)).
    ++ inversion H; subst.
       +++ apply ST_init_allocate_array. auto. auto. auto.
       +++ apply ST_synchronize1 with (event:=event). apply step_context with (E:=Cless_than1 Hole e2). auto. auto.
       +++ apply ST_synchronize2 with (event:=event). auto. auto.
       +++ apply ST_synchronize3 with (event:=event). auto. auto.
    ++ apply IHSC_program_steps with (m'0:=m') (e4'0:=e4') (e3'0:=e3') (e1'0:=e1') (l'0:=l') (m:=m0) (e4:=t) (e3:=t0) (e1:=t1) (l:=l0). auto. auto. Qed.
    
Fact steps_less_than_right : forall l l' e1 e1' e3 e3' e4 e4' m m' e2 t t',
t = (l, e1, e3, e4, m) ->
t' = (l', e1', e3', e4', m') ->
SC_program_steps t t' ->
SC_program_steps
(fst (fst (fst (fst t))), less_than (num e2) (snd (fst (fst (fst t)))), snd (fst (fst t)), snd (fst t), snd t) (fst (fst (fst (fst t'))), less_than (num e2) (snd (fst (fst (fst t')))), snd (fst (fst t')), snd (fst t'), snd t').
Proof. intros. generalize dependent l. generalize dependent e1. generalize dependent e3. generalize dependent e4. generalize dependent m.  generalize dependent l'. generalize dependent e1'. generalize dependent e3'. generalize dependent e4'. generalize dependent m'. generalize dependent e2. induction H1; intros.
  + apply SC_program_steps_reflexive.
  + subst. destruct q. destruct p. destruct p. destruct p. simpl in *. apply SC_program_steps_transitive with (q:=(l0, less_than (num e2) t1, t0, t, m0)).
    ++ inversion H; subst.
       +++ apply ST_init_allocate_array. auto. auto. auto.
       +++ apply ST_synchronize1 with (event:=event). assert (exists n, num e2 = num n). refine (ex_intro _ e2 _). auto. apply step_context with (E:=Cless_than2 (exist _ (num e2) H0) Hole). auto. auto.
       +++ apply ST_synchronize2 with (event:=event). auto. auto.
       +++ apply ST_synchronize3 with (event:=event). auto. auto.
    ++ apply IHSC_program_steps with (m'0:=m') (e4'0:=e4') (e3'0:=e3') (e1'0:=e1') (l'0:=l') (m:=m0) (e4:=t) (e3:=t0) (e1:=t1) (l:=l0). auto. auto. Qed.

Fact steps_and_left : forall l l' e1 e1' e3 e3' e4 e4' m m' e2 t t',
t = (l, e1, e3, e4, m) ->
t' = (l', e1', e3', e4', m') ->
SC_program_steps t t' ->
SC_program_steps
(fst (fst (fst (fst t))), and (snd (fst (fst (fst t)))) e2, snd (fst (fst t)), snd (fst t), snd t) (fst (fst (fst (fst t'))), and (snd (fst (fst (fst t')))) e2, snd (fst (fst t')), snd (fst t'), snd t').
Proof. intros. generalize dependent l. generalize dependent e1. generalize dependent e3. generalize dependent e4. generalize dependent m.  generalize dependent l'. generalize dependent e1'. generalize dependent e3'. generalize dependent e4'. generalize dependent m'. generalize dependent e2. induction H1; intros.
  + apply SC_program_steps_reflexive.
  + subst. destruct q. destruct p. destruct p. destruct p. simpl in *. apply SC_program_steps_transitive with (q:=(l0, and t1 e2, t0, t, m0)).
    ++ inversion H; subst.
       +++ apply ST_init_allocate_array. auto. auto. auto.
       +++ apply ST_synchronize1 with (event:=event). apply step_context with (E:=Cand1 Hole e2). auto. auto.
       +++ apply ST_synchronize2 with (event:=event). auto. auto.
       +++ apply ST_synchronize3 with (event:=event). auto. auto.
    ++ apply IHSC_program_steps with (m'0:=m') (e4'0:=e4') (e3'0:=e3') (e1'0:=e1') (l'0:=l') (m:=m0) (e4:=t) (e3:=t0) (e1:=t1) (l:=l0). auto. auto. Qed.
    
Fact steps_and_right : forall l l' e1 e1' e3 e3' e4 e4' m m' t t',
t = (l, e1, e3, e4, m) ->
t' = (l', e1', e3', e4', m') ->
SC_program_steps t t' ->
SC_program_steps
(fst (fst (fst (fst t))), and tru (snd (fst (fst (fst t)))), snd (fst (fst t)), snd (fst t), snd t) (fst (fst (fst (fst t'))), and tru (snd (fst (fst (fst t')))), snd (fst (fst t')), snd (fst t'), snd t').
Proof. intros. generalize dependent l. generalize dependent e1. generalize dependent e3. generalize dependent e4. generalize dependent m.  generalize dependent l'. generalize dependent e1'. generalize dependent e3'. generalize dependent e4'. generalize dependent m'. induction H1; intros.
  + apply SC_program_steps_reflexive.
  + subst. destruct q. destruct p. destruct p. destruct p. simpl in *. apply SC_program_steps_transitive with (q:=(l0, and tru t1, t0, t, m0)).
    ++ inversion H; subst.
       +++ apply ST_init_allocate_array. auto. auto. auto.
       +++ apply ST_synchronize1 with (event:=event). apply step_context with (E:=Cand2 (exist _ tru eq_refl) Hole). auto. auto.
       +++ apply ST_synchronize2 with (event:=event). auto. auto.
       +++ apply ST_synchronize3 with (event:=event). auto. auto.
    ++ apply IHSC_program_steps with (m'0:=m') (e4'0:=e4') (e3'0:=e3') (e1'0:=e1') (l'0:=l') (m:=m0) (e4:=t) (e3:=t0) (e1:=t1) (l:=l0). auto. auto. Qed.

Fact steps_read_left : forall l l' e1 e1' e3 e3' e4 e4' m m' e2 t t',
t = (l, e1, e3, e4, m) ->
t' = (l', e1', e3', e4', m') ->
SC_program_steps t t' ->
SC_program_steps
(fst (fst (fst (fst t))), read (snd (fst (fst (fst t)))) e2, snd (fst (fst t)), snd (fst t), snd t) (fst (fst (fst (fst t'))), read (snd (fst (fst (fst t')))) e2, snd (fst (fst t')), snd (fst t'), snd t').
Proof. intros. generalize dependent l. generalize dependent e1. generalize dependent e3. generalize dependent e4. generalize dependent m.  generalize dependent l'. generalize dependent e1'. generalize dependent e3'. generalize dependent e4'. generalize dependent m'. generalize dependent e2. induction H1; intros.
  + apply SC_program_steps_reflexive.
  + subst. destruct q. destruct p. destruct p. destruct p. simpl in *. apply SC_program_steps_transitive with (q:=(l0, read t1 e2, t0, t, m0)).
    ++ inversion H; subst.
       +++ apply ST_init_allocate_array. auto. auto. auto.
       +++ apply ST_synchronize1 with (event:=event). apply step_context with (E:=Cread1 Hole e2). auto. auto.
       +++ apply ST_synchronize2 with (event:=event). auto. auto.
       +++ apply ST_synchronize3 with (event:=event). auto. auto.
    ++ apply IHSC_program_steps with (m'0:=m') (e4'0:=e4') (e3'0:=e3') (e1'0:=e1') (l'0:=l') (m:=m0) (e4:=t) (e3:=t0) (e1:=t1) (l:=l0). auto. auto. Qed.
    
Fact steps_read_right : forall l l' e1 e1' e3 e3' e4 e4' m m' e2 t t',
t = (l, e1, e3, e4, m) ->
t' = (l', e1', e3', e4', m') ->
SC_program_steps t t' ->
SC_program_steps
(fst (fst (fst (fst t))), read (array e2) (snd (fst (fst (fst t)))), snd (fst (fst t)), snd (fst t), snd t) (fst (fst (fst (fst t'))), read (array e2) (snd (fst (fst (fst t')))), snd (fst (fst t')), snd (fst t'), snd t').
Proof. intros. generalize dependent l. generalize dependent e1. generalize dependent e3. generalize dependent e4. generalize dependent m.  generalize dependent l'. generalize dependent e1'. generalize dependent e3'. generalize dependent e4'. generalize dependent m'. generalize dependent e2. induction H1; intros.
  + apply SC_program_steps_reflexive.
  + subst. destruct q. destruct p. destruct p. destruct p. simpl in *. apply SC_program_steps_transitive with (q:=(l0, read (array e2) t1, t0, t, m0)).
    ++ inversion H; subst.
       +++ apply ST_init_allocate_array. auto. auto. auto.
       +++ apply ST_synchronize1 with (event:=event). assert (exists n, array e2 = array n). refine (ex_intro _ e2 _). auto. apply step_context with (E:=Cread2 (exist _ (array e2) H0) Hole). auto. auto.
       +++ apply ST_synchronize2 with (event:=event). auto. auto.
       +++ apply ST_synchronize3 with (event:=event). auto. auto.
    ++ apply IHSC_program_steps with (m'0:=m') (e4'0:=e4') (e3'0:=e3') (e1'0:=e1') (l'0:=l') (m:=m0) (e4:=t) (e3:=t0) (e1:=t1) (l:=l0). auto. auto. Qed.

Fact steps_write_left : forall l l' e1 e1' e3 e3' e4 e4' m m' e2 e5 t t',
t = (l, e1, e3, e4, m) ->
t' = (l', e1', e3', e4', m') ->
SC_program_steps t t' ->
SC_program_steps
(fst (fst (fst (fst t))), write (snd (fst (fst (fst t)))) e2 e5, snd (fst (fst t)), snd (fst t), snd t) (fst (fst (fst (fst t'))), write (snd (fst (fst (fst t')))) e2 e5, snd (fst (fst t')), snd (fst t'), snd t').
Proof. intros. generalize dependent l. generalize dependent e1. generalize dependent e3. generalize dependent e4. generalize dependent m.  generalize dependent l'. generalize dependent e1'. generalize dependent e3'. generalize dependent e4'. generalize dependent m'. generalize dependent e2. generalize dependent e5. induction H1; intros.
  + apply SC_program_steps_reflexive.
  + subst. destruct q. destruct p. destruct p. destruct p. simpl in *. apply SC_program_steps_transitive with (q:=(l0, write t1 e2 e5, t0, t, m0)).
    ++ inversion H; subst.
       +++ apply ST_init_allocate_array. auto. auto. auto.
       +++ apply ST_synchronize1 with (event:=event). apply step_context with (E:=Cwrite1 Hole e2 e5). auto. auto.
       +++ apply ST_synchronize2 with (event:=event). auto. auto.
       +++ apply ST_synchronize3 with (event:=event). auto. auto.
    ++ apply IHSC_program_steps with (m'0:=m') (e4'0:=e4') (e3'0:=e3') (e1'0:=e1') (l'0:=l') (m:=m0) (e4:=t) (e3:=t0) (e1:=t1) (l:=l0). auto. auto. Qed.
    
Fact steps_write_right : forall l l' e1 e1' e3 e3' e4 e4' m m' e2 e5 t t',
t = (l, e1, e3, e4, m) ->
t' = (l', e1', e3', e4', m') ->
SC_program_steps t t' ->
SC_program_steps
(fst (fst (fst (fst t))), write (array e2) (snd (fst (fst (fst t)))) e5, snd (fst (fst t)), snd (fst t), snd t) (fst (fst (fst (fst t'))), write (array e2) (snd (fst (fst (fst t')))) e5, snd (fst (fst t')), snd (fst t'), snd t').
Proof. intros. generalize dependent l. generalize dependent e1. generalize dependent e3. generalize dependent e4. generalize dependent m.  generalize dependent l'. generalize dependent e1'. generalize dependent e3'. generalize dependent e4'. generalize dependent m'. generalize dependent e2. generalize dependent e5. induction H1; intros.
  + apply SC_program_steps_reflexive.
  + subst. destruct q. destruct p. destruct p. destruct p. simpl in *. apply SC_program_steps_transitive with (q:=(l0, write (array e2) t1 e5, t0, t, m0)).
    ++ inversion H; subst.
       +++ apply ST_init_allocate_array. auto. auto. auto.
       +++ apply ST_synchronize1 with (event:=event). assert (exists n, array e2 = array n). refine (ex_intro _ e2 _). auto. apply step_context with (E:=Cwrite2 (exist _ (array e2) H0) Hole e5). auto. auto.
       +++ apply ST_synchronize2 with (event:=event). auto. auto.
       +++ apply ST_synchronize3 with (event:=event). auto. auto.
    ++ apply IHSC_program_steps with (m'0:=m') (e4'0:=e4') (e3'0:=e3') (e1'0:=e1') (l'0:=l') (m:=m0) (e4:=t) (e3:=t0) (e1:=t1) (l:=l0). auto. auto. Qed.

Fact steps_write_right_right : forall l l' e1 e1' e3 e3' e4 e4' m m' e2 e5 t t',
t = (l, e1, e3, e4, m) ->
t' = (l', e1', e3', e4', m') ->
SC_program_steps t t' ->
SC_program_steps
(fst (fst (fst (fst t))), write (array e2) (num e5) (snd (fst (fst (fst t)))), snd (fst (fst t)), snd (fst t), snd t) (fst (fst (fst (fst t'))), write (array e2) (num e5) (snd (fst (fst (fst t')))), snd (fst (fst t')), snd (fst t'), snd t').
Proof. intros. generalize dependent l. generalize dependent e1. generalize dependent e3. generalize dependent e4. generalize dependent m.  generalize dependent l'. generalize dependent e1'. generalize dependent e3'. generalize dependent e4'. generalize dependent m'. generalize dependent e2. induction H1; intros.
  + apply SC_program_steps_reflexive.
  + subst. destruct q. destruct p. destruct p. destruct p. simpl in *. apply SC_program_steps_transitive with (q:=(l0, write (array e2) (num e5) t1, t0, t, m0)).
    ++ inversion H; subst.
       +++ apply ST_init_allocate_array. auto. auto. auto.
       +++ apply ST_synchronize1 with (event:=event). assert (exists n, array e2 = array n). refine (ex_intro _ e2 _). auto. assert (exists n, num e5 = num n). refine (ex_intro _ e5 _). auto. apply step_context with (E:=Cwrite3 (exist _ (array e2) H0) (exist _ (num e5) H2) Hole). auto. auto.
       +++ apply ST_synchronize2 with (event:=event). auto. auto.
       +++ apply ST_synchronize3 with (event:=event). auto. auto.
    ++ apply IHSC_program_steps with (m'0:=m') (e4'0:=e4') (e3'0:=e3') (e1'0:=e1') (l'0:=l') (m:=m0) (e4:=t) (e3:=t0) (e1:=t1) (l:=l0). auto. auto. Qed.

Fact steps_not_left : forall l l' e1 e1' e3 e3' e4 e4' m m' t t',
t = (l, e1, e3, e4, m) ->
t' = (l', e1', e3', e4', m') ->
SC_program_steps t t' ->
SC_program_steps
(fst (fst (fst (fst t))), not (snd (fst (fst (fst t)))), snd (fst (fst t)), snd (fst t), snd t) (fst (fst (fst (fst t'))), not (snd (fst (fst (fst t')))), snd (fst (fst t')), snd (fst t'), snd t').
Proof. intros. generalize dependent l. generalize dependent e1. generalize dependent e3. generalize dependent e4. generalize dependent m.  generalize dependent l'. generalize dependent e1'. generalize dependent e3'. generalize dependent e4'. generalize dependent m'. induction H1; intros.
  + apply SC_program_steps_reflexive.
  + subst. destruct q. destruct p. destruct p. destruct p. simpl in *. apply SC_program_steps_transitive with (q:=(l0, not t1, t0, t, m0)).
    ++ inversion H; subst.
       +++ apply ST_init_allocate_array. auto. auto. auto.
       +++ apply ST_synchronize1 with (event:=event). apply step_context with (E:=Cnot Hole). auto. auto.
       +++ apply ST_synchronize2 with (event:=event). auto. auto.
       +++ apply ST_synchronize3 with (event:=event). auto. auto.
    ++ apply IHSC_program_steps with (m'0:=m') (e4'0:=e4') (e3'0:=e3') (e1'0:=e1') (l'0:=l') (m:=m0) (e4:=t) (e3:=t0) (e1:=t1) (l:=l0). auto. auto. Qed.

Fact steps_reference_left : forall l l' e1 e1' e3 e3' e4 e4' m m' t t',
t = (l, e1, e3, e4, m) ->
t' = (l', e1', e3', e4', m') ->
SC_program_steps t t' ->
SC_program_steps
(fst (fst (fst (fst t))), reference (snd (fst (fst (fst t)))), snd (fst (fst t)), snd (fst t), snd t) (fst (fst (fst (fst t'))), reference (snd (fst (fst (fst t')))), snd (fst (fst t')), snd (fst t'), snd t').
Proof. intros. generalize dependent l. generalize dependent e1. generalize dependent e3. generalize dependent e4. generalize dependent m.  generalize dependent l'. generalize dependent e1'. generalize dependent e3'. generalize dependent e4'. generalize dependent m'. induction H1; intros.
  + apply SC_program_steps_reflexive.
  + subst. destruct q. destruct p. destruct p. destruct p. simpl in *. apply SC_program_steps_transitive with (q:=(l0, reference t1, t0, t, m0)).
    ++ inversion H; subst.
       +++ apply ST_init_allocate_array. auto. auto. auto.
       +++ apply ST_synchronize1 with (event:=event). apply step_context with (E:=Creference Hole). auto. auto.
       +++ apply ST_synchronize2 with (event:=event). auto. auto.
       +++ apply ST_synchronize3 with (event:=event). auto. auto.
    ++ apply IHSC_program_steps with (m'0:=m') (e4'0:=e4') (e3'0:=e3') (e1'0:=e1') (l'0:=l') (m:=m0) (e4:=t) (e3:=t0) (e1:=t1) (l:=l0). auto. auto. Qed.

Fact steps_cast_left : forall l l' e1 e1' e3 e3' e4 e4' m m' t t',
t = (l, e1, e3, e4, m) ->
t' = (l', e1', e3', e4', m') ->
SC_program_steps t t' ->
SC_program_steps
(fst (fst (fst (fst t))), cast (snd (fst (fst (fst t)))), snd (fst (fst t)), snd (fst t), snd t) (fst (fst (fst (fst t'))), cast (snd (fst (fst (fst t')))), snd (fst (fst t')), snd (fst t'), snd t').
Proof. intros. generalize dependent l. generalize dependent e1. generalize dependent e3. generalize dependent e4. generalize dependent m.  generalize dependent l'. generalize dependent e1'. generalize dependent e3'. generalize dependent e4'. generalize dependent m'. induction H1; intros.
  + apply SC_program_steps_reflexive.
  + subst. destruct q. destruct p. destruct p. destruct p. simpl in *. apply SC_program_steps_transitive with (q:=(l0, cast t1, t0, t, m0)).
    ++ inversion H; subst.
       +++ apply ST_init_allocate_array. auto. auto. auto.
       +++ apply ST_synchronize1 with (event:=event). apply step_context with (E:=Ccast Hole). auto. auto.
       +++ apply ST_synchronize2 with (event:=event). auto. auto.
       +++ apply ST_synchronize3 with (event:=event). auto. auto.
    ++ apply IHSC_program_steps with (m'0:=m') (e4'0:=e4') (e3'0:=e3') (e1'0:=e1') (l'0:=l') (m:=m0) (e4:=t) (e3:=t0) (e1:=t1) (l:=l0). auto. auto. Qed.

Fact steps_case_left : forall l l' e1 e1' e3 e3' e4 e4' m m' e2 e5 t t',
t = (l, e1, e3, e4, m) ->
t' = (l', e1', e3', e4', m') ->
SC_program_steps t t' ->
SC_program_steps
(fst (fst (fst (fst t))), case (snd (fst (fst (fst t)))) e2 e5, snd (fst (fst t)), snd (fst t), snd t) (fst (fst (fst (fst t'))), case (snd (fst (fst (fst t')))) e2 e5, snd (fst (fst t')), snd (fst t'), snd t').
Proof. intros. generalize dependent l. generalize dependent e1. generalize dependent e3. generalize dependent e4. generalize dependent m.  generalize dependent l'. generalize dependent e1'. generalize dependent e3'. generalize dependent e4'. generalize dependent m'. generalize dependent e2. generalize dependent e5. induction H1; intros.
  + apply SC_program_steps_reflexive.
  + subst. destruct q. destruct p. destruct p. destruct p. simpl in *. apply SC_program_steps_transitive with (q:=(l0, case t1 e2 e5, t0, t, m0)).
    ++ inversion H; subst.
       +++ apply ST_init_allocate_array. auto. auto. auto.
       +++ apply ST_synchronize1 with (event:=event). apply step_context with (E:=Ccase Hole e2 e5). auto. auto.
       +++ apply ST_synchronize2 with (event:=event). auto. auto.
       +++ apply ST_synchronize3 with (event:=event). auto. auto.
    ++ apply IHSC_program_steps with (m'0:=m') (e4'0:=e4') (e3'0:=e3') (e1'0:=e1') (l'0:=l') (m:=m0) (e4:=t) (e3:=t0) (e1:=t1) (l:=l0). auto. auto. Qed.
