Require Import List.
Require Import Lambda.
Require Import Util.

Definition location_state := nat -> (option (nat * nat * bool)). (* location -> (base, size, locked) *)
Definition global_store := nat -> (option nat). (* location -> value *)
Definition memory_model := location_state * global_store.

Definition allocate (start : nat) (finish : nat) (init : list nat) (g : global_store) : global_store :=
(fun n => if andb (Nat.leb start n) (Nat.leb n finish) then Some (nth (n - start) init (0%nat)) else g 0).

Definition update_global (val : nat * nat) (g : global_store) : global_store :=
(fun n => if Nat.eqb n (fst val) then Some (snd val) else g n).

Definition update_location_state (location : nat) (base : nat) (size : nat) (locked : bool) (g : location_state) : location_state :=
(fun n => if Nat.eqb n location then Some (base, size, locked) else g n).

Inductive memory_step : memory_model -> mem_event -> memory_model -> Prop :=
  | ST_tau_step : forall mem, memory_step mem Tau mem
  | ST_read :  forall global value location offset location_state base size,
               location_state location = Some (base, size, false) ->
               offset < size ->
               global (base + offset) = Some value ->
               memory_step (location_state, global) (Read location offset value) (location_state, global)
  | ST_write : forall global global' offset value location location_state base size,
               location_state location = Some (base, size, false) ->
               offset < size ->
               global' = update_global (base + offset, value) global ->
               memory_step (location_state, global) (Write location offset value) (location_state, global')
  | ST_allocate_array : forall global global' init location size location_state base location_state',
               (forall n, base <= n < base + size -> global n = None) ->
               location_state location = None ->
               location_state' = update_location_state location base size false location_state ->
               global' = allocate base (base + size - 1) init global ->
               memory_step (location_state, global) (Allocate location size init) (location_state', global')
  | ST_reference : forall global location base size location_state b,
               location_state location = Some (base, size, b) ->
               memory_step (location_state, global) (Reference location base) (location_state, global)
  | ST_cast : forall global location location_state base size b,
               location_state location = Some (base, size, b) ->
               memory_step (location_state, global) (Cast base location) (location_state, global)
  | ST_lock : forall global location location_state location_state' base size,
               location_state location = Some (base, size, false) ->
               location_state' = update_location_state location base size true location_state ->
               memory_step (location_state, global) (Lock location) (location_state', global)
  | ST_unlock : forall global location location_state location_state' base size,
               location_state location = Some (base, size, true) ->
               location_state' = update_location_state location base size false location_state ->
               memory_step (location_state, global) (Lock location) (location_state', global).

(* A program is a pair (init, threads)
  1. init : (list (nat * (list nat))) denoting array variables with respective inital values,
  2. threads : (bool + unit) denotes the three currently running threads.
*)
Definition program := (list (nat * (list nat))) * ((sum bool unit) -> term).

Definition SC_machine := program * memory_model.

Definition thread_equals (t t' : sum bool unit) :=
  match t, t' with
    | inl b, inl b' => Bool.eqb b b'
    | inr _, inr _ => true
    | _, _ => false
  end.

Fact thread_equals_true_iff : forall t t', thread_equals t t' = true <-> t = t'.
Proof. intros. unfold iff. unfold iff. split.
  + destruct t; destruct t'; simpl.
    ++ intros. rewrite Bool.eqb_true_iff in H. subst. auto.
    ++ intros. inversion H.
    ++ intros. inversion H.
    ++ destruct u. destruct u0. intuition.
  + intros. subst. destruct t'; simpl; auto. apply Bool.eqb_true_iff. auto. Qed.

Fact thread_equals_false_iff : forall t t', thread_equals t t' = false <-> t <> t'.
Proof. intros. unfold iff. split.
  + intros. intros C. apply thread_equals_true_iff in C. rewrite H in C. inversion C.
  + intros. destruct t; destruct t'; simpl; auto. rewrite Bool.eqb_false_iff.  intros C. subst. contradiction H. auto. destruct u. destruct u0. contradiction H. auto. Qed.

Fact thread_equals_commutative : forall t t', thread_equals t t' = thread_equals t' t.
Proof. intros. destruct t; destruct t'; simpl; try (destruct b; destruct b0; simpl; auto); auto. Qed.

Inductive pstep : SC_machine -> SC_machine -> Prop :=
  | ST_init_allocate_array : forall xs threads threads' mem mem' size init,
                      size > 0 ->
                      length init <= size ->
                      memory_step mem (Allocate (length xs) size init) mem' ->
                      (forall t, threads t = threads' t) ->
                      pstep ((xs ++ ((size, init) :: nil), threads), mem) ((xs, threads'), mem')
  | ST_synchronize : forall event mem mem' threads thread threads' e,
                      step (threads thread) event e ->
                      memory_step mem event mem' ->
                      (forall t, threads' t = if thread_equals t thread then e else threads t) ->
                      pstep ((nil, threads), mem) ((nil, threads'), mem').

Inductive SC_program_steps : SC_machine -> SC_machine -> Prop :=
  | SC_program_steps_reflexive : forall l f g m,  (forall t, f t = g t) -> SC_program_steps (l, f, m) (l, g, m)
  | SC_program_steps_transitive : forall p q r, pstep p q -> SC_program_steps q r -> SC_program_steps p r.

Fact program_steps_same : forall l l' m' m'0 u u' v v',
SC_program_steps (l, u, m') (l', v, m'0) ->
(forall t, u t = u' t) ->
(forall t, v t = v' t) ->
SC_program_steps (l, u', m') (l', v', m'0).
Proof. intros. remember (l,u,m') as p. remember (l',v,m'0) as p'. generalize dependent l. generalize dependent l'. generalize dependent u. generalize dependent v. generalize dependent u'. generalize dependent v'. generalize dependent m'. generalize dependent m'0. induction H; intros.
  + inversion Heqp. inversion Heqp'. subst. apply SC_program_steps_reflexive. intros. rewrite <- H0. rewrite <- H1. auto.
  + subst. apply SC_program_steps_transitive with (q:=q). inversion H; subst.
    ++ apply ST_init_allocate_array. auto. auto. auto. intros. rewrite <- H2. auto.
    ++ apply ST_synchronize with (event:=event) (thread:=thread) (e:=e). rewrite <- H2. auto. auto. intros. rewrite <- H2. auto.
    ++ destruct q. destruct p. apply IHSC_program_steps with (l:=l0) (u:=t) (m':=m) (m'1:=m'0) (v0:=v) (l'0:=l'). auto. auto. auto. auto. Qed.

Fact steps_app_left : forall l l' threads threads' thread m m' f g e2 ,
SC_program_steps (l, threads, m) (l', threads', m') ->
(forall t, f t = if thread_equals t thread then app (threads t) e2 else threads t) ->
(forall t, g t = if thread_equals t thread then app (threads' t) e2 else threads' t) ->
SC_program_steps (l, f, m) (l', g, m').
Proof. intros. remember (l, threads, m) as p. remember (l', threads', m') as p'. generalize dependent l. generalize dependent l'. generalize dependent m. generalize dependent m'. generalize dependent e2. generalize dependent thread. generalize dependent threads'. generalize dependent threads. generalize dependent f. generalize dependent g. induction H; intros.
  + inversion Heqp. inversion Heqp'. subst. apply SC_program_steps_reflexive. intros. rewrite H0. rewrite H1. rewrite H. auto.
  +  subst. destruct q. destruct p. apply SC_program_steps_transitive with  (l0, fun thread' : bool + unit => if thread_equals thread' thread then app (t thread') e2 else t thread', m0). inversion H; subst.
       +++ apply ST_init_allocate_array. auto. auto. auto. intros. rewrite H1. rewrite H12. auto.
       +++ destruct (thread_equals thread thread0) eqn:ORIG.
           ++++ rewrite thread_equals_true_iff in ORIG. subst. apply ST_synchronize with (event:=event) (e:=app e e2) (thread:=thread0). destruct thread0; simpl.
                +++++ rewrite H1. simpl. rewrite Bool.eqb_reflx. apply step_context with (E:=Capp1 Hole e2). auto.
                +++++ rewrite H1. simpl. apply step_context with (E:=Capp1 Hole e2). auto.
                +++++ auto.
                +++++ intros. rewrite H11. rewrite H1. destruct (thread_equals t0 thread0) eqn:ORIG. auto. auto.
           ++++ apply ST_synchronize with (event:=event) (e:=e) (thread:=thread0). rewrite H1. rewrite thread_equals_commutative in ORIG. rewrite ORIG. auto. auto. intros. destruct (thread_equals t0 thread) eqn:ORIG1. rewrite thread_equals_true_iff in ORIG1. subst. rewrite ORIG. rewrite H1. assert (thread_equals thread thread = true). apply thread_equals_true_iff. auto. rewrite H3. rewrite H11. rewrite ORIG. auto. rewrite H11. rewrite H1. rewrite ORIG1. auto. 
        +++ apply IHSC_program_steps with (threads:=t) (threads'0:=threads') (thread:=thread) (e2:=e2). auto. auto. auto. auto. Qed.


Fact steps_app_right : forall l l' threads threads' thread m m' f g e2,
SC_program_steps (l, threads, m) (l', threads', m') ->
(forall t, f t = if thread_equals t thread then app (lam e2) (threads t) else threads t) ->
(forall t, g t = if thread_equals t thread then app (lam e2) (threads' t) else threads' t) ->
SC_program_steps (l, f, m) (l', g, m').
Proof. intros. remember (l, threads, m) as p. remember (l', threads', m') as p'. generalize dependent l. generalize dependent l'. generalize dependent m. generalize dependent m'. generalize dependent e2. generalize dependent thread. generalize dependent threads'. generalize dependent threads. generalize dependent f. generalize dependent g. induction H; intros.
  + inversion Heqp. inversion Heqp'. subst. apply SC_program_steps_reflexive. intros. rewrite H0. rewrite H1. rewrite H. auto.
  +  subst. destruct q. destruct p. apply SC_program_steps_transitive with  (l0, fun thread' : bool + unit => if thread_equals thread' thread then app (lam e2) (t thread') else t thread', m0). inversion H; subst.
       +++ apply ST_init_allocate_array. auto. auto. auto. intros. rewrite H1. rewrite H12. auto.
       +++ destruct (thread_equals thread thread0) eqn:ORIG.
           ++++ rewrite thread_equals_true_iff in ORIG. subst. apply ST_synchronize with (event:=event) (e:=app (lam e2) e) (thread:=thread0). assert (exists e', lam e2 = lam e'). refine (ex_intro _ e2 _). auto. destruct thread0; simpl.
                +++++ rewrite H1. simpl. rewrite Bool.eqb_reflx. apply step_context with (E:=Capp2 (exist _(lam e2) H3) Hole). auto.
                +++++ rewrite H1. simpl. apply step_context with (E:=Capp2 (exist _(lam e2) H3) Hole). auto.
                +++++ auto.
                +++++ intros. rewrite H11. rewrite H1. destruct (thread_equals t0 thread0) eqn:ORIG. auto. auto.
           ++++ apply ST_synchronize with (event:=event) (e:=e) (thread:=thread0). rewrite H1. rewrite thread_equals_commutative in ORIG. rewrite ORIG. auto. auto. intros. destruct (thread_equals t0 thread) eqn:ORIG1. rewrite thread_equals_true_iff in ORIG1. subst. rewrite ORIG. rewrite H1. assert (thread_equals thread thread = true). apply thread_equals_true_iff. auto. rewrite H3. rewrite H11. rewrite ORIG. auto. rewrite H11. rewrite H1. rewrite ORIG1. auto. 
        +++ apply IHSC_program_steps with (threads:=t) (threads'0:=threads') (thread:=thread) (e2:=e2). auto. auto. auto. auto. Qed.

Fact steps_plus_left : forall l l' threads threads' thread m m' f g e2 ,
SC_program_steps (l, threads, m) (l', threads', m') ->
(forall t, f t = if thread_equals t thread then plus (threads t) e2 else threads t) ->
(forall t, g t = if thread_equals t thread then plus (threads' t) e2 else threads' t) ->
SC_program_steps (l, f, m) (l', g, m').
Proof. intros. remember (l, threads, m) as p. remember (l', threads', m') as p'. generalize dependent l. generalize dependent l'. generalize dependent m. generalize dependent m'. generalize dependent e2. generalize dependent thread. generalize dependent threads'. generalize dependent threads. generalize dependent f. generalize dependent g. induction H; intros.
  + inversion Heqp. inversion Heqp'. subst. apply SC_program_steps_reflexive. intros. rewrite H0. rewrite H1. rewrite H. auto.
  +  subst. destruct q. destruct p. apply SC_program_steps_transitive with  (l0, fun thread' : bool + unit => if thread_equals thread' thread then plus (t thread') e2 else t thread', m0). inversion H; subst.
       +++ apply ST_init_allocate_array. auto. auto. auto. intros. rewrite H1. rewrite H12. auto.
       +++ destruct (thread_equals thread thread0) eqn:ORIG.
           ++++ rewrite thread_equals_true_iff in ORIG. subst. apply ST_synchronize with (event:=event) (e:=plus e e2) (thread:=thread0). destruct thread0; simpl.
                +++++ rewrite H1. simpl. rewrite Bool.eqb_reflx. apply step_context with (E:=Cplus1 Hole e2). auto.
                +++++ rewrite H1. simpl. apply step_context with (E:=Cplus1 Hole e2). auto.
                +++++ auto.
                +++++ intros. rewrite H11. rewrite H1. destruct (thread_equals t0 thread0) eqn:ORIG. auto. auto.
           ++++ apply ST_synchronize with (event:=event) (e:=e) (thread:=thread0). rewrite H1. rewrite thread_equals_commutative in ORIG. rewrite ORIG. auto. auto. intros. destruct (thread_equals t0 thread) eqn:ORIG1. rewrite thread_equals_true_iff in ORIG1. subst. rewrite ORIG. rewrite H1. assert (thread_equals thread thread = true). apply thread_equals_true_iff. auto. rewrite H3. rewrite H11. rewrite ORIG. auto. rewrite H11. rewrite H1. rewrite ORIG1. auto. 
        +++ apply IHSC_program_steps with (threads:=t) (threads'0:=threads') (thread:=thread) (e2:=e2). auto. auto. auto. auto. Qed.


Fact steps_plus_right : forall l l' threads threads' thread m m' f g e2,
SC_program_steps (l, threads, m) (l', threads', m') ->
(forall t, f t = if thread_equals t thread then plus (num e2) (threads t) else threads t) ->
(forall t, g t = if thread_equals t thread then plus (num e2) (threads' t) else threads' t) ->
SC_program_steps (l, f, m) (l', g, m').
Proof. intros. remember (l, threads, m) as p. remember (l', threads', m') as p'. generalize dependent l. generalize dependent l'. generalize dependent m. generalize dependent m'. generalize dependent e2. generalize dependent thread. generalize dependent threads'. generalize dependent threads. generalize dependent f. generalize dependent g. induction H; intros.
  + inversion Heqp. inversion Heqp'. subst. apply SC_program_steps_reflexive. intros. rewrite H0. rewrite H1. rewrite H. auto.
  +  subst. destruct q. destruct p. apply SC_program_steps_transitive with  (l0, fun thread' : bool + unit => if thread_equals thread' thread then plus (num e2) (t thread') else t thread', m0). inversion H; subst.
       +++ apply ST_init_allocate_array. auto. auto. auto. intros. rewrite H1. rewrite H12. auto.
       +++ destruct (thread_equals thread thread0) eqn:ORIG.
           ++++ rewrite thread_equals_true_iff in ORIG. subst. apply ST_synchronize with (event:=event) (e:=plus (num e2) e) (thread:=thread0). assert (exists e', num e2 = num e'). refine (ex_intro _ e2 _). auto. destruct thread0; simpl.
                +++++ rewrite H1. simpl. rewrite Bool.eqb_reflx. apply step_context with (E:=Cplus2 (exist _(num e2) H3) Hole). auto.
                +++++ rewrite H1. simpl. apply step_context with (E:=Cplus2 (exist _(num e2) H3) Hole). auto.
                +++++ auto.
                +++++ intros. rewrite H11. rewrite H1. destruct (thread_equals t0 thread0) eqn:ORIG. auto. auto.
           ++++ apply ST_synchronize with (event:=event) (e:=e) (thread:=thread0). rewrite H1. rewrite thread_equals_commutative in ORIG. rewrite ORIG. auto. auto. intros. destruct (thread_equals t0 thread) eqn:ORIG1. rewrite thread_equals_true_iff in ORIG1. subst. rewrite ORIG. rewrite H1. assert (thread_equals thread thread = true). apply thread_equals_true_iff. auto. rewrite H3. rewrite H11. rewrite ORIG. auto. rewrite H11. rewrite H1. rewrite ORIG1. auto. 
        +++ apply IHSC_program_steps with (threads:=t) (threads'0:=threads') (thread:=thread) (e2:=e2). auto. auto. auto. auto. Qed.

Fact steps_minus_left : forall l l' threads threads' thread m m' f g e2 ,
SC_program_steps (l, threads, m) (l', threads', m') ->
(forall t, f t = if thread_equals t thread then minus (threads t) e2 else threads t) ->
(forall t, g t = if thread_equals t thread then minus (threads' t) e2 else threads' t) ->
SC_program_steps (l, f, m) (l', g, m').
Proof. intros. remember (l, threads, m) as p. remember (l', threads', m') as p'. generalize dependent l. generalize dependent l'. generalize dependent m. generalize dependent m'. generalize dependent e2. generalize dependent thread. generalize dependent threads'. generalize dependent threads. generalize dependent f. generalize dependent g. induction H; intros.
  + inversion Heqp. inversion Heqp'. subst. apply SC_program_steps_reflexive. intros. rewrite H0. rewrite H1. rewrite H. auto.
  +  subst. destruct q. destruct p. apply SC_program_steps_transitive with  (l0, fun thread' : bool + unit => if thread_equals thread' thread then minus (t thread') e2 else t thread', m0). inversion H; subst.
       +++ apply ST_init_allocate_array. auto. auto. auto. intros. rewrite H1. rewrite H12. auto.
       +++ destruct (thread_equals thread thread0) eqn:ORIG.
           ++++ rewrite thread_equals_true_iff in ORIG. subst. apply ST_synchronize with (event:=event) (e:=minus e e2) (thread:=thread0). destruct thread0; simpl.
                +++++ rewrite H1. simpl. rewrite Bool.eqb_reflx. apply step_context with (E:=Cminus1 Hole e2). auto.
                +++++ rewrite H1. simpl. apply step_context with (E:=Cminus1 Hole e2). auto.
                +++++ auto.
                +++++ intros. rewrite H11. rewrite H1. destruct (thread_equals t0 thread0) eqn:ORIG. auto. auto.
           ++++ apply ST_synchronize with (event:=event) (e:=e) (thread:=thread0). rewrite H1. rewrite thread_equals_commutative in ORIG. rewrite ORIG. auto. auto. intros. destruct (thread_equals t0 thread) eqn:ORIG1. rewrite thread_equals_true_iff in ORIG1. subst. rewrite ORIG. rewrite H1. assert (thread_equals thread thread = true). apply thread_equals_true_iff. auto. rewrite H3. rewrite H11. rewrite ORIG. auto. rewrite H11. rewrite H1. rewrite ORIG1. auto. 
        +++ apply IHSC_program_steps with (threads:=t) (threads'0:=threads') (thread:=thread) (e2:=e2). auto. auto. auto. auto. Qed.


Fact steps_minus_right : forall l l' threads threads' thread m m' f g e2,
SC_program_steps (l, threads, m) (l', threads', m') ->
(forall t, f t = if thread_equals t thread then minus (num e2) (threads t) else threads t) ->
(forall t, g t = if thread_equals t thread then minus (num e2) (threads' t) else threads' t) ->
SC_program_steps (l, f, m) (l', g, m').
Proof. intros. remember (l, threads, m) as p. remember (l', threads', m') as p'. generalize dependent l. generalize dependent l'. generalize dependent m. generalize dependent m'. generalize dependent e2. generalize dependent thread. generalize dependent threads'. generalize dependent threads. generalize dependent f. generalize dependent g. induction H; intros.
  + inversion Heqp. inversion Heqp'. subst. apply SC_program_steps_reflexive. intros. rewrite H0. rewrite H1. rewrite H. auto.
  +  subst. destruct q. destruct p. apply SC_program_steps_transitive with  (l0, fun thread' : bool + unit => if thread_equals thread' thread then minus (num e2) (t thread') else t thread', m0). inversion H; subst.
       +++ apply ST_init_allocate_array. auto. auto. auto. intros. rewrite H1. rewrite H12. auto.
       +++ destruct (thread_equals thread thread0) eqn:ORIG.
           ++++ rewrite thread_equals_true_iff in ORIG. subst. apply ST_synchronize with (event:=event) (e:=minus (num e2) e) (thread:=thread0). assert (exists e', num e2 = num e'). refine (ex_intro _ e2 _). auto. destruct thread0; simpl.
                +++++ rewrite H1. simpl. rewrite Bool.eqb_reflx. apply step_context with (E:=Cminus2 (exist _(num e2) H3) Hole). auto.
                +++++ rewrite H1. simpl. apply step_context with (E:=Cminus2 (exist _(num e2) H3) Hole). auto.
                +++++ auto.
                +++++ intros. rewrite H11. rewrite H1. destruct (thread_equals t0 thread0) eqn:ORIG. auto. auto.
           ++++ apply ST_synchronize with (event:=event) (e:=e) (thread:=thread0). rewrite H1. rewrite thread_equals_commutative in ORIG. rewrite ORIG. auto. auto. intros. destruct (thread_equals t0 thread) eqn:ORIG1. rewrite thread_equals_true_iff in ORIG1. subst. rewrite ORIG. rewrite H1. assert (thread_equals thread thread = true). apply thread_equals_true_iff. auto. rewrite H3. rewrite H11. rewrite ORIG. auto. rewrite H11. rewrite H1. rewrite ORIG1. auto. 
        +++ apply IHSC_program_steps with (threads:=t) (threads'0:=threads') (thread:=thread) (e2:=e2). auto. auto. auto. auto. Qed.

Fact steps_modulo_left : forall l l' threads threads' thread m m' f g e2 ,
SC_program_steps (l, threads, m) (l', threads', m') ->
(forall t, f t = if thread_equals t thread then modulo (threads t) e2 else threads t) ->
(forall t, g t = if thread_equals t thread then modulo (threads' t) e2 else threads' t) ->
SC_program_steps (l, f, m) (l', g, m').
Proof. intros. remember (l, threads, m) as p. remember (l', threads', m') as p'. generalize dependent l. generalize dependent l'. generalize dependent m. generalize dependent m'. generalize dependent e2. generalize dependent thread. generalize dependent threads'. generalize dependent threads. generalize dependent f. generalize dependent g. induction H; intros.
  + inversion Heqp. inversion Heqp'. subst. apply SC_program_steps_reflexive. intros. rewrite H0. rewrite H1. rewrite H. auto.
  +  subst. destruct q. destruct p. apply SC_program_steps_transitive with  (l0, fun thread' : bool + unit => if thread_equals thread' thread then modulo (t thread') e2 else t thread', m0). inversion H; subst.
       +++ apply ST_init_allocate_array. auto. auto. auto. intros. rewrite H1. rewrite H12. auto.
       +++ destruct (thread_equals thread thread0) eqn:ORIG.
           ++++ rewrite thread_equals_true_iff in ORIG. subst. apply ST_synchronize with (event:=event) (e:=modulo e e2) (thread:=thread0). destruct thread0; simpl.
                +++++ rewrite H1. simpl. rewrite Bool.eqb_reflx. apply step_context with (E:=Cmodulo1 Hole e2). auto.
                +++++ rewrite H1. simpl. apply step_context with (E:=Cmodulo1 Hole e2). auto.
                +++++ auto.
                +++++ intros. rewrite H11. rewrite H1. destruct (thread_equals t0 thread0) eqn:ORIG. auto. auto.
           ++++ apply ST_synchronize with (event:=event) (e:=e) (thread:=thread0). rewrite H1. rewrite thread_equals_commutative in ORIG. rewrite ORIG. auto. auto. intros. destruct (thread_equals t0 thread) eqn:ORIG1. rewrite thread_equals_true_iff in ORIG1. subst. rewrite ORIG. rewrite H1. assert (thread_equals thread thread = true). apply thread_equals_true_iff. auto. rewrite H3. rewrite H11. rewrite ORIG. auto. rewrite H11. rewrite H1. rewrite ORIG1. auto. 
        +++ apply IHSC_program_steps with (threads:=t) (threads'0:=threads') (thread:=thread) (e2:=e2). auto. auto. auto. auto. Qed.


Fact steps_modulo_right : forall l l' threads threads' thread m m' f g e2,
SC_program_steps (l, threads, m) (l', threads', m') ->
(forall t, f t = if thread_equals t thread then modulo (num e2) (threads t) else threads t) ->
(forall t, g t = if thread_equals t thread then modulo (num e2) (threads' t) else threads' t) ->
SC_program_steps (l, f, m) (l', g, m').
Proof. intros. remember (l, threads, m) as p. remember (l', threads', m') as p'. generalize dependent l. generalize dependent l'. generalize dependent m. generalize dependent m'. generalize dependent e2. generalize dependent thread. generalize dependent threads'. generalize dependent threads. generalize dependent f. generalize dependent g. induction H; intros.
  + inversion Heqp. inversion Heqp'. subst. apply SC_program_steps_reflexive. intros. rewrite H0. rewrite H1. rewrite H. auto.
  +  subst. destruct q. destruct p. apply SC_program_steps_transitive with  (l0, fun thread' : bool + unit => if thread_equals thread' thread then modulo (num e2) (t thread') else t thread', m0). inversion H; subst.
       +++ apply ST_init_allocate_array. auto. auto. auto. intros. rewrite H1. rewrite H12. auto.
       +++ destruct (thread_equals thread thread0) eqn:ORIG.
           ++++ rewrite thread_equals_true_iff in ORIG. subst. apply ST_synchronize with (event:=event) (e:=modulo (num e2) e) (thread:=thread0). assert (exists e', num e2 = num e'). refine (ex_intro _ e2 _). auto. destruct thread0; simpl.
                +++++ rewrite H1. simpl. rewrite Bool.eqb_reflx. apply step_context with (E:=Cmodulo2 (exist _(num e2) H3) Hole). auto.
                +++++ rewrite H1. simpl. apply step_context with (E:=Cmodulo2 (exist _(num e2) H3) Hole). auto.
                +++++ auto.
                +++++ intros. rewrite H11. rewrite H1. destruct (thread_equals t0 thread0) eqn:ORIG. auto. auto.
           ++++ apply ST_synchronize with (event:=event) (e:=e) (thread:=thread0). rewrite H1. rewrite thread_equals_commutative in ORIG. rewrite ORIG. auto. auto. intros. destruct (thread_equals t0 thread) eqn:ORIG1. rewrite thread_equals_true_iff in ORIG1. subst. rewrite ORIG. rewrite H1. assert (thread_equals thread thread = true). apply thread_equals_true_iff. auto. rewrite H3. rewrite H11. rewrite ORIG. auto. rewrite H11. rewrite H1. rewrite ORIG1. auto. 
        +++ apply IHSC_program_steps with (threads:=t) (threads'0:=threads') (thread:=thread) (e2:=e2). auto. auto. auto. auto. Qed.

Fact steps_less_than_left : forall l l' threads threads' thread m m' f g e2 ,
SC_program_steps (l, threads, m) (l', threads', m') ->
(forall t, f t = if thread_equals t thread then less_than (threads t) e2 else threads t) ->
(forall t, g t = if thread_equals t thread then less_than (threads' t) e2 else threads' t) ->
SC_program_steps (l, f, m) (l', g, m').
Proof. intros. remember (l, threads, m) as p. remember (l', threads', m') as p'. generalize dependent l. generalize dependent l'. generalize dependent m. generalize dependent m'. generalize dependent e2. generalize dependent thread. generalize dependent threads'. generalize dependent threads. generalize dependent f. generalize dependent g. induction H; intros.
  + inversion Heqp. inversion Heqp'. subst. apply SC_program_steps_reflexive. intros. rewrite H0. rewrite H1. rewrite H. auto.
  +  subst. destruct q. destruct p. apply SC_program_steps_transitive with  (l0, fun thread' : bool + unit => if thread_equals thread' thread then less_than (t thread') e2 else t thread', m0). inversion H; subst.
       +++ apply ST_init_allocate_array. auto. auto. auto. intros. rewrite H1. rewrite H12. auto.
       +++ destruct (thread_equals thread thread0) eqn:ORIG.
           ++++ rewrite thread_equals_true_iff in ORIG. subst. apply ST_synchronize with (event:=event) (e:=less_than e e2) (thread:=thread0). destruct thread0; simpl.
                +++++ rewrite H1. simpl. rewrite Bool.eqb_reflx. apply step_context with (E:=Cless_than1 Hole e2). auto.
                +++++ rewrite H1. simpl. apply step_context with (E:=Cless_than1 Hole e2). auto.
                +++++ auto.
                +++++ intros. rewrite H11. rewrite H1. destruct (thread_equals t0 thread0) eqn:ORIG. auto. auto.
           ++++ apply ST_synchronize with (event:=event) (e:=e) (thread:=thread0). rewrite H1. rewrite thread_equals_commutative in ORIG. rewrite ORIG. auto. auto. intros. destruct (thread_equals t0 thread) eqn:ORIG1. rewrite thread_equals_true_iff in ORIG1. subst. rewrite ORIG. rewrite H1. assert (thread_equals thread thread = true). apply thread_equals_true_iff. auto. rewrite H3. rewrite H11. rewrite ORIG. auto. rewrite H11. rewrite H1. rewrite ORIG1. auto. 
        +++ apply IHSC_program_steps with (threads:=t) (threads'0:=threads') (thread:=thread) (e2:=e2). auto. auto. auto. auto. Qed.


Fact steps_less_than_right : forall l l' threads threads' thread m m' f g e2,
SC_program_steps (l, threads, m) (l', threads', m') ->
(forall t, f t = if thread_equals t thread then less_than (num e2) (threads t) else threads t) ->
(forall t, g t = if thread_equals t thread then less_than (num e2) (threads' t) else threads' t) ->
SC_program_steps (l, f, m) (l', g, m').
Proof. intros. remember (l, threads, m) as p. remember (l', threads', m') as p'. generalize dependent l. generalize dependent l'. generalize dependent m. generalize dependent m'. generalize dependent e2. generalize dependent thread. generalize dependent threads'. generalize dependent threads. generalize dependent f. generalize dependent g. induction H; intros.
  + inversion Heqp. inversion Heqp'. subst. apply SC_program_steps_reflexive. intros. rewrite H0. rewrite H1. rewrite H. auto.
  +  subst. destruct q. destruct p. apply SC_program_steps_transitive with  (l0, fun thread' : bool + unit => if thread_equals thread' thread then less_than (num e2) (t thread') else t thread', m0). inversion H; subst.
       +++ apply ST_init_allocate_array. auto. auto. auto. intros. rewrite H1. rewrite H12. auto.
       +++ destruct (thread_equals thread thread0) eqn:ORIG.
           ++++ rewrite thread_equals_true_iff in ORIG. subst. apply ST_synchronize with (event:=event) (e:=less_than (num e2) e) (thread:=thread0). assert (exists e', num e2 = num e'). refine (ex_intro _ e2 _). auto. destruct thread0; simpl.
                +++++ rewrite H1. simpl. rewrite Bool.eqb_reflx. apply step_context with (E:=Cless_than2 (exist _(num e2) H3) Hole). auto.
                +++++ rewrite H1. simpl. apply step_context with (E:=Cless_than2 (exist _(num e2) H3) Hole). auto.
                +++++ auto.
                +++++ intros. rewrite H11. rewrite H1. destruct (thread_equals t0 thread0) eqn:ORIG. auto. auto.
           ++++ apply ST_synchronize with (event:=event) (e:=e) (thread:=thread0). rewrite H1. rewrite thread_equals_commutative in ORIG. rewrite ORIG. auto. auto. intros. destruct (thread_equals t0 thread) eqn:ORIG1. rewrite thread_equals_true_iff in ORIG1. subst. rewrite ORIG. rewrite H1. assert (thread_equals thread thread = true). apply thread_equals_true_iff. auto. rewrite H3. rewrite H11. rewrite ORIG. auto. rewrite H11. rewrite H1. rewrite ORIG1. auto. 
        +++ apply IHSC_program_steps with (threads:=t) (threads'0:=threads') (thread:=thread) (e2:=e2). auto. auto. auto. auto. Qed.

Fact steps_and_left : forall l l' threads threads' thread m m' f g e2 ,
SC_program_steps (l, threads, m) (l', threads', m') ->
(forall t, f t = if thread_equals t thread then and (threads t) e2 else threads t) ->
(forall t, g t = if thread_equals t thread then and (threads' t) e2 else threads' t) ->
SC_program_steps (l, f, m) (l', g, m').
Proof. intros. remember (l, threads, m) as p. remember (l', threads', m') as p'. generalize dependent l. generalize dependent l'. generalize dependent m. generalize dependent m'. generalize dependent e2. generalize dependent thread. generalize dependent threads'. generalize dependent threads. generalize dependent f. generalize dependent g. induction H; intros.
  + inversion Heqp. inversion Heqp'. subst. apply SC_program_steps_reflexive. intros. rewrite H0. rewrite H1. rewrite H. auto.
  +  subst. destruct q. destruct p. apply SC_program_steps_transitive with  (l0, fun thread' : bool + unit => if thread_equals thread' thread then and (t thread') e2 else t thread', m0). inversion H; subst.
       +++ apply ST_init_allocate_array. auto. auto. auto. intros. rewrite H1. rewrite H12. auto.
       +++ destruct (thread_equals thread thread0) eqn:ORIG.
           ++++ rewrite thread_equals_true_iff in ORIG. subst. apply ST_synchronize with (event:=event) (e:=and e e2) (thread:=thread0). destruct thread0; simpl.
                +++++ rewrite H1. simpl. rewrite Bool.eqb_reflx. apply step_context with (E:=Cand1 Hole e2). auto.
                +++++ rewrite H1. simpl. apply step_context with (E:=Cand1 Hole e2). auto.
                +++++ auto.
                +++++ intros. rewrite H11. rewrite H1. destruct (thread_equals t0 thread0) eqn:ORIG. auto. auto.
           ++++ apply ST_synchronize with (event:=event) (e:=e) (thread:=thread0). rewrite H1. rewrite thread_equals_commutative in ORIG. rewrite ORIG. auto. auto. intros. destruct (thread_equals t0 thread) eqn:ORIG1. rewrite thread_equals_true_iff in ORIG1. subst. rewrite ORIG. rewrite H1. assert (thread_equals thread thread = true). apply thread_equals_true_iff. auto. rewrite H3. rewrite H11. rewrite ORIG. auto. rewrite H11. rewrite H1. rewrite ORIG1. auto. 
        +++ apply IHSC_program_steps with (threads:=t) (threads'0:=threads') (thread:=thread) (e2:=e2). auto. auto. auto. auto. Qed.


Fact steps_and_right : forall l l' threads threads' thread m m' f g,
SC_program_steps (l, threads, m) (l', threads', m') ->
(forall t, f t = if thread_equals t thread then and tru (threads t) else threads t) ->
(forall t, g t = if thread_equals t thread then and tru (threads' t) else threads' t) ->
SC_program_steps (l, f, m) (l', g, m').
Proof. intros. remember (l, threads, m) as p. remember (l', threads', m') as p'. generalize dependent l. generalize dependent l'. generalize dependent m. generalize dependent m'. generalize dependent thread. generalize dependent threads'. generalize dependent threads. generalize dependent f. generalize dependent g. induction H; intros.
  + inversion Heqp. inversion Heqp'. subst. apply SC_program_steps_reflexive. intros. rewrite H0. rewrite H1. rewrite H. auto.
  +  subst. destruct q. destruct p. apply SC_program_steps_transitive with  (l0, fun thread' : bool + unit => if thread_equals thread' thread then and tru (t thread') else t thread', m0). inversion H; subst.
       +++ apply ST_init_allocate_array. auto. auto. auto. intros. rewrite H1. rewrite H12. auto.
       +++ destruct (thread_equals thread thread0) eqn:ORIG.
           ++++ rewrite thread_equals_true_iff in ORIG. subst. apply ST_synchronize with (event:=event) (e:=and tru e) (thread:=thread0). destruct thread0; simpl.
                +++++ rewrite H1. simpl. rewrite Bool.eqb_reflx. apply step_context with (E:=Cand2 (exist _ tru eq_refl) Hole). auto.
                +++++ rewrite H1. simpl. apply step_context with (E:=Cand2 (exist _ tru eq_refl) Hole). auto.
                +++++ auto.
                +++++ intros. rewrite H11. rewrite H1. destruct (thread_equals t0 thread0) eqn:ORIG. auto. auto.
           ++++ apply ST_synchronize with (event:=event) (e:=e) (thread:=thread0). rewrite H1. rewrite thread_equals_commutative in ORIG. rewrite ORIG. auto. auto. intros. destruct (thread_equals t0 thread) eqn:ORIG1. rewrite thread_equals_true_iff in ORIG1. subst. rewrite ORIG. rewrite H1. assert (thread_equals thread thread = true). apply thread_equals_true_iff. auto. rewrite H3. rewrite H11. rewrite ORIG. auto. rewrite H11. rewrite H1. rewrite ORIG1. auto. 
        +++ apply IHSC_program_steps with (threads:=t) (threads'0:=threads') (thread:=thread). auto. auto. auto. auto. Qed.

Fact steps_read_left : forall l l' threads threads' thread m m' f g e2 ,
SC_program_steps (l, threads, m) (l', threads', m') ->
(forall t, f t = if thread_equals t thread then read (threads t) e2 else threads t) ->
(forall t, g t = if thread_equals t thread then read (threads' t) e2 else threads' t) ->
SC_program_steps (l, f, m) (l', g, m').
Proof. intros. remember (l, threads, m) as p. remember (l', threads', m') as p'. generalize dependent l. generalize dependent l'. generalize dependent m. generalize dependent m'. generalize dependent e2. generalize dependent thread. generalize dependent threads'. generalize dependent threads. generalize dependent f. generalize dependent g. induction H; intros.
  + inversion Heqp. inversion Heqp'. subst. apply SC_program_steps_reflexive. intros. rewrite H0. rewrite H1. rewrite H. auto.
  +  subst. destruct q. destruct p. apply SC_program_steps_transitive with  (l0, fun thread' : bool + unit => if thread_equals thread' thread then read (t thread') e2 else t thread', m0). inversion H; subst.
       +++ apply ST_init_allocate_array. auto. auto. auto. intros. rewrite H1. rewrite H12. auto.
       +++ destruct (thread_equals thread thread0) eqn:ORIG.
           ++++ rewrite thread_equals_true_iff in ORIG. subst. apply ST_synchronize with (event:=event) (e:=read e e2) (thread:=thread0). destruct thread0; simpl.
                +++++ rewrite H1. simpl. rewrite Bool.eqb_reflx. apply step_context with (E:=Cread1 Hole e2). auto.
                +++++ rewrite H1. simpl. apply step_context with (E:=Cread1 Hole e2). auto.
                +++++ auto.
                +++++ intros. rewrite H11. rewrite H1. destruct (thread_equals t0 thread0) eqn:ORIG. auto. auto.
           ++++ apply ST_synchronize with (event:=event) (e:=e) (thread:=thread0). rewrite H1. rewrite thread_equals_commutative in ORIG. rewrite ORIG. auto. auto. intros. destruct (thread_equals t0 thread) eqn:ORIG1. rewrite thread_equals_true_iff in ORIG1. subst. rewrite ORIG. rewrite H1. assert (thread_equals thread thread = true). apply thread_equals_true_iff. auto. rewrite H3. rewrite H11. rewrite ORIG. auto. rewrite H11. rewrite H1. rewrite ORIG1. auto. 
        +++ apply IHSC_program_steps with (threads:=t) (threads'0:=threads') (thread:=thread) (e2:=e2). auto. auto. auto. auto. Qed.


Fact steps_read_right : forall l l' threads threads' thread m m' f g e2,
SC_program_steps (l, threads, m) (l', threads', m') ->
(forall t, f t = if thread_equals t thread then read (array e2) (threads t) else threads t) ->
(forall t, g t = if thread_equals t thread then read (array e2) (threads' t) else threads' t) ->
SC_program_steps (l, f, m) (l', g, m').
Proof. intros. remember (l, threads, m) as p. remember (l', threads', m') as p'. generalize dependent l. generalize dependent l'. generalize dependent m. generalize dependent m'. generalize dependent e2. generalize dependent thread. generalize dependent threads'. generalize dependent threads. generalize dependent f. generalize dependent g. induction H; intros.
  + inversion Heqp. inversion Heqp'. subst. apply SC_program_steps_reflexive. intros. rewrite H0. rewrite H1. rewrite H. auto.
  +  subst. destruct q. destruct p. apply SC_program_steps_transitive with  (l0, fun thread' : bool + unit => if thread_equals thread' thread then read (array e2) (t thread') else t thread', m0). inversion H; subst.
       +++ apply ST_init_allocate_array. auto. auto. auto. intros. rewrite H1. rewrite H12. auto.
       +++ destruct (thread_equals thread thread0) eqn:ORIG.
           ++++ rewrite thread_equals_true_iff in ORIG. subst. apply ST_synchronize with (event:=event) (e:=read (array e2) e) (thread:=thread0). assert (exists e', array e2 = array e'). refine (ex_intro _ e2 _). auto. destruct thread0; simpl.
                +++++ rewrite H1. simpl. rewrite Bool.eqb_reflx. apply step_context with (E:=Cread2 (exist _(array e2) H3) Hole). auto.
                +++++ rewrite H1. simpl. apply step_context with (E:=Cread2 (exist _(array e2) H3) Hole). auto.
                +++++ auto.
                +++++ intros. rewrite H11. rewrite H1. destruct (thread_equals t0 thread0) eqn:ORIG. auto. auto.
           ++++ apply ST_synchronize with (event:=event) (e:=e) (thread:=thread0). rewrite H1. rewrite thread_equals_commutative in ORIG. rewrite ORIG. auto. auto. intros. destruct (thread_equals t0 thread) eqn:ORIG1. rewrite thread_equals_true_iff in ORIG1. subst. rewrite ORIG. rewrite H1. assert (thread_equals thread thread = true). apply thread_equals_true_iff. auto. rewrite H3. rewrite H11. rewrite ORIG. auto. rewrite H11. rewrite H1. rewrite ORIG1. auto. 
        +++ apply IHSC_program_steps with (threads:=t) (threads'0:=threads') (thread:=thread) (e2:=e2). auto. auto. auto. auto. Qed.

Fact steps_paire_left : forall l l' threads threads' thread m m' f g e2 ,
SC_program_steps (l, threads, m) (l', threads', m') ->
(forall t, f t = if thread_equals t thread then paire (threads t) e2 else threads t) ->
(forall t, g t = if thread_equals t thread then paire (threads' t) e2 else threads' t) ->
SC_program_steps (l, f, m) (l', g, m').
Proof. intros. remember (l, threads, m) as p. remember (l', threads', m') as p'. generalize dependent l. generalize dependent l'. generalize dependent m. generalize dependent m'. generalize dependent e2. generalize dependent thread. generalize dependent threads'. generalize dependent threads. generalize dependent f. generalize dependent g. induction H; intros.
  + inversion Heqp. inversion Heqp'. subst. apply SC_program_steps_reflexive. intros. rewrite H0. rewrite H1. rewrite H. auto.
  +  subst. destruct q. destruct p. apply SC_program_steps_transitive with  (l0, fun thread' : bool + unit => if thread_equals thread' thread then paire (t thread') e2 else t thread', m0). inversion H; subst.
       +++ apply ST_init_allocate_array. auto. auto. auto. intros. rewrite H1. rewrite H12. auto.
       +++ destruct (thread_equals thread thread0) eqn:ORIG.
           ++++ rewrite thread_equals_true_iff in ORIG. subst. apply ST_synchronize with (event:=event) (e:=paire e e2) (thread:=thread0). destruct thread0; simpl.
                +++++ rewrite H1. simpl. rewrite Bool.eqb_reflx. apply step_context with (E:=Cpaire1 Hole e2). auto.
                +++++ rewrite H1. simpl. apply step_context with (E:=Cpaire1 Hole e2). auto.
                +++++ auto.
                +++++ intros. rewrite H11. rewrite H1. destruct (thread_equals t0 thread0) eqn:ORIG. auto. auto.
           ++++ apply ST_synchronize with (event:=event) (e:=e) (thread:=thread0). rewrite H1. rewrite thread_equals_commutative in ORIG. rewrite ORIG. auto. auto. intros. destruct (thread_equals t0 thread) eqn:ORIG1. rewrite thread_equals_true_iff in ORIG1. subst. rewrite ORIG. rewrite H1. assert (thread_equals thread thread = true). apply thread_equals_true_iff. auto. rewrite H3. rewrite H11. rewrite ORIG. auto. rewrite H11. rewrite H1. rewrite ORIG1. auto. 
        +++ apply IHSC_program_steps with (threads:=t) (threads'0:=threads') (thread:=thread) (e2:=e2). auto. auto. auto. auto. Qed.


Fact steps_paire_right : forall l l' threads threads' thread m m' f g e2,
SC_program_steps (l, threads, m) (l', threads', m') ->
value e2 ->
(forall t, f t = if thread_equals t thread then paire e2 (threads t) else threads t) ->
(forall t, g t = if thread_equals t thread then paire e2 (threads' t) else threads' t) ->
SC_program_steps (l, f, m) (l', g, m').
Proof. intros. remember (l, threads, m) as p. remember (l', threads', m') as p'. generalize dependent l. generalize dependent l'. generalize dependent m. generalize dependent m'. generalize dependent thread. generalize dependent threads'. generalize dependent threads. generalize dependent f. generalize dependent g. generalize dependent e2. induction H; intros.
  + inversion Heqp. inversion Heqp'. subst. apply SC_program_steps_reflexive. intros. rewrite H1. rewrite H2. rewrite H. auto.
  +  subst. destruct q. destruct p. apply SC_program_steps_transitive with  (l0, fun thread' : bool + unit => if thread_equals thread' thread then paire e2 (t thread') else t thread', m0). inversion H; subst.
       +++ apply ST_init_allocate_array. auto. auto. auto. intros. rewrite H2. rewrite H13. auto.
       +++ destruct (thread_equals thread thread0) eqn:ORIG.
           ++++ rewrite thread_equals_true_iff in ORIG. subst. apply ST_synchronize with (event:=event) (e:=paire e2 e) (thread:=thread0). destruct thread0; simpl.
                +++++ rewrite H2. simpl. rewrite Bool.eqb_reflx. apply step_context with (E:=Cpaire2 (exist _ e2 H1) Hole). auto.
                +++++ rewrite H2. simpl. apply step_context with (E:=Cpaire2 (exist _ e2 H1) Hole). auto.
                +++++ auto.
                +++++ intros. rewrite H12. rewrite H2. destruct (thread_equals t0 thread0) eqn:ORIG. auto. auto.
           ++++ apply ST_synchronize with (event:=event) (e:=e) (thread:=thread0). rewrite H2. rewrite thread_equals_commutative in ORIG. rewrite ORIG. auto. auto. intros. destruct (thread_equals t0 thread) eqn:ORIG1. rewrite thread_equals_true_iff in ORIG1. subst. rewrite ORIG. rewrite H2. assert (thread_equals thread thread = true). apply thread_equals_true_iff. auto. rewrite H4. rewrite H12. rewrite ORIG. auto. rewrite H12. rewrite H2. rewrite ORIG1. auto. 
        +++ apply IHSC_program_steps with (e2:=e2) (threads:=t) (threads'0:=threads') (thread:=thread). auto. auto. auto. auto. auto. Qed.

Fact steps_write_left : forall l l' threads threads' thread m m' f g e2 e3,
SC_program_steps (l, threads, m) (l', threads', m') ->
(forall t, f t = if thread_equals t thread then write (threads t) e2 e3 else threads t) ->
(forall t, g t = if thread_equals t thread then write (threads' t) e2 e3 else threads' t) ->
SC_program_steps (l, f, m) (l', g, m').
Proof. intros. remember (l, threads, m) as p. remember (l', threads', m') as p'. generalize dependent l. generalize dependent l'. generalize dependent m. generalize dependent m'. generalize dependent e2. generalize dependent e3. generalize dependent thread. generalize dependent threads'. generalize dependent threads. generalize dependent f. generalize dependent g. induction H; intros.
  + inversion Heqp. inversion Heqp'. subst. apply SC_program_steps_reflexive. intros. rewrite H0. rewrite H1. rewrite H. auto.
  +  subst. destruct q. destruct p. apply SC_program_steps_transitive with  (l0, fun thread' : bool + unit => if thread_equals thread' thread then write (t thread') e2 e3 else t thread', m0). inversion H; subst.
       +++ apply ST_init_allocate_array. auto. auto. auto. intros. rewrite H1. rewrite H12. auto.
       +++ destruct (thread_equals thread thread0) eqn:ORIG.
           ++++ rewrite thread_equals_true_iff in ORIG. subst. apply ST_synchronize with (event:=event) (e:=write e e2 e3) (thread:=thread0). destruct thread0; simpl.
                +++++ rewrite H1. simpl. rewrite Bool.eqb_reflx. apply step_context with (E:=Cwrite1 Hole e2 e3). auto.
                +++++ rewrite H1. simpl. apply step_context with (E:=Cwrite1 Hole e2 e3). auto.
                +++++ auto.
                +++++ intros. rewrite H11. rewrite H1. destruct (thread_equals t0 thread0) eqn:ORIG. auto. auto.
           ++++ apply ST_synchronize with (event:=event) (e:=e) (thread:=thread0). rewrite H1. rewrite thread_equals_commutative in ORIG. rewrite ORIG. auto. auto. intros. destruct (thread_equals t0 thread) eqn:ORIG1. rewrite thread_equals_true_iff in ORIG1. subst. rewrite ORIG. rewrite H1. assert (thread_equals thread thread = true). apply thread_equals_true_iff. auto. rewrite H3. rewrite H11. rewrite ORIG. auto. rewrite H11. rewrite H1. rewrite ORIG1. auto. 
        +++ apply IHSC_program_steps with (threads:=t) (threads'0:=threads') (thread:=thread) (e2:=e2) (e3:=e3). auto. auto. auto. auto. Qed.


Fact steps_write_middle : forall l l' threads threads' thread m m' f g e2 e3,
SC_program_steps (l, threads, m) (l', threads', m') ->
(forall t, f t = if thread_equals t thread then write (array e2) (threads t) e3 else threads t) ->
(forall t, g t = if thread_equals t thread then write (array e2) (threads' t) e3 else threads' t) ->
SC_program_steps (l, f, m) (l', g, m').
Proof. intros. remember (l, threads, m) as p. remember (l', threads', m') as p'. generalize dependent l. generalize dependent l'. generalize dependent m. generalize dependent m'. generalize dependent e2. generalize dependent e3. generalize dependent thread. generalize dependent threads'. generalize dependent threads. generalize dependent f. generalize dependent g. induction H; intros.
  + inversion Heqp. inversion Heqp'. subst. apply SC_program_steps_reflexive. intros. rewrite H0. rewrite H1. rewrite H. auto.
  +  subst. destruct q. destruct p. apply SC_program_steps_transitive with  (l0, fun thread' : bool + unit => if thread_equals thread' thread then write (array e2) (t thread') e3 else t thread', m0). inversion H; subst.
       +++ apply ST_init_allocate_array. auto. auto. auto. intros. rewrite H1. rewrite H12. auto.
       +++ destruct (thread_equals thread thread0) eqn:ORIG.
           ++++ rewrite thread_equals_true_iff in ORIG. subst. apply ST_synchronize with (event:=event) (e:=write (array e2) e e3) (thread:=thread0). assert (exists e', array e2 = array e'). refine (ex_intro _ e2 _). auto. destruct thread0; simpl.
                +++++ rewrite H1. simpl. rewrite Bool.eqb_reflx. apply step_context with (E:=Cwrite2 (exist _(array e2) H3) Hole e3). auto.
                +++++ rewrite H1. simpl. apply step_context with (E:=Cwrite2 (exist _(array e2) H3) Hole e3). auto.
                +++++ auto.
                +++++ intros. rewrite H11. rewrite H1. destruct (thread_equals t0 thread0) eqn:ORIG. auto. auto.
           ++++ apply ST_synchronize with (event:=event) (e:=e) (thread:=thread0). rewrite H1. rewrite thread_equals_commutative in ORIG. rewrite ORIG. auto. auto. intros. destruct (thread_equals t0 thread) eqn:ORIG1. rewrite thread_equals_true_iff in ORIG1. subst. rewrite ORIG. rewrite H1. assert (thread_equals thread thread = true). apply thread_equals_true_iff. auto. rewrite H3. rewrite H11. rewrite ORIG. auto. rewrite H11. rewrite H1. rewrite ORIG1. auto. 
        +++ apply IHSC_program_steps with (threads:=t) (threads'0:=threads') (thread:=thread) (e2:=e2) (e3:=e3). auto. auto. auto. auto. Qed.

Fact steps_write_right : forall l l' threads threads' thread m m' f g e2 e3,
SC_program_steps (l, threads, m) (l', threads', m') ->
(forall t, f t = if thread_equals t thread then write (array e2) (num e3) (threads t) else threads t) ->
(forall t, g t = if thread_equals t thread then write (array e2) (num e3) (threads' t) else threads' t) ->
SC_program_steps (l, f, m) (l', g, m').
Proof. intros. remember (l, threads, m) as p. remember (l', threads', m') as p'. generalize dependent l. generalize dependent l'. generalize dependent m. generalize dependent m'. generalize dependent e2. generalize dependent e3. generalize dependent thread. generalize dependent threads'. generalize dependent threads. generalize dependent f. generalize dependent g. induction H; intros.
  + inversion Heqp. inversion Heqp'. subst. apply SC_program_steps_reflexive. intros. rewrite H0. rewrite H1. rewrite H. auto.
  +  subst. destruct q. destruct p. apply SC_program_steps_transitive with  (l0, fun thread' : bool + unit => if thread_equals thread' thread then write (array e2) (num e3) (t thread') else t thread', m0). inversion H; subst.
       +++ apply ST_init_allocate_array. auto. auto. auto. intros. rewrite H1. rewrite H12. auto.
       +++ destruct (thread_equals thread thread0) eqn:ORIG.
           ++++ rewrite thread_equals_true_iff in ORIG. subst. apply ST_synchronize with (event:=event) (e:=write (array e2) (num e3) e) (thread:=thread0). assert (exists e', array e2 = array e'). refine (ex_intro _ e2 _). auto. assert (exists e', num e3 = num e'). refine (ex_intro _ e3 _). auto. destruct thread0; simpl. auto.
                +++++ rewrite H1. simpl. rewrite Bool.eqb_reflx. apply step_context with (E:=Cwrite3 (exist _(array e2) H3) (exist _ (num e3) H4) Hole). auto.
                +++++ rewrite H1. simpl. apply step_context with (E:=Cwrite3 (exist _(array e2) H3) (exist _ (num e3) H4) Hole). auto.
                +++++ auto.
                +++++ intros. rewrite H11. rewrite H1. destruct (thread_equals t0 thread0) eqn:ORIG. auto. auto.
           ++++ apply ST_synchronize with (event:=event) (e:=e) (thread:=thread0). rewrite H1. rewrite thread_equals_commutative in ORIG. rewrite ORIG. auto. auto. intros. destruct (thread_equals t0 thread) eqn:ORIG1. rewrite thread_equals_true_iff in ORIG1. subst. rewrite ORIG. rewrite H1. assert (thread_equals thread thread = true). apply thread_equals_true_iff. auto. rewrite H3. rewrite H11. rewrite ORIG. auto. rewrite H11. rewrite H1. rewrite ORIG1. auto. 
        +++ apply IHSC_program_steps with (threads:=t) (threads'0:=threads') (thread:=thread) (e2:=e2) (e3:=e3). auto. auto. auto. auto. Qed.

Fact steps_case_left : forall l l' threads threads' thread m m' f g e2 e3,
SC_program_steps (l, threads, m) (l', threads', m') ->
(forall t, f t = if thread_equals t thread then case (threads t) e2 e3 else threads t) ->
(forall t, g t = if thread_equals t thread then case (threads' t) e2 e3 else threads' t) ->
SC_program_steps (l, f, m) (l', g, m').
Proof. intros. remember (l, threads, m) as p. remember (l', threads', m') as p'. generalize dependent l. generalize dependent l'. generalize dependent m. generalize dependent m'. generalize dependent e2. generalize dependent e3. generalize dependent thread. generalize dependent threads'. generalize dependent threads. generalize dependent f. generalize dependent g. induction H; intros.
  + inversion Heqp. inversion Heqp'. subst. apply SC_program_steps_reflexive. intros. rewrite H0. rewrite H1. rewrite H. auto.
  +  subst. destruct q. destruct p. apply SC_program_steps_transitive with  (l0, fun thread' : bool + unit => if thread_equals thread' thread then case (t thread') e2 e3 else t thread', m0). inversion H; subst.
       +++ apply ST_init_allocate_array. auto. auto. auto. intros. rewrite H1. rewrite H12. auto.
       +++ destruct (thread_equals thread thread0) eqn:ORIG.
           ++++ rewrite thread_equals_true_iff in ORIG. subst. apply ST_synchronize with (event:=event) (e:=case e e2 e3) (thread:=thread0). destruct thread0; simpl.
                +++++ rewrite H1. simpl. rewrite Bool.eqb_reflx. apply step_context with (E:=Ccase Hole e2 e3). auto.
                +++++ rewrite H1. simpl. apply step_context with (E:=Ccase Hole e2 e3). auto.
                +++++ auto.
                +++++ intros. rewrite H11. rewrite H1. destruct (thread_equals t0 thread0) eqn:ORIG. auto. auto.
           ++++ apply ST_synchronize with (event:=event) (e:=e) (thread:=thread0). rewrite H1. rewrite thread_equals_commutative in ORIG. rewrite ORIG. auto. auto. intros. destruct (thread_equals t0 thread) eqn:ORIG1. rewrite thread_equals_true_iff in ORIG1. subst. rewrite ORIG. rewrite H1. assert (thread_equals thread thread = true). apply thread_equals_true_iff. auto. rewrite H3. rewrite H11. rewrite ORIG. auto. rewrite H11. rewrite H1. rewrite ORIG1. auto. 
        +++ apply IHSC_program_steps with (threads:=t) (threads'0:=threads') (thread:=thread) (e2:=e2) (e3:=e3). auto. auto. auto. auto. Qed.

Fact steps_not_left : forall l l' threads threads' thread m m' f g ,
SC_program_steps (l, threads, m) (l', threads', m') ->
(forall t, f t = if thread_equals t thread then not (threads t) else threads t) ->
(forall t, g t = if thread_equals t thread then not (threads' t) else threads' t) ->
SC_program_steps (l, f, m) (l', g, m').
Proof. intros. remember (l, threads, m) as p. remember (l', threads', m') as p'. generalize dependent l. generalize dependent l'. generalize dependent m. generalize dependent m'. generalize dependent thread. generalize dependent threads'. generalize dependent threads. generalize dependent f. generalize dependent g. induction H; intros.
  + inversion Heqp. inversion Heqp'. subst. apply SC_program_steps_reflexive. intros. rewrite H0. rewrite H1. rewrite H. auto.
  +  subst. destruct q. destruct p. apply SC_program_steps_transitive with  (l0, fun thread' : bool + unit => if thread_equals thread' thread then not (t thread') else t thread', m0). inversion H; subst.
       +++ apply ST_init_allocate_array. auto. auto. auto. intros. rewrite H1. rewrite H12. auto.
       +++ destruct (thread_equals thread thread0) eqn:ORIG.
           ++++ rewrite thread_equals_true_iff in ORIG. subst. apply ST_synchronize with (event:=event) (e:=not e) (thread:=thread0). destruct thread0; simpl.
                +++++ rewrite H1. simpl. rewrite Bool.eqb_reflx. apply step_context with (E:=Cnot Hole). auto.
                +++++ rewrite H1. simpl. apply step_context with (E:=Cnot Hole). auto.
                +++++ auto.
                +++++ intros. rewrite H11. rewrite H1. destruct (thread_equals t0 thread0) eqn:ORIG. auto. auto.
           ++++ apply ST_synchronize with (event:=event) (e:=e) (thread:=thread0). rewrite H1. rewrite thread_equals_commutative in ORIG. rewrite ORIG. auto. auto. intros. destruct (thread_equals t0 thread) eqn:ORIG1. rewrite thread_equals_true_iff in ORIG1. subst. rewrite ORIG. rewrite H1. assert (thread_equals thread thread = true). apply thread_equals_true_iff. auto. rewrite H3. rewrite H11. rewrite ORIG. auto. rewrite H11. rewrite H1. rewrite ORIG1. auto. 
        +++ apply IHSC_program_steps with (threads:=t) (threads'0:=threads') (thread:=thread). auto. auto. auto. auto. Qed.


Fact steps_reference_left : forall l l' threads threads' thread m m' f g ,
SC_program_steps (l, threads, m) (l', threads', m') ->
(forall t, f t = if thread_equals t thread then reference (threads t) else threads t) ->
(forall t, g t = if thread_equals t thread then reference (threads' t) else threads' t) ->
SC_program_steps (l, f, m) (l', g, m').
Proof. intros. remember (l, threads, m) as p. remember (l', threads', m') as p'. generalize dependent l. generalize dependent l'. generalize dependent m. generalize dependent m'. generalize dependent thread. generalize dependent threads'. generalize dependent threads. generalize dependent f. generalize dependent g. induction H; intros.
  + inversion Heqp. inversion Heqp'. subst. apply SC_program_steps_reflexive. intros. rewrite H0. rewrite H1. rewrite H. auto.
  +  subst. destruct q. destruct p. apply SC_program_steps_transitive with  (l0, fun thread' : bool + unit => if thread_equals thread' thread then reference (t thread') else t thread', m0). inversion H; subst.
       +++ apply ST_init_allocate_array. auto. auto. auto. intros. rewrite H1. rewrite H12. auto.
       +++ destruct (thread_equals thread thread0) eqn:ORIG.
           ++++ rewrite thread_equals_true_iff in ORIG. subst. apply ST_synchronize with (event:=event) (e:=reference e) (thread:=thread0). destruct thread0; simpl.
                +++++ rewrite H1. simpl. rewrite Bool.eqb_reflx. apply step_context with (E:=Creference Hole). auto.
                +++++ rewrite H1. simpl. apply step_context with (E:=Creference Hole). auto.
                +++++ auto.
                +++++ intros. rewrite H11. rewrite H1. destruct (thread_equals t0 thread0) eqn:ORIG. auto. auto.
           ++++ apply ST_synchronize with (event:=event) (e:=e) (thread:=thread0). rewrite H1. rewrite thread_equals_commutative in ORIG. rewrite ORIG. auto. auto. intros. destruct (thread_equals t0 thread) eqn:ORIG1. rewrite thread_equals_true_iff in ORIG1. subst. rewrite ORIG. rewrite H1. assert (thread_equals thread thread = true). apply thread_equals_true_iff. auto. rewrite H3. rewrite H11. rewrite ORIG. auto. rewrite H11. rewrite H1. rewrite ORIG1. auto. 
        +++ apply IHSC_program_steps with (threads:=t) (threads'0:=threads') (thread:=thread). auto. auto. auto. auto. Qed.

Fact steps_cast_left : forall l l' threads threads' thread m m' f g ,
SC_program_steps (l, threads, m) (l', threads', m') ->
(forall t, f t = if thread_equals t thread then cast (threads t) else threads t) ->
(forall t, g t = if thread_equals t thread then cast (threads' t) else threads' t) ->
SC_program_steps (l, f, m) (l', g, m').
Proof. intros. remember (l, threads, m) as p. remember (l', threads', m') as p'. generalize dependent l. generalize dependent l'. generalize dependent m. generalize dependent m'. generalize dependent thread. generalize dependent threads'. generalize dependent threads. generalize dependent f. generalize dependent g. induction H; intros.
  + inversion Heqp. inversion Heqp'. subst. apply SC_program_steps_reflexive. intros. rewrite H0. rewrite H1. rewrite H. auto.
  +  subst. destruct q. destruct p. apply SC_program_steps_transitive with  (l0, fun thread' : bool + unit => if thread_equals thread' thread then cast (t thread') else t thread', m0). inversion H; subst.
       +++ apply ST_init_allocate_array. auto. auto. auto. intros. rewrite H1. rewrite H12. auto.
       +++ destruct (thread_equals thread thread0) eqn:ORIG.
           ++++ rewrite thread_equals_true_iff in ORIG. subst. apply ST_synchronize with (event:=event) (e:=cast e) (thread:=thread0). destruct thread0; simpl.
                +++++ rewrite H1. simpl. rewrite Bool.eqb_reflx. apply step_context with (E:=Ccast Hole). auto.
                +++++ rewrite H1. simpl. apply step_context with (E:=Ccast Hole). auto.
                +++++ auto.
                +++++ intros. rewrite H11. rewrite H1. destruct (thread_equals t0 thread0) eqn:ORIG. auto. auto.
           ++++ apply ST_synchronize with (event:=event) (e:=e) (thread:=thread0). rewrite H1. rewrite thread_equals_commutative in ORIG. rewrite ORIG. auto. auto. intros. destruct (thread_equals t0 thread) eqn:ORIG1. rewrite thread_equals_true_iff in ORIG1. subst. rewrite ORIG. rewrite H1. assert (thread_equals thread thread = true). apply thread_equals_true_iff. auto. rewrite H3. rewrite H11. rewrite ORIG. auto. rewrite H11. rewrite H1. rewrite ORIG1. auto. 
        +++ apply IHSC_program_steps with (threads:=t) (threads'0:=threads') (thread:=thread). auto. auto. auto. auto. Qed.

Fact steps_first_left : forall l l' threads threads' thread m m' f g ,
SC_program_steps (l, threads, m) (l', threads', m') ->
(forall t, f t = if thread_equals t thread then first (threads t) else threads t) ->
(forall t, g t = if thread_equals t thread then first (threads' t) else threads' t) ->
SC_program_steps (l, f, m) (l', g, m').
Proof. intros. remember (l, threads, m) as p. remember (l', threads', m') as p'. generalize dependent l. generalize dependent l'. generalize dependent m. generalize dependent m'. generalize dependent thread. generalize dependent threads'. generalize dependent threads. generalize dependent f. generalize dependent g. induction H; intros.
  + inversion Heqp. inversion Heqp'. subst. apply SC_program_steps_reflexive. intros. rewrite H0. rewrite H1. rewrite H. auto.
  +  subst. destruct q. destruct p. apply SC_program_steps_transitive with  (l0, fun thread' : bool + unit => if thread_equals thread' thread then first (t thread') else t thread', m0). inversion H; subst.
       +++ apply ST_init_allocate_array. auto. auto. auto. intros. rewrite H1. rewrite H12. auto.
       +++ destruct (thread_equals thread thread0) eqn:ORIG.
           ++++ rewrite thread_equals_true_iff in ORIG. subst. apply ST_synchronize with (event:=event) (e:=first e) (thread:=thread0). destruct thread0; simpl.
                +++++ rewrite H1. simpl. rewrite Bool.eqb_reflx. apply step_context with (E:=Cfirst Hole). auto.
                +++++ rewrite H1. simpl. apply step_context with (E:=Cfirst Hole). auto.
                +++++ auto.
                +++++ intros. rewrite H11. rewrite H1. destruct (thread_equals t0 thread0) eqn:ORIG. auto. auto.
           ++++ apply ST_synchronize with (event:=event) (e:=e) (thread:=thread0). rewrite H1. rewrite thread_equals_commutative in ORIG. rewrite ORIG. auto. auto. intros. destruct (thread_equals t0 thread) eqn:ORIG1. rewrite thread_equals_true_iff in ORIG1. subst. rewrite ORIG. rewrite H1. assert (thread_equals thread thread = true). apply thread_equals_true_iff. auto. rewrite H3. rewrite H11. rewrite ORIG. auto. rewrite H11. rewrite H1. rewrite ORIG1. auto. 
        +++ apply IHSC_program_steps with (threads:=t) (threads'0:=threads') (thread:=thread). auto. auto. auto. auto. Qed.

Fact steps_second_left : forall l l' threads threads' thread m m' f g ,
SC_program_steps (l, threads, m) (l', threads', m') ->
(forall t, f t = if thread_equals t thread then second (threads t) else threads t) ->
(forall t, g t = if thread_equals t thread then second (threads' t) else threads' t) ->
SC_program_steps (l, f, m) (l', g, m').
Proof. intros. remember (l, threads, m) as p. remember (l', threads', m') as p'. generalize dependent l. generalize dependent l'. generalize dependent m. generalize dependent m'. generalize dependent thread. generalize dependent threads'. generalize dependent threads. generalize dependent f. generalize dependent g. induction H; intros.
  + inversion Heqp. inversion Heqp'. subst. apply SC_program_steps_reflexive. intros. rewrite H0. rewrite H1. rewrite H. auto.
  +  subst. destruct q. destruct p. apply SC_program_steps_transitive with  (l0, fun thread' : bool + unit => if thread_equals thread' thread then second (t thread') else t thread', m0). inversion H; subst.
       +++ apply ST_init_allocate_array. auto. auto. auto. intros. rewrite H1. rewrite H12. auto.
       +++ destruct (thread_equals thread thread0) eqn:ORIG.
           ++++ rewrite thread_equals_true_iff in ORIG. subst. apply ST_synchronize with (event:=event) (e:=second e) (thread:=thread0). destruct thread0; simpl.
                +++++ rewrite H1. simpl. rewrite Bool.eqb_reflx. apply step_context with (E:=Csecond Hole). auto.
                +++++ rewrite H1. simpl. apply step_context with (E:=Csecond Hole). auto.
                +++++ auto.
                +++++ intros. rewrite H11. rewrite H1. destruct (thread_equals t0 thread0) eqn:ORIG. auto. auto.
           ++++ apply ST_synchronize with (event:=event) (e:=e) (thread:=thread0). rewrite H1. rewrite thread_equals_commutative in ORIG. rewrite ORIG. auto. auto. intros. destruct (thread_equals t0 thread) eqn:ORIG1. rewrite thread_equals_true_iff in ORIG1. subst. rewrite ORIG. rewrite H1. assert (thread_equals thread thread = true). apply thread_equals_true_iff. auto. rewrite H3. rewrite H11. rewrite ORIG. auto. rewrite H11. rewrite H1. rewrite ORIG1. auto. 
        +++ apply IHSC_program_steps with (threads:=t) (threads'0:=threads') (thread:=thread). auto. auto. auto. auto. Qed.

Fact steps_lock_left : forall l l' threads threads' thread m m' f g ,
SC_program_steps (l, threads, m) (l', threads', m') ->
(forall t, f t = if thread_equals t thread then lock (threads t) else threads t) ->
(forall t, g t = if thread_equals t thread then lock (threads' t) else threads' t) ->
SC_program_steps (l, f, m) (l', g, m').
Proof. intros. remember (l, threads, m) as p. remember (l', threads', m') as p'. generalize dependent l. generalize dependent l'. generalize dependent m. generalize dependent m'. generalize dependent thread. generalize dependent threads'. generalize dependent threads. generalize dependent f. generalize dependent g. induction H; intros.
  + inversion Heqp. inversion Heqp'. subst. apply SC_program_steps_reflexive. intros. rewrite H0. rewrite H1. rewrite H. auto.
  +  subst. destruct q. destruct p. apply SC_program_steps_transitive with  (l0, fun thread' : bool + unit => if thread_equals thread' thread then lock (t thread') else t thread', m0). inversion H; subst.
       +++ apply ST_init_allocate_array. auto. auto. auto. intros. rewrite H1. rewrite H12. auto.
       +++ destruct (thread_equals thread thread0) eqn:ORIG.
           ++++ rewrite thread_equals_true_iff in ORIG. subst. apply ST_synchronize with (event:=event) (e:=lock e) (thread:=thread0). destruct thread0; simpl.
                +++++ rewrite H1. simpl. rewrite Bool.eqb_reflx. apply step_context with (E:=Clock Hole). auto.
                +++++ rewrite H1. simpl. apply step_context with (E:=Clock Hole). auto.
                +++++ auto.
                +++++ intros. rewrite H11. rewrite H1. destruct (thread_equals t0 thread0) eqn:ORIG. auto. auto.
           ++++ apply ST_synchronize with (event:=event) (e:=e) (thread:=thread0). rewrite H1. rewrite thread_equals_commutative in ORIG. rewrite ORIG. auto. auto. intros. destruct (thread_equals t0 thread) eqn:ORIG1. rewrite thread_equals_true_iff in ORIG1. subst. rewrite ORIG. rewrite H1. assert (thread_equals thread thread = true). apply thread_equals_true_iff. auto. rewrite H3. rewrite H11. rewrite ORIG. auto. rewrite H11. rewrite H1. rewrite ORIG1. auto. 
        +++ apply IHSC_program_steps with (threads:=t) (threads'0:=threads') (thread:=thread). auto. auto. auto. auto. Qed.

Fact steps_unlock_left : forall l l' threads threads' thread m m' f g ,
SC_program_steps (l, threads, m) (l', threads', m') ->
(forall t, f t = if thread_equals t thread then unlock (threads t) else threads t) ->
(forall t, g t = if thread_equals t thread then unlock (threads' t) else threads' t) ->
SC_program_steps (l, f, m) (l', g, m').
Proof. intros. remember (l, threads, m) as p. remember (l', threads', m') as p'. generalize dependent l. generalize dependent l'. generalize dependent m. generalize dependent m'. generalize dependent thread. generalize dependent threads'. generalize dependent threads. generalize dependent f. generalize dependent g. induction H; intros.
  + inversion Heqp. inversion Heqp'. subst. apply SC_program_steps_reflexive. intros. rewrite H0. rewrite H1. rewrite H. auto.
  +  subst. destruct q. destruct p. apply SC_program_steps_transitive with  (l0, fun thread' : bool + unit => if thread_equals thread' thread then unlock (t thread') else t thread', m0). inversion H; subst.
       +++ apply ST_init_allocate_array. auto. auto. auto. intros. rewrite H1. rewrite H12. auto.
       +++ destruct (thread_equals thread thread0) eqn:ORIG.
           ++++ rewrite thread_equals_true_iff in ORIG. subst. apply ST_synchronize with (event:=event) (e:=unlock e) (thread:=thread0). destruct thread0; simpl.
                +++++ rewrite H1. simpl. rewrite Bool.eqb_reflx. apply step_context with (E:=Cunlock Hole). auto.
                +++++ rewrite H1. simpl. apply step_context with (E:=Cunlock Hole). auto.
                +++++ auto.
                +++++ intros. rewrite H11. rewrite H1. destruct (thread_equals t0 thread0) eqn:ORIG. auto. auto.
           ++++ apply ST_synchronize with (event:=event) (e:=e) (thread:=thread0). rewrite H1. rewrite thread_equals_commutative in ORIG. rewrite ORIG. auto. auto. intros. destruct (thread_equals t0 thread) eqn:ORIG1. rewrite thread_equals_true_iff in ORIG1. subst. rewrite ORIG. rewrite H1. assert (thread_equals thread thread = true). apply thread_equals_true_iff. auto. rewrite H3. rewrite H11. rewrite ORIG. auto. rewrite H11. rewrite H1. rewrite ORIG1. auto. 
        +++ apply IHSC_program_steps with (threads:=t) (threads'0:=threads') (thread:=thread). auto. auto. auto. auto. Qed.
