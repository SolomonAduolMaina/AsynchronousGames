Require Import List.
Require Import ZArith.
Require Import Lia.
Require Import Init.Nat.
Require Import Logic.Eqdep.
Require Import Logic.Eqdep_dec.
Require Import Arith.PeanoNat.
Require Import Bool.Bool.
Require Import AsynchronousGames.
Require Import Lifting.

Inductive leq_sum (P Q : PartialOrder) :
{i : I P + I Q & (sum unit (match i with
                            | inl i => N P i
                            | inr j => N Q j
                            end))} ->
{i : I P + I Q & (sum unit (match i with
                            | inl i => N P i
                            | inr j => N Q j
                            end))} ->
Prop :=
| leq_sum_left : forall i m m' a b,
leq P (existT _ i m) (existT _ i m') ->
a = (existT _ (inl i) m) ->
b = (existT _ (inl i) m') ->
leq_sum P Q a b
| leq_sum_right : forall i m m' a b,
leq Q (existT _ i m) (existT _ i m') ->
a = (existT _ (inr i) m) ->
b = (existT _ (inr i) m') ->
leq_sum P Q a b.

Definition partial_order_sum (P Q : PartialOrder) : PartialOrder.
  refine({| 
            I := (I P) + (I Q);
            N i := match i with
                      | inl i => N P i
                      | inr j => N Q j
                   end;
            leq := leq_sum P Q;
         |}).
Proof. 
- intros. destruct x. destruct x. 
+ apply leq_sum_left with (i:=i) (m:=s) (m':=s).
++ apply reflexive.
++ auto.
++ auto.
+ apply leq_sum_right with (i:=i) (m:=s) (m':=s).
++ apply reflexive.
++ auto.
++ auto.
- intros. destruct x. destruct y. destruct x.
+ destruct x0.
++ destruct H. inversion H.
+++ subst. inversion H3. subst. apply inj_pairT2 in H3. subst.
inversion H2. subst. apply inj_pairT2 in H2. subst. inversion H0.
++++ subst. inversion H4. subst. apply inj_pairT2 in H4. subst.
inversion H3. subst. apply inj_pairT2 in H3. subst.
assert ((existT (fun i : I P => (unit + N P i)%type) i m'0)
= (existT (fun i : I P => (unit + N P i)%type) i m0)).
{apply anti_symmetric. auto. } apply inj_pairT2 in H3. subst. auto.
++++ subst. inversion H4.
+++ subst. inversion H3.
++ destruct H. inversion H.
+++ subst. inversion H3.
+++ subst. inversion H2.
+ destruct H. destruct x0.
++ inversion H.
+++ subst. inversion H2.
+++ subst. inversion H3.
++ inversion H.
+++ subst. inversion H3.
+++ subst. inversion H3. subst. apply inj_pairT2 in H3. subst.
inversion H2. subst. apply inj_pairT2 in H2. subst. inversion H0.
++++ subst. inversion H4.
++++ subst. inversion H4. subst. apply inj_pairT2 in H4. subst.
inversion H3. subst. apply inj_pairT2 in H3. subst.
assert ((existT (fun i : I Q => (unit + N Q i)%type) i m0)
        = (existT (fun i : I Q => (unit + N Q i)%type) i m'0)).
{apply anti_symmetric. auto. }
apply inj_pairT2 in H3. subst. auto.
- intros. destruct x. destruct y. destruct z. destruct H. inversion H.
+ subst. inversion H3. subst. apply inj_pairT2 in H3. subst.
inversion H2. subst. apply inj_pairT2 in H2. subst. inversion H0.
++ subst. inversion H4. subst. apply inj_pairT2 in H4. subst. 
inversion H3. subst. apply inj_pairT2 in H3. subst.
assert (leq P (existT (fun i : I P => (unit + N P i)%type) i0 m)
       (existT (fun i : I P => (unit + N P i)%type) i0 m'0)).
{apply transitive with (y:=(existT (fun i : I P => (unit + N P i)%type) i0 m0)). auto. }
apply leq_sum_left with (i:=i0) (m:=m) (m':=m'0). auto. auto. auto.
++ subst. inversion H3. 
+ subst. inversion H3. subst. apply inj_pairT2 in H3. subst.
inversion H2. subst. apply inj_pairT2 in H2. subst. inversion H0.
++ subst. inversion H3.
++ subst. inversion H3. subst. apply inj_pairT2 in H3. subst. inversion H4. subst.
apply inj_pairT2 in H4. subst.
assert ( leq Q (existT (fun i : I Q => (unit + N Q i)%type) i0 m)
       (existT (fun i : I Q => (unit + N Q i)%type) i0 m'0)).
{apply transitive with (y:=(existT (fun i : I Q => (unit + N Q i)%type) i0 m0)). auto. }
apply leq_sum_right with (i:=i0) (m:=m) (m':=m'0). auto. auto. auto.
- intros. unfold iff. split.
+ intros. inversion H. 
++ subst. inversion H1. inversion H2. auto.
++ subst. inversion H1. inversion H2. auto.
+ intros. subst. destruct i'.
++ apply leq_sum_left with (i:=i) (m:=inl tt) (m':=m).
+++ apply unit_is_least. auto.
+++ auto.
+++ auto.
++ apply leq_sum_right with (i:=i) (m:=inl tt) (m':=m).
+++ apply unit_is_least. auto.
+++ auto.
+++ auto.
- intros. inversion H.
+ subst. inversion H1. inversion H2. subst. auto.
+ subst. inversion H1. inversion H2. subst. auto.
Defined.

Inductive incompatible_sum (E F : EventStructure) :
(M (partial_order_sum (P E) (P F))) ->
(M (partial_order_sum (P E) (P F))) ->
Prop :=
| incomp_sum_least : forall i i' m m',
(i <> i') ->
incompatible_sum E F (existT _ i m) (existT _ i' m')
| incomp_sum_left : forall i m m' a b,
incompatible E (existT _ i m) (existT _ i m') ->
a = (existT _ (inl i) m) ->
b = (existT _ (inl i) m') ->
incompatible_sum E F a b
| incomp_sum_right : forall i m m' a b,
incompatible F (existT _ i m) (existT _ i m') ->
a = (existT _ (inr i) m) ->
b = (existT _ (inr i) m') ->
incompatible_sum E F a b.

Ltac flatten_all :=
  repeat (let e := fresh "e" in
      match goal with
      | h: context[match ?x with | _ => _ end] |- _ => destruct x eqn:e
      | |- context[match ?x with | _ => _ end] => destruct x eqn:e
      end).

Definition event_structure_sum (E F : EventStructure) : EventStructure.
  refine({| 
            P := partial_order_sum (P E) (P F);
            incompatible := incompatible_sum E F;
            ideal m := match m with
                      | existT _ (inl i) m =>
                      map (fun x => match x with
                                    | existT _ i (inl tt) => existT _ (inl i) (inl tt)
                                    | existT _ i (inr m) => existT _ (inl i) (inr m)
                      end) (ideal E (existT _ i m))
                      | existT _ (inr i) m =>
                      map (fun x => match x with
                                    | existT _ i (inl tt) => existT _ (inr i) (inl tt)
                                    | existT _ i (inr m) => existT _ (inr i) (inr m)
                      end) (ideal F (existT _ i m))
                      end;
         |}).
Proof.
- intros. inversion H.
+ subst. apply incomp_sum_least. auto.
+ subst. inversion H.
++ subst. contradiction H2. auto.
++ subst. inversion H2. subst. apply inj_pairT2 in H2. subst.
apply inj_pairT2 in H3. subst. 
apply incomp_sum_left with (m:=m'0) (m':=m0).
+++ apply symmetric. auto.
+++ auto.
+++ auto.
++ subst. inversion H3.
+ subst. apply incomp_sum_right with (m:=m') (m':=m).
++ apply symmetric. auto.
++ auto.
++ auto.
- unfold not. intros. inversion H.
+ subst. contradiction H2. auto.
+ subst. apply inj_pairT2 in H2. subst.
assert (~ incompatible E
       (existT (fun i : I (P E) => (unit + N (P E) i)%type) i
          m')
       (existT (fun i : I (P E) => (unit + N (P E) i)%type) i
          m')).
{apply irreflexive. } contradiction H1.
+ subst. apply inj_pairT2 in H2. subst.
assert (~ incompatible F
       (existT (fun i : I (P F) => (unit + N (P F) i)%type) i
          m')
       (existT (fun i : I (P F) => (unit + N (P F) i)%type) i
          m')).
{apply irreflexive. } contradiction H1.
- intros. simpl. flatten_all.
+ subst. unfold iff. split.
++ intros. inversion H.
+++ subst. destruct m.
++++ destruct m'.
+++++ apply in_map_iff.
refine (ex_intro _ (existT _ i0 (inl tt)) _). split.
++++++ destruct u. auto.
++++++ inversion H2. subst. apply inj_pairT2 in H2. subst.
apply ideal_finite. destruct u. destruct u0. auto.
+++++ inversion H2. subst. apply inj_pairT2 in H2. subst.
apply in_map_iff.
refine (ex_intro _ (existT _ i0 (inl tt)) _). split.
++++++ destruct u. auto.
++++++ apply ideal_finite. destruct u. auto.
++++ inversion H2. subst. apply inj_pairT2 in H2. subst.
apply in_map_iff.
refine (ex_intro _ (existT _ i0 (inr n)) _). split.
+++++ auto.
+++++ apply ideal_finite. auto.
+++ subst. inversion H2.
++ intros. apply in_map_iff in H. destruct H. destruct H.
subst. destruct x. apply ideal_finite in H0.
assert (H1 := H0). apply leq_same_component in H0. subst. destruct s0.
+++ destruct u. apply leq_sum_left with (i:=i) (m:=inl tt) (m':=s).
++++ apply unit_is_least. auto.
++++ auto.
++++ auto.
+++ apply leq_sum_left with (i:=i) (m:=inr n) (m':=s).
++++ auto.
++++ auto.
++++ auto.
+ subst. unfold iff. split.
++ intros. inversion H.
+++ subst. inversion H2.
+++ subst. inversion H2. subst. apply inj_pairT2 in H2. subst.
apply in_map_iff.
refine (ex_intro _ (existT _ i0 m) _). split.
++++ simpl. destruct m.
+++++ destruct u. auto.
+++++ auto.
++++ apply ideal_finite. auto.
++ intros. apply in_map_iff in H. destruct H. destruct H. subst.
destruct x. apply ideal_finite in H0. assert (H1 := H0).
apply leq_same_component in H0. subst. destruct s0.
+++ destruct u. apply leq_sum_right with (i:=i) (m:=inl tt) (m':=s); auto.
+++ apply leq_sum_right with (i:=i) (m:=inr n) (m':=s); auto.
- intros. destruct H. inversion H.
+ subst. inversion H0; subst; inversion H3; subst; apply incomp_sum_least; auto.
+ subst. inversion H0.
++ subst. inversion H3. subst. apply inj_pairT2 in H3. subst.
apply incomp_sum_left with (i:=i0) (m:=m) (m':=m'0).
apply incompatible_closed with (y:=existT (fun i : I (P E) => (unit + N (P E) i)%type) i0 m0).
auto. auto. auto.
++ subst. apply incomp_sum_least. easy.
+ subst. inversion H0.
++ subst. apply incomp_sum_least. easy.
++ subst. inversion H3. subst. apply inj_pairT2 in H3. subst.
apply incomp_sum_right with (i:=i0) (m:=m) (m':=m'0).
apply incompatible_closed with (existT (fun i : I (P F) => (unit + N (P F) i)%type) i0 m0).
auto. auto. auto.
Defined.

Fixpoint cast_sum_to_left E F (l : Position (event_structure_sum E F))
: Position E :=
match l with
| nil => nil
| (existT _ (inl i) m) :: xs
=> (existT _ i m) :: (cast_sum_to_left E F xs)
| (existT _ (inr i) m) :: xs => cast_sum_to_left E F xs
end.

Fixpoint cast_sum_to_right E F (l : Position (event_structure_sum E F))
: Position F :=
match l with
| nil => nil
| (existT _ (inr i) m) :: xs
=> (existT _ i m) :: (cast_sum_to_right E F xs)
| (existT _ (inl i) m) :: xs => cast_sum_to_right E F xs
end.

Fixpoint cast_sum_inf_to_left E F (l : InfinitePosition (event_structure_sum E F))
: InfinitePosition E :=
match l with
| stream _ (existT _ (inl i) m) f =>
stream _ (existT _ i m) (fun _ => cast_sum_inf_to_left E F (f tt))
| stream _ (existT _ _ _) f => cast_sum_inf_to_left E F (f tt)
end.

Fixpoint cast_sum_inf_to_right E F (l : InfinitePosition (event_structure_sum E F))
: InfinitePosition F :=
match l with
| stream _ (existT _ (inr i) m) f =>
stream _ (existT _ i m) (fun _ => cast_sum_inf_to_right E F (f tt))
| stream _ (existT _ _ _) f => cast_sum_inf_to_right E F (f tt)
end.

Fact initial_in_sum_is_initial :
forall E F m, initial_move (P (event_structure_sum E F)) m <->
((exists i n, m = existT _ (inl i) n /\ initial_move (P E) (existT _ i n))
\/
(exists i n, m = existT _ (inr i) n /\ initial_move (P F) (existT _ i n))).
Proof. unfold iff. split.
+ intros. rewrite initial_is_unit in H. destruct H. subst. destruct x.
++ left. refine (ex_intro _ i _). refine (ex_intro _ (inl tt) _). split.
+++ auto.
+++ apply initial_is_unit. refine (ex_intro _ i _). auto.
++ right. refine (ex_intro _ i _). refine (ex_intro _ (inl tt) _). split.
+++ auto.
+++ apply initial_is_unit. refine (ex_intro _ i _). auto.
+ intros. destruct H.
++ destruct H. destruct H. destruct H. subst. rewrite initial_is_unit.
rewrite initial_is_unit in H0. destruct H0. inversion H. subst. apply inj_pairT2 in H.
subst. refine (ex_intro _ (inl x1) _). auto.
++ destruct H. destruct H. destruct H. subst. rewrite initial_is_unit.
rewrite initial_is_unit in H0. destruct H0. inversion H. subst. apply inj_pairT2 in H.
subst. refine (ex_intro _ (inr x1) _). auto.
Qed.

Fact second_in_sum_is_second :
forall E F m, second_move (P (event_structure_sum E F)) m <->
((exists i n, m = existT _ (inl i) n /\ second_move (P E) (existT _ i n))
\/
(exists i n, m = existT _ (inr i) n /\ second_move (P F) (existT _ i n))).
Proof. unfold iff. split.
+ intros. unfold second_move in H. destruct H. rewrite initial_is_unit in H.
destruct m. destruct x.
++ left. refine (ex_intro _ i _). refine (ex_intro _ s _). split.
+++ auto.
+++  unfold second_move. split.
++++ rewrite initial_is_unit. unfold not. intros. destruct H1. inversion H1.
subst. apply inj_pairT2 in H1. subst. contradiction H. refine (ex_intro _ (inl x) _).
auto.
++++ intros. destruct n. destruct H1. assert (H3 := H1). 
apply leq_same_component in H1. subst.
assert (initial_move (P (event_structure_sum E F)) 
(existT _ (inl i) s0)).
{apply H0. split.
+ simpl. apply leq_sum_left with (i:=i) (m:=s0) (m':=s). auto. auto. auto.
+ unfold not. intros. apply inj_pairT2 in H1. subst. contradiction H2. auto. }
rewrite initial_is_unit. rewrite initial_is_unit in H1. destruct H1. inversion H1.
subst. apply inj_pairT2 in H1. subst. refine (ex_intro _ i _). auto.
++ right. refine (ex_intro _ i _). refine (ex_intro _ s _). split.
+++ auto.
+++  unfold second_move. split.
++++ rewrite initial_is_unit. unfold not. intros. destruct H1. inversion H1.
subst. apply inj_pairT2 in H1. subst. contradiction H. refine (ex_intro _ (inr x) _).
auto.
++++ intros. destruct n. destruct H1. assert (H3 := H1). 
apply leq_same_component in H1. subst.
assert (initial_move (P (event_structure_sum E F)) 
(existT _ (inr i) s0)).
{apply H0. split.
+ simpl. apply leq_sum_right with (i:=i) (m:=s0) (m':=s). auto. auto. auto.
+ unfold not. intros. apply inj_pairT2 in H1. subst. contradiction H2. auto. }
rewrite initial_is_unit. rewrite initial_is_unit in H1. destruct H1. inversion H1.
subst. apply inj_pairT2 in H1. subst. refine (ex_intro _ i _). auto.
+ intros. destruct H.
++ destruct H. destruct H. destruct H. subst. unfold second_move in H0. unfold second_move.
destruct H0. rewrite initial_is_unit in H. split.
+++ rewrite initial_is_unit. unfold not. intros. contradiction H. destruct H1.
inversion H1. subst. apply inj_pairT2 in H1. subst. refine (ex_intro _ x _). auto.
+++ intros. destruct n. destruct H1. assert (H3 := H1).
apply leq_same_component in H1. subst. inversion H3.
++++ subst. inversion H5. subst. apply inj_pairT2 in H5. subst. apply inj_pairT2 in H4. subst.
assert (initial_move (P E)
(existT (fun i : I (P E) => (unit + N (P E) i)%type) i m)).
{apply H0. split.
+ auto.
+ unfold not. intros. apply inj_pairT2 in H4. subst. contradiction H2. auto. }
rewrite initial_is_unit in H4. rewrite initial_is_unit. destruct H4. inversion H4. subst.
apply inj_pairT2 in H7. subst. refine (ex_intro _ (inl x) _). auto.
++++ subst. inversion H5.
++ destruct H. destruct H. destruct H. subst. unfold second_move in H0.
destruct H0. unfold second_move. split.
+++ rewrite initial_is_unit in H. rewrite initial_is_unit. unfold not. intros.
contradiction H. destruct H1. inversion H1. subst. apply inj_pairT2 in H1. subst.
refine (ex_intro _ x _). auto.
+++ intros. destruct n. destruct H1. inversion H1.
++++ subst. inversion H5.
++++ subst. inversion H5. subst. apply inj_pairT2 in H5. subst. destruct x1.
+++++ inversion H4.
+++++
assert (initial_move (P F)
(existT (fun i : I (P F) => (unit + N (P F) i)%type) i0 s)).
{apply H0. inversion H4. subst. apply inj_pairT2 in H4. subst. split.
+ auto.
+ unfold not. intros. apply inj_pairT2 in H4. subst. contradiction H2. auto. }
rewrite initial_is_unit. rewrite initial_is_unit in H5. destruct H5.
inversion H5. subst. apply inj_pairT2 in H5. subst. refine (ex_intro _ (inr x) _).
auto.
Defined.

Definition inf_plus i j :=
match i,j with
| plus_infinity, plus_infinity => plus_infinity
| _, _ => minus_infinity
end.

Definition asynchronous_arena_sum (A B : AsynchronousArena) 
(positive1 : (finite_payoff_position A) nil = (-1)%Z)
(positive2 : (finite_payoff_position B) nil = (-1)%Z)
: AsynchronousArena.
  refine({| 
            E := event_structure_sum (E A) (E B);
            polarity m := match m with
                          | existT _ (inl i) m => (polarity A) (existT _ i m)
                          | existT _ (inr i) m => (polarity B) (existT _ i m)
                          end;
            finite_payoff_position l := 
                let left := (cast_sum_to_left (E A) (E B) l) in
                if Nat.eqb (length l) (length left) then
                finite_payoff_position A left else 
                finite_payoff_position B (cast_sum_to_right (E A) (E B) l);
            finite_payoff_walk w :=
              let fp := cast_sum_to_left _ _ (fst (fst w)) in
              let fm := cast_sum_to_left _ _ (snd (fst w)) in
              let sp := cast_sum_to_left _ _ (fst (snd w)) in
              let sm := cast_sum_to_left _ _ (snd (snd w)) in
              if Nat.eqb (length fm) (length (snd (fst w))) &&
                 Nat.eqb (length sm) (length (snd (snd w))) then
              finite_payoff_walk A ((fp, fm), (sp, sm)) else
              let fp := cast_sum_to_right _ _ (fst (fst w)) in
              let fm := cast_sum_to_right _ _ (snd (fst w)) in
              let sp := cast_sum_to_right _ _ (fst (snd w)) in
              let sm := cast_sum_to_right _ _ (snd (snd w)) in
              finite_payoff_walk B ((fp, fm), (sp, sm));
             infinite_payoff l :=
              let left := infinite_payoff A (cast_sum_inf_to_left _ _ l) in
              let right := infinite_payoff B (cast_sum_inf_to_right _ _ l) in
              inf_plus left right;
         |}).
Proof.
- left. auto.
- intros. flatten_all.
+ subst. split.
++ intros. simpl. auto.
++ intros. simpl. apply initial_in_sum_is_initial in H. destruct H.
+++ destruct H. destruct H. destruct H. inversion H. subst. apply inj_pairT2 in H.
subst. apply polarity_first in H1. apply H1 in H0. auto.
+++ destruct H. destruct H. destruct H. inversion H.
+ subst. split.
++ intros. subst. simpl. auto.
++ intros. simpl. apply initial_in_sum_is_initial in H. destruct H.
+++ destruct H. destruct H. destruct H. inversion H.
+++ destruct H. destruct H. destruct H. inversion H. subst. apply inj_pairT2 in H.
subst. apply polarity_first in H1. apply H1 in H0. lia.
- intros. flatten_all.
+ subst. split.
++ intros. simpl. apply second_in_sum_is_second in H. destruct H.
+++ destruct H. destruct H. destruct H. inversion H. subst. apply inj_pairT2 in H. subst.
apply polarity_second in H1. apply H1 in H0. auto.
+++ destruct H. destruct H. destruct H. inversion H.
++ intros. simpl. auto.
+ intros. simpl. split.
++ intros. apply second_in_sum_is_second in H. destruct H.
+++ destruct H. destruct H. destruct H. inversion H.
+++ destruct H. destruct H. destruct H. inversion H. subst. apply inj_pairT2 in H. subst.
apply polarity_second in H1. apply H1 in H0. auto. lia.
++ intros. auto.
- intros. destruct H. destruct w. destruct p. destruct p0. simpl in *. subst. simpl.
apply initial_null. auto.
Defined.

Definition asynchronous_game_sum_positive (G H: AsynchronousGame) 
(pos1 : (finite_payoff_position (A G)) nil = (-1)%Z)
(pos2 : (finite_payoff_position (A H)) nil = (-1)%Z)
: AsynchronousGame.
  refine({| 
             A := asynchronous_arena_sum (A G) (A H) pos1 pos2;
             X := product_group (X G) (X H);
             Y := product_group (Y G) (Y H);
             action g m h := match m with
                                | existT _ (inl i) m => 
                                  (match action G (fst g) (existT _ i m) (fst h) with
                                    | existT _ i m => existT _ (inl i) m
                                  end)
                                | existT _ (inr i) m => 
                                  (match action H (snd g) (existT _ i m) (snd h) with
                                    | existT _ i m => existT _ (inr i) m
                                  end)
                              end;
        |}).
Proof.
- intros. flatten_all.
+ subst. simpl in e1. rewrite action_id in e1. inversion e1. subst. apply inj_pairT2 in e1.
subst. auto.
+ subst. simpl in e1. rewrite action_id in e1. inversion e1. subst. apply inj_pairT2 in e1.
subst. auto.
- intros. destruct g. destruct h. destruct h'. destruct g'. 
flatten_all; subst; simpl fst in *; simpl snd in *; inversion e2; subst;
rewrite action_compatible in e1; apply inj_pairT2 in e2; subst; rewrite e3 in e1;
rewrite e1 in e5; inversion e5; subst; apply inj_pairT2 in e5; subst; auto.
- intros. destruct g. destruct h. simpl fst in *. flatten_all; simpl fst in *.
simpl snd in *; subst; assert (H1:=H0); apply leq_same_component in H0; inversion H0; subst.
+ assert (leq _
(action G g (existT (fun i : I (P (E (A G))) => (unit + N (P (E (A G))) i)%type) i0 s) g1)
(action G g (existT (fun i : I (P (E (A G))) => (unit + N (P (E (A G))) i)%type) i0 s1) g1)).
{apply coherence_1. inversion H1.
+ subst. inversion H4. subst. apply inj_pairT2 in H3. subst. apply inj_pairT2 in H4. subst. auto. 
+ subst. inversion H4. } rewrite e4 in H2. rewrite e1 in H2. simpl. assert (H3:=H2). 
apply leq_same_component in H3. subst. apply leq_sum_left with (i:=x2) (m:=s0) (m':=s2). auto. auto. auto.
+ subst. inversion H0.
++ subst. inversion H3.
++ subst. inversion H2.
+ subst. inversion H0.
++ subst. inversion H2.
++ subst. inversion H3.
+ subst. simpl fst in *. simpl snd in *.
assert (leq _
(action H g0
       (existT (fun i : I (P (E (A H))) => (unit + N (P (E (A H))) i)%type) i s)
       g2)
(action H g0
       (existT (fun i : I (P (E (A H))) => (unit + N (P (E (A H))) i)%type) i0 s1)
       g2)).
{apply coherence_1. inversion H0.
+ subst. inversion H3.
+ subst. inversion H2. inversion H2. subst. apply inj_pairT2 in H2. subst. inversion H3. inversion H3.
subst. apply inj_pairT2 in H3. subst. auto. }
rewrite e4 in H1. rewrite e1 in H1. assert (H2:=H1). apply leq_same_component in H1. subst.
simpl. apply leq_sum_right with (i:=x2) (m:=s0) (m':=s2). auto. auto. auto.
- intros. destruct g. destruct h. flatten_all; simpl fst in *; simpl snd in *; subst.
+ simpl. rewrite <- e1. apply coherence_2.
+ simpl. rewrite <- e1. apply coherence_2.
- intros. destruct g. flatten_all; simpl fst in *; simpl snd in *; subst; destruct H0.
+ remember ((existT
          (fun i : I (P (E (asynchronous_arena_sum (A G) (A H) pos1 pos2))) =>
           (unit + N (P (E (asynchronous_arena_sum (A G) (A H) pos1 pos2))) i)%type)
          (inl i) s)).
assert (s1 =
     (let (x, m) := s1 in
      match
        x as x0
        return
          (unit + N (P (E (asynchronous_arena_sum (A G) (A H) pos1 pos2))) x0 ->
           M (P (E (asynchronous_arena_sum (A G) (A H) pos1 pos2))))
      with
      | inl i =>
          fun
            m0 : unit +
                 N (P (E (asynchronous_arena_sum (A G) (A H) pos1 pos2))) (inl i) =>
          let (i0, m1) :=
            action G (fst (g, g0))
              (existT (fun i0 : I (P (E (A G))) => (unit + N (P (E (A G))) i0)%type)
                 i m0) (fst (id (product_group (Y G) (Y H)))) in
          existT
            (fun i1 : I (P (E (asynchronous_arena_sum (A G) (A H) pos1 pos2))) =>
             (unit + N (P (E (asynchronous_arena_sum (A G) (A H) pos1 pos2))) i1)%type)
            (inl i0) m1
      | inr i =>
          fun
            m0 : unit +
                 N (P (E (asynchronous_arena_sum (A G) (A H) pos1 pos2))) (inr i) =>
          let (i0, m1) :=
            action H (snd (g, g0))
              (existT (fun i0 : I (P (E (A H))) => (unit + N (P (E (A H))) i0)%type)
                 i m0) (snd (id (product_group (Y G) (Y H)))) in
          existT
            (fun i1 : I (P (E (asynchronous_arena_sum (A G) (A H) pos1 pos2))) =>
             (unit + N (P (E (asynchronous_arena_sum (A G) (A H) pos1 pos2))) i1)%type)
            (inr i0) m1
      end m)).
{apply H1. apply reflexive. } subst. 
destruct (action G (fst (g, g0))
          (existT (fun i0 : I (P (E (A G))) => (unit + N (P (E (A G))) i0)%type) i s)
          (fst (id (product_group (Y G) (Y H))))) eqn:eqn1. simpl fst in *. rewrite e1 in eqn1.
inversion H2. inversion H2. subst. apply inj_pairT2 in H2. subst. inversion eqn1. subst.
apply inj_pairT2 in eqn1. subst. auto.
+ remember ((existT
          (fun i : I (P (E (asynchronous_arena_sum (A G) (A H) pos1 pos2))) =>
           (unit + N (P (E (asynchronous_arena_sum (A G) (A H) pos1 pos2))) i)%type)
          (inr i) s)).
assert (s1 =
     (let (x, m) := s1 in
      match
        x as x0
        return
          (unit + N (P (E (asynchronous_arena_sum (A G) (A H) pos1 pos2))) x0 ->
           M (P (E (asynchronous_arena_sum (A G) (A H) pos1 pos2))))
      with
      | inl i =>
          fun
            m0 : unit +
                 N (P (E (asynchronous_arena_sum (A G) (A H) pos1 pos2))) (inl i) =>
          let (i0, m1) :=
            action G (fst (g, g0))
              (existT (fun i0 : I (P (E (A G))) => (unit + N (P (E (A G))) i0)%type) i
                 m0) (fst (id (product_group (Y G) (Y H)))) in
          existT
            (fun i1 : I (P (E (asynchronous_arena_sum (A G) (A H) pos1 pos2))) =>
             (unit + N (P (E (asynchronous_arena_sum (A G) (A H) pos1 pos2))) i1)%type)
            (inl i0) m1
      | inr i =>
          fun
            m0 : unit +
                 N (P (E (asynchronous_arena_sum (A G) (A H) pos1 pos2))) (inr i) =>
          let (i0, m1) :=
            action H (snd (g, g0))
              (existT (fun i0 : I (P (E (A H))) => (unit + N (P (E (A H))) i0)%type) i
                 m0) (snd (id (product_group (Y G) (Y H)))) in
          existT
            (fun i1 : I (P (E (asynchronous_arena_sum (A G) (A H) pos1 pos2))) =>
             (unit + N (P (E (asynchronous_arena_sum (A G) (A H) pos1 pos2))) i1)%type)
            (inr i0) m1
      end m)).
{apply H1. apply reflexive. } subst.
destruct (action H (snd (g, g0))
          (existT (fun i0 : I (P (E (A H))) => (unit + N (P (E (A H))) i0)%type) i s)
          (snd (id (product_group (Y G) (Y H))))) eqn:eqn1.
simpl snd in *. rewrite e1 in eqn1. inversion eqn1. subst. apply inj_pairT2 in eqn1.
subst. inversion H2. inversion H2. subst. apply inj_pairT2 in H2. auto.
- intros. destruct h. flatten_all; simpl fst in *; subst; destruct H0.
+ remember ((existT
          (fun i : I (P (E (asynchronous_arena_sum (A G) (A H) pos1 pos2))) =>
           (unit + N (P (E (asynchronous_arena_sum (A G) (A H) pos1 pos2))) i)%type)
          (inl i) s)).
assert (s1 =
     (let (x, m) := s1 in
      match
        x as x0
        return
          (unit + N (P (E (asynchronous_arena_sum (A G) (A H) pos1 pos2))) x0 ->
           M (P (E (asynchronous_arena_sum (A G) (A H) pos1 pos2))))
      with
      | inl i =>
          fun
            m0 : unit +
                 N (P (E (asynchronous_arena_sum (A G) (A H) pos1 pos2))) (inl i) =>
          let (i0, m1) :=
            action G (fst (id (product_group (X G) (X H))))
              (existT (fun i0 : I (P (E (A G))) => (unit + N (P (E (A G))) i0)%type) i
                 m0) (fst (g, g0)) in
          existT
            (fun i1 : I (P (E (asynchronous_arena_sum (A G) (A H) pos1 pos2))) =>
             (unit + N (P (E (asynchronous_arena_sum (A G) (A H) pos1 pos2))) i1)%type)
            (inl i0) m1
      | inr i =>
          fun
            m0 : unit +
                 N (P (E (asynchronous_arena_sum (A G) (A H) pos1 pos2))) (inr i) =>
          let (i0, m1) :=
            action H (snd (id (product_group (X G) (X H))))
              (existT (fun i0 : I (P (E (A H))) => (unit + N (P (E (A H))) i0)%type) i
                 m0) (snd (g, g0)) in
          existT
            (fun i1 : I (P (E (asynchronous_arena_sum (A G) (A H) pos1 pos2))) =>
             (unit + N (P (E (asynchronous_arena_sum (A G) (A H) pos1 pos2))) i1)%type)
            (inr i0) m1
      end m)).
{apply H1. apply reflexive. } subst. destruct
(action G (fst (id (product_group (X G) (X H))))
          (existT (fun i0 : I (P (E (A G))) => (unit + N (P (E (A G))) i0)%type) i s)
          (fst (g, g0))) eqn:eqn1.
simpl fst in *. rewrite e1 in eqn1. inversion eqn1. subst. apply inj_pairT2 in eqn1.
apply inj_pairT2 in H5. subst. inversion H2. inversion H2. subst. apply inj_pairT2 in H2. auto.
+ simpl snd in *. remember
((existT
          (fun i : I (P (E (asynchronous_arena_sum (A G) (A H) pos1 pos2))) =>
           (unit + N (P (E (asynchronous_arena_sum (A G) (A H) pos1 pos2))) i)%type)
          (inr i) s)).
assert (s1 =
     (let (x, m) := s1 in
      match
        x as x0
        return
          (unit + N (P (E (asynchronous_arena_sum (A G) (A H) pos1 pos2))) x0 ->
           M (P (E (asynchronous_arena_sum (A G) (A H) pos1 pos2))))
      with
      | inl i =>
          fun
            m0 : unit +
                 N (P (E (asynchronous_arena_sum (A G) (A H) pos1 pos2))) (inl i) =>
          let (i0, m1) :=
            action G (fst (id (product_group (X G) (X H))))
              (existT (fun i0 : I (P (E (A G))) => (unit + N (P (E (A G))) i0)%type) i
                 m0) (fst (g, g0)) in
          existT
            (fun i1 : I (P (E (asynchronous_arena_sum (A G) (A H) pos1 pos2))) =>
             (unit + N (P (E (asynchronous_arena_sum (A G) (A H) pos1 pos2))) i1)%type)
            (inl i0) m1
      | inr i =>
          fun
            m0 : unit +
                 N (P (E (asynchronous_arena_sum (A G) (A H) pos1 pos2))) (inr i) =>
          let (i0, m1) :=
            action H (snd (id (product_group (X G) (X H))))
              (existT (fun i0 : I (P (E (A H))) => (unit + N (P (E (A H))) i0)%type) i
                 m0) (snd (g, g0)) in
          existT
            (fun i1 : I (P (E (asynchronous_arena_sum (A G) (A H) pos1 pos2))) =>
             (unit + N (P (E (asynchronous_arena_sum (A G) (A H) pos1 pos2))) i1)%type)
            (inr i0) m1
      end m)).
{apply H1. apply reflexive. } subst.
destruct (action H (snd (id (product_group (X G) (X H))))
          (existT (fun i0 : I (P (E (A H))) => (unit + N (P (E (A H))) i0)%type) i s)
          (snd (g, g0))) eqn:eqn1. simpl snd in *. inversion H2. inversion H2. subst.
apply inj_pairT2 in H2. subst. rewrite e1 in eqn1. inversion eqn1. subst. apply inj_pairT2 in eqn1.
auto.
- intros. destruct g. destruct h. destruct i; simpl fst; simpl snd.
+ destruct (action G g
       (existT (fun i : I (P (E (A G))) => (unit + N (P (E (A G))) i)%type) i
          (inl tt)) g1) eqn:eqn1. refine (ex_intro _ (inl x) _). flatten_all. 
assert (existT
         (fun i : I (P (E (A G))) =>
          (unit + N (P (E (A G))) i)%type) x s = 
existT
      (fun i : I (P (E (A G))) =>
       (unit + N (P (E (A G))) i)%type) x0 s0).
{rewrite <- eqn1. rewrite <- e. auto. } inversion H0. subst. apply inj_pairT2 in H3. subst.
assert (exists k,
 action G g
      (existT (fun i : I (P (E (A G))) => (unit + N (P (E (A G))) i)%type) i (inl tt)) g1 = 
existT (fun i : I (P (E (A G))) => (unit + N (P (E (A G))) i)%type) k (inl tt)).
{apply action_preserves_initial. }
destruct H1. 
assert (existT (fun i : I (P (E (A G))) => (unit + N (P (E (A G))) i)%type) x0 s0 = 
existT (fun i : I (P (E (A G))) => (unit + N (P (E (A G))) i)%type) x (inl tt)).
{rewrite <- e. rewrite <- H1. auto. } inversion H2. subst. apply inj_pairT2 in H2.
subst. auto.
+ flatten_all.
assert (exists k,
action H g0
      (existT (fun i : I (P (E (A H))) => (unit + N (P (E (A H))) i)%type) i (inl tt)) g2 = 
existT (fun i : I (P (E (A H))) => (unit + N (P (E (A H))) i)%type) k (inl tt)).
{apply action_preserves_initial. }
destruct H0.
assert (existT (fun i : I (P (E (A H))) => (unit + N (P (E (A H))) i)%type) x s = 
     existT (fun i : I (P (E (A H))) => (unit + N (P (E (A H))) i)%type) x0 (inl tt)).
{rewrite <- e. rewrite <- H0. auto. }
inversion H1. subst. apply inj_pairT2 in H1. subst. refine (ex_intro _ (inr x0) _). auto.
- intros. destruct i.
+ flatten_all. refine (ex_intro _ (inl x) _).
assert (exists k k1,
action G (fst g)
      (existT (fun i : I (P (E (A G))) => (unit + N (P (E (A G))) i)%type) i (inr m))
      (fst h) = 
existT (fun i : I (P (E (A G))) => (unit + N (P (E (A G))) i)%type) k (inr k1)).
{apply action_preserves_non_initial. }
destruct H0. destruct H0. rewrite e in H0. inversion H0. subst. apply inj_pairT2 in H3. subst.
refine (ex_intro _ x1 _). auto.
+ flatten_all. refine (ex_intro _ (inr x) _).
assert (exists k k1,
action H (snd g)
      (existT (fun i : I (P (E (A H))) => (unit + N (P (E (A H))) i)%type) i (inr m))
      (snd h) = 
existT (fun i : I (P (E (A H))) => (unit + N (P (E (A H))) i)%type) k (inr k1)).
{apply action_preserves_non_initial. }
destruct H0. destruct H0. rewrite e in H0. inversion H0. subst. apply inj_pairT2 in H3. subst.
refine (ex_intro _ x1 _). auto.
Defined.

Definition asynchronous_game_sum_left (G H: AsynchronousGame) 
(neg : (finite_payoff_position (A G)) nil = (1)%Z)
(pos : (finite_payoff_position (A H)) nil = (-1)%Z) : AsynchronousGame :=
asynchronous_game_sum_positive
(asynchronous_game_lifting G neg (1)%Z)
H
(positive_lifting_is_positive G neg (1)%Z)
pos.

Definition asynchronous_game_sum_right (G H: AsynchronousGame) 
(pos : (finite_payoff_position (A G)) nil = (-1)%Z)
(neg : (finite_payoff_position (A H)) nil = (1)%Z) : AsynchronousGame :=
asynchronous_game_sum_positive
G
(asynchronous_game_lifting H neg (1)%Z)
pos
(positive_lifting_is_positive H neg (1)%Z).

Definition asynchronous_game_sum_negative (G H: AsynchronousGame) 
(neg1 : (finite_payoff_position (A G)) nil = (1)%Z)
(neg2 : (finite_payoff_position (A H)) nil = (1)%Z) : AsynchronousGame :=
asynchronous_game_sum_positive
(asynchronous_game_lifting G neg1 (1)%Z)
(asynchronous_game_lifting H neg2 (1)%Z)
(positive_lifting_is_positive G neg1 (1)%Z)
(positive_lifting_is_positive H neg2 (1)%Z).

Definition asynchronous_game_sum (G H: AsynchronousGame) :
AsynchronousGame :=
match initial_payoff (A G), initial_payoff (A H) with
| left p, left p' => asynchronous_game_sum_positive G H p p'
| left p, right p' => asynchronous_game_sum_right G H p p'
| right p, left p' => asynchronous_game_sum_left G H p p'
| right p, right p' => asynchronous_game_sum_negative G H p p'
end.