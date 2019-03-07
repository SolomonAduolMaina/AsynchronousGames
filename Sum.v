Require Import List.
Require Import ZArith.
Require Import Lia.
Require Import Init.Nat.
Require Import Logic.Eqdep.
Require Import Logic.Eqdep_dec.
Require Import Arith.PeanoNat.
Require Import Bool.Bool.
Require Import Util.
Require Import Group.
Require Import AsynchronousGames.
Require Import Lifting.

Definition M_of_sum (P Q: AsynchronousGame) :=
{i : I P + I Q & (sum unit (match i with
                            | inl i => N P i
                            | inr j => N Q j
                            end))}.

Inductive leq_sum (P Q : AsynchronousGame) :
(M_of_sum P Q) -> (M_of_sum P Q) -> Prop :=
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

Inductive incompatible_sum (E F : AsynchronousGame) :
(M_of_sum E F) -> (M_of_sum E F) -> Prop :=
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

Fixpoint cast_sum_to_left E F (l : Position (M_of_sum E F)) : Position (M E) :=
match l with
    | nil => nil
    | (existT _ (inl i) m) :: xs => (existT _ i m) :: (cast_sum_to_left E F xs)
    | (existT _ (inr i) m) :: xs => cast_sum_to_left E F xs
end.

Fixpoint cast_sum_to_right E F (l : Position (M_of_sum E F)) : Position (M F) :=
match l with
    | nil => nil
    | (existT _ (inr i) m) :: xs => (existT _ i m) :: (cast_sum_to_right E F xs)
    | (existT _ (inl i) m) :: xs => cast_sum_to_right E F xs
end.

Definition inl_move_is_projection (A B : AsynchronousGame) 
(m : (M_of_sum A B)) 
(m' : M A) : Prop :=
exists i k, m = existT _ (inl i) k /\ m' = existT _ i k.

Definition inr_move_is_projection (A B : AsynchronousGame) 
(m : (M_of_sum A B)) 
(m' : M B) : Prop :=
exists i k, m = existT _ (inr i) k /\ m' = existT _ i k.

Definition infinite_payoff_right_finite (A B : AsynchronousGame) 
(f : InfinitePosition (M_of_sum A B) ) 
(inf : bool) :=
(exists g, (forall n, inl_move_is_projection A B (f n) (g n)) /\ 
(infinite_payoff A g inf))
\/
(exists g, (forall n, inr_move_is_projection A B (f n) (g n)) /\ 
(infinite_payoff B g inf)).


Definition asynchronous_game_sum_positive (G H: AsynchronousGame) 
(pos1 : positive_or_negative G = true)
(pos2 : positive_or_negative H = true) : AsynchronousGame :=
         {| 
            I := (I G) + (I H);
            N i := match i with
                      | inl i => N G i
                      | inr j => N H j
                   end;
            leq := leq_sum G H;

            incompatible := incompatible_sum G H;
            ideal m := match m with
                      | existT _ (inl i) m =>
                      map (fun x => match x with
                                    | existT _ i (inl tt) => existT _ (inl i) (inl tt)
                                    | existT _ i (inr m) => existT _ (inl i) (inr m)
                      end) (ideal G (existT _ i m))
                      | existT _ (inr i) m =>
                      map (fun x => match x with
                                    | existT _ i (inl tt) => existT _ (inr i) (inl tt)
                                    | existT _ i (inr m) => existT _ (inr i) (inr m)
                      end) (ideal H (existT _ i m))
                      end;

            polarity m := match m with
                          | existT _ (inl i) m => (polarity G) (existT _ i m)
                          | existT _ (inr i) m => (polarity H) (existT _ i m)
                          end;
            finite_payoff_position l := 
                let left := (cast_sum_to_left G H l) in
                if Nat.eqb (length l) (length left) then
                finite_payoff_position G left else 
                finite_payoff_position H (cast_sum_to_right G H l);
            finite_payoff_walk w :=
              let fp := cast_sum_to_left _ _ (fst (fst w)) in
              let fm := cast_sum_to_left _ _ (snd (fst w)) in
              let sp := cast_sum_to_left _ _ (fst (snd w)) in
              let sm := cast_sum_to_left _ _ (snd (snd w)) in
              if Nat.eqb (length fm) (length (snd (fst w))) &&
                 Nat.eqb (length sm) (length (snd (snd w))) then
              finite_payoff_walk G ((fp, fm), (sp, sm)) else
              let fp := cast_sum_to_right _ _ (fst (fst w)) in
              let fm := cast_sum_to_right _ _ (snd (fst w)) in
              let sp := cast_sum_to_right _ _ (fst (snd w)) in
              let sm := cast_sum_to_right _ _ (snd (snd w)) in
              finite_payoff_walk H ((fp, fm), (sp, sm));
             infinite_payoff f inf := infinite_payoff_right_finite G H f inf;
            positive_or_negative := true;

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
        |}.

Definition asynchronous_game_sum_left (G H: AsynchronousGame) 
(neg : positive_or_negative G = false)
(pos : positive_or_negative H = true) : AsynchronousGame :=
asynchronous_game_sum_positive
(lifting G neg (1)%Z) H
(positive_lifting_is_positive G neg (1)%Z) pos.

Definition asynchronous_game_sum_right (G H: AsynchronousGame) 
(pos : positive_or_negative G = true)
(neg : positive_or_negative H = false) : AsynchronousGame :=
asynchronous_game_sum_positive
G (lifting H neg (1)%Z)
pos (positive_lifting_is_positive H neg (1)%Z).

Definition asynchronous_game_sum_negative (G H: AsynchronousGame) 
(neg1 : positive_or_negative G = false)
(neg2 : positive_or_negative H = false) : AsynchronousGame :=
asynchronous_game_sum_positive
(lifting G neg1 (1)%Z)
(lifting H neg2 (1)%Z)
(positive_lifting_is_positive G neg1 (1)%Z)
(positive_lifting_is_positive H neg2 (1)%Z).

Program Definition asynchronous_game_sum (G H: AsynchronousGame) :
AsynchronousGame :=
match positive_or_negative G, positive_or_negative H with
| true, true => asynchronous_game_sum_positive G H eq_refl eq_refl
| true, false => asynchronous_game_sum_right G H eq_refl eq_refl
| false, true => asynchronous_game_sum_left G H eq_refl eq_refl
| false, false => asynchronous_game_sum_negative G H eq_refl eq_refl
end.


(*Proof. 
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
- intros. destruct i.
+ destruct j.
++ destruct (index_equality P i i0).
+++ subst. left. auto.
+++ right. unfold not. intros. inversion H. contradiction n.
++ right. unfold not. intros. inversion H.
+ destruct j.
++ right. unfold not. intros. inversion H.
++ destruct (index_equality Q i i0).
+++ subst. left. auto.
+++ right. unfold not. intros. inversion H. contradiction n.
Defined.


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


Proof.
- split.
+ intros. flatten_all. subst.
++
assert (left_action _ _ (actl G)).
{apply restriction_to_left_is_action. }
destruct H0. unfold actl in *. unfold left_action. simpl in e1. rewrite H0 in e1. inversion e1. subst. apply inj_pairT2 in e1. subst. auto.
++
assert (left_action _ _ (actl H)).
{apply restriction_to_left_is_action. }
destruct H0. unfold actl in *. unfold left_action. simpl in e1. 
rewrite H0 in e1. inversion e1. subst. apply inj_pairT2 in e1. subst. auto.
+ intros. destruct x. destruct x.
++ flatten_all.
+++ subst. simpl fst in *.
assert (left_action _ _ (actl G)).
{apply restriction_to_left_is_action. }
destruct H0. unfold actl in *. unfold left_action.
rewrite <- H1 in e3. inversion e. subst. apply inj_pairT2 in e. subst. rewrite e0 in e3.
rewrite e2 in e3. inversion e3. subst. apply inj_pairT2 in e3. subst. auto.
+++ inversion e.
++ flatten_all.
+++ inversion e.
+++ subst. simpl snd in *.
assert (left_action _ _ (actl H)).
{apply restriction_to_left_is_action. }
destruct H0. unfold actl in *. unfold left_action.
rewrite <- H1 in e3. inversion e. subst. apply inj_pairT2 in e. subst. rewrite e0 in e3.
rewrite e2 in e3. inversion e3. subst. apply inj_pairT2 in e3. subst. auto.
- split.
+ intros. flatten_all. subst.
++
assert (right_action _ _ (actr G)).
{apply restriction_to_right_is_action. }
destruct H0. unfold actr in *. unfold right_action. simpl in e1. rewrite H0 in e1. inversion e1. subst. apply inj_pairT2 in e1. subst. auto.
++
assert (right_action _ _ (actr H)).
{apply restriction_to_right_is_action. }
destruct H0. unfold actr in *. unfold right_action. simpl in e1. 
rewrite H0 in e1. inversion e1. subst. apply inj_pairT2 in e1. subst. auto.
+ intros. destruct x. destruct x.
++ flatten_all.
+++ subst. simpl fst in *.
assert (right_action _ _ (actr G)).
{apply restriction_to_right_is_action. }
destruct H0. unfold actr in *. unfold right_action.
rewrite <- H1 in e3. inversion e. subst. apply inj_pairT2 in e. subst. rewrite e0 in e3.
rewrite e2 in e3. inversion e3. subst. apply inj_pairT2 in e3. subst. auto.
+++ inversion e.
++ flatten_all.
+++ inversion e.
+++ subst. simpl snd in *.
assert (right_action _ _ (actr H)).
{apply restriction_to_right_is_action. }
destruct H0. unfold actr in *. unfold right_action.
rewrite <- H1 in e3. inversion e. subst. apply inj_pairT2 in e. subst. rewrite e0 in e3.
rewrite e2 in e3. inversion e3. subst. apply inj_pairT2 in e3. subst. auto.
- intros. destruct m. destruct n. inversion H0.
+ subst. inversion H3. subst. apply inj_pairT2 in H3. apply inj_pairT2 in H6. subst. inversion H2.
subst. apply inj_pairT2 in H2. subst. flatten_all.
assert (leq _
(action G (fst g)
       (existT (fun i : I (P (E (A G))) => (unit + N (P (E (A G))) i)%type) i m) 
       (fst h))
(action G (fst g)
       (existT (fun i : I (P (E (A G))) => (unit + N (P (E (A G))) i)%type) i m') 
       (fst h))).
{apply coherence_1. auto. }
rewrite e0 in H2. rewrite e in H2. assert (H3:=H2). apply leq_same_component in H3. subst.
simpl. apply leq_sum_left with (i:=x0) (m:=s) (m':=s0). auto. auto. auto.
+ subst. inversion H3. subst. apply inj_pairT2 in H3. apply inj_pairT2 in H6. subst. inversion H2.
subst. apply inj_pairT2 in H2. subst. flatten_all.
assert (leq _
(action H (snd g)
      (existT (fun i : I (P (E (A H))) => (unit + N (P (E (A H))) i)%type)
         i m) (snd h))
(action H (snd g)
      (existT (fun i : I (P (E (A H))) => (unit + N (P (E (A H))) i)%type)
         i m') (snd h))).
{apply coherence_1. auto. }
rewrite e0 in H2. rewrite e in H2. assert (H3:=H2). apply leq_same_component in H3. subst.
simpl. apply leq_sum_right with (i:=x0) (m:=s) (m':=s0). auto. auto. auto.
- intros. destruct m. destruct x.
+ flatten_all. simpl. rewrite <- e. apply coherence_2.
+ flatten_all. simpl. rewrite <- e. apply coherence_2.
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
*)
