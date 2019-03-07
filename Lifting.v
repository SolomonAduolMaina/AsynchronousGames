Require Import List.
Require Import ZArith.
Require Import Lia.
Require Import Init.Nat.
Require Import Logic.Eqdep.
Require Import Logic.Eqdep_dec.
Require Import Arith.PeanoNat.
Require Import Bool.Bool.
Require Import Group.
Require Import AsynchronousGames.

Definition M_of_lifting (G : AsynchronousGame) :=
{i : unit & (sum unit (M G))}.

Fixpoint contains_only_initial G (p : Position (M_of_lifting G)) :=
match p with
| nil => false
| existT _ tt (inl tt) :: nil => true
| existT _ tt (inl tt) :: xs  => contains_only_initial G xs
| _ => false
end.

Fixpoint cast_to_original G (p : Position (M_of_lifting G)) :
Position (M G) :=
match p with
| nil => nil
| existT _ tt (inl tt) :: xs => cast_to_original G xs
| existT _ tt (inr m) :: xs => m :: (cast_to_original G xs)
end.

Definition lifting (G : AsynchronousGame) 
(negative : positive_or_negative G = false) (p : Z)
: AsynchronousGame :=
        {| 
            I := unit;
            N x := M G;
            leq m n := match m,n with
                       | existT _ tt (inl _), _ => True
                       | existT _ tt (inr m), existT _ tt (inr n) => (leq G) m n
                       | _, _ => False
                       end;

            incompatible m n := match m,n with
                                | existT _ tt (inr m), existT _ tt (inr n) => incompatible G m n
                                | _, _ => False
                                end;
            ideal m := match m with
                       | existT _ tt (inl tt) => (existT _ tt (inl tt)) :: nil
                       | existT _ tt (inr m) =>
                        (existT _ tt (inl tt)) :: (map (fun x => existT _ tt (inr x)) (ideal G m))
                       end;

            polarity m := match m with
                          | existT _ tt (inl tt) => true
                          | existT _ tt (inr m) => (polarity G) m
                          end;
            finite_payoff_position l :=
              (match l with
                | nil => (-1)%Z
                | _ => if contains_only_initial G l then p else
                       finite_payoff_position G (cast_to_original G l)
              end);
            finite_payoff_walk w :=
              match w with
                | ((_, nil), (_, nil)) => 0%Z
                | ((_::_, _), (_::_, _)) =>
                    let fp := cast_to_original G (fst (fst w)) in
                    let fm := cast_to_original G (snd (fst w)) in
                    let sp := cast_to_original G (fst (snd w)) in
                    let sm := cast_to_original G (snd (snd w)) in
                    finite_payoff_walk G ((fp, fm), (sp, sm)) 
                | _ => finite_payoff_position G 
                       (cast_to_original G ((fst (snd w)) ++ (snd (snd w))))
               end;
            infinite_payoff f inf := match f 0 with
                                      | existT _ tt (inl tt) => (exists g, 
                                        (forall n, n > 0 -> exists m, 
                                        (f n = existT _ tt (inr m) /\ g (n-1) = m /\ 
                                         infinite_payoff G g inf)))
                                      | _ => False
                                     end;
            positive_or_negative := true;

             X := X G;
             Y := Y G;
             action g m h := match m with
                                | existT _ tt (inl tt) => m
                                | existT _ tt (inr m) => 
                                  existT _ tt (inr (action G g m h))
                             end;
        |}.

Fact positive_lifting_is_positive :
forall (G : AsynchronousGame) (negative : positive_or_negative G = false) (p : Z), 
positive_or_negative (lifting G negative p) = true.
Proof. auto. Qed.

(*Definition I_def (P : PartialOrder) := unit.

Definition N_def (P : PartialOrder) := (fun (x : unit) => M P).

Definition leq_def (P : PartialOrder) := 
(fun (m n : {i : unit & (sum unit (M P))}) => match m,n with
                       | existT _ tt (inl _), _ => True
                       | existT _ tt (inr m), existT _ tt (inr n) => (leq P) m n
                       | _, _ => False
                       end).

Fact reflexive_proof (P : PartialOrder) : forall x, leq_def P x x.
Proof.
unfold leq_def. intros. destruct x. destruct x. destruct s.
++ auto.
++ apply reflexive.
Qed.

Fact anti_symmetric_proof (P : PartialOrder) :
forall x y, leq_def P x y /\ leq_def P y x -> x = y.
Proof. unfold leq_def.
intros. destruct x. destruct x. destruct H. destruct y. destruct x.
destruct s.
+ destruct s0.
++ destruct u. destruct u0. auto.
++ contradiction H0.
+ destruct s0.
++ contradiction H.
++ assert (m = m0).
{apply anti_symmetric. auto. } subst. auto.
Qed.

Fact transitive_proof (P : PartialOrder) :
forall x y z, leq_def P x y /\ leq_def P y z -> leq_def P x z.
Proof.
intros. destruct x. destruct y. destruct z. destruct x. destruct x1.
destruct x0. destruct H. destruct s.
+ destruct s0.
++ auto.
++ auto.
+ destruct s0.
++ contradiction H.
++ destruct s1.
+++ apply H0.
+++ apply transitive with (y:=m0). auto.
Qed.

Fact unit_is_least_proof (P : PartialOrder) :
forall i i' m, 
    leq_def P (existT _ i (inl tt)) (existT _ i' m) <-> i = i'.
Proof. intros. destruct i. destruct i'. easy. Qed.

Fact leq_same_component_proof (P : PartialOrder) :
forall i i' m m',
    leq_def P (existT _ i m) (existT _ i' m') -> i = i'.
Proof. intros. destruct i. destruct i'. auto. Qed.

Fact index_equality_proof (P : PartialOrder) :
forall (i j : I_def P), {i = j} + {i <> j}.
Proof. intros. left. destruct i. destruct j. auto. Qed.


Definition P_def (E : EventStructure) := partial_order_lifting (P E).

Definition incompatible_def (E : EventStructure) :=
fun (m n : M (P_def E)) =>
    match m,n with
         | existT _ tt (inr m), existT _ tt (inr n) => incompatible E m n
         | _, _ => False
    end.

Definition ideal_def (E : EventStructure) : (M (P_def E) ) -> (list (M (P_def E)))
:=
fun (m : (M (partial_order_lifting (P E)))) =>
    match m with
       | existT _ tt (inl tt) => (existT _ tt (inl tt)) :: nil
       | existT _ tt (inr m) =>
         (existT _ tt (inl tt)) :: (map (fun x => existT _ tt (inr x)) (ideal E m))
    end.

Fact symmetric_proof (E : EventStructure) :
forall x y, incompatible_def E x y -> incompatible_def E y x.
Proof.
intros. destruct x. destruct y. destruct x. destruct x0. destruct s0.
+ destruct s;contradiction H.
+ destruct s.
++ auto.
++ apply symmetric. auto.
Qed.

Fact irreflexive_proof (E : EventStructure) :
forall x, not (incompatible_def E x x).
Proof.
unfold not. intros. destruct x. destruct x. destruct s.
+ auto.
+ apply irreflexive in H. auto.
Qed.

Fact ideal_finite_proof (E : EventStructure) :
forall x y, leq_def (P E) y x <-> In y (ideal_def E x).
Proof.
intros. destruct x. destruct y. destruct x. destruct x0. destruct s.
+ destruct s0.
++ unfold iff. destruct u. destruct u0. split.
+++ intros. left. auto.
+++ intros. simpl. auto. 
++ unfold iff. destruct u. split.
+++ intros. simpl in H. contradiction H.
+++ intros. destruct H; inversion H.
+ unfold iff. split.
++ intros. destruct s0.
+++ left. destruct u. auto.
+++ right. simpl in H. apply ideal_finite in H.
++++ apply in_map_iff. refine (ex_intro _ m0 _). auto.
++ intros. destruct H.
+++ apply inj_pairT2 in H. subst. simpl. auto.
+++ apply in_map_iff in H. destruct H. destruct H.
apply inj_pairT2 in H. subst. simpl. apply ideal_finite. auto.
Qed.

Fact incompatible_closed_proof (E : EventStructure) :
forall x y z, (incompatible_def E x y) /\ (leq_def (P E) y z) -> 
incompatible_def E x z.
Proof.
intros. destruct x. destruct y. destruct z. destruct x.
destruct x0. destruct x1. destruct s.
+ destruct H. contradiction H.
+ destruct s0.
++ destruct H. contradiction H.
++ destruct s1.
+++ simpl in H. destruct H. auto.
+++ simpl in H. apply incompatible_closed with (y:=n0). auto.
Qed.


Fixpoint cast_lifting E (l : Position (event_structure_lifting E))
: Position E :=
match l with
| nil => nil
| (existT _ tt (inl tt)) :: xs => cast_lifting E xs
| (existT _ tt (inr m)) :: xs => m :: cast_lifting E xs
end.

Fact second_in_lifting_is_initial:
forall E m, second_move (P (event_structure_lifting E)) m <->
(exists i, m = existT _ tt (inr (existT _ i (inl tt)))).
Proof. intros. unfold iff. split.
- intros. unfold second_move in H. destruct m. destruct H.
destruct s.
+ rewrite initial_is_unit in H. contradiction H. refine (ex_intro _ x _).
destruct u. auto.
+ destruct x. destruct n.
++ destruct s.
+++ destruct u. refine (ex_intro _ x _). auto.
+++ assert
(initial_move (P (event_structure_lifting E)) 
(existT
          (fun i : I (P (event_structure_lifting E)) =>
           (unit + N (P (event_structure_lifting E)) i)%type) tt
          (inr (existT (fun i : I (P E) => (unit + N (P E) i)%type) x (inl tt))))).
{apply H0. split.
+ simpl. apply unit_is_least. auto.
+ unfold not. intros. inversion H1. }
rewrite initial_is_unit in H1. destruct H1. inversion H1.
- intros. destruct H. subst. unfold second_move. split.
+ unfold not. intros. rewrite initial_is_unit in H. destruct H. inversion H.
+ intros. destruct H. destruct n.
++ destruct x0. destruct s.
+++ simpl in H. rewrite initial_is_unit.
refine (ex_intro _ tt _). destruct u. auto.
+++ simpl in H. destruct n.
++++ assert (H1:=H). apply leq_same_component in H. subst.
assert 
((existT (fun i : I (P E) => (unit + N (P E) i)%type) x s) =
       (existT (fun i : I (P E) => (unit + N (P E) i)%type) x (inl tt))).
{apply anti_symmetric. split.
+ auto.
+ apply unit_is_least. auto. } apply inj_pairT2 in H. subst. contradiction H0.
auto.
Qed.


Definition E_def (A : AsynchronousArena) := 
 event_structure_lifting (E A).

Definition polarity_def (A : AsynchronousArena) := 
fun (m : M (P (E_def A))) => match m with
                          | existT _ tt (inl tt) => true
                          | existT _ tt (inr m) => (polarity A) m
                          end.

Definition finite_payoff_position_def (A : AsynchronousArena) (p : Z) :=
fun l => (match l with
                | nil => (-1)%Z
                | _ => if contains_only_initial _ l then p else
                       finite_payoff_position A (cast_to_original _ l)
              end).

Definition finite_payoff_walk_def (A : AsynchronousArena) :=
fun w =>
match w with
                | ((_, nil), (_, nil)) => 0%Z
                | ((_::_, _), (_::_, _)) =>
                    let fp := cast_to_original _ (fst (fst w)) in
                    let fm := cast_to_original _ (snd (fst w)) in
                    let sp := cast_to_original _ (fst (snd w)) in
                    let sm := cast_to_original _ (snd (snd w)) in
                    finite_payoff_walk A ((fp, fm), (sp, sm)) 
                | _ => finite_payoff_position A 
                       (cast_to_original _ ((fst (snd w)) ++ (snd (snd w))))
               end.

Definition infinite_payoff_def (A : AsynchronousArena) :=
fun (f : nat -> (M (P (E_def A)))) inf =>
match f 0 with
        | existT _ tt (inl tt) => (exists g, 
           (forall n, n > 0 -> exists m, 
           (f n = existT _ tt (inr m) /\ g (n-1) = m /\ 
           infinite_payoff A g inf)))
         | _ => False
end.

Fact initial_payoff_proof (A : AsynchronousArena) (p : Z):
sumbool
(finite_payoff_position_def A p nil = (-1)%Z)
    (finite_payoff_position_def A p nil = (1)%Z).
Proof. left. auto. Qed.

Fact polarity_first_proof (A : AsynchronousArena) (p : Z):
forall m, initial_move (P (E_def A)) m -> 
    ((polarity_def A m = true -> finite_payoff_position_def A p nil = (-1)%Z)
    /\
    (polarity_def A m = false -> finite_payoff_position_def A p nil = (1)%Z)).
Proof.
intros. destruct m. destruct x. destruct s.
+ destruct u. easy.
+ rewrite initial_is_unit in H. destruct H. inversion H.
Qed.

Fact polarity_second_proof (A : AsynchronousArena) (p : Z)
(negative : (finite_payoff_position A) nil = (1)%Z):
forall m, second_move (P (E_def A)) m -> 
    ((polarity_def A m = true -> finite_payoff_position_def A p nil = (1)%Z)
    /\
    (polarity_def A m = false -> finite_payoff_position_def A p nil = (-1)%Z)).
Proof.
unfold polarity_def. unfold E_def in *.
intros. destruct m. destruct x. rewrite second_in_lifting_is_initial in H.
destruct H. inversion H. subst. 
assert (initial_move _ (existT (fun i : I (P (E A)) => (unit + N (P (E A)) i)%type) x
      (inl tt)) ).
{apply initial_is_unit. refine (ex_intro _ x _). auto. }
apply polarity_first in H0. rewrite negative in H0. intuition.
Qed.

Fact initial_null_proof (A : AsynchronousArena):
forall w,
    (snd (fst w) = nil /\ snd (snd w) = nil) -> 
    finite_payoff_walk_def A w = 0%Z.
Proof. unfold finite_payoff_walk_def.
intros. destruct w. destruct p. destruct p0. simpl in *. destruct H. subst. simpl.
destruct l; destruct l1; auto.
Qed.

Definition A_def (G : AsynchronousGame) 
(negative : (finite_payoff_position (A G)) nil = (1)%Z)
(p : Z) := asynchronous_arena_lifting (A G) negative p.

Definition X_def (G : AsynchronousGame) := X G.

Definition Y_def (G : AsynchronousGame) := Y G.

Definition action_def (G : AsynchronousGame)
(negative : (finite_payoff_position (A G)) nil = (1)%Z)
(p : Z)  := 
fun g (m : M (P_def (E (A G)))) h =>
match m with
                                | existT _ tt (inl tt) => m
                                | existT _ tt (inr m) => 
                                  existT _ tt (inr (action G g m h))
                             end.

Definition actl_def (G : AsynchronousGame)
(negative : (finite_payoff_position (A G)) nil = (1)%Z)
(p : Z) :=
(fun g m => action_def G negative p g m (id (Y_def G))).

Definition actr_def (G : AsynchronousGame)
(negative : (finite_payoff_position (A G)) nil = (1)%Z)
(p : Z) :=
(fun m h => action_def G negative p (id (X_def G)) m h).

Fact restriction_to_left_is_action_proof (G : AsynchronousGame)
(negative : (finite_payoff_position (A G)) nil = (1)%Z)
(p : Z) :
left_action (X_def G) (M (P (E (A_def G negative p)))) (actl_def G negative p).
Proof. unfold X_def. unfold A_def. unfold actl_def. unfold action_def.
intros. unfold left_action. split.
+ intros. destruct x. destruct x. destruct s.
++ destruct u. auto.
++ assert (left_action _ _ (actl G)).
{apply restriction_to_left_is_action. }
destruct H. unfold actl in *. rewrite H. auto.
+ intros. destruct x. destruct x. destruct s.
++ destruct u. auto.
++ assert (left_action _ _ (actl G)).
{apply restriction_to_left_is_action. }
destruct H. unfold actl in *. rewrite H0. auto.
Qed.

Fact restriction_to_right_is_action_proof (G : AsynchronousGame)
(negative : (finite_payoff_position (A G)) nil = (1)%Z)
(p : Z) :
right_action (Y_def G) (M (P (E (A_def G negative p)))) (actr_def G negative p).
Proof. unfold X_def. unfold A_def. unfold actr_def. unfold action_def.
intros. unfold right_action. split.
+ intros. destruct x. destruct x. destruct s.
++ destruct u. auto.
++ assert (right_action _ _ (actr G)).
{apply restriction_to_right_is_action. }
destruct H. unfold actr in *. rewrite H. auto.
+ intros. destruct x. destruct x. destruct s.
++ destruct u. auto.
++ assert (right_action _ _ (actr G)).
{apply restriction_to_right_is_action. }
destruct H. unfold actr in *. rewrite H0. auto.
Qed.

Fact coherence_1_proof (G : AsynchronousGame) 
(negative : (finite_payoff_position (A G)) nil = (1)%Z)
(p : Z) : forall m n g h,
    leq_def (P (E (A G))) m n -> 
    leq_def (P (E (A G)))
    (action_def G negative p g m h) 
    (action_def G negative p g n h).
Proof. unfold leq_def. unfold action_def.
intros. simpl. destruct m. simpl in H. destruct x.
destruct s.
+ destruct u. auto.
+ destruct n. destruct x. destruct s.
++ contradiction H.
++ apply coherence_1. auto.
Qed.

Fact coherence_2_proof (G : AsynchronousGame) 
(negative : (finite_payoff_position (A G)) nil = (1)%Z)
(p : Z) :
forall m g h,
    polarity_def (A G) (action_def G negative p g m h) = polarity_def (A G) m.
Proof. unfold polarity_def. unfold action_def.
intros. destruct m. destruct x. destruct s.
+ destruct u. auto.
+ simpl. apply coherence_2.
Qed.

Fact action_preserves_initial_proof (G : AsynchronousGame) 
(negative : (finite_payoff_position (A G)) nil = (1)%Z)
(p : Z) :
forall i g h,
    exists i', action_def G negative p g (existT _ i (inl tt)) h = existT _ i' (inl tt).
Proof. unfold action_def.
intros. destruct i. refine (ex_intro _ tt _). auto.
Qed.

Fact action_preserves_non_initial_proof (G : AsynchronousGame) 
(negative : (finite_payoff_position (A G)) nil = (1)%Z)
(p : Z) :
forall i g h m,
    exists i' m', action_def G negative p g (existT _ i (inr m)) h = existT _ i' (inr m').
Proof. unfold action_def.
intros. destruct i. refine (ex_intro _ tt _).
refine (ex_intro _ (action G g m h) _). auto.
Qed.*)



