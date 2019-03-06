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

Definition partial_order_lifting (P : PartialOrder) : PartialOrder.
  refine({| 
            I := unit;
            N x := M P;
            leq m n := match m,n with
                       | existT _ tt (inl _), _ => True
                       | existT _ tt (inr m), existT _ tt (inr n) => (leq P) m n
                       | _, _ => False
                       end;
         |}).
Proof. 
- intros. destruct x. destruct x. destruct s.
++ auto.
++ apply reflexive.
- intros. destruct x. destruct x. destruct H. destruct y. destruct x.
destruct s.
+ destruct s0.
++ destruct u. destruct u0. auto.
++ contradiction H0.
+ destruct s0.
++ contradiction H.
++ assert (m = m0).
{apply anti_symmetric. auto. } subst. auto.
- intros. destruct x. destruct y. destruct z. destruct x. destruct x1.
destruct x0. destruct H. destruct s.
+ destruct s0.
++ auto.
++ auto.
+ destruct s0.
++ contradiction H.
++ destruct s1.
+++ apply H0.
+++ apply transitive with (y:=m0). auto.
- intros. destruct i. destruct i'. easy.
- intros. destruct i. destruct i'. auto.
- intros. left. destruct i. destruct j. auto.
Defined.

Definition event_structure_lifting (E : EventStructure) : EventStructure.
  refine({| 
            P := partial_order_lifting (P E);
            incompatible m n := match m,n with
                                | existT _ tt (inr m), existT _ tt (inr n) => incompatible E m n
                                | _, _ => False
                                end;
            ideal m := match m with
                       | existT _ tt (inl tt) => (existT _ tt (inl tt)) :: nil
                       | existT _ tt (inr m) =>
                        (existT _ tt (inl tt)) :: (map (fun x => existT _ tt (inr x)) (ideal E m))
                       end;
         |}).
Proof.
- intros. destruct x. destruct y. destruct x. destruct x0. destruct s0.
+ destruct s;contradiction H.
+ destruct s.
++ auto.
++ apply symmetric. auto.
- unfold not. intros. destruct x. destruct x. destruct s.
+ auto.
+ apply irreflexive in H. auto.
- intros. destruct x. destruct y. destruct x. destruct x0. destruct s.
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
++++ apply in_map_iff. refine (ex_intro _ n0 _). auto.
++ intros. destruct H.
+++ apply inj_pairT2 in H. subst. simpl. auto.
+++ apply in_map_iff in H. destruct H. destruct H.
apply inj_pairT2 in H. subst. simpl. apply ideal_finite. auto.
- intros. destruct x. destruct y. destruct z. destruct x.
destruct x0. destruct x1. destruct s.
+ destruct H. contradiction H.
+ destruct s0.
++ destruct H. contradiction H.
++ destruct s1.
+++ simpl in H. destruct H. auto.
+++ simpl in H. apply incompatible_closed with (y:=n0). auto.
Defined.

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

Fixpoint contains_only_initial E (p : Position (event_structure_lifting E)) :=
match p with
| nil => false
| existT _ tt (inl tt) :: nil => true
| existT _ tt (inl tt) :: xs  => contains_only_initial E xs
| _ => false
end.

Fixpoint cast_to_original E (p : Position (event_structure_lifting E)) :
Position E :=
match p with
| nil => nil
| existT _ tt (inl tt) :: xs => cast_to_original E xs
| existT _ tt (inr m) :: xs => m :: (cast_to_original E xs)
end.

Definition asynchronous_arena_lifting (A : AsynchronousArena) 
(negative : (finite_payoff_position A) nil = (1)%Z)
(p : Z)
: AsynchronousArena.
  refine({| 
            E := event_structure_lifting (E A);
            polarity m := match m with
                          | existT _ tt (inl tt) => true
                          | existT _ tt (inr m) => (polarity A) m
                          end;
            finite_payoff_position l :=
              (match l with
                | nil => (-1)%Z
                | _ => if contains_only_initial _ l then p else
                       finite_payoff_position A (cast_to_original _ l)
              end);
            finite_payoff_walk w :=
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
               end;
            infinite_payoff f inf := match f 0 with
                                      | existT _ tt (inl tt) => (exists g, 
                                        (forall n, n > 0 -> exists m, 
                                        (f n = existT _ tt (inr m) /\ g (n-1) = m /\ 
                                         infinite_payoff A g inf)))
                                      | _ => False
                                     end;
         |}).
Proof.
- left. auto.
- intros. destruct m. destruct x. destruct s.
+ destruct u. easy.
+ rewrite initial_is_unit in H. destruct H. inversion H.
- intros. destruct m. destruct x. rewrite second_in_lifting_is_initial in H.
destruct H. inversion H. subst. 
assert (initial_move _ (existT (fun i : I (P (E A)) => (unit + N (P (E A)) i)%type) x
      (inl tt)) ).
{apply initial_is_unit. refine (ex_intro _ x _). auto. }
apply polarity_first in H0. rewrite negative in H0. intuition.
- intros. destruct w. destruct p0. destruct p1. simpl in *. destruct H. subst. simpl.
destruct p0; destruct p1; auto.
Defined.

Definition lifting (G : AsynchronousGame) 
(negative : (finite_payoff_position (A G)) nil = (1)%Z)
(p : Z)
: AsynchronousGame.
  refine({| 
             A := asynchronous_arena_lifting (A G) negative p;
             X := X G;
             Y := Y G;
             action g m h := match m with
                                | existT _ tt (inl tt) => m
                                | existT _ tt (inr m) => 
                                  existT _ tt (inr (action G g m h))
                             end;
        |}).
Proof.
- intros. unfold left_action. split.
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
- intros. unfold right_action. split.
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
- intros. simpl. destruct m. simpl in H. destruct x.
destruct s.
+ destruct u. auto.
+ destruct n. destruct x. destruct s.
++ contradiction H.
++ apply coherence_1. auto.
- intros. destruct m. destruct x. destruct s.
+ destruct u. auto.
+ simpl. apply coherence_2.
- intros. destruct i. refine (ex_intro _ tt _). auto.
- intros. destruct i. refine (ex_intro _ tt _).
refine (ex_intro _ (action G g m h) _). auto.
Defined.

Fact positive_lifting_is_positive :
forall (G : AsynchronousGame) 
(neg : (finite_payoff_position (A G)) nil = (1)%Z)
(p : Z),
finite_payoff_position 
(A (lifting G neg p)) nil = (-1)%Z.
Proof. intros. auto. Qed.
