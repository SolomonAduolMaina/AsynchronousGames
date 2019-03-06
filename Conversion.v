Require Import Strings.String.
Require Import List.
Require Import ZArith.
Require Import LinearLogic.
Require Import Group.
Require Import AsynchronousGames.
Require Import Dual.
Require Import Lifting.
Require Import Sum.
Require Import Tensor.
Require Import Exponential.

Definition interpretation := string -> AsynchronousGame.

Inductive empty_type : Type := .

Definition zero_partial_order : PartialOrder.
refine({| 
            I := empty_type;
            N i := empty_type;
            leq m n := True;
         |}).
Proof.
- intros. destruct x. destruct x.
- intros. destruct x. destruct x.
- intros. destruct x. destruct x.
- intros. destruct i.
- intros. destruct i.
- intros. destruct i.
Defined.

Definition zero_event_structure : EventStructure.
refine({| 
            P := zero_partial_order;
            incompatible m n := True;
            ideal m := nil;
         |}).
Proof.
- intros. destruct x. destruct x.
- intros. destruct x. destruct x.
- intros. destruct x. destruct x.
- intros. destruct x. destruct x.
Defined.

Definition zero_asynchronous_arena : AsynchronousArena.
  refine({| 
            E := zero_event_structure;
            polarity m := true;
            finite_payoff_position l := (-1)%Z;
            finite_payoff_walk w := 0%Z;
             infinite_payoff f inf := True
         |}).
Proof.
- intros. left. auto.
- intros. destruct m. destruct x.
- intros. destruct m. destruct x.
- auto.
Defined.

Definition ZERO : AsynchronousGame.
  refine({| 
             A := zero_asynchronous_arena;
             X := trivial_group;
             Y := trivial_group;
             action g m h := m
        |}).
Proof.
- intros. unfold left_action. split.
+ intros. auto.
+ intros. auto.
- intros. unfold right_action. split.
+ intros. auto.
+ intros. auto.
- intros. destruct m. destruct x.
- intros. destruct m. destruct x.
- intros. destruct i.
- intros. destruct i.
Defined.

Definition TOP : AsynchronousGame := dual ZERO.

Fact top_is_negative : finite_payoff_position (A TOP) nil = (1)%Z.
Proof. intros. auto. Qed.

Definition ONE : AsynchronousGame :=
lifting TOP top_is_negative 0%Z.

Definition BOTTOM : AsynchronousGame := dual ONE.

Fixpoint convert (A : formula) (f : interpretation) :
AsynchronousGame :=
match A with
| prop_variable A => f A
| neg_prop_variable A => dual (f A)
| one => ONE
| bottom => BOTTOM
| zero => ZERO
| top => TOP
| times A B => tensor (convert A f) (convert B f)
| par A B => dual (tensor (dual (convert A f)) (dual (convert B f)))
| plus A B => asynchronous_game_sum (convert A f) (convert B f)
| conj A B => dual (asynchronous_game_sum (dual (convert A f)) (dual (convert B f)))
| of_course A => exponential (convert A f)
| why_not A => dual (exponential (dual (convert A f)))
end.

Definition game_par A B := dual (tensor (dual A) (dual B)).

Fixpoint parify l :=
match l with
| nil => ZERO
| A :: nil => A
| A :: xs => game_par A (parify xs)
end.

Definition interpret (l : sequent) (f : interpretation) :=
parify (map (fun x => convert x f) l).
