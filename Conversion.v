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

Inductive empty_type : Type := .

Definition ZERO : AsynchronousGame :=
        {| 
            I := empty_type;
            N i := empty_type;
            leq m n := True;

            incompatible m n := True;
            ideal m := nil;

            polarity m := true;
            finite_payoff_position l := (-1)%Z;
            finite_payoff_walk w := 0%Z;
            infinite_payoff f inf := True;
            positive_or_negative := true;

            X := trivial_group;
            Y := trivial_group;
            action g m h := m
        |}.

Definition TOP : AsynchronousGame := dual ZERO.

Fact top_is_negative : positive_or_negative TOP = false%Z.
Proof. auto. Qed.

Definition ONE : AsynchronousGame :=
lifting TOP top_is_negative 0%Z.

Definition BOTTOM : AsynchronousGame := dual ONE.

Definition interpretation := string -> AsynchronousGame.

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
