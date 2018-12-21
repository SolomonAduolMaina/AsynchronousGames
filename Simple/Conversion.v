Require Import LinearLogic.
Require Import AsynchronousGames.

Definition interpretation := propositional_variable -> Game.

Fixpoint convert (A : formula) (f : interpretation) : Game :=
match A with
| prop_variable A => f A
| one => ONE
| bottom => BOTTOM
| zero => ZERO
| top => TOP
| times A B => tensor (convert A f) (convert B f)
| par A B => 
dual (tensor (dual (convert A f)) (dual (convert B f)))
| plus A B => sum (convert A f) (convert B f)
| conj A B => 
dual (sum (dual (convert A f)) (dual (convert B f)))
| of_course A => exponential (convert A f)
| why_not A => dual (exponential (dual (convert A f)))
end.