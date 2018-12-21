Require Import Strings.String.
Require Import List.

Inductive propositional_variable :=
| variable : string -> propositional_variable
| negation : propositional_variable -> propositional_variable.

Inductive formula :=
| prop_variable : propositional_variable -> formula
| zero : formula
| one : formula
| top : formula
| bottom : formula
| times : formula -> formula -> formula
| par : formula -> formula -> formula
| plus : formula -> formula -> formula
| conj : formula -> formula -> formula
| of_course : formula -> formula
| why_not : formula -> formula.

Fixpoint negate (A : formula) : formula :=
match A with
| prop_variable (variable A) => 
prop_variable (negation (variable A))
| prop_variable (negation A) => prop_variable A
| one => bottom
| bottom => one
| zero => top
| top => zero
| times A B => par (negate A) (negate B)
| par A B => times (negate A) (negate B)
| plus A B => conj (negate A) (negate B)
| conj A B => plus (negate A) (negate B)
| of_course A => why_not (negate A)
| why_not A => of_course (negate A)
end.

Definition sequent := list formula.

Fixpoint why_not_list l :=
match l with
| nil => nil
| x :: xs => (why_not x) :: (why_not_list xs)
end.

Inductive valid (l : sequent) : Prop :=
| axiom : forall (X : propositional_variable),
l = (prop_variable X) :: (negate (prop_variable X)) :: nil ->
valid l
| exchange : forall Gamma A B Delta,
valid (Gamma ++ (A :: B :: nil) ++ Delta) ->
l = (Gamma ++ (B :: A :: nil) ++ Delta) ->
valid l
| cut : forall Gamma Delta A,
valid ((prop_variable A) :: Gamma) ->
valid ((negate (prop_variable A)) :: Delta) ->
l = Gamma ++ Delta ->
valid l
| conj_intro : forall Gamma A B,
valid (A :: Gamma) ->
valid (B :: Gamma) ->
l = (conj A B) :: Gamma ->
valid l
| top_intro : forall Gamma,
l = top :: Gamma ->
valid l
| sum_intro_left : forall Gamma A B,
valid (A :: Gamma) ->
l = (plus A B) :: Gamma ->
valid l
| sum_intro_right : forall Gamma A B,
valid (B :: Gamma) ->
l = (plus A B) :: Gamma ->
valid l
| tensor_intro : forall Gamma Delta A B,
valid (A :: Gamma) ->
valid (B :: Delta) ->
l = (times A B) :: (Gamma ++ Delta) ->
valid l
| one_intro : l = one :: nil -> valid l
| par_intro : forall Gamma A B,
valid (A :: B :: Gamma) ->
l = (par A B) :: Gamma ->
valid l
| bottom_intro : forall Gamma,
l = bottom :: Gamma ->
valid l
| dereliction_why_not : forall A Gamma,
valid (A :: Gamma) ->
l = (why_not A) :: Gamma ->
valid l
| weakening_why_not : forall A Gamma,
valid Gamma ->
l = (why_not A) :: Gamma ->
valid l
| contraction_why_not : forall A Gamma,
valid ((why_not A) :: (why_not A) :: Gamma) ->
l = (why_not A) :: Gamma ->
valid l
| of_course_intro : forall A Gamma,
valid (A :: (why_not_list Gamma)) ->
l = (of_course A) :: (why_not_list Gamma) ->
valid l.






