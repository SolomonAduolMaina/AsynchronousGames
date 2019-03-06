Require Import AsynchronousGames.
Require Import List.
Import ListNotations.
Open Scope Z.

Arguments existT {_ _}.
Ltac inv H := inversion H; clear H; subst.

(* NOTE: Need better notation *)
Notation "'Opp'" := false.
Notation "'Ply'" := true.

Fixpoint payoff_pos_from_move
         (E: EventStructure) (κ_empty: Z) (κ_M: M (P E) -> Z): Position E -> Z :=
  fix f p :=
    match p with
    | [] => κ_empty
    | [m] => κ_M m
    | _::p => f p
    end.

Section Booleans.

  (* NOTE: Need to change name of fiels I and N, clashes with definitions from ZArith *)
  Definition Bool_PO: PartialOrder.
    refine {|
      I := unit;
      N := fun _ => bool;

      (* NOTE: it's really not reasonable to work with sigma types everywhere *)
      (* NOTE: Only need lt, and take the reflexive closure? *)
      (* NOTE: Use the standard library's typeclasse for POs? *)
      (* NOTE: Could lighten things by defining
         Definition Mtrue := existT _ (inr true), and so on...
         but really what I want is to have:
         Inductive MBool := | MInit | MTrue | MFalse.
       *)
      leq m n :=
        match m,n with
        | existT _ (inl _), _ => True
        | existT _ (inr b1), existT _ (inr b2) => b1 = b2
        | _,_ => False
        end
      |}.
    - intros [[] []]; auto.
    - intros [[] [[]|]] [[] [[]|]]; repeat (subst; intuition).
    - intros [[] [[]|]] [[] [[]|]] [[] [[]|]]; repeat (subst; intuition).
    - intros [] []; unfold iff; auto.
    - intros [] [] [[] |] [[] |]; unfold iff; auto.
    - decide equality.
  Defined.

  Definition Bool_ES: EventStructure.
    refine {|
        P := Bool_PO;
        (* NOTE: Does it change anything to make Mtrue and Mfalse incompatible? *)
        incompatible := fun _ _ => False;
        (* NOTE: Do we actually use in practice the computational content of ideal? *)
        ideal := fun '(existT _ m) =>
                   match m with
                   | inl _ => [existT _ m]
                   | inr _ => [existT _ (inl tt); existT _ m]
                   end
      |}.
    - intros; auto. 
    - intros; auto. 
    - intros [[] [[]|]] [[] [[]|]]; simpl; intuition try (subst; easy).
      inv H; subst; auto.
    - intros [[] [[]|]] [[] [[]|]] [[] [[]|]]; simpl; intuition try easy.
  Defined.

  Definition Bool_AA: AsynchronousArena.
    refine {|
        E := Bool_ES;
        polarity :=
          fun '(existT _ m) =>
            match m with
            | inl _ => Opp 
            | inr _ => Ply
            end;
        finite_payoff_position :=
          payoff_pos_from_move Bool_ES 1 (* Bool is a negative game *)
                               (fun '(existT _ m) => match m with
                                                  | inl _ => -1 (* Opp asked for a value *)
                                                  | inr _ => 0  (* We gave back the value, everyone happy *)
                                                  end);
          (* NOTE: isn't the payoff on finite positions uniquely defined by a payoff function on moves, plus on the empty position?
             By Axiom 6 of arenas, setting x to the empty walk from the empty position.
             See payoff_pos_from_move.
             Actually if you have the polarity function already, you don't even need the payoff of the empty position by Axiom 2.
           *)
        finite_payoff_walk := fun _ => 0;
          (* The only unspecified walks would be
             false/true -> init -> false/true
             init -> init -> false/true
             init -> init -> init
             false/true -> init -> init
             false/true -> false/true -> false/true
             But I'm not quite sure what they should be
           *)
        infinite_payoff := fun _ _ => False;


      |}.
    - (* NOTE: Why such a complicated thing? *)
      right; reflexivity.
    - simpl.
      intros [[] [[] | []]]; unfold initial_move; simpl; intros INIT; intuition.
      inv H.
      specialize (INIT (existT tt (inl tt)) Logic.I).
      inv INIT.
      specialize (INIT (existT tt (inl tt)) Logic.I).
      inv INIT.
    -
      (* This is more complicated than it should *)
      simpl.
      intros [[] []] SECOND.
      + exfalso; destruct u.
        destruct SECOND as [NFIRST _]; apply NFIRST.
        unfold initial_move; simpl.
        intros [[] [[] | []]] H; intuition.
      + split; [intuition |].
        intros abs; inv abs.
    - intros. reflexivity. 
  Defined.

  (* What should be the actions for such a game? *)
  (* Definition Bool_AG: AsynchronousGame. *)
  (*   refine {| *)
  (*       A := Bool_AA *)
  (*     |}. *)


End Booleans.



