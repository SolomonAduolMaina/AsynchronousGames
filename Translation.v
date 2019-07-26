Require Import TSO.
Require Import SC.

Fixpoint translate_type (tau : TSO.type) : SC.type := 
match tau with
  | TSO.Nat => Nat
  | TSO.Unit => Unit
  | TSO.NatRef => Product (Ref Nat) (Ref (Arrow Nat (Product Nat Nat)))
  | TSO.Arrow tau tau' => Arrow (translate_type tau) (translate_type tau')
end.

Definition flip : SC.term :=
app (lam "x" (Ref Nat) (fork (deref (var "x")) (assign (var "x") (num 1))))
    (new_ref Nat (num 0)).

Definition choose_n : SC.term :=
app
  (lam "x" (Ref Nat) 
    (fics (Arrow Unit Nat)
        (lam "f" (Arrow Unit Nat) 
          (lam "u" Unit 
            (ifzero flip 
              (deref (var "x")) 
              (seq (assign (var "x") (plus (var "x") (num 1))) (app (var "f") yunit))
            )
          )
        )
      )
    )
  (new_ref Nat (num 0)).

Definition nat_equals (m n: SC.term) :=
ifzero (minus m n) (ifzero (minus n m) (num 1) (num 0)) (num 0).

Definition invalidate (v k : SC.term) :=
assign v
  (lam "x" Nat 
    (ifzero (nat_equals (var "x") k)
      (app (deref v) k)
      (paire (num 0) (second (app (deref v) k)))
    )
  ).

Definition flush (e : SC.term) :=
app
  (lam "k" (Ref (Arrow Nat (Product Nat Nat)))
    (ifzero (first (app (deref (first e)) (var "k")))
            yunit
            (seq 
              (invalidate e (var "k"))
              (assign (second e) (second (app (deref (first e)) (var "k"))))
            )
    )
  )
  choose_n.

Definition flush_many (e : SC.term) :=
fics (Arrow Unit Unit)
  (lam "f" (Arrow Unit Unit) 
    (lam "u" Unit 
      (ifzero flip 
        yunit 
        (seq (flush e) (app (var "f") yunit))
      )
    )
  ).

Definition set_local (v k e : SC.term) :=
assign v
  (lam "n" Nat 
    (ifzero (nat_equals (var "n") k)
            (app (deref v) k)
            (paire (num 1) e)
    )
  ).

Definition local_read (v k : SC.term) := second (app (deref v) k).

Fixpoint translate_term (e : TSO.term) (k : nat) : SC.term := 
match e with
  | TSO.var x => var x
  | TSO.app e1 e2 => app (translate_term e1 k) (translate_term e2 k)
  | TSO.lam x tau e => lam x (translate_type tau) (translate_term e k)
  | TSO.ifzero e e1 e2 => 
    ifzero (translate_term e k) (translate_term e1 k) (translate_term e2 k)
  | TSO.fics tau e => fics (translate_type tau) (translate_term e k)
  | TSO.num n => num n
  | TSO.yunit => yunit
  | TSO.ref n => 
    paire (ref Nat n) (ref (Arrow Nat (Product Nat Nat)) (Nat.mul 2 n))
  | TSO.new_ref =>
    paire (new_ref Nat (num 0)) 
          (new_ref (Arrow Nat (Product Nat Nat)) (lam "x" Nat (paire (num 0) (num 0))))
  | TSO.fork e e' => fork (translate_term e k) (translate_term e' (S k))
  | TSO.assign e e' => 
    let e := translate_term e k in
    let e' := translate_term e' k in
    seq (flush_many e) (seq (set_local (first e) (num k) e') (flush_many e))
  | TSO.deref e => 
    let e := translate_term e k in
    seq (flush_many e)
        (ifzero (first (app (deref (first e)) (num k)))
           (deref (second e))
           (local_read (first e) (num k)))
end.

