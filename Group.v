Record Group := {
      G : Type;
      mult : G -> G -> G;
      id : G;
      inverse : G -> G;

      associative : forall (x y z : G),
      mult x (mult y z) = mult (mult x y) z;
      id_exists : forall (x : G), 
      mult id x = x /\ mult x id = x;
      inverses_exist : forall (x : G),
      mult x (inverse x) = id /\ mult (inverse x) x = id;
}.

Fact inverse_is_unique (G: Group) : forall x y z,
mult G x y = id G /\ mult G x z = id G -> y = z.
Proof. intros. destruct H. rewrite <- H in H0.
assert (mult G (inverse G x) (mult G x z) = 
mult G (inverse G x) (mult G x y) ).
{  rewrite H0. reflexivity. }
rewrite associative in H1. rewrite associative in H1.
assert (mult G (inverse G x) x = id G).
{ apply inverses_exist. }
rewrite H2 in H1. 
assert (mult G (id G) z = z /\ mult G (id G) y = y).
{ split. 
+ apply id_exists.
+ apply id_exists. }
destruct H3. rewrite H3 in H1. rewrite H4 in H1. auto.
Qed.

Fact mult_inverse (G: Group) : forall g g',
mult G (inverse G g') (inverse G g) = inverse G (mult G g g').
Proof. intros. 
assert (mult G (mult G g g') (mult G (inverse G g') (inverse G g)) = id G /\
mult G (mult G g g') (inverse G (mult G g g')) = id G).
{ assert (mult G (mult G g g') (inverse G (mult G g g')) = id G).
{ apply inverses_exist. }
assert (mult G (mult G g g') (mult G (inverse G g') (inverse G g)) = id G).
{ rewrite associative. 
assert (mult G (mult G g g') (inverse G g') = g).
{ rewrite <- associative.
assert (mult G g' (inverse G g') = id G).
{ apply inverses_exist. }
rewrite H0. apply id_exists.
  }
rewrite H0. apply inverses_exist.
 }
rewrite H. rewrite H0. auto.
} apply inverse_is_unique with (G0:=G) (x:=mult G g g')
(y:=mult G (inverse G g') (inverse G g)) (z:=inverse G (mult G g g')).
auto.
Qed.

Fact inverse_id_is_id (G: Group) : inverse G (id G) = id G.
Proof. apply inverse_is_unique with (G0:=G) (x:=id G) 
(y:= inverse G (id G)) (z:=id G). 
split.
+ apply inverses_exist.
+ apply id_exists.
Qed.

Definition trivial_group : Group.
refine({|
          G := unit;
          mult a b := tt;
          id := tt
      |}).
Proof.
- auto.
- auto.
- intros. destruct x. auto.
- auto.
Defined.

Definition product_group (X Y : Group) : Group.
refine ({|
        G := (G X) * (G Y);
        mult m n := (mult _ (fst m) (fst n), mult _ (snd m) (snd n));
        id := (id _, id _);
        inverse m := (inverse _ (fst m), inverse _ (snd m))
       |}).
Proof.
- intros. destruct x. destruct y. destruct z. simpl.
rewrite associative. rewrite associative. reflexivity.
- intros. destruct x. simpl.
assert (mult _ (id _) g = g /\ mult _ g (id _) = g).
{ apply id_exists. }
assert (mult _ (id _) g0 = g0 /\ mult _ g0 (id _) = g0).
{ apply id_exists. }
destruct H0. destruct H. rewrite H. rewrite H1. rewrite H0. rewrite H2. auto.
- intros. destruct x. simpl. 
assert (mult _ g (inverse _ g) = id _ /\ mult _ (inverse _ g) g = id _).
{ apply inverses_exist. }
assert (mult _ g0 (inverse _ g0) = id _ /\ mult _ (inverse _ g0) g0 = id _).
{ apply inverses_exist. }
destruct H. destruct H0. rewrite H. rewrite H1. rewrite H0. rewrite H2. auto.
Defined.

Definition opposite_group (X : Group) : Group.
refine ({|
        G := (G X) ;
        mult m n := mult X n m;
        id := id X;
        inverse m := inverse X m
       |}).
Proof.
- intros. rewrite associative. auto.
- intros. split.
+ apply id_exists.
+ apply id_exists. 
- intros. split.
+ apply inverses_exist.
+ apply inverses_exist.
Defined.