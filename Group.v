Require Import Logic.FunctionalExtensionality.
Require Import Logic.ProofIrrelevance.

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

Definition indexed_product_group (X : Group) (I : Type) : Group.
refine ({|
        G := I -> (G X);
        mult f g := (fun i => mult X (f i) (g i));
        id := (fun i => id X);
        inverse f := (fun i => inverse X (f i));
       |}).
Proof.
- intros. apply functional_extensionality. intros. apply associative.
- intros.
assert ((fun i : I => mult X (id X) (x i)) = (fun i : I => x i)).
{apply functional_extensionality. intros. apply id_exists. }
assert ((fun i : I => mult X (x i) (id X)) = (fun i : I => x i)).
{apply functional_extensionality. intros. apply id_exists. }
rewrite H. rewrite H0. auto.
- intros.
assert ((fun i : I => mult X (x i) (inverse X (x i))) = (fun i : I => id X)).
{apply functional_extensionality. intros. apply inverses_exist. }
assert ((fun i : I => mult X (inverse X (x i)) (x i)) = (fun i : I => id X)).
{apply functional_extensionality. intros. apply inverses_exist. }
rewrite H. rewrite H0. auto.
Defined.

Definition bijective A (f : (A -> A) * (A -> A)) :=
(forall a, (fst f) ((snd f) a) = a /\ (snd f) ((fst f) a) = a).

Fact bijections_compose : forall A (f g : (A -> A) * (A -> A)),
bijective A f -> bijective A g->
bijective A ((fun x => (fst g) ((fst f) x)), (fun x => (snd f) ((snd g) x))).
Proof. intros. unfold bijective in *. destruct f. destruct g. simpl in *.
simpl. unfold bijective. split.
+ intros. assert (a (a0 (a2 a3)) = a2 a3). {apply H. }
rewrite H1. apply H0.
+ intros. assert (a2 (a1 (a a3)) = a a3). {apply H0. }
rewrite H1. apply H.
Qed.

Fact identity_is_bijective : forall A,
bijective A ((fun x => x), (fun x => x)).
Proof. intros. unfold bijective. auto.
Qed.

Fact inverse_is_bijective : forall A (f : ((A -> A) * (A -> A))),
bijective A f -> bijective A (snd f, fst f).
Proof. intros. destruct f. unfold bijective. unfold bijective in H.
simpl. simpl in *. split; apply H.
Qed.

Definition permutation_group (A : Type) : Group.
refine ({|
        G := {f : ((A -> A) * (A -> A)) | bijective A f};
        mult m n := let (f, p) := m in
                    let (g, p') := n in
                    exist (bijective A) 
                    ((fun x => (fst g) ((fst f) x)), 
                    (fun x => (snd f) ((snd g) x)))
                    (bijections_compose A f g p p');
        id := exist (bijective A) ((fun x => x), (fun x => x))
             (identity_is_bijective A);
        inverse m := let (f, p) := m in 
                     exist (bijective A) (snd f, fst f) 
                     (inverse_is_bijective A f p);
       |}).
Proof.
- intros. destruct x. destruct y. destruct z. destruct x.
destruct x0. destruct x1. simpl in *. simpl.
apply subset_eq_compat. auto.
- intros. destruct x. destruct x. simpl. split.
+ apply subset_eq_compat. auto.
+ apply subset_eq_compat. auto.
- intros. destruct x. destruct x. simpl. split.
+ apply subset_eq_compat. unfold bijective in b. simpl in *.
assert ((fun x : A => a0 (a x) ) = (fun x : A => x) ).
{apply functional_extensionality. intros. apply b. }
rewrite H. auto.
+ apply subset_eq_compat. unfold bijective in b. simpl in *.
assert ((fun x : A => a (a0 x) ) = (fun x : A => x) ).
{apply functional_extensionality. intros. apply b. }
rewrite H. auto.
Defined.

Definition wreath_product (X : Group) : Group.
refine ({|
        G := (G (indexed_product_group X nat)) * (G (permutation_group nat));
        mult m n := let (gs, bij) := m in
                    let (f, p) := bij in 
                    let (pi, _) := f in
                    let (gs', bij') := n in
                    let (f', p') := bij' in 
                    let (pi', _) := f' in
                    let new_gs := (fun i => mult _ (gs' (pi i)) (gs i) ) in
                    let new_bij := exist _
                    ((fun x => (fst f') ((fst f) x)), 
                    (fun x => (snd f) ((snd f') x)))
                    (bijections_compose _ f f' p p') in (new_gs, new_bij);
        id := ((fun _ => id X), exist _ ((fun n => n), (fun n => n)) (identity_is_bijective _));
        inverse m := let (gs, bij) := m in
                    let (f, p) := bij in 
                    let (pi, pi_inv) := f in
                    let new_bij := inverse _ bij in 
                    let new_f := (fun n => inverse _ (gs (pi_inv n))) in
                    (new_f, new_bij)
       |}).
Proof.
- intros. destruct x. destruct y. destruct z. destruct g0. destruct x.
destruct g2. destruct x. destruct g4. destruct x. simpl. f_equal.
+ apply functional_extensionality. intros. rewrite associative. auto.
+ apply subset_eq_compat. auto.
- intros. destruct x. destruct g0. destruct x. simpl. split.
+ f_equal.
++ apply functional_extensionality. intros. apply id_exists.
++ apply subset_eq_compat. auto.
+ f_equal.
++ apply functional_extensionality. intros. apply id_exists.
++ apply subset_eq_compat. auto.
- intros. destruct x. destruct g0. destruct x. simpl. split.
+ f_equal.
++ apply functional_extensionality. intros. unfold bijective in b.
simpl in b. assert (n0 (n x) = x). {apply b. } rewrite H.
apply inverses_exist.
++ apply subset_eq_compat. unfold bijective in b. simpl in b. f_equal.
+++ apply functional_extensionality. intros. apply b.
+++ apply functional_extensionality. intros. apply b.
+ f_equal.
++ apply functional_extensionality. intros. unfold bijective in b.
simpl in b. apply inverses_exist.
++ apply subset_eq_compat. unfold bijective in b. simpl in b. f_equal.
+++ apply functional_extensionality. intros. apply b.
+++ apply functional_extensionality. intros. apply b.
Defined.
