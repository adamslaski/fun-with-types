Inductive ex_t (X:Type) (P : X->Type) : Type :=
ex_t_intro : forall (witness:X), P witness -> ex_t X P.

Notation "'exists_t' x : X , p" := (ex_t _ (fun x:X => p))
(at level 200, x ident, right associativity) : type_scope.

Inductive and_t (A B : Type) : Type :=  conj_t : A -> B -> and_t A B.
Notation "A &&& B" := (and_t A B) (at level 80): type_scope.
Inductive or_t (A B : Type) : Type :=  
  left_t : A -> or_t A B
| right_t : B -> or_t A B.
Notation "A ||| B" := (or_t A B) (at level 85) : type_scope.


Lemma DoubleInduction 
: forall p: nat -> Type, 
  p 0 -> p 1 -> (forall n : nat, p n &&& p (1 + n) -> p (2 + n)) -> forall n : nat, p n.
assert  (
  X:forall p: nat -> Type, 
  p 0 -> p 1 -> (forall n : nat, p n &&& p (1 + n) -> p (2 + n)) -> forall n : nat, p n &&& p (1+n)).
intros.
induction n.
split; simpl; assumption.
split.
destruct IHn.
simpl in p1.
assumption.
apply X1.
apply IHn.
intros.
apply X; assumption.
Qed.

Require Import Omega.

Definition OddOrEven n := exists_t m:nat, (n = m + m) ||| (n = m + m + 1).

Lemma AllOddOrEven : forall n:nat, OddOrEven n.
apply (DoubleInduction OddOrEven); unfold OddOrEven.
exists 0; apply left_t; trivial.
exists 0; right; trivial.
intros.
destruct H.
destruct e.
exists (witness+1).
destruct o.
left.
omega.
right.
omega.
Qed.

Extraction Language Haskell.
Recursive Extraction AllOddOrEven.  

