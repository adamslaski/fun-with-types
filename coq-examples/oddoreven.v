Lemma DoubleInduction : forall p: nat -> Prop, p 0 -> p 1 -> (forall n : nat, p n /\ p (1 + n) -> p (2 + n)) -> forall n : nat, p n.
assert  (X:forall p: nat -> Prop, p 0 -> p 1 -> (forall n : nat, p n /\ p (1 + n) -> p (2 + n)) -> forall n : nat, p n /\ p (1+n)).
intros.
induction n.
split; simpl; assumption.
split.
destruct IHn.
simpl in H3.
assumption.
apply H1.
apply IHn.
intros.
apply X; assumption.
Qed.

Require Import Omega.

Definition OddOrEven n := exists m:nat, n = m + m \/ n = m + m + 1.

Lemma AllOddOrEven : forall n:nat, OddOrEven n.
apply (DoubleInduction OddOrEven); unfold OddOrEven.
exists 0; left; trivial.
exists 0; right; trivial.
intros.
destruct H.
destruct H.
exists (x+1).
destruct H.
left.
omega.
right.
omega.
Qed.


Extraction Language Haskell.
Recursive Extraction AllOddOrEven.
