Inductive nat : Set :=
  | O : nat
  | S : nat -> nat.


Definition zero := O.
Definition one := S O.

Definition pred n :=
  match n with
    | O => n
    | S u => u
  end.

Fixpoint add n m :=
  match n with
  | O => m
  | S p => S (add p m)
  end.

Compute (add (S O) (S (S O))).

Fixpoint silly n m :=
  match n with
  | O => m
  | S p => silly (S p) (S m)
  end.


Theorem inc_comm : 
  forall  m n :nat, add (S m) n = add m (S n).
intros.
simpl.
induction m.
simpl.
trivial.
simpl.
rewrite <- IHm.
trivial.
Qed.

Theorem addition_commutativity : 
  forall  m n :nat, add m n = add n m.
intros.
induction n.
simpl.
induction m.
simpl.
trivial.
simpl.
rewrite -> IHm.
trivial.
rewrite <- (inc_comm m n).
simpl.
rewrite IHn.
trivial.
Qed.