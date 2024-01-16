Require Import Reals.

Local Open Scope R_scope.

Lemma abs_triangle_inequality :
  forall x y : R, Rabs (x + y) <= Rabs x + Rabs y.
Proof.
  intros x y.
  apply Rabs_triang.
Qed.
