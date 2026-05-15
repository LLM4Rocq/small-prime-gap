From Stdlib Require Import ZArith.
From mathcomp Require Import all_ssreflect all_algebra.

Import GRing.Theory.
Local Open Scope ring_scope.

(* The auxiliary identity: char_poly evaluated at l is det(l*I - A). *)
Lemma char_poly_horner_eval (R : comRingType) (n : nat) (A : 'M[R]_n) (l : R) :
  (char_poly A).[l] = \det (l%:M - A).
Proof.
have e : map_mx (horner_eval l) (char_poly_mx A) = l%:M - A.
  apply/matrixP=> i j; rewrite !mxE.
  rewrite horner_evalE hornerD hornerN hornerC.
  by rewrite hornerMn hornerX.
rewrite -e det_map_mx.
by rewrite /char_poly /=.
Qed.

(* The main "pencil" identity: relates det of the matrix pencil
   `l*M1 - M2` to char_poly of M1^{-1}*M2. *)
Lemma det_pencil (R : comUnitRingType) (n : nat) (M1 M2 : 'M[R]_n) (l : R) :
  M1 \in unitmx ->
  \det (l *: M1 - M2) = \det M1 * (char_poly (invmx M1 *m M2)).[l].
Proof.
move=> uM1.
have step : l *: M1 - M2 = M1 *m (l%:M - invmx M1 *m M2).
  rewrite mulmxBr mul_mx_scalar mulmxA mulmxV //.
  by rewrite mul1mx.
by rewrite step det_mulmx char_poly_horner_eval.
Qed.
