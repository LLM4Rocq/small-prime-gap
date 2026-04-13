(* CharPolyScale.v — char_poly scaling formula

   For an n×n matrix M over a field F and nonzero scalar c:
     (char_poly (c *: M))`_k = c ^+ (n - k) * (char_poly M)`_k
   for all k ≤ n.

   Proof strategy:
   1. Factor c%:P from the polynomial matrix:
        'X%:M - c%:P *: M^polyC = c%:P *: ((c^-1)%:P *: 'X%:M - M^polyC)
   2. Apply detZ: det(c%:P *: A) = c%:P ^+ n * det(A)
   3. Recognize the inner matrix as char_poly_mx M composed with c^-1 *: 'X
   4. Use det_map_mx to get det(map_mx f A) = f(det A) for rmorphism f
   5. Extract coefficients: (c^n * p(X/c))_k = c^(n-k) * p_k
*)

From mathcomp Require Import all_boot all_algebra.
Import GRing.Theory.

Open Scope ring_scope.

Section CharPolyScaling.
Variable (F : fieldType) (n : nat).

(* Coefficient of p composed with c^-1 *: 'X *)
Lemma coef_comp_scaleX (c : F) (p : {poly F}) (k : nat) :
  c != 0 ->
  (p \Po (c^-1 *: 'X))`_k = c^-1 ^+ k * p`_k.
Proof.
move=> Hc.
rewrite coef_comp_poly.
under eq_bigr do rewrite exprZn coefZ coefXn mulrA.
case: (ltnP k (size p)) => Hk.
- rewrite (bigD1 (Ordinal Hk)) //= eqxx mulr1.
  rewrite big1; first by rewrite addr0 mulrC.
  move=> i Hi.
  suff -> : (k == i :> nat) = false by rewrite mulr0.
  apply/negbTE/negP => /eqP Hki.
  move/negP: Hi; apply; apply/eqP/ord_inj => /=.
  exact: esym Hki.
- rewrite nth_default ?mulr0 //.
  apply: big1 => i _.
  suff -> : (k == i :> nat) = false by rewrite mulr0.
  apply/negbTE/negP => /eqP Hki.
  have : (i < size p)%N := ltn_ord i.
  by rewrite -Hki ltnNge Hk.
Qed.

(* Main result: characteristic polynomial scaling formula *)
Lemma char_poly_scale (c : F) (M : 'M[F]_n) (k : nat) :
  c != 0 ->
  (k <= n)%N ->
  (char_poly (c *: M))`_k = c ^+ (n - k) * (char_poly M)`_k.
Proof.
move=> Hc Hkn.
(* Unfold char_poly and rewrite the scalar multiplication *)
rewrite /char_poly /char_poly_mx map_mxZ /=.
set B := (M ^ polyC)%sesqui.
(* Factor c%:P from the polynomial matrix *)
have Hfactor : 'X%:M - c%:P *: B =
  c%:P *: ((c^-1)%:P *: 'X%:M - B) :> 'M[{poly F}]_n.
  rewrite scalerBr scalerA -polyCM mulrV; last by rewrite unitfE.
  by rewrite polyC1 scale1r.
rewrite Hfactor detZ.
(* Recognize the inner det as char_poly M composed with c^-1 *: 'X *)
have Hcomp : \det ((c^-1)%:P *: 'X%:M - B) =
  (\det ('X%:M - B)) \Po (c^-1 *: 'X).
  have -> : (c^-1)%:P *: 'X%:M - B =
    map_mx (comp_poly (c^-1 *: 'X)) ('X%:M - B) :> 'M[{poly F}]_n.
    apply/matrixP => i j.
    rewrite [RHS]mxE /B !mxE comp_polyB comp_polyC.
    case Hi: (i == j).
      by rewrite !mulr1n comp_polyX mul_polyC.
    rewrite !mulr0n comp_polyC; by rewrite mulr0.
  exact: det_map_mx.
rewrite Hcomp.
(* Extract the coefficient: c^n * (p(X/c))_k = c^(n-k) * p_k *)
set p := \det ('X%:M - B).
rewrite -polyC_exp coefCM coef_comp_scaleX //.
rewrite mulrA exprVn -expfB_cond //.
by rewrite (negbTE Hc) add0n.
Qed.

End CharPolyScaling.
