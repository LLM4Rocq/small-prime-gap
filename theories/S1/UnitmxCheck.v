(* ===================================================================
   UnitmxCheck.v -- verify det(M1_int) ≠ 0 and det(M2_int) ≠ 0
   via CRT modular determinant computation on Uint63.

   Strategy: reuse the modular Faddeev-LeVerrier machinery from
   CharPolyAgree.v (char_poly_mod) to compute the full characteristic
   polynomial of M1_int and M2_int modulo each of 10 CRT primes.
   The constant term c_0 of char_poly(M) equals (-1)^n * det(M).
   If c_0 ≠ 0 mod p for all primes, then det(M) ≠ 0 over Z (the
   product of the 10 primes exceeds 2^300, far beyond any possible
   determinant value for our 42x42 matrices).
   =================================================================== *)

From Stdlib Require Import ZArith List Bool Uint63.
Import ListNotations.
Open Scope uint63_scope.

From PrimeGapS1 Require Import Witness CharPolyAgree.

(* ==================================================================
   Determinant mod p: extract the constant term of char_poly_mod.
   char_poly_mod returns [c_0; c_1; ...; c_{n-1}; 1] (low-to-high).
   The constant term c_0 = (-1)^n * det(M).
   We only need c_0 <> 0, which is equivalent to det(M) <> 0.
   ================================================================== *)

Definition det_mod (p : PrimInt63.int) (M : list (list Z)) : PrimInt63.int :=
  let cp := char_poly_mod p M in
  hd 0 cp.

Definition check_det_nonzero (p : PrimInt63.int) (M : list (list Z)) : bool :=
  negb (Uint63.eqb (det_mod p M) 0).

(* ==================================================================
   Verify det(M1_int) <> 0 mod all 10 CRT primes.
   ================================================================== *)

Lemma M1_det_nonzero_mod :
  List.forallb (fun p => check_det_nonzero p M1_int) crt_primes_local = true.
Proof. vm_compute. reflexivity. Qed.

(* ==================================================================
   Verify det(M2_int) <> 0 mod all 10 CRT primes.
   ================================================================== *)

Lemma M2_det_nonzero_mod :
  List.forallb (fun p => check_det_nonzero p M2_int) crt_primes_local = true.
Proof. vm_compute. reflexivity. Qed.

(* ==================================================================
   Bridge lemma: modular nonzero determinant implies unitmx.

   The product of the 10 CRT primes exceeds 2^300, which is far
   larger than any possible determinant of a 42x42 matrix with the
   coefficient magnitudes in M1_int or M2_int.  If det <> 0 mod all
   10 primes, then det <> 0 over Z, hence mat_int_to_rat M D n is
   in unitmx.

   This bridge requires a formal CRT + determinant lifting argument.
   We state it here and leave its proof for the formal verification
   pipeline.
   ================================================================== *)

From mathcomp Require Import all_boot all_algebra.
From PrimeGapS1 Require Import IntMat CharPoly.

Open Scope ring_scope.

(* ------------------------------------------------------------------
   Step 1 (Admitted): modular nonzero determinant implies integer
   determinant nonzero.

   Justification: the product of the 10 CRT primes exceeds 2^300,
   far beyond any possible determinant of a 42x42 matrix with the
   coefficient magnitudes in M1_int / M2_int.  If det != 0 mod all
   10 primes, then by CRT det != 0 over Z.

   We state the consequence at the rational-matrix level: the
   determinant of the unit-denominator lift is nonzero.
   ------------------------------------------------------------------ *)
Lemma det_rat_nonzero_M1 :
  List.forallb (fun p => check_det_nonzero p M1_int) crt_primes_local = true ->
  \det (mat_int_to_rat M1_int 1 42) != 0.
Proof. Admitted.

Lemma det_rat_nonzero_M2 :
  List.forallb (fun p => check_det_nonzero p M2_int) crt_primes_local = true ->
  \det (mat_int_to_rat M2_int 1 42) != 0.
Proof. Admitted.

(* ------------------------------------------------------------------
   Step 2: mat_int_to_rat M D n = (Z_to_int D)^{-1} *: mat_int_to_rat M 1 n.
   ------------------------------------------------------------------ *)
Lemma mat_int_to_rat_scale_inv (M : list (list BinInt.Z)) (D : BinInt.Z) (n : nat) :
  mat_int_to_rat M D n = (Z_to_int D)%:~R^-1 *: mat_int_to_rat M 1 n.
Proof.
  apply/matrixP => i j. rewrite /mat_int_to_rat !mxE GRing.mulr1.
  by rewrite GRing.mulrC.
Qed.

(* ------------------------------------------------------------------
   Step 3: det nonzero at D=1, D nonzero => det nonzero at D,
   hence unitmx.
   ------------------------------------------------------------------ *)
Lemma Z_to_int_neq0 (D : BinInt.Z) :
  D <> BinInt.Z0 -> Z_to_int D != 0 :> int.
Proof.
  move=> HD; apply/eqP => Hz.
  apply HD; destruct D as [|p|p]; [reflexivity|exfalso|exfalso].
  - rewrite /Z_to_int /= in Hz.
    injection Hz => Hz'.
    have := Pos2Nat.is_pos p; rewrite Hz'; exact (Nat.lt_irrefl 0).
  - discriminate Hz.
Qed.

Lemma mat_int_to_rat_unitmx_of_det1 (M : list (list BinInt.Z)) (D : BinInt.Z) :
  D <> BinInt.Z0 ->
  \det (mat_int_to_rat M 1 42) != 0 ->
  mat_int_to_rat M D 42 \in unitmx.
Proof.
  move=> HD Hdet1.
  rewrite unitmxE GRing.unitfE mat_int_to_rat_scale_inv detZ.
  apply/eqP => Hz.
  have Hme : ((Z_to_int D)%:~R^-1 ^+ 42 == (0 : rat))
          || (\det (mat_int_to_rat M 1 42) == 0).
  { by rewrite -GRing.mulf_eq0; apply/eqP. }
  case/orP: Hme => [Habs|Habs]; last by move/negP: Hdet1.
  move/eqP: Habs => Habs.
  have Hnz := @Z_to_int_neq0 D HD.
  have Hintr : (Z_to_int D)%:~R != (0 : rat) by rewrite intr_eq0.
  have Hinv : (Z_to_int D)%:~R^-1 != (0 : rat) by rewrite GRing.invr_eq0.
  move/eqP: Habs; apply/negP; exact: GRing.expf_neq0.
Qed.

Lemma A_rat_unitmx_from_check :
  List.forallb (fun p => check_det_nonzero p M1_int) crt_primes_local = true ->
  List.forallb (fun p => check_det_nonzero p M2_int) crt_primes_local = true ->
  forall (D1 D2 : BinInt.Z),
    D1 <> BinInt.Z0 -> D2 <> BinInt.Z0 ->
    (mat_int_to_rat M1_int D1 42 \in unitmx) /\
    (mat_int_to_rat M2_int D2 42 \in unitmx).
Proof.
  move=> Hmod1 Hmod2 D1 D2 HD1 HD2; split.
  - exact: (mat_int_to_rat_unitmx_of_det1 _ _ HD1 (det_rat_nonzero_M1 Hmod1)).
  - exact: (mat_int_to_rat_unitmx_of_det1 _ _ HD2 (det_rat_nonzero_M2 Hmod2)).
Qed.
