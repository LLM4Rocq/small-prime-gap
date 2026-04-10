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

Lemma A_rat_unitmx_from_check :
  List.forallb (fun p => check_det_nonzero p M1_int) crt_primes_local = true ->
  List.forallb (fun p => check_det_nonzero p M2_int) crt_primes_local = true ->
  forall (D1 D2 : BinInt.Z),
    D1 <> BinInt.Z0 -> D2 <> BinInt.Z0 ->
    (mat_int_to_rat M1_int D1 42 \in unitmx) /\
    (mat_int_to_rat M2_int D2 42 \in unitmx).
Admitted.
