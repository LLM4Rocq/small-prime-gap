(* ==================================================================
   CRTPencilHadamardGeneric.v

   Generic Hadamard coefficient bound on the constant coefficient of
   `char_poly_int M`, parameterised on
     - the matrix M
     - a proof `mat_dim M = 42`
     - a row-length proof
     - a sealed Z literal D (= constant coef of char_poly_int M)
     - a `det_eq_nth` rewrite linking D to `nth 0 (char_poly_int M)`.

   The two specialisations (M = M1_int with crt_product_710,
   M = pencil_mat_int with crt_product_710 — same product after the
   clean-pencil refactor, since the clean pencil's 2613-bit determinant
   fits in the 710-prime ~21300-bit headroom) then drop to ~10-line
   wrappers around `apply gen_*` + the shipped vm_compute equalities.
   ================================================================== *)

From Stdlib Require Import ZArith List Lia.
From PrimeGapS1 Require Import IntMat IntPoly Witness CharPoly.
From PrimeGapS1 Require Import CRTBridge.
From PrimeGapS1 Require Import AllRowsLenHelper.
From PrimeGapS1 Require Import CRTLift.

Open Scope Z_scope.

Section HadamardGeneric.

Variable M : mat.
Variable D : Z.
Hypothesis M_dim     : mat_dim M = 42%nat.
Hypothesis M_rows_42 : forall i, (i < length M)%nat -> length (nth i M nil) = 42%nat.
Hypothesis det_eq_nth : D = nth 0 (char_poly_int M) 0%Z.

Lemma gen_fl_all_divisible :
  fl_all_divisible 42 Z.one M (meye 42) (mzero 42) Z.one.
Proof.
  apply fl_all_divisible_from_L2; [exact M_dim | exact M_rows_42].
Qed.

Lemma gen_fl_loop_coeff (k : nat) (Hk : (k < 42)%nat) :
  (Z.abs (nth k (fl_loop 42 Z.one M (meye 42) (mzero 42) Z.one nil) 0%Z)
   <= fl_bound_aux 42 1 (Z.of_nat 42) (max_abs_entry M) 0 1 1)%Z.
Proof.
  apply (fl_loop_coeff_bound 42 Z.one M (meye 42) (mzero 42) Z.one
           nil 42 (max_abs_entry M) 0 1 1).
  + exact M_dim.
  + exact M_rows_42.
  + reflexivity.
  + exact (mat_dim_mzero 42).
  + apply all_rows_len_mzero.
  + reflexivity.
  + reflexivity.
  + apply max_abs_entry_nonneg.
  + rewrite max_abs_entry_mzero. reflexivity.
  + reflexivity.
  + reflexivity.
  + intros c' Hc'. destruct Hc'.
  + lia.
  + apply gen_fl_all_divisible.
  + apply nth_In. rewrite fl_loop_length. simpl. exact Hk.
Qed.

Lemma gen_det_abs_bound :
  (Z.abs D <= fl_coeff_bound 42 (max_abs_entry M))%Z.
Proof.
  rewrite det_eq_nth.
  assert (H42 : (0 < 42)%nat) by lia.
  rewrite (char_poly_int_nth_lt M 42 0 M_dim H42).
  unfold fl_coeff_bound.
  exact (gen_fl_loop_coeff 0 H42).
Qed.

End HadamardGeneric.
