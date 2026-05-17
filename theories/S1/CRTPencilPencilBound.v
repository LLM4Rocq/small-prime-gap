(* ==================================================================
   CRTPencilPencilBound.v

   Hadamard bound on |D_pencil_int| -- specialises the generic chain
   in `CRTPencilHadamardGeneric.v` to M = pencil_mat_int and the
   shipped literal `D_pencil_int_value`.

   The crt-product bound is 1210-prime (~32500 bits, > 2 *
   |D_pencil_int_value|), assembled in `CRTPencilExtraPrimesProof.v`.
   ================================================================== *)

From Stdlib Require Import ZArith List Lia.
From PrimeGapS1 Require Import IntMat IntPoly Witness CharPoly.
From PrimeGapS1 Require Import AllRowsLenHelper.
From PrimeGapS1 Require Import CRTLift.
From PrimeGapS1 Require Import CertL2.
From PrimeGapS1 Require Import CertPencilDef.
From PrimeGapS1 Require Import Witness_PencilDet.
From PrimeGapS1 Require Import Witness_PencilBound.
From PrimeGapS1 Require Import CRTPencilExtraPrimes.
From PrimeGapS1 Require Import CRTPencilExtraPrimesProof.   (* crt_product_pencil *)
From PrimeGapS1 Require Import CRTPencilHadamardGeneric.

Open Scope Z_scope.

(* Hadamard bound on |D_pencil_int| via the generic chain.  The
   row-length hyp is built directly from `pencil_mat_int_wf`. *)
Lemma D_pencil_int_abs_bound :
  (Z.abs D_pencil_int <= fl_coeff_bound 42 (max_abs_entry pencil_mat_int))%Z.
Proof.
  apply (gen_det_abs_bound pencil_mat_int D_pencil_int pencil_mat_int_dim
           (fun i Hi => pencil_mat_int_wf i Hi)
           D_pencil_int_eq_nth).
Qed.

(* vm_compute equality between symbolic bound and shipped literal. *)
Lemma fl_coeff_bound_pencil_eq :
  fl_coeff_bound 42 (max_abs_entry pencil_mat_int) = fl_coeff_bound_pencil_value.
Proof. vm_compute. reflexivity. Qed.

Lemma crt_bound_pencil_sufficient_literal :
  (2 * fl_coeff_bound_pencil_value + 2 * Z.abs D_pencil_int_value
   < crt_product_pencil)%Z.
Proof. apply Z.ltb_lt. vm_compute. reflexivity. Qed.

Lemma crt_bound_pencil_sufficient :
  (2 * fl_coeff_bound 42 (max_abs_entry pencil_mat_int) +
   2 * Z.abs D_pencil_int_value < crt_product_pencil)%Z.
Proof. rewrite fl_coeff_bound_pencil_eq. exact crt_bound_pencil_sufficient_literal. Qed.
