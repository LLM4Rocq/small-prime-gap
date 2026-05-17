(* ==================================================================
   CRTPencilM1Bound.v

   Hadamard coefficient bound on |det_M1_int|, used by `det_M1_int_eq`
   in `CRTPencilCheck.v`.  Specialises the generic chain in
   `CRTPencilHadamardGeneric.v` to M = M1_int + the shipped literal
   `det_M1_int_value`, then runs the `vm_compute` discharge against
   the precomputed Hadamard literal `fl_coeff_bound_M1_value`.
   ================================================================== *)

From Stdlib Require Import ZArith List Lia.
From PrimeGapS1 Require Import IntMat IntPoly Witness CharPoly.
From PrimeGapS1 Require Import AllRowsLenHelper.
From PrimeGapS1 Require Import CRTLift.
From PrimeGapS1 Require Import CertL2.   (* M1_int_dim'/wf'/rows_42 *)
From PrimeGapS1 Require Import CertPencilDef.   (* det_M1_int *)
From PrimeGapS1 Require Import Witness_PencilDet.
From PrimeGapS1 Require Import Witness_M1Bound.
From PrimeGapS1 Require Import CRTPencilHadamardGeneric.

Open Scope Z_scope.

(* Hadamard bound on |det_M1_int| via the generic chain. *)
Lemma det_M1_int_abs_bound :
  (Z.abs det_M1_int <= fl_coeff_bound 42 (max_abs_entry M1_int))%Z.
Proof.
  apply (gen_det_abs_bound M1_int det_M1_int M1_int_dim'
           (forallb_all_rows_len 42%nat M1_int M1_int_rows_42)
           det_M1_int_eq_nth).
Qed.

(* vm_compute equality between the symbolic bound and the shipped literal. *)
Lemma fl_coeff_bound_M1_eq :
  fl_coeff_bound 42 (max_abs_entry M1_int) = fl_coeff_bound_M1_value.
Proof. vm_compute. reflexivity. Qed.

(* Sufficient inequality on the shipped literals: discharged by vm_compute. *)
Lemma crt_bound_M1_sufficient_literal :
  (2 * fl_coeff_bound_M1_value + 2 * Z.abs det_M1_int_value
   < crt_product_710)%Z.
Proof. apply Z.ltb_lt. vm_compute. reflexivity. Qed.

Lemma crt_bound_M1_sufficient :
  (2 * fl_coeff_bound 42 (max_abs_entry M1_int) +
   2 * Z.abs det_M1_int_value < crt_product_710)%Z.
Proof. rewrite fl_coeff_bound_M1_eq. exact crt_bound_M1_sufficient_literal. Qed.
