(* ==================================================================
   CRTPencilPencilBound.v

   Hadamard bound on |D_pencil_int| -- specialises the generic chain
   in `CRTPencilHadamardGeneric.v` to M = pencil_mat_int (the CLEAN
   pencil from Witness_PencilClean.v) and the shipped literal
   `D_pencil_int_value` (= `D_pencil_clean_value`).

   The crt-product bound is the SAME 710-prime CRT product used for
   M1 (~21300 bits, > 2 * |D_pencil_int_value| + 2 * Hadamard bound).
   No prime extension required since the clean pencil's det is only
   2613 bits.
   ================================================================== *)

From Stdlib Require Import ZArith List Lia.
From PrimeGapS1 Require Import IntMat IntPoly Witness CharPoly.
From PrimeGapS1 Require Import AllRowsLenHelper.
From PrimeGapS1 Require Import CRTLift.
From PrimeGapS1 Require Import CertL2.
From PrimeGapS1 Require Import CertPencilDef.
From PrimeGapS1 Require Import Witness_PencilDet.
From PrimeGapS1 Require Import Witness_PencilClean.
From PrimeGapS1 Require Import Witness_PencilBound.
From PrimeGapS1.CharPolyAgree Require Import Def.    (* crt_product_710 *)
From PrimeGapS1 Require Import CRTPencilHadamardGeneric.

Open Scope Z_scope.

(* Row-length hyp lifted via the forallb proof in CertPencilDef. *)
Lemma pencil_mat_int_rows_42_lift :
  forall i, (i < List.length pencil_mat_int)%nat ->
            List.length (List.nth i pencil_mat_int nil) = 42%nat.
Proof.
  intros i Hi. apply pencil_mat_int_wf. lia.
Qed.

(* Hadamard bound on |D_pencil_int| via the generic chain. *)
Lemma D_pencil_int_abs_bound :
  (Z.abs D_pencil_int <= fl_coeff_bound 42 (max_abs_entry pencil_mat_int))%Z.
Proof.
  apply (gen_det_abs_bound pencil_mat_int D_pencil_int pencil_mat_int_dim
           pencil_mat_int_rows_42_lift
           D_pencil_int_eq_nth).
Qed.

(* vm_compute equality between symbolic bound and shipped literal. *)
Lemma fl_coeff_bound_pencil_eq :
  fl_coeff_bound 42 (max_abs_entry pencil_mat_int) = fl_coeff_bound_pencil_value.
Proof. vm_compute. reflexivity. Qed.

Lemma crt_bound_pencil_sufficient_literal :
  (2 * fl_coeff_bound_pencil_value + 2 * Z.abs D_pencil_int_value
   < crt_product_710)%Z.
Proof. apply Z.ltb_lt. vm_compute. reflexivity. Qed.

Lemma crt_bound_pencil_sufficient :
  (2 * fl_coeff_bound 42 (max_abs_entry pencil_mat_int) +
   2 * Z.abs D_pencil_int_value < crt_product_710)%Z.
Proof. rewrite fl_coeff_bound_pencil_eq. exact crt_bound_pencil_sufficient_literal. Qed.
