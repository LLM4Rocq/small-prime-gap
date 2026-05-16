(* ==================================================================
   CRTPencilM1Bound.v

   Hadamard coefficient bound on |det_M1_int|, used by `det_M1_int_eq`
   in `CRTPencilCheck.v`.  Split out as a sibling file because the
   `vm_compute` discharge on the bound check (line ~30 below) needs to
   re-verify a moderately large Coq term at kernel-Qed time.  Putting
   it next to the heavy `CRTPencilChecksProof.v` (12-min vm_compute
   cache) inflates kernel-Qed time non-monotonically.

   This file imports only what's needed: `Witness` (for M1_int),
   `CRTLift` (for fl_coeff_bound + fl_loop_coeff_bound + crt_product),
   `Witness_PencilDet` (det_M1_int_value), and `Witness_M1Bound` (the
   shipped Hadamard bound literal).  No matter-of-fact mathcomp; the
   ssreflect-style `(k < 42)%coq_nat` clash in `CRTPencilCheck.v` is
   avoided.

   Mirror of `A_int_fl_loop_coeff` / `fl_crt_bound` in `CRTLift.v`.
   ================================================================== *)

From Stdlib Require Import ZArith List Lia.
From PrimeGapS1 Require Import IntMat IntPoly Witness CharPoly.
From PrimeGapS1 Require Import CRTBridge.   (* fl_all_divisible_from_L2 *)
From PrimeGapS1 Require Import CharPolyAgree.   (* forallb_all_rows_len *)
From PrimeGapS1 Require Import CRTLift.
From PrimeGapS1 Require Import CertL2.   (* M1_int_dim'/rows_42/wf' *)
From PrimeGapS1 Require Import CertPencilDef.   (* det_M1_int *)
From PrimeGapS1 Require Import Witness_PencilDet.
From PrimeGapS1 Require Import Witness_M1Bound.

Open Scope Z_scope.

(* ================================================================== *)
(*  fl_all_divisible specialised to M1_int.                            *)
(* ================================================================== *)

Lemma M1_int_fl_all_divisible :
  fl_all_divisible 42 Z.one M1_int (meye 42) (mzero 42) Z.one.
Proof.
  apply fl_all_divisible_from_L2;
    [exact M1_int_dim' | exact (forallb_all_rows_len 42%nat M1_int M1_int_rows_42)].
Qed.

(* ================================================================== *)
(*  Coefficient bound on each fl_loop output entry.                    *)
(* ================================================================== *)

Lemma M1_int_fl_loop_coeff (k : nat) (Hk : (k < 42)%nat) :
  (Z.abs (List.nth k (fl_loop 42 Z.one M1_int (meye 42) (mzero 42) Z.one nil) 0%Z)
   <= fl_bound_aux 42 1 (Z.of_nat 42) (max_abs_entry M1_int) 0 1 1)%Z.
Proof.
  apply (fl_loop_coeff_bound 42 Z.one M1_int (meye 42) (mzero 42) Z.one
            nil 42 (max_abs_entry M1_int) 0 1 1).
  + exact M1_int_dim'.
  + exact (forallb_all_rows_len 42%nat M1_int M1_int_rows_42).
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
  + apply M1_int_fl_all_divisible.
  + apply List.nth_In. rewrite fl_loop_length. simpl. exact Hk.
Qed.

(* ================================================================== *)
(*  Bound on |det_M1_int|.                                             *)
(* ================================================================== *)

Lemma det_M1_int_abs_bound :
  (Z.abs det_M1_int <= fl_coeff_bound 42 (max_abs_entry M1_int))%Z.
Proof.
  rewrite det_M1_int_eq_nth.
  assert (H42 : (0 < 42)%nat) by lia.
  rewrite (char_poly_int_nth_lt M1_int 42 0 M1_int_dim' H42).
  unfold fl_coeff_bound.
  exact (M1_int_fl_loop_coeff 0 H42).
Qed.

(* ================================================================== *)
(*  Hadamard bound check + sufficient inequality.                      *)
(* ================================================================== *)

Lemma fl_coeff_bound_M1_eq :
  fl_coeff_bound 42 (max_abs_entry M1_int) = fl_coeff_bound_M1_value.
Proof. vm_compute. reflexivity. Qed.

Lemma crt_bound_M1_sufficient_literal :
  (2 * fl_coeff_bound_M1_value + 2 * Z.abs det_M1_int_value
   < crt_product_710)%Z.
Proof. apply Z.ltb_lt. vm_compute. reflexivity. Qed.

Lemma crt_bound_M1_sufficient :
  (2 * fl_coeff_bound 42 (max_abs_entry M1_int) +
   2 * Z.abs det_M1_int_value < crt_product_710)%Z.
Proof. rewrite fl_coeff_bound_M1_eq. exact crt_bound_M1_sufficient_literal. Qed.
