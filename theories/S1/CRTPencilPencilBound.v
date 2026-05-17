(* ==================================================================
   CRTPencilPencilBound.v

   Hadamard bound on |D_pencil_int| via `fl_coeff_bound 42
   (max_abs_entry pencil_mat_int)` — analogue of `CRTPencilM1Bound.v`
   for the pencil matrix.

   Shipped literal `fl_coeff_bound_pencil_value` in
   `Witness_PencilBound.v` (34348 bits, computed by Python from the
   same recurrence as `fl_bound_aux`).

   Together with `crt_product_pencil_pos` (from
   `CRTPencilExtraPrimesProof.v`, 1210-prime product ~32500 bits),
   this gives the sufficient inequality

     2 * fl_coeff_bound 42 (max_abs_entry pencil_mat_int)
     + 2 * |D_pencil_int_value| < crt_product_pencil

   used by `D_pencil_int_eq` in the lift below.
   ================================================================== *)

From Stdlib Require Import ZArith List Lia.
From mathcomp Require Import all_ssreflect.
From PrimeGapS1 Require Import IntMat IntPoly Witness CharPoly.
From PrimeGapS1 Require Import CRTBridge.
From PrimeGapS1 Require Import AllRowsLenHelper.
From PrimeGapS1 Require Import CRTLift.
From PrimeGapS1 Require Import CertL2.   (* M1_int_dim'/wf' (and M2 lemmas below) *)
From PrimeGapS1 Require Import CertPencilDef.   (* pencil_mat_int, D_pencil_int, etc *)
From PrimeGapS1 Require Import Witness_PencilDet.
From PrimeGapS1 Require Import Witness_PencilBound.
From PrimeGapS1 Require Import CRTPencilExtraPrimes.
From PrimeGapS1 Require Import CRTPencilExtraPrimesProof.   (* crt_product_pencil *)

Open Scope Z_scope.

(* ================================================================== *)
(*  fl_all_divisible specialised to pencil_mat_int.                    *)
(* ================================================================== *)

Lemma pencil_mat_int_fl_all_divisible :
  fl_all_divisible 42 Z.one pencil_mat_int (meye 42) (mzero 42) Z.one.
Proof.
  apply fl_all_divisible_from_L2.
  - exact pencil_mat_int_dim.
  - apply forallb_all_rows_len.
    apply List.forallb_forall. intros row Hrow.
    apply List.In_nth with (d := nil) in Hrow.
    destruct Hrow as [i [Hi <-]].
    apply Nat.eqb_eq.
    have HM := pencil_mat_int_wf.
    have Hpenc_42 : length pencil_mat_int = 42%nat
      by move: pencil_mat_int_dim; unfold mat_dim.
    rewrite Hpenc_42 in Hi.
    exact (HM i Hi).
Qed.

(* ================================================================== *)
(*  Coefficient bound on fl_loop output for pencil_mat_int.            *)
(* ================================================================== *)

Lemma pencil_mat_int_fl_loop_coeff (k : nat) (Hk : (k < 42)%coq_nat) :
  (Z.abs (List.nth k (fl_loop 42 Z.one pencil_mat_int (meye 42) (mzero 42) Z.one nil) 0%Z)
   <= fl_bound_aux 42 1 (Z.of_nat 42) (max_abs_entry pencil_mat_int) 0 1 1)%Z.
Proof.
  apply (fl_loop_coeff_bound 42 Z.one pencil_mat_int (meye 42) (mzero 42) Z.one
            nil 42 (max_abs_entry pencil_mat_int) 0 1 1).
  + exact pencil_mat_int_dim.
  + apply forallb_all_rows_len.
    apply List.forallb_forall. intros row Hrow.
    apply List.In_nth with (d := nil) in Hrow.
    destruct Hrow as [i [Hi <-]].
    apply Nat.eqb_eq.
    have Hpenc_42 : length pencil_mat_int = 42%nat
      by move: pencil_mat_int_dim; unfold mat_dim.
    rewrite Hpenc_42 in Hi.
    exact (pencil_mat_int_wf i Hi).
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
  + apply pencil_mat_int_fl_all_divisible.
  + apply List.nth_In. rewrite fl_loop_length. simpl. exact Hk.
Qed.

(* ================================================================== *)
(*  Bound on |D_pencil_int|.                                           *)
(* ================================================================== *)

Lemma D_pencil_int_abs_bound :
  (Z.abs D_pencil_int <= fl_coeff_bound 42 (max_abs_entry pencil_mat_int))%Z.
Proof.
  rewrite D_pencil_int_eq_nth.
  assert (H42 : (0 < 42)%coq_nat) by lia.
  rewrite (char_poly_int_nth_lt pencil_mat_int 42 0 pencil_mat_int_dim H42).
  unfold fl_coeff_bound.
  exact (pencil_mat_int_fl_loop_coeff 0 H42).
Qed.

(* ================================================================== *)
(*  Hadamard inequality: 2 * bound + 2 * |literal| < crt_product_pencil. *)
(* ================================================================== *)

(* fl_coeff_bound 42 (max_abs_entry pencil_mat_int) = shipped literal.
   vm_compute equality. *)
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
