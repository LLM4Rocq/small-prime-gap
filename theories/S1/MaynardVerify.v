(* ==================================================================
   MaynardVerify.v — kernel-verified agreement between the shipped
   integer matrices (M1_int, M2_int in Witness.v, divided by D_M1,
   D_M2) and Maynard's closed-form specification from MaynardSpec.v.

   This file closes the trust gap on the 42x42 input matrices by
   assembling six per-row-range chunks of the M2 check (proved in
   parallel by `make -j` from MaynardVerify/M2_0..5.v), plus the
   re-export of the M1 check `all_match_M1Z_true` from
   MaynardVerify/Def.v.

   == Method =======================================================

   We compare, entry-by-entry, the shipped rational matrix

       M1_rat[i][j] := Z_to_rat (M1_int[i][j]) / Z_to_rat D_M1

   with Maynard's closed form `M1_entry` (resp. `M2_entry`) given in
   MaynardSpec.v as a rational function of (b_i, c_i, b_j, c_j) via
   the G_{n,2}(k) polynomial.

   To avoid the MathComp `'M[rat]_42` canonical-structure blow-up
   (REPORT.md §4d), the check stays at the Z level via
   cross-multiplication

       (num_spec i j) * D = (M_int i j) * (den_spec i j),

   folded as a `forallb` over the 42x42 grid.

   == Timing on the cleanup branch =================================

   M1: a single ~90 s `vm_compute` Qed (`all_match_M1Z_true`,
   MaynardVerify/Def.v).

   M2: split into six 7-row chunks (`MaynardVerify/M2_<k>.v`,
   k = 0..5) so `make -j` runs them concurrently.  The assembly
   `all_match_M2Z_true` below stitches them via `forallb_app` plus
   the trivial `seq_split_42` rewrite — no per-entry recomputation.

   == Why no `M1_rat = M1_spec : 'M[rat]_42` Qed ===================

   The entry-wise bool equalities above carry the load-bearing
   numerical content.  Promoting them to a matrix equality in
   `'M[rat]_42` triggers the HB canonical-structure elaborator at
   the concrete dimension 42 (REPORT.md §4d): proofs that run in
   seconds at abstract `n` stall for >30 min at `n = 42`.

   `Print Assumptions` on `all_match_M1Z_true` and
   `all_match_M2Z_true` reports only the standard
   `PrimInt63` / `Uint63Axioms` primitive-integer interface.
   ================================================================ *)

From Stdlib Require Import ZArith List Lia.
From mathcomp Require Import all_ssreflect all_algebra.

From PrimeGapS1.MaynardVerify Require Export Def.
From PrimeGapS1.MaynardVerify Require Import
  M2_0 M2_1 M2_2 M2_3 M2_4 M2_5.

Import ListNotations.

(* ------------------------------------------------------------------
   Trivial helpers for the row-range assembly.
   ------------------------------------------------------------------ *)

Lemma seq_split_42 :
  List.seq 0 42 =
    List.seq 0 7 ++ List.seq 7 7 ++ List.seq 14 7
    ++ List.seq 21 7 ++ List.seq 28 7 ++ List.seq 35 7.
Proof. vm_compute. reflexivity. Qed.

Lemma M2_check_rows_app : forall l1 l2 : list nat,
  M2_check_rows (l1 ++ l2) = M2_check_rows l1 && M2_check_rows l2.
Proof. intros l1 l2. apply List.forallb_app. Qed.

(* ------------------------------------------------------------------
   Assembly: six 7-row chunks compose to the full 42-row check.
   ------------------------------------------------------------------ *)

Lemma all_match_M2Z_true : all_match_M2Z = true.
Proof.
  unfold all_match_M2Z.
  rewrite seq_split_42.
  rewrite !M2_check_rows_app.
  rewrite M2_check_rows_0_6 M2_check_rows_7_13 M2_check_rows_14_20
          M2_check_rows_21_27 M2_check_rows_28_34 M2_check_rows_35_41.
  reflexivity.
Qed.
