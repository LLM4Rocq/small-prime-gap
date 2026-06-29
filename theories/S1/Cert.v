(* theories/S1/Cert.v  (rayleigh branch — slim, Rayleigh-quotient route)

   This file is the slim auditor's bridge from the paper-form spec
   `MaynardSpec.M{1,2}_spec_ij` to the FLINT-shipped integer matrices
   `Witness.M{1,2}_int / Witness.D_M{1,2}`:

       M_{i,j}_spec  =  Z2rat (mat_get M_int i j) / Z2rat D_M
                                          for all  i, j < 42.

   The theorem `CertRayleigh.maynard_M105_certified_rayleigh` combines
   this two-way identity (which gives auditor-level parity with Maynard's
   paper formulas) with the strict Rayleigh-quotient bound on
   `(v_witness, M1, M2)`.

   This file itself uses no eigenvalue, characteristic polynomial,
   realalg, IVT, Sturm, or CRT machinery; the only Z-level Qed it feeds
   downstream is the entry-by-entry `all_match_M{1,2}Z = true` check
   from `MaynardVerify/Def.v` + `MaynardVerify/M2_{0..5}.v`.  (The
   eigenvalue theorem `MaynardEigen.maynard_M105_certified` does build a
   characteristic polynomial mod p, perform a Chinese-remainder lift, and
   exhibit an eigenvalue > 4, all axiom-free; IVT / Sturm / realalg are
   used nowhere.) *)

From Stdlib Require Import ZArith.

From mathcomp Require Import all_boot all_algebra.
Import GRing.Theory.

From PrimeGapS1 Require Import IntMat Witness.
From PrimeGapS1 Require Import MaynardVerify MaynardSpec MaynardSpecBridge.
From PrimeGapS1.MaynardVerify Require Import Def.

Local Open Scope ring_scope.

Lemma D_M1_pos : Z.lt 0 D_M1. Proof. by vm_compute. Qed.
Lemma D_M2_pos : Z.lt 0 D_M2. Proof. by vm_compute. Qed.

(* `Opaque` is re-declared here (does not propagate via Require) so
   the unifier doesn't expand `mat_get M{1,2}_int` during proofs that
   touch the per-entry booleans. *)
Opaque M1_entry_matchZ M2_entry_matchZ.

Lemma M1_spec_eq_int {i j} :
  (i < 42)%nat -> (j < 42)%nat ->
  M1_spec_ij i j = Z2rat (mat_get M1_int i j) / Z2rat D_M1.
Proof.
  move=> Hi Hj.
  rewrite M1_spec_rat_eq.
  move: (M1_entry_match_in_grid Hi Hj).
  rewrite M1_entry_matchZ_E => /Z.eqb_eq Hcross.
  rewrite [m1_num_den_at i j]surjective_pairing.
  by apply: qfrac_eq_div;
    [exact: m1_num_den_at_den_pos | exact: D_M1_pos | exact: Hcross].
Qed.

Lemma M2_spec_eq_int {i j} :
  (i < 42)%nat -> (j < 42)%nat ->
  M2_spec_ij i j = Z2rat (mat_get M2_int i j) / Z2rat D_M2.
Proof.
  move=> Hi Hj.
  rewrite M2_spec_rat_eq.
  move: (M2_entry_match_in_grid Hi Hj).
  rewrite M2_entry_matchZ_E => /Z.eqb_eq Hcross.
  rewrite [m2_num_den_at i j]surjective_pairing.
  by apply: qfrac_eq_div;
    [exact: m2_num_den_at_den_pos | exact: D_M2_pos | exact: Hcross].
Qed.
