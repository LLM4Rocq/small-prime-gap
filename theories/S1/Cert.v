(* theories/S1/Cert.v
   ---------------------------------------------------------------
   Per-matrix rat-level identities (auditor checklist item 4):
   paper-form spec entry equals FLINT integer entry over the
   common denominator.

   Composes:
     - MaynardSpecBridge.M{1,2}_spec_rat_eq  (rat = qfrac of Z-pair)
     - MaynardVerify.M{1,2}_entry_match_in_grid  (per-entry from grid)
     - MaynardSpecBridge.qfrac_eq_div  (Z cross-mult -> rat division)
     - MaynardSpecBridge.{D_M{1,2}_pos, m{1,2}_num_den_at_den_pos}

   `M{1,2}_spec_eq_int` are surfaced directly in the headline
   `CertPencil.maynard_M105_certified_pencil`.
   --------------------------------------------------------------- *)

From Stdlib Require Import ZArith List.
Import ListNotations.

From mathcomp Require Import all_boot all_algebra.
Import GRing.Theory Num.Theory.

From PrimeGapS1 Require Import IntMat Witness.
From PrimeGapS1 Require Import MaynardVerify MaynardSpec MaynardSpecBridge.
From PrimeGapS1.MaynardVerify Require Import Def.

Open Scope ring_scope.

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
  have Hmatch : M1_entry_matchZ i j = true := M1_entry_match_in_grid Hi Hj.
  rewrite M1_entry_matchZ_E in Hmatch.
  move/Z.eqb_eq: Hmatch => Hcross.
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
  have Hmatch : M2_entry_matchZ i j = true := M2_entry_match_in_grid Hi Hj.
  rewrite M2_entry_matchZ_E in Hmatch.
  move/Z.eqb_eq: Hmatch => Hcross.
  rewrite [m2_num_den_at i j]surjective_pairing.
  by apply: qfrac_eq_div;
    [exact: m2_num_den_at_den_pos | exact: D_M2_pos | exact: Hcross].
Qed.
