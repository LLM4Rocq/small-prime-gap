(* ============================================================== *)
(*  Smoke.v -- chain[0] anchor for the IVT proof.                  *)
(*                                                                  *)
(*  After the cleanup branch only `chain_0_matches_charpoly` lives  *)
(*  here, the foundational round-trip that ties chain[0] (lifted    *)
(*  from BigZ) to `charpoly_int`, consumed by                       *)
(*  `CertL1.shipped_chain_hd` -> `CertL1.maynard_L1_concrete`.      *)
(*                                                                  *)
(*  The IVT route reads only signs_at_x0[0] and signs_at_inf[0],    *)
(*  whose anchoring goes via this lemma plus CRTSigns.signs_at_*    *)
(*  _shipped.  Chain entries 1..42 of the shipped Sturm chain are   *)
(*  not consumed by the headline; the 10-prime PRS cross-check      *)
(*  that earlier validated those entries was retired in the         *)
(*  cleanup branch.                                                 *)
(* ============================================================== *)

From Stdlib Require Import ZArith List.
Import ListNotations.
Open Scope Z_scope.

From PrimeGapS1 Require Import Witness WitnessChain Recompose IntPoly.
From Bignums Require Import BigZ.

(* The first chain entry (chain[0]) is the integer-cleared char poly itself,
   so it must equal `lift_bigZ chain_0 = charpoly_int`.  This is the
   foundational sanity round-trip: bigZ → Z conversion produces the same
   polynomial that Witness.v ships separately as `charpoly_int`. *)
Lemma chain_0_matches_charpoly :
  lift_bigZ chain_0 = charpoly_int.
Proof. vm_compute. reflexivity. Qed.
