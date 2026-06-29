(**md**************************************************************************)
(* # EigenBridge                                                             *)
(*                                                                           *)
(* Eigenvalue route for M_{105} > 4 on the rayleigh branch.  Phase 2 here:   *)
(* the rational matrices and the `matches_closed_forms` trust contract.      *)
(* The spectral bridge (Phases 3-5) is added on top of `SpectralCrux` and    *)
(* the positive-definiteness certificate.                                    *)
(*                                                                           *)
(* ```                                                                       *)
(*   M1_rat == M1_int / D_M1   as 'M[rat]_42                                  *)
(*   M2_rat == M2_int / D_M2   as 'M[rat]_42                                  *)
(*   A_rat  == invmx M1_rat *m M2_rat        (= M1^-1 M2)                     *)
(*   M105   == 105 *: A_rat                  (= 105 * M1^-1 M2)               *)
(*   matches_closed_forms M == M is M105 and the paper-form spec entries      *)
(*                             agree with the FLINT-shipped integer data      *)
(* ```                                                                       *)
(******************************************************************************)

From mathcomp Require Import all_ssreflect all_algebra.
From PrimeGapS1 Require Import IntMat CharPoly Witness.
From PrimeGapS1 Require Import MaynardSpec MaynardSpecBridge Cert.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Open Scope ring_scope.

(* The paper-form rational matrices, as genuine mathcomp matrices. *)
Definition M1_rat : 'M[rat]_42 := mat_int_to_rat M1_int D_M1 42.
Definition M2_rat : 'M[rat]_42 := mat_int_to_rat M2_int D_M2 42.

(* The generalized-eigenvalue object and its 105-scaling. *)
Definition A_rat : 'M[rat]_42 := invmx M1_rat *m M2_rat.
Definition M105 : 'M[rat]_42 := 105%:Q *: A_rat.

(* Trust contract: M is the closed-form M105, and the paper spec entries     *)
(* match the FLINT-shipped integer matrices entrywise.                        *)
Definition matches_closed_forms (M : 'M[rat]_42) : Prop :=
  [/\ M = M105,
      (forall i j, (i < 42)%nat -> (j < 42)%nat ->
         M1_spec_ij i j = Z2rat (mat_get M1_int i j) / Z2rat D_M1)
    & (forall i j, (i < 42)%nat -> (j < 42)%nat ->
         M2_spec_ij i j = Z2rat (mat_get M2_int i j) / Z2rat D_M2)].

Lemma matches_closed_forms_M105 : matches_closed_forms M105.
Proof.
split; first by [].
- move=> i j Hi Hj; exact: (M1_spec_eq_int Hi Hj).
- move=> i j Hi Hj; exact: (M2_spec_eq_int Hi Hj).
Qed.
