(* ==================================================================
   MaynardBasis.v — the 42-element basis matching Witness.basis.

   Order is the Mathematica xExponents[5]/yExponents[5] enumeration
   (see flint_probe.py:xExponents_mma / yExponents_mma).  The bridge
   lemma `maynard_basis_eq_witness` pins it to the shipped `basis`
   list in `Witness.v` by `vm_compute`.
   ================================================================== *)

From Stdlib Require Import List.
From mathcomp Require Import all_ssreflect.
From PrimeGapS1 Require Import Witness.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition maynard_basis : list (nat * nat) :=
  [ (0, 0); (1, 0); (0, 1); (2, 0); (1, 1); (3, 0)
  ; (0, 2); (2, 1); (4, 0); (1, 2); (3, 1); (5, 0)
  ; (0, 3); (2, 2); (4, 1); (6, 0); (1, 3); (3, 2)
  ; (5, 1); (7, 0); (0, 4); (2, 3); (4, 2); (6, 1)
  ; (8, 0); (1, 4); (3, 3); (5, 2); (7, 1); (9, 0)
  ; (0, 5); (2, 4); (4, 3); (6, 2); (8, 1); (10, 0)
  ; (1, 5); (3, 4); (5, 3); (7, 2); (9, 1); (11, 0)
  ]%nat.

Lemma maynard_basis_size : length maynard_basis = 42.
Proof. reflexivity. Qed.

Lemma maynard_basis_eq_witness : maynard_basis = Witness.basis.
Proof. vm_compute. reflexivity. Qed.
