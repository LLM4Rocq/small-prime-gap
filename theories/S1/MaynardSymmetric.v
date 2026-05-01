(* ==================================================================
   MaynardSymmetric.v — entry-wise symmetry of M1_int and M2_int.

   M_1 and M_2 are Gram matrices of L^2 inner products on the
   42-dim restricted subspace of polynomial test functions; they are
   manifestly symmetric on the paper side.  This file kernel-checks
   that the FLINT-shipped integer matrices satisfy the symmetric
   property entry-wise.

   This closes one of the two implicit hypotheses that Maynard's
   Lemma 8.3 needs (the other being that M_1 is positive definite,
   which is a more substantial formalization since MathComp does not
   define `posdef` — see AUDIT.md / REPORT.md).

   Both lemmas are independent of `MaynardVerify.v` (no dependency on
   the closed-form spec); they read only the shipped integer matrices
   from `Witness.v`.
   ================================================================== *)

From Stdlib Require Import ZArith List.
From mathcomp Require Import all_ssreflect.
From PrimeGapS1 Require Import IntMat Witness.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Per-entry symmetry test. *)
Definition M1_sym_entry (i j : nat) : bool :=
  Z.eqb (mat_get M1_int i j) (mat_get M1_int j i).

Definition M2_sym_entry (i j : nat) : bool :=
  Z.eqb (mat_get M2_int i j) (mat_get M2_int j i).

Definition M1_is_symmetric_b : bool :=
  List.forallb
    (fun i => List.forallb (fun j => M1_sym_entry i j) (List.seq 0 42))
    (List.seq 0 42).

Definition M2_is_symmetric_b : bool :=
  List.forallb
    (fun i => List.forallb (fun j => M2_sym_entry i j) (List.seq 0 42))
    (List.seq 0 42).

(* The two headline numerical facts.  Each is decided by a single
   vm_compute on a 42x42 grid (faster than MaynardVerify's spec
   cross-check, since no closed-form spec is recomputed). *)

Lemma M1_int_symmetric : M1_is_symmetric_b = true.
Proof. vm_compute. reflexivity. Qed.

Lemma M2_int_symmetric : M2_is_symmetric_b = true.
Proof. vm_compute. reflexivity. Qed.
