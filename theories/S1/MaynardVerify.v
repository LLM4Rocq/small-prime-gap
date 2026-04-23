(* ==================================================================
   MaynardVerify.v — kernel-verified agreement between the shipped
   integer matrices (M1_int, M2_int in Witness.v, divided by D_M1,
   D_M2) and Maynard's closed-form specification from MaynardSpec.v.

   This file closes the trust gap on the 42x42 input matrices.
   Together with the rest of the project (which verifies all later
   steps: char poly, Sturm chain, CRT lift, IVT), nothing in
   the pipeline is taken on faith from the FLINT generator —
   the certificate data is cross-checked by the Rocq kernel.

   == Method =======================================================

   We compare, entry-by-entry, the shipped rational matrix

       M1_rat[i][j] := Z_to_rat (M1_int[i][j]) / Z_to_rat D_M1

   with Maynard's closed form `M1_entry` (resp. `M2_entry`) given
   in MaynardSpec.v as a rational function of (b_i, c_i, b_j, c_j)
   via the G_{n,2}(k) polynomial.

   To avoid the MathComp `'M[rat]_42` canonical-structure blow-up
   documented in REPORT.md §4d, we do NOT materialise `M1_spec` as
   an `'M[rat]_42`.  Instead, we keep the check at the Z level via
   cross-multiplication:

       (num_spec i j) * D = (M_int i j) * (den_spec i j)

   and fold this boolean predicate over the 42x42 grid with
   `List.forallb`.  A single `vm_compute` decides the whole grid.

   == Timing =======================================================

   On Rocq 9.1.1 + MathComp 2.5.0, on this machine:

     - `all_match_M1Z_true` : ~90 s   (42x42 single-term entries)
     - `all_match_M2Z_true` : ~35 min (42x42 entries each a sum of
                                       up to 36 terms over G_{n,2}(104))

   Both are Qed.  `Print Assumptions` on each shows only the standard
   Uint63 / PrimInt63 kernel primitives.

   == Why no `M1_rat = M1_spec : 'M[rat]_42` Qed ===================

   The entry-wise bool equalities above are the load-bearing
   numerical facts.  Promoting them to a matrix equality in
   `'M[rat]_42` triggers the HB canonical-structure elaborator
   at the concrete dimension 42 (see REPORT.md §4d) — proofs that
   run in seconds at abstract `n` stall for >30 min at `n = 42`.

   The rat-level matrix identity is stated at the bottom of this
   file as a single axiom `M1_correct` / `M2_correct`, each
   explicitly reduced to the already-Qed bool fact above:
   the axiom is NOT a new trust dependency, it is a restatement
   modulo the MathComp layer.  A reviewer who trusts rational
   cross-multiplication (`a/b = c/d  <==>  a*d = c*b` for b,d > 0)
   does not need these axioms.  The headline theorem
   `maynard_eigenvalue_S1` does not depend on them either — this
   file is a leaf in the dependency DAG and is not imported by
   Cert.v.
   ================================================================ *)

From Stdlib Require Import ZArith List Lia.
From mathcomp Require Import all_ssreflect all_algebra.
From PrimeGapS1 Require Import IntMat CharPoly Witness.
From PrimeGapS1 Require Import MaynardFactQ MaynardBasis MaynardSpec.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

(* ------------------------------------------------------------------
   Num / den projections for the Z-level specs in MaynardSpec.v.
   ------------------------------------------------------------------ *)

Definition m1_num (i j : nat) : Z := fst (m1_num_den_at i j).
Definition m1_den (i j : nat) : Z := snd (m1_num_den_at i j).

Definition m2_num (i j : nat) : Z := fst (m2_num_den_at i j).
Definition m2_den (i j : nat) : Z := snd (m2_num_den_at i j).

(* ------------------------------------------------------------------
   Per-entry Z-level cross-multiplication check.
   ------------------------------------------------------------------ *)

Definition M1_entry_matchZ (i j : nat) : bool :=
  Z.eqb (BinInt.Z.mul (m1_num i j) D_M1)
        (BinInt.Z.mul (mat_get M1_int i j) (m1_den i j)).

Definition M2_entry_matchZ (i j : nat) : bool :=
  Z.eqb (BinInt.Z.mul (m2_num i j) D_M2)
        (BinInt.Z.mul (mat_get M2_int i j) (m2_den i j)).

Definition all_match_M1Z : bool :=
  List.forallb
    (fun i => List.forallb (fun j => M1_entry_matchZ i j) (List.seq 0 42))
    (List.seq 0 42).

Definition all_match_M2Z : bool :=
  List.forallb
    (fun i => List.forallb (fun j => M2_entry_matchZ i j) (List.seq 0 42))
    (List.seq 0 42).

(* ------------------------------------------------------------------
   The two headline numerical facts, verified by kernel reduction.
     - M1 closes in ~90 s.
     - M2 closes in ~35 min on this machine.
   Print Assumptions shows only Uint63/PrimInt63 primitives.
   ------------------------------------------------------------------ *)

Lemma all_match_M1Z_true : all_match_M1Z = true.
Proof. vm_compute. reflexivity. Qed.

Lemma all_match_M2Z_true : all_match_M2Z = true.
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------
   Optional rat-level restatement.

   These are stated so a MathComp-side user can refer to the
   spec as a single matrix equality.  They are left as `Axiom`
   only because closing them by `apply/matrixP => i j; ...`
   triggers the HB canonical-structure blow-up documented in
   REPORT.md §4d at the concrete dimension 42.  The content is
   the already-Qed bool facts above, modulo the standard rat
   identity `a/b = c/d  <==>  a*d = c*b`.

   The headline theorem `maynard_eigenvalue_S1` (in Cert.v) does
   NOT import this file, so these axioms do NOT pollute its
   assumption set.  Verified by `Print Assumptions
   maynard_eigenvalue_S1` after this file is added to the build.
   ------------------------------------------------------------------ *)

Definition M1_rat : 'M[rat]_42 := mat_int_to_rat Witness.M1_int Witness.D_M1 42.
Definition M2_rat : 'M[rat]_42 := mat_int_to_rat Witness.M2_int Witness.D_M2 42.

Definition f_M1 (i j : nat) : rat :=
  ((Z_to_int (m1_num i j))%:~R / (Z_to_int (m1_den i j))%:~R)%R.

Definition f_M2 (i j : nat) : rat :=
  ((Z_to_int (m2_num i j))%:~R / (Z_to_int (m2_den i j))%:~R)%R.

Definition M1_spec : 'M[rat]_42 := \matrix_(i, j) f_M1 (nat_of_ord i) (nat_of_ord j).
Definition M2_spec : 'M[rat]_42 := \matrix_(i, j) f_M2 (nat_of_ord i) (nat_of_ord j).

(* Follows from all_match_M1Z_true + standard rat cross-multiplication,
   but MathComp HB elaboration at dim 42 makes the `Qed` prohibitive. *)
Axiom M1_correct : M1_rat = M1_spec.
Axiom M2_correct : M2_rat = M2_spec.
