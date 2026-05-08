(* ==================================================================
   MaynardVerifyDef.v -- definitions for the Z-level cross-check
   between the FLINT-shipped integer matrices and Maynard's closed
   form, plus the fast M1 check.

   The heavy M2 check is split across MaynardVerifyM2_0..5.v (one
   chunk of 7 rows per file, parallelised by `make -j`); the assembly
   lives in MaynardVerify.v.
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
   Per-entry Z-level cross-multiplication checks.
   ------------------------------------------------------------------ *)

Definition M1_entry_matchZ (i j : nat) : bool :=
  Z.eqb (BinInt.Z.mul (m1_num i j) D_M1)
        (BinInt.Z.mul (mat_get M1_int i j) (m1_den i j)).

Definition M2_entry_matchZ (i j : nat) : bool :=
  Z.eqb (BinInt.Z.mul (m2_num i j) D_M2)
        (BinInt.Z.mul (mat_get M2_int i j) (m2_den i j)).

(* ------------------------------------------------------------------
   Row-restricted M2 check used by the chunked Qeds.

   `M2_check_rows rows` runs the full 42-column check on each row in
   `rows`.  The 6 chunks in MaynardVerifyM2_0..5.v each prove
   `M2_check_rows [k; k+1; ...; k+6] = true` by `vm_compute`; the
   assembly in MaynardVerify.v re-builds `seq 0 42` from those 6
   subranges via `forallb_app` and concludes `all_match_M2Z = true`.
   ------------------------------------------------------------------ *)

Definition M2_check_rows (rows : list nat) : bool :=
  List.forallb
    (fun i => List.forallb (fun j => M2_entry_matchZ i j) (List.seq 0 42))
    rows.

Definition all_match_M1Z : bool :=
  List.forallb
    (fun i => List.forallb (fun j => M1_entry_matchZ i j) (List.seq 0 42))
    (List.seq 0 42).

Definition all_match_M2Z : bool := M2_check_rows (List.seq 0 42).

(* ------------------------------------------------------------------
   M1 closed-form match: ~90 s on this machine.  No splitting needed.
   ------------------------------------------------------------------ *)

Lemma all_match_M1Z_true : all_match_M1Z = true.
Proof. vm_compute. reflexivity. Qed.
