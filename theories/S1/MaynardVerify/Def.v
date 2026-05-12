(* ==================================================================
   MaynardVerify/Def.v -- definitions for the Z-level cross-check
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

(* ------------------------------------------------------------------
   Eta-style unfold lemmas, proved BEFORE making the per-entry
   booleans opaque.  Downstream uses `rewrite M{1,2}_entry_matchZ_E`
   to expose the Z.eqb form without touching the Definition (which
   `Opaque` blocks below).
   ------------------------------------------------------------------ *)

Lemma M1_entry_matchZ_E i j :
  M1_entry_matchZ i j
  = (m1_num i j * D_M1 =? mat_get M1_int i j * m1_den i j)%Z.
Proof. by []. Qed.

Lemma M2_entry_matchZ_E i j :
  M2_entry_matchZ i j
  = (m2_num i j * D_M2 =? mat_get M2_int i j * m2_den i j)%Z.
Proof. by []. Qed.

(* ------------------------------------------------------------------
   Mark the per-entry booleans Opaque: prevents the unifier from
   eagerly delta-reducing them into `mat_get M{1,2}_int` and
   expanding the 1764-cell FLINT matrix during downstream
   typechecking.  Cert.v rewrites via `M{1,2}_entry_matchZ_E` above.
   ------------------------------------------------------------------ *)

Opaque M1_entry_matchZ M2_entry_matchZ.

(* ------------------------------------------------------------------
   Generic: extract a per-element bool from a 42-grid forallb.
   ------------------------------------------------------------------ *)

Lemma forallb_seq_in {n} {f : nat -> bool} {i} :
  List.forallb f (List.seq 0 n) = true ->
  (i < n)%nat -> f i = true.
Proof.
  move=> H Hi.
  rewrite -> List.forallb_forall in H.
  apply: H; apply: (proj2 (List.in_seq n 0 i)).
  by split; [apply: Nat.le_0_l | apply/ltP; exact: Hi].
Qed.

(* ------------------------------------------------------------------
   Per-entry corollary of `all_match_M1Z_true`.  M2 sibling lives in
   MaynardVerify.v next to the chunk-assembled `all_match_M2Z_true`.
   ------------------------------------------------------------------ *)

Lemma M1_entry_match_in_grid {i j} :
  (i < 42)%nat -> (j < 42)%nat ->
  M1_entry_matchZ i j = true.
Proof.
  move=> Hi Hj.
  have HM := all_match_M1Z_true.
  rewrite /all_match_M1Z in HM.
  have Hrow : forallb (M1_entry_matchZ i) (List.seq 0 42) = true
    := forallb_seq_in HM Hi.
  exact: forallb_seq_in Hrow Hj.
Qed.
