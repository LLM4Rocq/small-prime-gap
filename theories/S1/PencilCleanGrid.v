(* ==================================================================
   PencilCleanGrid.v

   Per-entry cross-check between `pencil_int_clean` (shipped via
   `Witness_PencilClean.v`) and the obvious "scaled subtraction"
   formula:

     D_M1 * D_M2 * pencil_int_clean[i][j]
         = D_pencil_clean * (4*D_M2*M1_int[i][j]
                              - 105*D_M1*M2_int[i][j]).

   Both sides equal D_M1 * D_M2 * D_pencil_clean * (4*M1_rat[i][j]
   - 105*M2_rat[i][j]), so the identity is true by construction.  We
   close it as a 42x42 bool grid via `vm_compute`, then extract a
   per-cell corollary for the rational bridge in `CertPencil.v`.

   Same pattern as `MaynardVerify.all_match_M1Z_true` /
   `M1_entry_match_in_grid`.
   ================================================================== *)

From Stdlib Require Import ZArith List Lia.
Import ListNotations.
From mathcomp Require Import ssreflect ssrbool ssrnat.

From PrimeGapS1 Require Import IntMat Witness.
From PrimeGapS1 Require Import Witness_PencilClean.

Open Scope Z_scope.

(* The per-entry equation, as a bool via Z.eqb.  Marked Opaque after the
   eta-style unfold lemma below — the vm_compute Qed should NOT walk this
   Definition body when used by downstream files; the same trick as in
   `MaynardVerify/Def.v`. *)
Definition pencil_clean_match_at (i j : nat) : bool :=
  Z.eqb (D_M1 * D_M2 * mat_get pencil_int_clean i j)
        (D_pencil_clean *
         (4 * D_M2 * mat_get M1_int i j
          - 105 * D_M1 * mat_get M2_int i j)).

Definition all_pencil_clean_match : bool :=
  List.forallb
    (fun i => List.forallb (fun j => pencil_clean_match_at i j) (List.seq 0 42))
    (List.seq 0 42).

Lemma pencil_clean_match_at_E i j :
  pencil_clean_match_at i j =
    (D_M1 * D_M2 * mat_get pencil_int_clean i j
     =? D_pencil_clean *
        (4 * D_M2 * mat_get M1_int i j
         - 105 * D_M1 * mat_get M2_int i j))%Z.
Proof. reflexivity. Qed.

Opaque pencil_clean_match_at.

(* The heavy vm_compute: 1764 cross-multiplications, each at ~2500-bit
   integers (D_M1 * D_M2 * entry + the shipped 689-bit D_pencil_clean
   times the per-entry combination).  Expected ~30 s. *)
Lemma all_pencil_clean_match_true : all_pencil_clean_match = true.
Proof. vm_compute. reflexivity. Qed.

(* Generic forallb_seq projection. *)
Lemma forallb_seq_in_clean {n} {f : nat -> bool} {i} :
  List.forallb f (List.seq 0 n) = true ->
  (i < n)%nat -> f i = true.
Proof.
  move=> H Hi.
  rewrite -> List.forallb_forall in H.
  apply: H.
  apply: (proj2 (List.in_seq n 0 i)).
  split; [apply: Nat.le_0_l | apply/ltP; exact: Hi].
Qed.

(* Per-cell corollary, mirror of `MaynardVerify.M1_entry_match_in_grid`. *)
Lemma pencil_clean_match_in_grid {i j} :
  (i < 42)%nat -> (j < 42)%nat ->
  pencil_clean_match_at i j = true.
Proof.
  move=> Hi Hj.
  have HM := all_pencil_clean_match_true.
  unfold all_pencil_clean_match in HM.
  have Hrow : List.forallb (fun j => pencil_clean_match_at i j) (List.seq 0 42) = true
    := forallb_seq_in_clean HM Hi.
  exact: forallb_seq_in_clean Hrow Hj.
Qed.

(* Z-equality form, ready for use in the rational bridge. *)
Lemma pencil_clean_match_Z {i j} :
  (i < 42)%nat -> (j < 42)%nat ->
  D_M1 * D_M2 * mat_get pencil_int_clean i j =
  D_pencil_clean *
    (4 * D_M2 * mat_get M1_int i j
     - 105 * D_M1 * mat_get M2_int i j).
Proof.
  move=> Hi Hj.
  have H := pencil_clean_match_in_grid Hi Hj.
  rewrite pencil_clean_match_at_E in H.
  by apply Z.eqb_eq in H.
Qed.
