(* ==================================================================
   CertPencilDef.v

   Integer-side definitions for the determinant-pencil M_{105} > 4
   proof.

   * pencil_mat_int : the CLEAN integer pencil
       pencil_int_clean[i][j] := D_pencil_clean * (4*M1_rat[i][j]
                                                   - 105*M2_rat[i][j]),
     shipped in Witness_PencilClean.v.  The clean pencil scales by
     D_pencil_clean (689 bits) instead of D_M1*D_M2 (1368 bits), so
     |det| is 2613 bits (vs. 31131 in the old `4*D_M2*M1 - 105*D_M1*M2`
     formulation).  The clean determinant fits comfortably under the
     710-prime CRT product — no prime extension is required.

   * D_pencil_int : the constant coef of `char_poly_int pencil_mat_int`
     (= det up to sign for n = 42), sealed via a sigT witness so the
     Qed kernel never reduces through it.  The shipped literal
     `D_pencil_clean_value` (in Witness_PencilClean.v) is the integer
     value, closed against D_pencil_int by the 710-prime CRT chain in
     `CRTPencilCheck.v`.

   * det_M1_int : same sigT seal for det(M1_int), with literal
     `det_M1_int_value` shipped in Witness_PencilDet.v (unchanged).

   Structural facts (dim/wf/non-emptiness of fl_loop output) needed
   downstream by the CRT cross-check and the eigenvalue assembly.

   This file uses ONLY Stdlib + the project's integer-level modules
   (`IntMat`, `IntPoly`, `Witness`, `CharPoly`).  No mathcomp/algebra
   imports.  Compiles in <30s.
   ================================================================== *)

From Stdlib Require Import ZArith List Lia.
Import ListNotations.

From mathcomp Require Import all_ssreflect.

From PrimeGapS1 Require Import IntMat IntPoly Witness CharPoly.
From PrimeGapS1 Require Import CertL2.   (* M1_int_dim' / M1_int_wf' *)
From PrimeGapS1 Require Import Witness_PencilClean. (* pencil_int_clean *)

Open Scope Z_scope.

(* ================================================================== *)
(*  Z-side definitions                                                  *)
(* ================================================================== *)

(* Subtract two Z-vectors / Z-matrices via add/neg-scale.  We keep
   `vadd` (already in IntMat.v) and define the negated-scale form
   inline; we also alias `vsub`/`msub` for readability. *)

Definition vsub (xs ys : list Z) : list Z :=
  vadd xs (vscale (-1) ys).

Definition msub (A B : list (list Z)) : list (list Z) :=
  madd A (mscale (-1) B).

(* The integer pencil matrix at l = 4/105.  We use the CLEAN pencil
   shipped in Witness_PencilClean.v, equal entry-wise to
     D_pencil_clean * (4*M1_rat - 105*M2_rat).
   Cross-multiplication identity:
     D_M1 * D_M2 * pencil_int_clean[i][j]
       = D_pencil_clean * (4*D_M2*M1_int[i][j] - 105*D_M1*M2_int[i][j])
   is closed in PencilCleanGrid.v. *)

Definition pencil_mat_int : list (list Z) := pencil_int_clean.

(* The integer determinants.  Both are extracted as the constant
   coefficient of `char_poly_int` (which equals det up to sign;
   for n = 42 even, the sign factor is +1).

   Strong sealing via Qed-protected sigT witness — `Opaque` alone is
   insufficient because the kernel can still reduce through it during
   Qed-time conversion checks.  By going through `proj1_sig` of a
   Qed-sealed `existsT`, the body is truly hidden from the kernel.
   The bridge lemmas `det_M1_int_eq_nth` / `D_pencil_int_eq_nth` give
   downstream code access to the value without unsealing. *)

Lemma det_M1_int_witness : { z : Z | z = List.nth 0 (char_poly_int M1_int) BinInt.Z0 }.
Proof. exists (List.nth 0 (char_poly_int M1_int) BinInt.Z0). reflexivity. Qed.

Lemma D_pencil_int_witness : { z : Z | z = List.nth 0 (char_poly_int pencil_mat_int) BinInt.Z0 }.
Proof. exists (List.nth 0 (char_poly_int pencil_mat_int) BinInt.Z0). reflexivity. Qed.

Definition det_M1_int : Z := proj1_sig det_M1_int_witness.
Definition D_pencil_int : Z := proj1_sig D_pencil_int_witness.

Lemma det_M1_int_eq_nth :
  det_M1_int = List.nth 0 (char_poly_int M1_int) BinInt.Z0.
Proof. exact (proj2_sig det_M1_int_witness). Qed.

Lemma D_pencil_int_eq_nth :
  D_pencil_int = List.nth 0 (char_poly_int pencil_mat_int) BinInt.Z0.
Proof. exact (proj2_sig D_pencil_int_witness). Qed.

(* ================================================================== *)
(*  Structural facts                                                    *)
(* ================================================================== *)

(* List-level helpers, used in pencil_mat_int_{dim,wf}. *)
Lemma length_vadd_eq (xs ys : list Z) :
  length xs = length ys -> length (vadd xs ys) = length xs.
Proof.
  revert ys. induction xs as [|x xs IH]; intros [|y ys] Hlen; simpl in *;
  try discriminate; try reflexivity.
  injection Hlen as Hlen'. rewrite IH; auto.
Qed.

Lemma length_vscale (c : Z) (xs : list Z) : length (vscale c xs) = length xs.
Proof. by rewrite /vscale List.length_map. Qed.

Lemma nth_madd_eq (A B : mat) (i : nat) :
  length A = length B ->
  List.nth i (madd A B) nil = vadd (List.nth i A nil) (List.nth i B nil).
Proof.
  revert B i. induction A as [|a A IH]; intros [|b B] [|i] Hlen;
  simpl in *; try discriminate; try reflexivity.
  apply IH. lia.
Qed.

Lemma length_madd (A B : mat) :
  length A = length B ->
  length (madd A B) = length A.
Proof.
  revert B. induction A as [|a A IH]; intros [|b B] Hlen;
  simpl in *; try discriminate; try reflexivity.
  injection Hlen as Hlen'. by rewrite IH.
Qed.

(* M2_int's structural facts (M1_int's are in CertL2.v). *)
Lemma M2_int_dim' : mat_dim M2_int = 42%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma M2_int_rows_42 : forallb (fun row => Nat.eqb (List.length row) 42) M2_int = true.
Proof. vm_compute. reflexivity. Qed.

Lemma M2_int_wf' : forall i, (i < length M2_int)%coq_nat ->
  length (List.nth i M2_int []) = 42%nat.
Proof.
  intros i Hi.
  pose proof (proj1 (List.forallb_forall _ _) M2_int_rows_42
                    (List.nth i M2_int [])
                    (List.nth_In _ _ Hi)) as H.
  apply Nat.eqb_eq in H. exact H.
Qed.

(* pencil_mat_int = pencil_int_clean: dim 42 and wf, verified by vm_compute
   on the shipped 42x42 literal. *)
Lemma pencil_mat_int_dim : mat_dim pencil_mat_int = 42%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma pencil_mat_int_rows_42 :
  forallb (fun row => Nat.eqb (List.length row) 42) pencil_mat_int = true.
Proof. vm_compute. reflexivity. Qed.

Lemma pencil_mat_int_wf : forall i, (i < length pencil_mat_int)%coq_nat ->
  length (List.nth i pencil_mat_int []) = 42%nat.
Proof.
  intros i Hi.
  pose proof (proj1 (List.forallb_forall _ _) pencil_mat_int_rows_42
                    (List.nth i pencil_mat_int [])
                    (List.nth_In _ _ Hi)) as H.
  apply Nat.eqb_eq in H. exact H.
Qed.

(* char_poly_int *_neq_nil: FL produces a length-43 list, so non-empty. *)
Lemma char_poly_int_pencil_neq_nil : char_poly_int pencil_mat_int <> nil.
Proof. unfold char_poly_int. destruct (fl_loop _ _ _ _ _ _ _); discriminate. Qed.

Lemma char_poly_int_M1_int_neq_nil : char_poly_int M1_int <> nil.
Proof. unfold char_poly_int. destruct (fl_loop _ _ _ _ _ _ _); discriminate. Qed.
