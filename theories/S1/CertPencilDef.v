(* ==================================================================
   CertPencilDef.v

   Integer-side definitions for the determinant-pencil M_{105} > 4
   proof: the pencil matrix `pencil_mat_int := 4*D_M2*M1_int -
   105*D_M1*M2_int`, its determinant `D_pencil_int`, and the
   determinant of `M1_int` (`det_M1_int`).

   Structural facts (dim/wf/non-emptiness of fl_loop output) needed
   downstream by the CRT cross-check in `CRTPencilCheck.v` and the
   eigenvalue assembly in `CertPencil.v`.

   This file uses ONLY Stdlib + the project's integer-level modules
   (`IntMat`, `IntPoly`, `Witness`, `CharPoly`).  No mathcomp/algebra
   imports.  Compiles in <30s.  Splitting it out of `CertPencil.v`
   avoids re-doing the heavy mathcomp elaboration each time the CRT
   bridge file is touched.
   ================================================================== *)

From Stdlib Require Import ZArith List Lia.
Import ListNotations.

From mathcomp Require Import all_ssreflect.

From PrimeGapS1 Require Import IntMat IntPoly Witness CharPoly.
From PrimeGapS1 Require Import CertL2.   (* M1_int_dim' / M1_int_wf' *)

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

(* The integer pencil matrix at l = 4/105: clear the denominator 105
   by multiplying l *: M1_rat - M2_rat through by D_M1 * D_M2 * 105.
   Concretely we work with
     N := 4 * D_M2 * M1_int  +  (-(105 * D_M1)) * M2_int
   as a list (list Z). *)

Definition pencil_mat_int : list (list Z) :=
  madd (mscale (BinInt.Z.mul 4 D_M2) M1_int)
       (mscale (BinInt.Z.opp (BinInt.Z.mul 105 D_M1)) M2_int).

(* The integer determinants.  Both are extracted as the constant
   coefficient of `char_poly_int` (which equals det up to sign;
   for n = 42 even, the sign factor is +1). *)

Definition D_pencil_int : Z :=
  List.nth 0 (char_poly_int pencil_mat_int) BinInt.Z0.

Definition det_M1_int : Z := List.nth 0 (char_poly_int M1_int) BinInt.Z0.

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

(* pencil_mat_int dimension and well-formedness. *)
Lemma pencil_mat_int_dim : mat_dim pencil_mat_int = 42%nat.
Proof.
  rewrite /pencil_mat_int /mat_dim.
  have HM1 : length M1_int = 42%nat by move: M1_int_dim'; unfold mat_dim.
  have HM2 : length M2_int = 42%nat by move: M2_int_dim'; unfold mat_dim.
  rewrite length_madd; rewrite /mscale !List.length_map; first by exact: HM1.
  by rewrite HM1 HM2.
Qed.

Lemma pencil_mat_int_wf : forall i, (i < length pencil_mat_int)%coq_nat ->
  length (List.nth i pencil_mat_int []) = 42%nat.
Proof.
  intros i Hi.
  have Hwf1 := M1_int_wf'.
  have Hwf2 := M2_int_wf'.
  have HM1_42 : length M1_int = 42%nat by move: M1_int_dim'; unfold mat_dim.
  have HM2_42 : length M2_int = 42%nat by move: M2_int_dim'; unfold mat_dim.
  have HmsM1_42 : length (mscale (BinInt.Z.mul 4 D_M2) M1_int) = 42%nat
    by rewrite /mscale List.length_map HM1_42.
  have HmsM2_42 : length (mscale (BinInt.Z.opp (BinInt.Z.mul 105 D_M1)) M2_int) = 42%nat
    by rewrite /mscale List.length_map HM2_42.
  have Hlen_eq : length (mscale (BinInt.Z.mul 4 D_M2) M1_int)
               = length (mscale (BinInt.Z.opp (BinInt.Z.mul 105 D_M1)) M2_int)
    by rewrite HmsM1_42 HmsM2_42.
  have Hpenc_42 : length pencil_mat_int = 42%nat
    by rewrite /pencil_mat_int (length_madd _ _ Hlen_eq) HmsM1_42.
  rewrite /pencil_mat_int (nth_madd_eq _ _ _ Hlen_eq).
  have Hi_M1 : (i < length M1_int)%coq_nat
    by rewrite Hpenc_42 in Hi; rewrite HM1_42; exact Hi.
  have Hi_M2 : (i < length M2_int)%coq_nat
    by rewrite Hpenc_42 in Hi; rewrite HM2_42; exact Hi.
  have HrowM1 : length (List.nth i (mscale (BinInt.Z.mul 4 D_M2) M1_int) nil) = 42%nat.
  { rewrite /mscale.
    rewrite (List.nth_indep _ nil (vscale (BinInt.Z.mul 4 D_M2) nil));
      [|rewrite List.length_map; exact Hi_M1].
    by rewrite List.map_nth length_vscale (Hwf1 i Hi_M1). }
  have HrowM2 : length (List.nth i (mscale (BinInt.Z.opp (BinInt.Z.mul 105 D_M1)) M2_int) nil) = 42%nat.
  { rewrite /mscale.
    rewrite (List.nth_indep _ nil (vscale (BinInt.Z.opp (BinInt.Z.mul 105 D_M1)) nil));
      [|rewrite List.length_map; exact Hi_M2].
    by rewrite List.map_nth length_vscale (Hwf2 i Hi_M2). }
  rewrite length_vadd_eq; first by exact: HrowM1.
  by rewrite HrowM1 HrowM2.
Qed.

(* char_poly_int *_neq_nil: FL produces a length-43 list, so non-empty. *)
Lemma char_poly_int_pencil_neq_nil : char_poly_int pencil_mat_int <> nil.
Proof. unfold char_poly_int. destruct (fl_loop _ _ _ _ _ _ _); discriminate. Qed.

Lemma char_poly_int_M1_int_neq_nil : char_poly_int M1_int <> nil.
Proof. unfold char_poly_int. destruct (fl_loop _ _ _ _ _ _ _); discriminate. Qed.
