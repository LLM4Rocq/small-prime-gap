(* ==================================================================
   theories/S1/CertPencil.v

   End-to-end "determinant-sign + IVT" proof that the rat matrix
   A_rat = M1^{-1} M2 has a realalg eigenvalue strictly above 4/105.

   Strategy:
     1. Take precomputed integer determinants
          det_M1_int_value  := det(M1_int)            (positive)
          D_pencil_int_value := det(4*D_M2*M1_int - 105*D_M1*M2_int)
                                                       (negative)
        shipped as Z literals in Witness_PencilDet.v.

     2. Close `det_M1_int = det_M1_int_value` and
        `D_pencil_int = D_pencil_int_value` via per-prime CRT lifts
        (CRTPencilCheck.v + CRTPencilCheckExt.v) over 710 / 1210
        Uint63 primes plus the Hadamard coefficient bound
        (CRTPencilM1Bound.v / CRTPencilPencilBound.v via the generic
        CRTPencilHadamardGeneric.v).

     3. Bridge via Agent A's `det_pencil`:
          \det (l *: M1 - M2) = \det M1 * (char_poly (M1^-1 *m M2)).[l]
        Specialising l := 4/105 gives (char_poly A_rat).[4/105] < 0.

     4. Leading coefficient: char_poly A_rat is monic of degree 42, so
        its leading coefficient is 1 > 0; above the Cauchy bound the
        evaluation is positive.

     5. IVT (`poly_ivtoo`) yields a realalg root in (4/105, cb).

     6. `eigenvalue_root_char` + `map_char_poly` convert to
        `eigenvalue (map_mx ratr A_rat) lambda`.

   Drop-in alternative to `Cert.maynard_eigenvalue_S1` (main route).
   ================================================================== *)

From Stdlib Require Import ZArith List Lia.
Import ListNotations.

From mathcomp Require Import all_boot all_algebra.
From mathcomp.real_closed Require Import polyrcf realalg.

From PrimeGapS1 Require Import IntMat IntPoly Witness CharPoly Bridge.
From PrimeGapS1 Require Import MaynardSpec MaynardSpecBridge.
From PrimeGapS1 Require Import CertL2.
From PrimeGapS1 Require Import DetPencil.        (* Agent A's deliverable: det_pencil *)
From PrimeGapS1 Require Import Cert.             (* M1_spec_eq_int, M2_spec_eq_int    *)
From PrimeGapS1 Require Import CertPencilDef.    (* sealed det_M1_int, D_pencil_int, pencil_mat_int *)
From PrimeGapS1 Require Import Witness_PencilDet.
From PrimeGapS1 Require Import CRTPencilCheck.     (* det_M1_int_eq *)
From PrimeGapS1 Require Import CRTPencilCheckExt.  (* D_pencil_int_eq via 1210-prime extension *)
From PrimeGapS1 Require AbstractPencilHelper.      (* abstract_pencil_scale -- Require, NOT Import *)

Import GRing.Theory Num.Theory.
Import order.Order.POrderTheory.

Local Open Scope ring_scope.

(* ==================================================================
   Section 0: the rat-level M1, M2 matrices and the pencil scalar.
   ================================================================== *)

Definition M1_rat : 'M[rat]_42 := mat_int_to_rat M1_int D_M1 42.
Definition M2_rat : 'M[rat]_42 := mat_int_to_rat M2_int D_M2 42.

(* The threshold scalar 4/105 as a rat. *)
Definition lambda_q : rat := 4%:Q / 105%:Q.

(* ==================================================================
   Section 1: integer determinant signs (via the shipped literals).
   ================================================================== *)

Lemma D_pencil_int_neg : BinInt.Z.lt D_pencil_int BinInt.Z0.
Proof. rewrite D_pencil_int_eq. exact D_pencil_int_value_neg. Qed.

Lemma det_M1_int_pos : BinInt.Z.lt BinInt.Z0 det_M1_int.
Proof. rewrite det_M1_int_eq. exact det_M1_int_value_pos. Qed.

(* ==================================================================
   Section 2: bridge to char_poly A_rat via Agent A's det_pencil.
   ================================================================== *)

(* Z2rat sign helpers -- generic-typed to avoid triggering unfolding of
   large Z definitions inside case analysis. *)
Lemma Z2rat_pos_gen (z : Z) : Z.lt 0 z -> 0 < Z2rat z.
Proof.
move=> Hz; rewrite /Z2rat ltr0z.
case: z Hz => [|p|p] //= _.
apply/leP; exact: Pos2Nat.is_pos.
Qed.

Lemma Z2rat_neg_gen (z : Z) : Z.lt z 0 -> Z2rat z < 0.
Proof.
move=> Hz; rewrite /Z2rat ltrz0.
by case: z Hz => [|p|p] //=.
Qed.

(* Generic: det of (mat_int_to_rat M 1 n) equals Z2rat of the constant
   coefficient of char_poly_int M, when n is even.  Abstract over (n, M)
   so the unifier never walks the concrete 42x42 matrix cells. *)
Lemma det_mat_int_to_rat_via_charpoly (M : mat) (n : nat)
  (sq : mat_dim M = n)
  (wf : forall i, (i < List.length M)%coq_nat -> List.length (List.nth i M nil) = n)
  (Hne : char_poly_int M <> nil)
  (Heven : exists k, n = (k.*2)%nat) :
  \det (mat_int_to_rat M 1 n) = Z2rat (List.nth 0 (char_poly_int M) BinInt.Z0).
Proof.
have Hcorr : pol_to_polyrat (char_poly_int M) = char_poly (mat_int_to_rat M 1 n)
  := @char_poly_int_correct M n sq wf.
have Hcoef0 : (char_poly (mat_int_to_rat M 1 n))`_0
             = (-1) ^+ n * \det (mat_int_to_rat M 1 n) := char_poly_det _.
have Hcoef0' := pol_to_polyrat_coef0 (char_poly_int M) Hne.
have Hsign : (-1 : rat) ^+ n = 1.
{ case: Heven => k ->.
  by elim: k => [|k IH] //; rewrite doubleS exprS exprS mulN1r mulN1r opprK. }
have Hhd_eq : head BinInt.Z0 (char_poly_int M) =
              List.nth 0 (char_poly_int M) BinInt.Z0.
{ by case: (char_poly_int M) Hne. }
have Hcalc : (-1 : rat) ^+ n * \det (mat_int_to_rat M 1 n) =
             Z2rat (List.nth 0 (char_poly_int M) BinInt.Z0).
{ rewrite -Hcoef0 -Hcorr Hcoef0' /Z2rat Hhd_eq. reflexivity. }
by rewrite -Hcalc Hsign mul1r.
Qed.

Lemma M1_int_dim_even : exists k, (42 = k.*2)%nat.
Proof. by exists 21%nat. Qed.

(* `abstract_pencil_scale` and the scalar `intrM` helper lemmas live in
   AbstractPencilHelper.v -- separated so their proofs don't walk
   M1_rat/M2_rat/pencil_mat_int cells (which combinatorially explode
   memory at concrete 42x42). *)

(* M2_int well-formedness, mirror of M1_int_dim'/wf'. *)
Lemma M2_int_dim' : mat_dim M2_int = 42%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma M2_int_rows_42 : forallb (fun row => Nat.eqb (List.length row) 42) M2_int = true.
Proof. vm_compute. reflexivity. Qed.

Lemma M2_int_wf' : forall i, (i < length M2_int)%coq_nat ->
  length (List.nth i M2_int []) = 42%nat.
Proof. by move=> i Hi; move: M2_int_rows_42; rewrite List.forallb_forall =>
  /(_ _ (List.nth_In _ _ Hi)) /Nat.eqb_eq. Qed.

(* List-level helpers used in pencil_mat_int_{dim,wf}. *)
Lemma length_vadd_eq (xs ys : list Z) :
  length xs = length ys -> length (vadd xs ys) = length xs.
Proof.
elim: xs ys => [|x xs IH] [|y ys] //= [Hlen]; rewrite IH //.
Qed.

Lemma length_vscale (c : Z) (xs : list Z) : length (vscale c xs) = length xs.
Proof. by rewrite /vscale List.length_map. Qed.

Lemma nth_madd_eq (A B : mat) (i : nat) :
  length A = length B ->
  List.nth i (madd A B) nil = vadd (List.nth i A nil) (List.nth i B nil).
Proof.
elim: A B i => [|a A IH] [|b B] [|i] //= Hlen.
by apply: IH; lia.
Qed.

Lemma length_madd (A B : mat) :
  length A = length B ->
  length (madd A B) = length A.
Proof.
elim: A B => [|a A IH] [|b B] //= [Hlen]. by rewrite IH.
Qed.

(* pencil_mat_int has dim 42 since both summands do. *)
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
move=> i Hi.
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

Lemma char_poly_int_pencil_neq_nil : char_poly_int pencil_mat_int <> nil.
Proof. unfold char_poly_int. destruct (fl_loop _ _ _ _ _ _ _); discriminate. Qed.

(* The scaled pencil's det in terms of mat_int_to_rat pencil_mat_int.
   `rewrite D_pencil_int_eq_nth` exposes the nth-of-char_poly_int form
   so apply unifies without forcing the kernel to chase the sigT seal
   on D_pencil_int (chasing it triggers OOM). *)
Lemma det_pencil_rat_aux :
  \det (mat_int_to_rat pencil_mat_int 1 42) = Z2rat D_pencil_int.
Proof.
  rewrite D_pencil_int_eq_nth.
  apply: det_mat_int_to_rat_via_charpoly;
    [exact: pencil_mat_int_dim
    |exact: pencil_mat_int_wf
    |exact: char_poly_int_pencil_neq_nil
    |exact: M1_int_dim_even].
Qed.

(* Bridge: K *: (lambda_q *: M1_rat - M2_rat) equals
   mat_int_to_rat pencil_mat_int 1 42, where K := 105*D_M1*D_M2.
   Uses [in RHS]/cbv beta zeta tricks to keep the rewrite engine from
   walking the heavy concrete matrix cells. *)
Lemma pencil_rat_scaled_eq :
  let K : rat := (Z_to_int (Z.mul (Z.mul 105 D_M1) D_M2))%:~R in
  K *: (lambda_q *: M1_rat - M2_rat) = mat_int_to_rat pencil_mat_int 1 42.
Proof.
  intro K.
  set cM1 : rat := (Z_to_int D_M1)%:~R.
  set cM2 : rat := (Z_to_int D_M2)%:~R.
  set c105 : rat := (Z_to_int 105)%:~R.
  set c4 : rat := (Z_to_int 4)%:~R.
  have HK : K = c105 * cM1 * cM2
    := AbstractPencilHelper.Z_to_int_mul_mul_intrM_three 105 D_M1 D_M2.
  have HcM1_ne : cM1 != 0
    by rewrite /cM1 intr_eq0; apply: Z_to_int_neq0'; discriminate.
  have HcM2_ne : cM2 != 0
    by rewrite /cM2 intr_eq0; apply: Z_to_int_neq0'; discriminate.
  have Hc105_ne : c105 != 0
    by rewrite /c105 intr_eq0; apply: Z_to_int_neq0'; discriminate.
  have Hlq : lambda_q = c4 / c105.
  { rewrite /lambda_q /c4 /c105. reflexivity. }
  set M1' : 'M[rat]_42 := mat_int_to_rat M1_int 1 42.
  set M2' : 'M[rat]_42 := mat_int_to_rat M2_int 1 42.
  have HM1 : M1_rat = cM1^-1 *: M1'.
  { rewrite /M1_rat /cM1 /M1'. exact: mat_int_to_rat_scale_inv'. }
  have HM2 : M2_rat = cM2^-1 *: M2'.
  { rewrite /M2_rat /cM2 /M2'. exact: mat_int_to_rat_scale_inv'. }
  rewrite HK HM1 HM2 Hlq.
  rewrite (AbstractPencilHelper.abstract_pencil_scale 42 M1' M2' cM1 cM2 c105 c4
             HcM1_ne HcM2_ne Hc105_ne).
  rewrite /pencil_mat_int /M1' /M2'.
  rewrite (mat_int_to_rat_madd
             (mscale (Z.mul 4 D_M2) M1_int)
             (mscale (Z.opp (Z.mul 105 D_M1)) M2_int) 42).
  - rewrite !mat_int_to_rat_mscale.
    rewrite /c4 /cM2 /c105 /cM1.
    have ZM2 : (Z_to_int (4 * D_M2))%:~R = (Z_to_int 4)%:~R * (Z_to_int D_M2)%:~R :> rat
      := AbstractPencilHelper.Z_to_int_mul_intrM_two _ _.
    have ZM3 : (Z_to_int (- (105 * D_M1)))%:~R
             = - ((Z_to_int 105)%:~R * (Z_to_int D_M1)%:~R) :> rat
      := AbstractPencilHelper.Z_to_int_opp_mul_intrM _ _.
    rewrite [in RHS]ZM2.
    rewrite [in RHS]ZM3.
    rewrite [X in _ = _ + X]scaleNr.
    reflexivity.
  - rewrite mat_dim_mscale_eq. exact: M1_int_dim'.
  - rewrite mat_dim_mscale_eq. exact: M2_int_dim'.
  - move=> i Hi. rewrite CRTLift.length_mscale in Hi.
    rewrite (List.map_nth (vscale (4 * D_M2)) M1_int [::] i).
    unfold vscale.
    rewrite List.length_map. exact (M1_int_wf' i Hi).
  - move=> i Hi. rewrite CRTLift.length_mscale in Hi.
    rewrite (List.map_nth (vscale (- (105 * D_M1))) M2_int [::] i).
    unfold vscale.
    rewrite List.length_map. exact (M2_int_wf' i Hi).
Qed.

Lemma pencil_rat_eq_int_scaled :
  exists (c : rat), 0 < c
   /\ \det (lambda_q *: M1_rat - M2_rat) = c * (Z2rat D_pencil_int).
Proof.
  set K : rat := (Z_to_int (Z.mul (Z.mul 105 D_M1) D_M2))%:~R.
  have HK_pos : 0 < K.
  { rewrite /K ltr0z; apply/ltP. by apply: (Pos2Nat.is_pos _). }
  have HK_neq0 : K != 0 by apply: lt0r_neq0.
  exists (K^-1 ^+ 42).
  split.
  - apply: exprn_gt0; rewrite invr_gt0; exact: HK_pos.
  - have Hscale := pencil_rat_scaled_eq.
    cbv beta zeta in Hscale.
    have Hdet : \det (K *: (lambda_q *: M1_rat - M2_rat))
              = \det (mat_int_to_rat pencil_mat_int 1 42)
      by rewrite Hscale.
    rewrite [X in X = _]detZ in Hdet.
    rewrite det_pencil_rat_aux in Hdet.
    have HK42_neq0 : K ^+ 42 != 0 := expf_neq0 42 HK_neq0.
    apply: (mulfI HK42_neq0).
    rewrite -Hdet.
    set D := \det (lambda_q *: M1_rat - M2_rat).
    clearbody K D.
    clear -HK_neq0 HK42_neq0.
    by rewrite mulrA mulrA -exprMn divff // expr1n mul1r.
Qed.

Lemma char_poly_int_M1_int_neq_nil : char_poly_int M1_int <> nil.
Proof. unfold char_poly_int. destruct (fl_loop _ _ _ _ _ _ _); discriminate. Qed.

Lemma det_M1_rat_aux :
  \det (mat_int_to_rat M1_int 1 42) = Z2rat det_M1_int.
Proof.
  rewrite det_M1_int_eq_nth.
  apply: det_mat_int_to_rat_via_charpoly;
    [exact: M1_int_dim'
    |exact: M1_int_wf'
    |exact: char_poly_int_M1_int_neq_nil
    |exact: M1_int_dim_even].
Qed.

Lemma det_M1_rat_eq_int_scaled :
  exists (c : rat), 0 < c
   /\ \det M1_rat = c * (Z2rat det_M1_int).
Proof.
  set d := ((Z_to_int D_M1)%:~R : rat).
  have Hd_pos : 0 < d.
  { rewrite /d ltr0z; apply/ltP. by apply: (Pos2Nat.is_pos _). }
  have Hd_neq0 : d != 0 by apply: lt0r_neq0.
  exists (d^-1 ^+ 42).
  split.
  - apply: exprn_gt0; rewrite invr_gt0; exact: Hd_pos.
  - rewrite /M1_rat (mat_int_to_rat_scale_inv' M1_int D_M1 42).
    rewrite detZ -det_M1_rat_aux.
    congr (_ * _).
Qed.

(* Abstract-dimension helper to bypass canonical-structure elaboration
   cost at concrete n=42 (mirrors the AbstractMatScale design in CertL2). *)
Section UnitScaleHelper.
Variable (F : fieldType) (n : nat).
Variables (A : 'M[F]_n) (c : F).
Hypothesis Hc : c != 0.
Hypothesis HA : A \in unitmx.

Lemma scale_inv_unit : c^-1 *: A \in unitmx.
Proof. rewrite unitmxZ //. by rewrite unitfE invr_neq0. Qed.
End UnitScaleHelper.

Lemma M1_rat_unit : M1_rat \in unitmx.
Proof.
  rewrite /M1_rat (mat_int_to_rat_scale_inv' M1_int D_M1 42).
  apply: scale_inv_unit; last by exact: M1_1_unit.
  rewrite intr_eq0.
  by apply: Z_to_int_neq0'; discriminate.
Qed.

Lemma A_rat_decomp : A_rat = invmx M1_rat *m M2_rat.
Proof. by rewrite /A_rat /M1_rat /M2_rat. Qed.

(* Agent A's det_pencil specialised to lambda_q. *)
Lemma pencil_at_lambda :
  \det (lambda_q *: M1_rat - M2_rat) =
  \det M1_rat * (char_poly A_rat).[lambda_q].
Proof.
  rewrite A_rat_decomp.
  exact: det_pencil M1_rat_unit.
Qed.

(* Generic-typed abstract bridge -- avoids canonical-structure
   elaboration on concrete 'M[rat]_42 matrices. *)
Section AbstractPencilNeg.
Variables (M1r M2r : 'M[rat]_42) (lq : rat) (Ar : 'M[rat]_42).
Variables (Dpi dMi : Z).
Variables (cp cM : rat).
Hypothesis HcM_pos : 0 < cM.
Hypothesis HcP_pos : 0 < cp.
Hypothesis Hp : \det (lq *: M1r - M2r) = cp * Z2rat Dpi.
Hypothesis Hm : \det M1r = cM * Z2rat dMi.
Hypothesis Hpa : \det (lq *: M1r - M2r) = \det M1r * (char_poly Ar).[lq].
Hypothesis HdMi : Z.lt 0 dMi.
Hypothesis HDpi : Z.lt Dpi 0.

Lemma abstract_charpoly_neg : (char_poly Ar).[lq] < 0.
Proof.
have HZM_pos : 0 < Z2rat dMi := Z2rat_pos_gen _ HdMi.
have HZP_neg : Z2rat Dpi < 0 := Z2rat_neg_gen _ HDpi.
have HdetM1_pos : 0 < \det M1r.
{ rewrite Hm. exact: (mulr_gt0 HcM_pos HZM_pos). }
have HdetM1_ne : \det M1r != 0 := lt0r_neq0 HdetM1_pos.
have Hpenc : \det M1r * (char_poly Ar).[lq] = cp * Z2rat Dpi.
{ rewrite -Hpa. exact: Hp. }
have Hneg_num : cp * Z2rat Dpi < 0 by rewrite pmulr_rlt0.
have HP_eq : (char_poly Ar).[lq] = (cp * Z2rat Dpi) / \det M1r.
{ have HH : (char_poly Ar).[lq] * \det M1r = cp * Z2rat Dpi.
  { by rewrite mulrC. }
  by rewrite -HH -mulrA mulfV // mulr1. }
rewrite HP_eq.
by rewrite ltr_pdivrMr // mul0r.
Qed.

End AbstractPencilNeg.

Lemma charpoly_neg_at_threshold_rat :
  (char_poly A_rat).[lambda_q] < 0.
Proof.
  have [cp [Hcp_pos Hp]] := pencil_rat_eq_int_scaled.
  have [cM [HcM_pos Hm]] := det_M1_rat_eq_int_scaled.
  exact: (abstract_charpoly_neg M1_rat M2_rat lambda_q A_rat D_pencil_int det_M1_int
                                cp cM HcM_pos Hcp_pos Hp Hm pencil_at_lambda
                                det_M1_int_pos D_pencil_int_neg).
Qed.

Lemma charpoly_lc_pos_rat :
  0 < lead_coef (char_poly A_rat).
Proof.
  have Hmon : char_poly A_rat \is monic := char_poly_monic A_rat.
  by rewrite (monicP Hmon) ltr01.
Qed.

Lemma charpoly_neq0_rat : char_poly A_rat != 0.
Proof.
  apply/eqP => H0.
  have Hlc := charpoly_lc_pos_rat.
  by rewrite H0 lead_coef0 ltxx in Hlc.
Qed.

(* ==================================================================
   Section 3: lift to realalg + Cauchy bound + IVT.
   ================================================================== *)

Definition charpoly_A_realalg : {poly realalg} :=
  map_poly (ratr : rat -> realalg) (char_poly A_rat).

Definition lambda_ralg : realalg := ratr lambda_q.

Lemma charpoly_A_realalg_lead_coef :
  lead_coef charpoly_A_realalg = 1.
Proof.
  rewrite /charpoly_A_realalg.
  rewrite (lead_coef_map (ratr : {rmorphism rat -> realalg})).
  by rewrite (monicP (char_poly_monic _)) rmorph1.
Qed.

Lemma charpoly_A_realalg_neq0 : charpoly_A_realalg != 0.
Proof.
  apply/eqP => H0.
  have Hlc := charpoly_A_realalg_lead_coef.
  rewrite H0 lead_coef0 in Hlc.
  by have := oner_neq0 realalg; rewrite -Hlc eqxx.
Qed.

Lemma charpoly_A_realalg_size :
  size charpoly_A_realalg = 43.
Proof.
  rewrite /charpoly_A_realalg.
  rewrite (size_map_poly (ratr : {rmorphism rat -> realalg})).
  exact: size_char_poly.
Qed.

Lemma charpoly_A_realalg_neg_at_threshold :
  charpoly_A_realalg.[lambda_ralg] < 0.
Proof.
  rewrite /charpoly_A_realalg /lambda_ralg.
  rewrite (horner_map (ratr : {rmorphism rat -> realalg})).
  rewrite ltrq0.
  exact: charpoly_neg_at_threshold_rat.
Qed.

Lemma charpoly_A_realalg_lc_pos :
  (0 : realalg) < lead_coef charpoly_A_realalg.
Proof.
  by rewrite charpoly_A_realalg_lead_coef ltr01.
Qed.

(* P_realalg at its Cauchy bound is positive (mirror of charpoly_pos_at_cb). *)
Lemma charpoly_A_realalg_pos_at_cb :
  0 < charpoly_A_realalg.[cauchy_bound charpoly_A_realalg].
Proof.
  set P := charpoly_A_realalg.
  set b := cauchy_bound P.
  have HP : P != 0 := charpoly_A_realalg_neq0.
  have Hlc : 0 < lead_coef P := charpoly_A_realalg_lc_pos.
  have Hpb : ~~ root P b.
  { apply/negP => Hroot.
    have Hin : b \in `[b, +oo[ by rewrite in_itv /= lexx.
    by have := ge_cauchy_bound HP Hin; rewrite Hroot. }
  have Hsgn : Num.sg P.[b] = sgp_pinfty P.
  { have := sgp_pinftyP (ge_cauchy_bound HP).
    move/(_ b).
    rewrite in_itv /= lexx //.
    by move=> /(_ isT). }
  rewrite -sgr_gt0 Hsgn /sgp_pinfty sgr_gt0 //.
Qed.

Lemma threshold_lt_cb_A :
  lambda_ralg < cauchy_bound charpoly_A_realalg.
Proof.
  apply: (lt_le_trans (y := 1)).
  - rewrite /lambda_ralg /lambda_q.
    rewrite -(rmorph1 (ratr : {rmorphism rat -> realalg})).
    rewrite ltr_rat.
    by rewrite ltr_pdivrMr ?mul1r ?ltr_nat //.
  - rewrite /cauchy_bound lerDl mulr_ge0 // ?invr_ge0 ?normr_ge0 //.
    apply: sumr_ge0 => i _; exact: normr_ge0.
Qed.

(* IVT: realalg root of P_realalg lies in (lambda_ralg, cb). *)
Lemma maynard_root_above_threshold :
  exists lambda : realalg,
    root charpoly_A_realalg lambda
    /\ lambda_ralg < lambda.
Proof.
  set P := charpoly_A_realalg.
  set a := lambda_ralg.
  set b := cauchy_bound P.
  have Hab : a <= b by apply: ltW; exact: threshold_lt_cb_A.
  have Hpa : P.[a] < 0 := charpoly_A_realalg_neg_at_threshold.
  have Hpb : 0 < P.[b] := charpoly_A_realalg_pos_at_cb.
  have Hprod : P.[a] * P.[b] < 0.
  { by rewrite nmulr_rlt0 //; apply: Hpb. }
  case: (poly_ivtoo Hab Hprod) => x Hx Hroot.
  exists x; split; first exact: Hroot.
  by move: Hx; rewrite inE /= => /andP [].
Qed.

(* ==================================================================
   Section 4: the headline pencil theorem.
   ================================================================== *)

Theorem maynard_eigenvalue_S1_pencil :
  exists lambda : realalg,
    eigenvalue (map_mx (ratr : rat -> realalg) A_rat) lambda
    /\ (ratr (4%:Q / 105%:Q) : realalg) < lambda.
Proof.
  have [lambda [Hroot Hgt]] := maynard_root_above_threshold.
  exists lambda; split; last first.
  - by move: Hgt; rewrite /lambda_ralg /lambda_q.
  - rewrite eigenvalue_root_char -(map_char_poly (ratr : {rmorphism rat -> realalg})).
    exact: Hroot.
Qed.

(* ==================================================================
   Section 5: trust contract (mirrors Cert.maynard_M105_certified).
   ================================================================== *)

Theorem maynard_M105_certified_pencil :
  (forall i j : nat, (i < 42)%nat -> (j < 42)%nat ->
     M1_spec_ij i j = Z2rat (mat_get M1_int i j) / Z2rat D_M1) /\
  (forall i j : nat, (i < 42)%nat -> (j < 42)%nat ->
     M2_spec_ij i j = Z2rat (mat_get M2_int i j) / Z2rat D_M2) /\
  exists lambda : realalg,
    eigenvalue (map_mx (ratr : rat -> realalg) A_rat) lambda
    /\ (ratr (4%:Q / 105%:Q) : realalg) < lambda.
Proof.
  split; first by move=> i j Hi Hj; apply: M1_spec_eq_int.
  split; first by move=> i j Hi Hj; apply: M2_spec_eq_int.
  exact: maynard_eigenvalue_S1_pencil.
Qed.
