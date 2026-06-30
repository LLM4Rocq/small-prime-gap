(* ==================================================================
   theories/S1/CertPencil.v

   End-to-end "determinant-sign + IVT" proof that the rat matrix
   A_rat = M1^{-1} M2 has a realalg eigenvalue strictly above 4/105.

   Strategy:
     1. Take precomputed integer determinants
          det_M1_int_value  := det(M1_int)            (positive)
          D_pencil_int_value := det(pencil_int_clean)  (negative,
                          = D_pencil_clean * (4*M1_rat - 105*M2_rat)
                          scaled to integers).

     2. Close `det_M1_int = det_M1_int_value` and
        `D_pencil_int = D_pencil_int_value` via per-prime CRT lifts
        over the SAME 710-prime CRT product (CRTPencilCheck.v) — no
        prime extension needed thanks to the CLEAN pencil's small
        determinant size (2613 bits vs. 31131 in the old form).

     3. Bridge via Agent A's `det_pencil`:
          \det (l *: M1 - M2) = \det M1 * (char_poly (M1^-1 *m M2)).[l]
        Specialising l := 4/105 gives (char_poly A_rat).[4/105] < 0.

     4. Leading coefficient: char_poly A_rat is monic of degree 42, so
        its leading coefficient is 1 > 0; above the Cauchy bound the
        evaluation is positive.

     5. IVT (`poly_ivtoo`) yields a realalg root in (4/105, cb).

     6. `eigenvalue_root_char` + `map_char_poly` convert to
        `eigenvalue (map_mx ratr A_rat) lambda`.
   ================================================================== *)

From Stdlib Require Import ZArith List Lia.
Import ListNotations.

From mathcomp Require Import all_boot all_algebra.
From mathcomp.real_closed Require Import polyrcf realalg.

From PrimeGapS1 Require Import IntMat IntPoly Witness CharPoly.
From PrimeGapS1 Require Import MaynardSpec MaynardSpecBridge.
From PrimeGapS1 Require Import CertL2.
From PrimeGapS1 Require Import DetPencil.        (* Agent A's deliverable: det_pencil *)
From PrimeGapS1 Require Import Cert.             (* M1_spec_eq_int, M2_spec_eq_int    *)
From PrimeGapS1 Require Import Witness_PencilDet.       (* det_M1_int_value *)
From PrimeGapS1 Require Import Witness_PencilClean.     (* pencil_int_clean, D_pencil_int_value *)
From PrimeGapS1 Require Import CertPencilDef.    (* sealed det_M1_int, D_pencil_int, pencil_mat_int *)
From PrimeGapS1 Require Import PencilCleanGrid.  (* per-entry cross-check pencil_clean_match_Z *)
From PrimeGapS1 Require Import CRTPencilCheck.   (* det_M1_int_eq, D_pencil_int_eq -- both over 710 primes *)
From PrimeGapS1 Require AbstractPencilHelper.    (* pencil_cell_eq -- Require, NOT Import *)

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

(* Note: M2_int_dim'/wf', pencil_mat_int_dim/wf, char_poly_int_*_neq_nil
   all live in CertPencilDef.v -- vm_compute'd on the shipped 42x42
   matrix literals (no list-induction proofs required after the move to
   the clean integer pencil). *)

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

(* ==================================================================
   Section 2b: the rat-level bridge between pencil_int_clean and
   K *: (lambda_q *: M1_rat - M2_rat), where
        K := (D_pencil_clean * 105)%:~R.
   Per-entry consequence of the cross-multiplication identity
        D_M1 * D_M2 * pencil_int_clean[i,j]
          = D_pencil_clean * (4*D_M2*M1[i,j] - 105*D_M1*M2[i,j]),
   shipped via `pencil_clean_match_Z` in PencilCleanGrid.v.

   We work generically through a one-cell scalar identity (proved by
   the `field` tactic on rationals) and then upgrade to matrices via
   `apply/matrixP => i j`.  No mathcomp.algebra_tactics needed in this
   file — the abstract helper lives below.
   ================================================================== *)

(* The integer scalar K (D_pencil_clean * 105) as a rational, plus a
   per-cell algebraic identity proved at the scalar level. *)
Definition K_clean : rat :=
  (Z_to_int (BinInt.Z.mul D_pencil_clean 105))%:~R.

(* The matrix-level bridge, derived from `AbstractPencilHelper.pencil_cell_eq`
   cell-by-cell via the per-entry cross-check `pencil_clean_match_Z`. *)
Lemma pencil_rat_scaled_eq :
  K_clean *: (lambda_q *: M1_rat - M2_rat) =
  mat_int_to_rat pencil_mat_int 1 42.
Proof.
have HD1 : ((Z_to_int D_M1)%:~R : rat) != 0
  by rewrite intr_eq0; apply: Z_to_int_neq0'; discriminate.
have HD2 : ((Z_to_int D_M2)%:~R : rat) != 0
  by rewrite intr_eq0; apply: Z_to_int_neq0'; discriminate.
have Hcross : forall (i j : 'I_42),
  BinInt.Z.mul (BinInt.Z.mul D_M1 D_M2)
    (mat_get pencil_mat_int (nat_of_ord i) (nat_of_ord j)) =
  BinInt.Z.mul D_pencil_clean
    (BinInt.Z.sub
      (BinInt.Z.mul (BinInt.Z.mul 4 D_M2) (mat_get M1_int (nat_of_ord i) (nat_of_ord j)))
      (BinInt.Z.mul (BinInt.Z.mul 105 D_M1) (mat_get M2_int (nat_of_ord i) (nat_of_ord j)))).
{ move=> i j. change pencil_mat_int with pencil_int_clean.
  exact: pencil_clean_match_Z (ltn_ord i) (ltn_ord j). }
exact: (AbstractPencilHelper.pencil_matrix_bridge 42 M1_int M2_int pencil_mat_int
          D_M1 D_M2 D_pencil_clean HD1 HD2 Hcross).
Qed.

Lemma pencil_rat_eq_int_scaled :
  exists (c : rat), 0 < c
   /\ \det (lambda_q *: M1_rat - M2_rat) = c * (Z2rat D_pencil_int).
Proof.
  set K : rat := K_clean.
  have HK_pos : 0 < K.
  { rewrite /K /K_clean ltr0z; apply/ltP. by apply: (Pos2Nat.is_pos _). }
  have HK_neq0 : K != 0 by apply: lt0r_neq0.
  exists (K^-1 ^+ 42).
  split.
  - apply: exprn_gt0; rewrite invr_gt0; exact: HK_pos.
  - have Hscale := pencil_rat_scaled_eq.
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
   Section 5: trust contract.
   ================================================================== *)

(* Headline in the main-branch shape (over realalg); M105 = 105 *: A_rat. *)

Definition M105 : 'M[rat]_42 := 105%:Q *: A_rat.

Definition matches_closed_forms (M : 'M[rat]_42) : Prop :=
  [/\ M = M105,
      (forall i j, (i < 42)%nat -> (j < 42)%nat ->
         M1_spec_ij i j = Z2rat (mat_get M1_int i j) / Z2rat D_M1)
    & (forall i j, (i < 42)%nat -> (j < 42)%nat ->
         M2_spec_ij i j = Z2rat (mat_get M2_int i j) / Z2rat D_M2)].

Lemma matches_closed_forms_M105 : matches_closed_forms M105.
Proof.
split; first by [].
- by move=> i j Hi Hj; apply: M1_spec_eq_int.
- by move=> i j Hi Hj; apply: M2_spec_eq_int.
Qed.

(* The S1 eigenvalue bound, rescaled from (A_rat, 4/105) to (M105, 4). *)
Lemma maynard_eigenvalue_S1_pencil_M105 :
  exists lambda : realalg,
    eigenvalue (map_mx (ratr : rat -> realalg) M105) lambda /\ (4 < lambda).
Proof.
have [mu [Heig Hgt]] := maynard_eigenvalue_S1_pencil.
have h105ne : (105%:Q : rat) != 0 by rewrite intr_eq0.
exists (ratr (105%:Q) * mu); split.
- have -> : map_mx (ratr : rat -> realalg) M105
         = ratr (105%:Q) *: map_mx (ratr : rat -> realalg) A_rat.
    by apply/matrixP=> i j; rewrite /M105 !mxE rmorphM.
  have [v Hv vnz] := eigenvalueP Heig.
  apply/eigenvalueP; exists v => //.
  by rewrite -scalemxAr Hv scalerA.
- have h105 : (0 : realalg) < ratr (105%:Q) by rewrite ltr0q.
  have e4 : ratr (105%:Q) * ratr (4%:Q / 105%:Q) = 4 :> realalg.
    rewrite -rmorphM.
    have -> : (105%:Q * (4%:Q / 105%:Q) = 4%:Q :> rat).
      by rewrite mulrC (mulfVK h105ne).
    by rewrite rmorph_int.
  by rewrite -e4 ltr_pM2l.
Qed.

(* ------------------------------------------------------------------
   The headline theorem, in the main-branch shape: matches_closed_forms
   M105 plus a real eigenvalue of M105 strictly above 4 (over realalg).
   ------------------------------------------------------------------ *)
Theorem maynard_M105_certified_pencil :
  matches_closed_forms M105 /\
  exists lambda : realalg,
    eigenvalue (map_mx (ratr : rat -> realalg) M105) lambda /\ (4 < lambda).
Proof.
split; [exact: matches_closed_forms_M105 | exact: maynard_eigenvalue_S1_pencil_M105].
Qed.
