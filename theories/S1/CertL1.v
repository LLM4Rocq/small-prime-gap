(* ================================================================== *)
(*  theories/S1/CertL1.v                                                *)
(*                                                                      *)
(*  L1: prove that charpoly_int has a real root above 4/105.            *)
(*                                                                      *)
(*  Proof strategy: intermediate value theorem (poly_ivtoo).            *)
(*    P(4/105) < 0   — from BigZ-verified sign data (CRTSigns.v)       *)
(*    P(cb)    > 0   — from leading coefficient positivity              *)
(*    IVT gives a root in (4/105, cb).                                  *)
(*                                                                      *)
(*  Zero project axioms — depends only on Uint63 kernel primitives.     *)
(* ================================================================== *)

From Stdlib Require Import ZArith List Lia.
Import ListNotations.

From mathcomp Require Import all_boot all_algebra.
From mathcomp.real_closed Require Import polyrcf qe_rcf_th realalg.
Import GRing.Theory Num.Theory.

From PrimeGapS1 Require Import IntPoly SignChain Witness Bridge.
From PrimeGapS1 Require Import WitnessChain CRTSigns Recompose Smoke.

Local Open Scope ring_scope.

(* ================================================================== *)
(*  Section 1: Facts verified by vm_compute on concrete data.           *)
(*                                                                      *)
(*  These are purely integer / nat computations that reduce in          *)
(*  milliseconds.                                                       *)
(* ================================================================== *)

Lemma den_pos : BinInt.Z.lt BinInt.Z0 105.
Proof. reflexivity. Qed.

(* signs_at_inf has 43 entries, matching the 43-entry chain
   (degree-42 polynomial -> 43 Sturm chain entries).  Used inline by
   sign_at_rat_charpoly and sign_at_pinf_charpoly to discharge the
   non-empty obligation on `WitnessChain.sturm_chain`. *)
Lemma signs_at_inf_length : List.length signs_at_inf = 43%nat.
Proof. vm_compute. reflexivity. Qed.

(* The threshold 4/105 is below the Cauchy bound. *)
Lemma threshold_lt_cb :
  (threshold_ralg 4 105
     < cauchy_bound (pol_to_polyralg charpoly_int))%R.
Proof.
  apply: (order.Order.POrderTheory.lt_le_trans (y := 1)).
    rewrite /threshold_ralg ltr_pdivrMr.
      rewrite mul1r ltr_int. done.
      rewrite ltr0z. done.
    rewrite /cauchy_bound lerDl mulr_ge0 // ?invr_ge0 ?normr_ge0 //;
    apply: sumr_ge0 => i _; apply: normr_ge0.
Qed.

(* The head of the shipped chain is charpoly_int. *)
Lemma shipped_chain_hd :
  List.hd nil WitnessChain.sturm_chain = charpoly_int.
Proof.
change (Recompose.lift_bigZ WitnessChain.chain_0 = charpoly_int).
exact: Smoke.chain_0_matches_charpoly.
Qed.

(* ================================================================== *)
(*  Section 5: IVT-based root existence.                                *)
(* We prove the headline result (maynard_L1_concrete) FIRST using
   the intermediate value theorem, then derive the exact Sturm count
   from the existence result. *)

(* sign_at_rat charpoly_int 4 105 = -1, extracted from sign data. *)
Lemma sign_at_rat_charpoly : sign_at_rat charpoly_int 4 105 = BinNums.Zneg BinNums.xH.
Proof.
(* The head of signs_at_x0 is sign_at_rat of the head of sturm_chain.
   The head of sturm_chain is charpoly_int (by shipped_chain_hd).
   The head of signs_at_x0 is -1 (by vm_compute on the Z list). *)
transitivity (List.hd BinInt.Z0 signs_at_x0).
2: by vm_compute.
have Hsx := signs_at_x0_shipped.
(* Hsx : signs_at_x0 = map (fun p => sign_at_rat p 4 105) sturm_chain *)
have Hne : WitnessChain.sturm_chain <> nil.
{ move=> H. have := signs_at_inf_length.
  rewrite signs_at_inf_shipped H /=. discriminate. }
transitivity (sign_at_rat (List.hd nil WitnessChain.sturm_chain) 4 105).
  by rewrite shipped_chain_hd.
symmetry. rewrite Hsx.
destruct WitnessChain.sturm_chain as [|h t]; first by exfalso; apply Hne.
by [].
Qed.

(* sign_at_pinf charpoly_int = 1, extracted from sign data. *)
Lemma sign_at_pinf_charpoly : sign_at_pinf charpoly_int = BinNums.Zpos BinNums.xH.
Proof.
transitivity (List.hd BinInt.Z0 signs_at_inf).
2: by vm_compute.
have Hsi := signs_at_inf_shipped.
have Hne : WitnessChain.sturm_chain <> nil.
{ move=> H. have := signs_at_inf_length.
  rewrite signs_at_inf_shipped H /=. discriminate. }
transitivity (sign_at_pinf (List.hd nil WitnessChain.sturm_chain)).
  by rewrite shipped_chain_hd.
symmetry. rewrite Hsi. by destruct WitnessChain.sturm_chain.
Qed.

(* P is negative at threshold 4/105. *)
Lemma charpoly_neg_at_threshold :
  ((pol_to_polyralg charpoly_int).[threshold_ralg 4 105] < 0)%R.
Proof.
have Hrat := sign_at_rat_matches charpoly_int 4 105 den_pos.
rewrite /sgn_matches in Hrat.
destruct Hrat as [_ [Hneg _]].
apply/Hneg. rewrite sign_at_rat_charpoly. reflexivity.
Qed.

(* P has positive leading coefficient. *)
Lemma charpoly_lc_pos :
  (0 < lead_coef (pol_to_polyralg charpoly_int))%R.
Proof.
have Hpinf := sign_at_pinf_matches charpoly_int.
rewrite /sgn_matches in Hpinf.
destruct Hpinf as [_ [_ Hpos]].
apply/Hpos. rewrite sign_at_pinf_charpoly. reflexivity.
Qed.

(* P is nonzero (has positive leading coefficient). *)
Lemma charpoly_neq0 : (pol_to_polyralg charpoly_int != 0)%R.
Proof.
apply/negP => /eqP H0.
have Hlc := charpoly_lc_pos. rewrite H0 lead_coef0 in Hlc.
by have := ltr0_neq0 Hlc; rewrite eqxx.
Qed.

(* P evaluated at the Cauchy bound is positive.
   Proof: all roots lie in (-cb, cb), so P has no root >= cb.
   Above all roots, sgr(P(x)) = sgr(lc(P)) = 1 > 0. *)
Lemma charpoly_pos_at_cb :
  (0 < (pol_to_polyralg charpoly_int).[cauchy_bound (pol_to_polyralg charpoly_int)])%R.
Proof.
set P := pol_to_polyralg charpoly_int.
set b := cauchy_bound P.
have HP : P != 0 := charpoly_neq0.
have Hlc : (0 < lead_coef P)%R := charpoly_lc_pos.
(* P(b) != 0 because b = cauchy_bound and all roots < b *)
have Hpb : ~~ root P b.
{ apply/negP => Hroot.
  have Hin : b \in `[b, +oo[
    by rewrite in_itv /= preorder.Order.PreorderTheory.lexx.
  by have := ge_cauchy_bound HP Hin; rewrite Hroot. }
(* sgr(P(b)) = sgr(lc(P)) because b is above all roots *)
have Hsgn : Num.sg P.[b] = sgp_pinfty P.
{ have := sgp_pinftyP (ge_cauchy_bound HP).
  move/(_ b).
  rewrite in_itv /= preorder.Order.PreorderTheory.lexx //.
  by move=> /(_ isT). }
rewrite -sgr_gt0 Hsgn /sgp_pinfty sgr_gt0 //.
Qed.

(* ================================================================== *)
(*  Section 6: The headline L1 lemma (IVT-based proof).                 *)
(*                                                                      *)
(*  Prove existence of a real root of charpoly_int above 4/105 using    *)
(*  the intermediate value theorem. P(4/105) < 0 and P(cb) > 0, so     *)
(*  by IVT there is a root in (4/105, cb).                              *)
(* ================================================================== *)

Lemma maynard_L1_concrete :
  exists lambda : realalg,
    root (pol_to_polyralg charpoly_int) lambda
    /\ (threshold_ralg 4 105 < lambda)%R.
Proof.
set P := pol_to_polyralg charpoly_int.
set a := threshold_ralg 4 105.
set b := cauchy_bound P.
have Hab : (a <= b)%R by apply: order.Order.POrderTheory.ltW; exact: threshold_lt_cb.
have Hpa : (P.[a] < 0)%R := charpoly_neg_at_threshold.
have Hpb : (0 < P.[b])%R := charpoly_pos_at_cb.
have Hprod : (P.[a] * P.[b] < 0)%R.
{ by rewrite nmulr_rlt0 //; apply: Hpb. }
case: (poly_ivtoo Hab Hprod) => x Hx Hroot.
exists x; split; first exact: Hroot.
by move: Hx; rewrite inE /= => /andP [].
Qed.

