(* ================================================================== *)
(*  theories/S1/CertL1.v                                                *)
(*                                                                      *)
(*  L1: prove that charpoly_int has a real root above 4/105.            *)
(*                                                                      *)
(*  Proof strategy: intermediate value theorem (poly_ivtoo).            *)
(*    P(4/105) < 0   — by direct vm_compute on charpoly_int             *)
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

Import order.Order.POrderTheory.

Local Open Scope ring_scope.

(* ================================================================== *)
(*  Section 1: Facts verified by vm_compute on concrete data.           *)
(* ================================================================== *)

Lemma den_pos : BinInt.Z.lt BinInt.Z0 105.
Proof. reflexivity. Qed.

(* The threshold 4/105 is below the Cauchy bound. *)
Lemma threshold_lt_cb :
  (threshold_ralg 4 105
     < cauchy_bound (pol_to_polyralg charpoly_int))%R.
Proof.
  apply: (lt_le_trans (y := 1)).
    rewrite /threshold_ralg ltr_pdivrMr.
      rewrite mul1r ltr_int. done.
      rewrite ltr0z. done.
    rewrite /cauchy_bound lerDl mulr_ge0 // ?invr_ge0 ?normr_ge0 //;
    apply: sumr_ge0 => i _; apply: normr_ge0.
Qed.

(* ================================================================== *)
(*  Section 2: IVT-based root existence.                                *)
(* ================================================================== *)

(* sign_at_rat charpoly_int 4 105 = -1, by direct vm_compute. *)
Lemma sign_at_rat_charpoly :
  sign_at_rat charpoly_int 4 105 = BinNums.Zneg BinNums.xH.
Proof. vm_compute. reflexivity. Qed.

(* sign_at_pinf charpoly_int = 1, by direct vm_compute. *)
Lemma sign_at_pinf_charpoly :
  sign_at_pinf charpoly_int = BinNums.Zpos BinNums.xH.
Proof. vm_compute. reflexivity. Qed.

(* P is negative at threshold 4/105. *)
Lemma charpoly_neg_at_threshold :
  ((pol_to_polyralg charpoly_int).[threshold_ralg 4 105] < 0)%R.
Proof.
have Hrat := sign_at_rat_matches charpoly_int 4 105 den_pos.
rewrite /sgn_matches in Hrat.
case: Hrat => _ [Hneg _]; apply/Hneg.
by rewrite sign_at_rat_charpoly.
Qed.

(* P has positive leading coefficient. *)
Lemma charpoly_lc_pos :
  (0 < lead_coef (pol_to_polyralg charpoly_int))%R.
Proof.
have Hpinf := sign_at_pinf_matches charpoly_int.
rewrite /sgn_matches in Hpinf.
case: Hpinf => _ [_ Hpos]; apply/Hpos.
by rewrite sign_at_pinf_charpoly.
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
(*  Section 3: The headline L1 lemma (IVT-based proof).                 *)
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
have Hab : (a <= b)%R by apply: ltW; exact: threshold_lt_cb.
have Hpa : (P.[a] < 0)%R := charpoly_neg_at_threshold.
have Hpb : (0 < P.[b])%R := charpoly_pos_at_cb.
have Hprod : (P.[a] * P.[b] < 0)%R.
{ by rewrite nmulr_rlt0 //; apply: Hpb. }
case: (poly_ivtoo Hab Hprod) => x Hx Hroot.
exists x; split; first exact: Hroot.
by move: Hx; rewrite inE /= => /andP [].
Qed.
