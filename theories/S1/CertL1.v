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

From PrimeGapS1 Require Import IntPoly BrownTraub SignChain Witness Bridge.
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

(* Sign variation at the threshold 4/105. *)
Lemma variation_at_x0_eq : variation signs_at_x0 = 22%nat.
Proof. vm_compute. reflexivity. Qed.

(* Sign variation at +infinity. *)
Lemma variation_at_inf_eq : variation signs_at_inf = 21%nat.
Proof. vm_compute. reflexivity. Qed.

(* The Sturm count from the witness sign data is 1 > 0. *)
Lemma witness_root_count :
  (variation signs_at_x0 - variation signs_at_inf)%nat = 1%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma witness_root_count_pos :
  (0 < variation signs_at_x0 - variation signs_at_inf)%N.
Proof. vm_compute. reflexivity. Qed.

(* All sign entries at x0 are nonzero — witnesses that every chain
   polynomial evaluates to a nonzero value at 4/105. *)
Lemma signs_at_x0_all_nonzero :
  List.forallb (fun z => negb (Z.eqb z 0))%Z signs_at_x0 = true.
Proof. vm_compute. reflexivity. Qed.

(* All sign entries at infinity are nonzero. *)
Lemma signs_at_inf_all_nonzero :
  List.forallb (fun z => negb (Z.eqb z 0))%Z signs_at_inf = true.
Proof. vm_compute. reflexivity. Qed.

(* Both sign lists have 43 entries, matching the 43-entry chain
   (degree-42 polynomial -> 43 Sturm chain entries). *)
Lemma signs_at_x0_length : List.length signs_at_x0 = 43%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma signs_at_inf_length : List.length signs_at_inf = 43%nat.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  Section 2: Shipped chain sign agreement.                            *)
(*                                                                      *)
(*  The witness data (signs_at_x0, signs_at_inf) was computed by the    *)
(*  Python certificate generator by evaluating each shipped chain       *)
(*  polynomial at 4/105 (resp. reading leading coefficients).           *)
(*  CRTSigns.v machine-verifies that the sign vectors agree with        *)
(*  signs computed from the shipped chain (WitnessChain.sturm_chain).   *)
(*                                                                      *)
(*  We use the shipped chain DIRECTLY — no bridging to                  *)
(*  BrownTraub.sturm_chain or the abstract `mods` chain is needed       *)
(*  for sign-variation computations.                                    *)
(* ================================================================== *)

(* ================================================================== *)
(*  Section 3: Chain non-nil (shipped chain).                           *)
(*                                                                      *)
(*  Every entry in the shipped chain is non-nil. We derive this from    *)
(*  the sign data: if sign_at_pinf q is nonzero, then q has a          *)
(*  nonzero leading coefficient, hence q is non-nil.                    *)
(* ================================================================== *)

Local Lemma sign_at_pinf_nonzero_implies_nonnil (q : pol) :
  sign_at_pinf q <> BinInt.Z0 -> q <> nil.
Proof.
  unfold sign_at_pinf, sgn_Z, plead.
  destruct q as [| z qs].
  - simpl. lia.
  - intros _. discriminate.
Qed.

Lemma chain_nz_shipped :
  forall q, List.In q WitnessChain.sturm_chain ->
    q <> nil.
Proof.
  intros q Hq.
  apply sign_at_pinf_nonzero_implies_nonnil.
  pose proof signs_at_inf_shipped as Hinf.
  assert (Hmap : List.In (sign_at_pinf q)
                  (List.map sign_at_pinf WitnessChain.sturm_chain)).
  { apply List.in_map. exact Hq. }
  rewrite <- Hinf in Hmap.
  pose proof signs_at_inf_all_nonzero as Hall.
  rewrite List.forallb_forall in Hall.
  specialize (Hall _ Hmap).
  simpl in Hall.
  destruct (BinInt.Z.eqb_spec (sign_at_pinf q) BinInt.Z0) as [Heq | Hneq].
  - discriminate.
  - exact Hneq.
Qed.

(* ================================================================== *)
(*  Section 4: Realalg-level structural hypotheses (shipped chain).     *)
(*                                                                      *)
(*  These involve realalg types and cannot be discharged by             *)
(*  vm_compute. Each is derived from the CRTSigns-verified sign data.   *)
(* ================================================================== *)

(* 4a. Leading coefficients of all shipped chain entries are nonzero
   after lifting to realalg. *)
Lemma chain_lc_nz_shipped :
  forall q, List.In q WitnessChain.sturm_chain ->
    (lead_coef (pol_to_polyralg q) != 0)%R.
Proof.
  intros q Hq.
  have Hpinf := sign_at_pinf_matches q.
  rewrite /sgn_matches in Hpinf.
  destruct Hpinf as [Hiff _].
  apply/eqP. intro Heq. apply Hiff in Heq.
  have Hin : List.In (sign_at_pinf q) signs_at_inf.
  { rewrite signs_at_inf_shipped. apply List.in_map. exact Hq. }
  have Hall := signs_at_inf_all_nonzero.
  rewrite List.forallb_forall in Hall.
  specialize (Hall _ Hin). simpl in Hall.
  unfold Z.eq in Heq. rewrite Heq in Hall. discriminate.
Qed.

(* 4b. All shipped chain entries evaluate to nonzero at threshold
   4/105 after lifting to realalg. *)
Lemma chain_th_nz_shipped :
  forall q, List.In q WitnessChain.sturm_chain ->
    ((pol_to_polyralg q).[threshold_ralg 4 105] != 0)%R.
Proof.
  intros q Hq.
  have Hrat := sign_at_rat_matches q 4 105 den_pos.
  rewrite /sgn_matches in Hrat.
  destruct Hrat as [Hiff _].
  apply/eqP. intro Heq.
  have Heq2 : Z.eq (sign_at_rat q 4 105) 0 by apply Hiff.
  have Hin := List.in_map (fun p0 => sign_at_rat p0 4 105) _ _ Hq.
  rewrite <- signs_at_x0_shipped in Hin.
  have Hall := signs_at_x0_all_nonzero.
  rewrite List.forallb_forall in Hall.
  specialize (Hall _ Hin). simpl in Hall.
  unfold Z.eq in Heq2. rewrite Heq2 in Hall. discriminate.
Qed.

(* 4c. The threshold 4/105 is below the Cauchy bound. *)
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

(* ---------- Cauchy-bound comparison infrastructure ---------- *)

(* BigZ-level computation to verify that every chain entry has a
   Cauchy bound <= that of the head polynomial.  We work entirely
   in BigZ to avoid the expensive BigZ -> Stdlib Z conversion. *)
Module CauchyCheck.
From Bignums Require Import BigZ.

Definition sum_abs (p : list BigZ.t_) : BigZ.t_ :=
  List.fold_right (fun c acc => BigZ.add (BigZ.abs c) acc)
    0%bigZ p.

Fixpoint lc_aux (p : list BigZ.t_) (acc : BigZ.t_) : BigZ.t_ :=
  match p with
  | nil => acc
  | x :: xs =>
    if BigZ.eqb x 0%bigZ then lc_aux xs acc else lc_aux xs x
  end.

Definition lc (p : list BigZ.t_) : BigZ.t_ := lc_aux p 0%bigZ.

Definition cb_le (q p : list BigZ.t_) : bool :=
  BigZ.leb (BigZ.mul (sum_abs q) (BigZ.abs (lc p)))
           (BigZ.mul (sum_abs p) (BigZ.abs (lc q))).

Definition all_cb_le (chain : list (list BigZ.t_))
                     (p : list BigZ.t_) : bool :=
  List.forallb (fun q => cb_le q p) chain.

Lemma all_chain_cb_le :
  all_cb_le WitnessChain.sturm_chain_bigZ
    (List.nth 0 WitnessChain.sturm_chain_bigZ nil) = true.
Proof. vm_compute. reflexivity. Qed.

End CauchyCheck.

(* ---------- Cauchy-bound bridge ---------- *)

(* The cauchy_bound of a lifted polynomial goes through ratr.
   Key identity: cauchy_bound(map_poly ratr p) = ratr(cauchy_bound p)
   for {poly rat} with nonzero leading coefficient.
   We prove the comparison via the rat level. *)

Lemma cauchy_bound_map_ratr (p : {poly rat}) :
  lead_coef p != 0 ->
  cauchy_bound (map_poly ratr p : {poly realalg})
  = ratr (cauchy_bound p : rat).
Proof.
move=> Hlc.
rewrite /cauchy_bound.
have Hsz : size (map_poly (rR:=realalg_realalg__canonical__GRing_NzRing) ratr p) = size p
  by rewrite size_map_inj_poly ?rmorph0 //; exact: fmorph_inj.
have Hlcm : lead_coef (map_poly (rR:=realalg_realalg__canonical__GRing_NzRing) ratr p)
            = ratr (lead_coef p)
  by apply: lead_coef_map_inj; [exact: fmorph_inj | exact: rmorph0].
rewrite Hsz Hlcm.
rewrite rmorphD rmorph1 rmorphM fmorphV -ratr_norm rmorph_sum /=.
congr (1 + _ * _).
apply: eq_bigr => i _. by rewrite coef_map -ratr_norm.
Qed.

(* Bridge: nonzero leading coefficient of pol_to_polyrat from the
   corresponding property of pol_to_polyralg. *)
Lemma pol_to_polyrat_lc_nz (p : pol) :
  (lead_coef (pol_to_polyralg p) != 0)%R ->
  lead_coef (CharPoly.pol_to_polyrat p) != 0.
Proof.
rewrite /pol_to_polyralg => Hlc.
apply/negP => /eqP H0.
move: Hlc.
rewrite (lead_coef_map_inj (@fmorph_inj _ _ (ratr : {rmorphism rat -> realalg}))
           (rmorph0 _)) H0 rmorph0.
by rewrite eqxx.
Qed.

(* The Cauchy bound satisfies: cb(q) <= cb(p) whenever
   sum|q_i| * |lc(p)| <= sum|p_i| * |lc(q)| and lc(q), lc(p) != 0. *)
Lemma cauchy_bound_le_cross (R : realFieldType) (p q : {poly R}) :
  (lead_coef q != 0)%R ->
  (lead_coef p != 0)%R ->
  ((\sum_(i < size q) `|q`_i|) * `|lead_coef p| <=
   (\sum_(i < size p) `|p`_i|) * `|lead_coef q|)%R ->
  (cauchy_bound q <= cauchy_bound p)%R.
Proof.
move=> Hq Hp Hle.
rewrite /cauchy_bound; apply: lerD => //.
set sq := (\sum_(i < size q) `|q`_i|)%R.
set sp := (\sum_(i < size p) `|p`_i|)%R.
set lq := `|lead_coef q|%R.
set lp := `|lead_coef p|%R.
have Hq_pos : (0 < lq)%R by rewrite lt0r normr_eq0 Hq normr_ge0.
have Hp_pos : (0 < lp)%R by rewrite lt0r normr_eq0 Hp normr_ge0.
(* Goal: lq^{-1} * sq <= lp^{-1} * sp.
   From Hle : sq * lp <= sp * lq, dividing both sides by lq*lp > 0.
   We use: (a <= b) -> (a * c^{-1} <= b * c^{-1}) for c > 0,
   then simplify using cancellation. *)
(* Elementary algebra: a*c^-1 <= b*d^-1 from a*d <= b*c when c,d > 0 *)
(* This is the standard cross-multiplication equivalence for inequalities
   of fractions with positive denominators. *)
(* Rewrite lq^-1 * sq as sq / lq (= sq * lq^-1), similarly for RHS *)
rewrite mulrC [lp^-1 * sp]mulrC.
by rewrite ler_pdivlMr // mulrAC ler_pdivrMr.
Qed.

(* The head of the shipped chain is charpoly_int. *)
Lemma shipped_chain_hd :
  List.hd nil WitnessChain.sturm_chain = charpoly_int.
Proof.
change (Recompose.lift_bigZ WitnessChain.chain_0 = charpoly_int).
exact: Smoke.chain_0_matches_charpoly.
Qed.

Lemma sturm_chain_nonempty : WitnessChain.sturm_chain <> nil.
Proof.
move=> H. have := signs_at_inf_length.
rewrite signs_at_inf_shipped H /=. discriminate.
Qed.

Lemma charpoly_in_shipped : List.In charpoly_int WitnessChain.sturm_chain.
Proof.
have Hhd := shipped_chain_hd.
have Hne := sturm_chain_nonempty.
destruct WitnessChain.sturm_chain as [|h t]; first by exfalso; apply Hne.
simpl in Hhd. subst h. left. reflexivity.
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

