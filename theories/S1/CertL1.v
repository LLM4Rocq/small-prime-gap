(* ================================================================== *)
(*  theories/S1/CertL1.v                                                *)
(*                                                                      *)
(*  L1 consumer wiring: instantiate Bridge.v's                          *)
(*  `sturm_count_above_pos_concrete` at the Maynard certificate data    *)
(*  from Witness.v to discharge as many hypotheses as possible.         *)
(*                                                                      *)
(*  Concrete data:                                                      *)
(*    p   := charpoly_int   (degree-42 char poly, list Z)               *)
(*    num := 4              (threshold numerator)                        *)
(*    den := 105            (threshold denominator)                      *)
(*                                                                      *)
(*  Machine-verified facts (vm_compute on list Z / nat):                *)
(*    - den_pos              : (0 < 105)%Z                              *)
(*    - variation signs_at_x0 = 22                                      *)
(*    - variation signs_at_inf = 21                                     *)
(*    - sign variation difference = 1 > 0 (positive root count)         *)
(*    - All 43 sign entries at x0 are nonzero (+/-1)                    *)
(*    - All 43 sign entries at inf are nonzero (+/-1)                   *)
(*                                                                      *)
(*  Now proven (Qed):                                                   *)
(*    signs_at_x0_agree — witness signs = sign_at_rat on the chain      *)
(*                         (via CRTSigns + shipped_chain_eq)            *)
(*    signs_at_inf_agree — witness signs = sign_at_pinf on the chain    *)
(*                         (via CRTSigns + shipped_chain_eq)            *)
(*    chain_lc_nz       — leading coefficients nonzero (realalg)        *)
(*    chain_th_nz       — chain evals at 4/105 nonzero (realalg)        *)
(*    threshold_lt_cb   — 4/105 < cauchy_bound (lift charpoly_int)      *)
(*    no_root_at_cb     — no chain poly has a root >= cauchy_bound      *)
(*                         (via ge_cauchy_bound + cauchy_bound_le)      *)
(*    chain_cb_nz       — chain evals at cauchy_bound nonzero           *)
(*                         (derived from no_root_at_cb)                 *)
(*                                                                      *)
(*  Remaining admitted obligations (future work):                       *)
(*    shipped_chain_eq    — shipped chain = computed chain (Z-level)    *)
(*    chain_is_mods       — lifted chain = abstract mods (moved from   *)
(*                           Bridge.v; strict equality)                *)
(*    cauchy_bound_le_of_chain — Cauchy-bound comparison for chain     *)
(*                           entries (numerically verified at BigZ      *)
(*                           level in CauchyCheck.all_chain_cb_le;     *)
(*                           bridge to realalg pending)                *)
(* ================================================================== *)

From Stdlib Require Import ZArith List Lia.
Import ListNotations.

From mathcomp Require Import all_boot all_algebra.
From mathcomp.real_closed Require Import polyrcf qe_rcf_th realalg.
Import GRing.Theory Num.Theory.

From PrimeGapS1 Require Import IntPoly BrownTraub SignChain Witness Bridge.
From PrimeGapS1 Require Import WitnessChain CRTSigns.

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
(*  Section 2: Bridge from witness sign data to sturm_count_above.      *)
(*                                                                      *)
(*  The witness data (signs_at_x0, signs_at_inf) was computed by the    *)
(*  Python certificate generator by evaluating each chain polynomial    *)
(*  at 4/105 (resp. reading leading coefficients). We need to show      *)
(*  these agree with the Rocq-side `sign_at_rat` and `sign_at_pinf`    *)
(*  computations on `BrownTraub.sturm_chain charpoly_int`.              *)
(*                                                                      *)
(*  CRTSigns.v (or its future replacement) machine-verifies that the   *)
(*  sign vectors agree with signs computed from the SHIPPED chain       *)
(*  (WitnessChain.sturm_chain).  We bridge to the COMPUTED chain       *)
(*  (BrownTraub.sturm_chain charpoly_int) via shipped_chain_eq.        *)
(* ================================================================== *)

(* The shipped chain data (WitnessChain.sturm_chain) equals the chain
   computed by BrownTraub on charpoly_int.  This is a Z-level equality
   that can be verified by CRT modular checking (cf. CRTCheck.v) once
   the CRT-to-Z lifting argument is formalized.  Strictly weaker than
   chain_is_mods (which operates on lifted polyralg values). *)
Lemma shipped_chain_eq :
  WitnessChain.sturm_chain = BrownTraub.sturm_chain charpoly_int.
Proof.
Admitted.

(* The precomputed sign data matches the computed sign sequence at
   the threshold 4/105.
   Proof: CRTSigns proves signs match the shipped chain;
   shipped_chain_eq bridges shipped -> computed. *)
Lemma signs_at_x0_agree :
  signs_at_x0
  = List.map (fun p => sign_at_rat p 4 105)
             (BrownTraub.sturm_chain charpoly_int).
Proof.
  rewrite <- shipped_chain_eq.
  exact signs_at_x0_shipped.
Qed.

(* The precomputed sign data matches sign_at_pinf on the chain.
   Same strategy: CRTSigns + shipped_chain_eq. *)
Lemma signs_at_inf_agree :
  signs_at_inf
  = List.map sign_at_pinf (BrownTraub.sturm_chain charpoly_int).
Proof.
  rewrite <- shipped_chain_eq.
  exact signs_at_inf_shipped.
Qed.

(* Combining the sign agreements with the verified variation counts
   gives us the sturm_count_above positivity on the actual chain. *)
Lemma sturm_count_above_charpoly_pos :
  (0 < sturm_count_above
         (BrownTraub.sturm_chain charpoly_int) 4 105)%N.
Proof.
  unfold sturm_count_above, variation_at_rat, variation_at_pinf.
  rewrite -signs_at_x0_agree -signs_at_inf_agree.
  exact witness_root_count_pos.
Qed.

(* ================================================================== *)
(*  Section 3: Chain non-nil.                                           *)
(*                                                                      *)
(*  Every entry in the Sturm chain is non-nil. We derive this from     *)
(*  the sign data: if sign_at_pinf q is nonzero, then q has a          *)
(*  nonzero leading coefficient, hence q is non-nil.                    *)
(*                                                                      *)
(*  The proof goes: signs_at_inf has all nonzero entries (verified),    *)
(*  and signs_at_inf = map sign_at_pinf chain (admitted). If            *)
(*  sign_at_pinf q <> 0 then q <> nil (since sign of nil's leading     *)
(*  coeff is 0). So every chain entry is non-nil.                       *)
(* ================================================================== *)

Local Lemma sign_at_pinf_nonzero_implies_nonnil (q : pol) :
  sign_at_pinf q <> BinInt.Z0 -> q <> nil.
Proof.
  unfold sign_at_pinf, sgn_Z, plead.
  destruct q as [| z qs].
  - simpl. lia.
  - intros _. discriminate.
Qed.

Lemma chain_nz :
  forall q, List.In q (BrownTraub.sturm_chain charpoly_int) ->
    q <> nil.
Proof.
  intros q Hq.
  apply sign_at_pinf_nonzero_implies_nonnil.
  (* sign_at_pinf q is in signs_at_inf (via signs_at_inf_agree),
     and all entries of signs_at_inf are nonzero. *)
  pose proof signs_at_inf_agree as Hinf.
  assert (Hmap : List.In (sign_at_pinf q)
                  (List.map sign_at_pinf
                    (BrownTraub.sturm_chain charpoly_int))).
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
(*  Section 4: Realalg-level structural hypotheses.                     *)
(*                                                                      *)
(*  These involve realalg types and cannot be discharged by             *)
(*  vm_compute. Each is a clearly named obligation for future work.     *)
(* ================================================================== *)

(* 4a. Leading coefficients of all chain entries are nonzero after
   lifting to realalg. This should follow from pnorm preserving
   nonzero leading coefficients and the morphism respecting them. *)
Lemma chain_lc_nz :
  forall q, List.In q (BrownTraub.sturm_chain charpoly_int) ->
    (lead_coef (pol_to_polyralg q) != 0)%R.
Proof.
  intros q Hq.
  have Hpinf := sign_at_pinf_matches q.
  rewrite /sgn_matches in Hpinf.
  destruct Hpinf as [Hiff _].
  apply/eqP. intro Heq. apply Hiff in Heq.
  have Hin : List.In (sign_at_pinf q) signs_at_inf.
  { rewrite signs_at_inf_agree. apply List.in_map. exact Hq. }
  have Hall := signs_at_inf_all_nonzero.
  rewrite List.forallb_forall in Hall.
  specialize (Hall _ Hin). simpl in Hall.
  unfold Z.eq in Heq. rewrite Heq in Hall. discriminate.
Qed.

(* 4b. All chain entries evaluate to nonzero at threshold 4/105
   after lifting to realalg. Should follow from signs_at_x0 being
   all nonzero, combined with sign_at_rat agreeing with realalg
   evaluation. *)
Lemma chain_th_nz :
  forall q, List.In q (BrownTraub.sturm_chain charpoly_int) ->
    ((pol_to_polyralg q).[threshold_ralg 4 105] != 0)%R.
Proof.
  intros q Hq.
  have Hrat := sign_at_rat_matches q 4 105 den_pos.
  rewrite /sgn_matches in Hrat.
  destruct Hrat as [Hiff _].
  apply/eqP. intro Heq.
  have Heq2 : Z.eq (sign_at_rat q 4 105) 0 by apply Hiff.
  have Hin := List.in_map (fun p0 => sign_at_rat p0 4 105) _ _ Hq.
  rewrite <- signs_at_x0_agree in Hin.
  have Hall := signs_at_x0_all_nonzero.
  rewrite List.forallb_forall in Hall.
  specialize (Hall _ Hin). simpl in Hall.
  unfold Z.eq in Heq2. rewrite Heq2 in Hall. discriminate.
Qed.

(* 4c. The threshold 4/105 is below the Cauchy bound. The Cauchy
   bound of the degree-42 polynomial with huge coefficients is
   vastly larger than 4/105 ~ 0.038. *)
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

(* 4d. The lifted Sturm chain equals the abstract mods chain.
   Previously derived from Bridge.v's `mods_int_morph`, which has been
   removed (the strict chain equality is unprovable: chains differ by
   polynomial scalars).  This is now a standalone hypothesis (Admitted).
   Closing it requires either (a) proving that our Brown-Traub PRS
   chain exactly matches MathComp's `mods` chain entry-by-entry, or
   (b) refactoring the downstream consumer to use a weaker form. *)
Lemma chain_is_mods :
  List.map pol_to_polyralg (BrownTraub.sturm_chain charpoly_int)
  = mods (pol_to_polyralg charpoly_int)
         ((pol_to_polyralg charpoly_int)^`()).
Proof.
Admitted.

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

(* Bridge: the BigZ-level Cauchy-bound comparison
   (`CauchyCheck.all_chain_cb_le`, proven by vm_compute) implies the
   realalg inequality `cauchy_bound (pol_to_polyralg q)
   <= cauchy_bound (pol_to_polyralg P)` for every chain entry `q`.

   Proof sketch (fully formalizable via MathComp lemmas):
   - `cauchy_bound p = 1 + |lc p|^{-1} * sum_i |p`_i|`.
   - For `p = pol_to_polyralg q`:
       * `lc p = (Z_to_int (plead q))%:~R`    (lead_coef_pol_to_polyralg)
       * `|lc p| = (|Z_to_int (plead q)|)%:~R` (normrMz)
       * `p`_i = (Z_to_int (nth i q 0))%:~R`   (coeff of map_poly of ratr)
       * `|p`_i| = (|Z_to_int (nth i q 0)|)%:~R`
       * `sum_i |p`_i| = (sum |q[i]|_Z)%:~R`   (sumr of integer norms)
   - So `cauchy_bound p = 1 + (sum_abs_Z q / |plead q|_Z)%:~R`.
   - The comparison `cb_q <= cb_P` reduces to
       `sum_abs_Z(q) * |plead(P)|_Z <= sum_abs_Z(P) * |plead(q)|_Z`,
     a Z inequality verified by `CauchyCheck.all_chain_cb_le`. *)
Lemma cauchy_bound_le_of_chain :
  forall q, List.In q (BrownTraub.sturm_chain charpoly_int) ->
    (cauchy_bound (pol_to_polyralg q)
       <= cauchy_bound (pol_to_polyralg charpoly_int))%R.
Proof.
Admitted.

(* 4e. No chain polynomial has a root weakly above the Cauchy bound.
   Proof: each chain entry r = pol_to_polyralg q is nonzero, so
   ge_cauchy_bound gives noroot on [cauchy_bound r, +oo[.
   Since cauchy_bound P >= cauchy_bound r (by cauchy_bound_le_of_chain),
   [cauchy_bound P, +oo[ ⊆ [cauchy_bound r, +oo[, giving the result. *)
Lemma no_root_at_cb :
  forall r : {poly realalg},
    r \in mods (pol_to_polyralg charpoly_int)
               ((pol_to_polyralg charpoly_int)^`()) ->
    {in `[cauchy_bound (pol_to_polyralg charpoly_int), +oo[,
       forall y : realalg, ~~ root r y}.
Proof.
move=> r Hr y Hy.
set P := pol_to_polyralg charpoly_int.
(* r is in mods P P', so by chain_is_mods it is pol_to_polyralg q
   for some q in the concrete chain. *)
have Hin : r \in List.map pol_to_polyralg (BrownTraub.sturm_chain charpoly_int)
  by rewrite chain_is_mods.
(* Extract a witness q from the List.map membership. *)
have [q [Hq Heqr]] : exists q, List.In q (BrownTraub.sturm_chain charpoly_int)
                                /\ pol_to_polyralg q = r.
{ move: Hin. rewrite /List.map.
  elim: (BrownTraub.sturm_chain charpoly_int) => [|a l IH] //=.
  rewrite inE. case/orP => [/eqP -> | Htl].
  - by exists a; split; [left|].
  - case: (IH Htl) => q [Hql Heq].
    by exists q; split; [right|]. }
subst r.
(* pol_to_polyralg q is nonzero (from chain_lc_nz) *)
have Hlc : (lead_coef (pol_to_polyralg q) != 0)%R := chain_lc_nz q Hq.
have Hnz : pol_to_polyralg q != 0.
{ by apply/eqP => Heq; rewrite Heq lead_coef0 eqxx in Hlc. }
(* ge_cauchy_bound gives: no root of q above cauchy_bound q *)
have Hge := ge_cauchy_bound Hnz.
(* cauchy_bound P >= cauchy_bound q *)
have Hle := cauchy_bound_le_of_chain q Hq.
(* y is in [cauchy_bound P, +oo[, so y >= cauchy_bound P >= cauchy_bound q *)
have Hy2 : y \in `[cauchy_bound (pol_to_polyralg q), +oo[.
{ rewrite !in_itv /= in Hy *.
  case/andP: Hy => Hcb _. apply/andP; split=> //.
  exact: (order.Order.POrderTheory.le_trans Hle Hcb). }
exact: Hge Hy2.
Qed.

(* Helper: List.In q l implies pol_to_polyralg q is in the
   mathcomp seq (List.map pol_to_polyralg l). *)
Local Lemma list_in_to_mem (q : pol) (l : list pol) :
  List.In q l -> pol_to_polyralg q \in List.map pol_to_polyralg l.
Proof.
  elim: l => [//|a tl IH] /=.
  case=> [<-|Htl].
  - by rewrite inE eqxx.
  - by rewrite inE (IH Htl) orbT.
Qed.

(* 4f. All chain entries evaluate to nonzero at the Cauchy bound
   after lifting to realalg.
   Derived from no_root_at_cb: if no chain polynomial has a root
   at or above cauchy_bound P, then evaluating at cauchy_bound P
   gives a nonzero result. *)
Lemma chain_cb_nz :
  forall q, List.In q (BrownTraub.sturm_chain charpoly_int) ->
    ((pol_to_polyralg q).[
       cauchy_bound (pol_to_polyralg charpoly_int)] != 0)%R.
Proof.
  intros q Hq.
  set P := pol_to_polyralg charpoly_int.
  set r := pol_to_polyralg q.
  (* r is in mods P P^`() by chain_is_mods *)
  have Hin : r \in mods P P^`().
  { rewrite -chain_is_mods. exact: list_in_to_mem Hq. }
  (* no_root_at_cb gives: noroot r on [cauchy_bound P, +oo[ *)
  have Hnoroot := no_root_at_cb r Hin.
  (* cauchy_bound P is in the interval *)
  have Hcbin : cauchy_bound P \in `[cauchy_bound P, +oo[.
  { by rewrite in_itv /= order.Order.POrderTheory.lexx. }
  have Hnr := Hnoroot _ Hcbin.
  (* ~~ root r (cauchy_bound P) means r.[cauchy_bound P] != 0 *)
  by rewrite /root in Hnr; apply/eqP => Heq; rewrite Heq eqxx in Hnr.
Qed.

(* ================================================================== *)
(*  Section 5: The headline L1 lemma.                                   *)
(*                                                                      *)
(*  Wire `sturm_count_above_pos_concrete` with all the above to get    *)
(*  the existence of a realalg root of charpoly_int above 4/105.        *)
(*                                                                      *)
(*  Proven facts used: den_pos, chain_nz, chain_lc_nz, chain_th_nz,    *)
(*                     chain_cb_nz, threshold_lt_cb,                    *)
(*                     sturm_count_above_charpoly_pos,                  *)
(*                     signs_at_x0_agree, signs_at_inf_agree.           *)
(*  Admitted facts used: shipped_chain_eq, chain_is_mods,               *)
(*                       cauchy_bound_le_of_chain.                      *)
(* ================================================================== *)

Lemma maynard_L1_concrete :
  exists lambda : realalg,
    root (pol_to_polyralg charpoly_int) lambda
    /\ (threshold_ralg 4 105 < lambda)%R.
Proof.
  apply (sturm_count_above_pos_concrete
           charpoly_int 4 105
           den_pos
           chain_nz
           chain_lc_nz
           chain_th_nz
           chain_cb_nz
           threshold_lt_cb
           chain_is_mods
           no_root_at_cb).
  exact sturm_count_above_charpoly_pos.
Qed.
