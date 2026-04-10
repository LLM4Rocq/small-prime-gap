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
(*  Named admitted obligations (future work):                           *)
(*    chain_eq_precomp  — precomputed chain = BrownTraub.sturm_chain    *)
(*    signs_at_x0_agree — witness signs = sign_at_rat on the chain      *)
(*    signs_at_inf_agree — witness signs = sign_at_pinf on the chain    *)
(*    chain_lc_nz       — leading coefficients nonzero (realalg)        *)
(*    chain_th_nz       — chain evals at 4/105 nonzero (realalg)        *)
(*    chain_cb_nz       — chain evals at cauchy_bound nonzero           *)
(*    threshold_lt_cb   — 4/105 < cauchy_bound (lift charpoly_int)      *)
(*    chain_is_mods     — lifted chain = abstract mods                  *)
(*    no_root_at_cb     — no chain poly roots >= cauchy_bound           *)
(* ================================================================== *)

From Stdlib Require Import ZArith List Lia.
Import ListNotations.

From mathcomp Require Import all_boot all_algebra.
From mathcomp.real_closed Require Import polyrcf qe_rcf_th realalg.
Import GRing.Theory Num.Theory.

From PrimeGapS1 Require Import IntPoly BrownTraub SignChain Witness Bridge.

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
(*  This is a computational equality, but the chain polynomials have    *)
(*  coefficients up to ~200 000 bits, making direct vm_compute          *)
(*  intractable in Rocq. Future work: either (a) use native_compute    *)
(*  with bignum support, or (b) verify the chain equality via a         *)
(*  modular-arithmetic certificate.                                     *)
(* ================================================================== *)

(* The precomputed sign data matches the computed sign sequence at
   the threshold 4/105. *)
Lemma signs_at_x0_agree :
  signs_at_x0
  = List.map (fun p => sign_at_rat p 4 105)
             (BrownTraub.sturm_chain charpoly_int).
Proof.
  (* Computational equality on list Z, but the intermediate chain
     polynomials have ~200 kbit coefficients. Intractable for
     vm_compute; a modular-arithmetic certificate or segmented
     native_compute can close this. *)
Admitted.

(* The precomputed sign data matches sign_at_pinf on the chain. *)
Lemma signs_at_inf_agree :
  signs_at_inf
  = List.map sign_at_pinf (BrownTraub.sturm_chain charpoly_int).
Proof.
  (* Same computational issue as signs_at_x0_agree. *)
Admitted.

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
Admitted.

(* 4b. All chain entries evaluate to nonzero at threshold 4/105
   after lifting to realalg. Should follow from signs_at_x0 being
   all nonzero, combined with sign_at_rat agreeing with realalg
   evaluation. *)
Lemma chain_th_nz :
  forall q, List.In q (BrownTraub.sturm_chain charpoly_int) ->
    ((pol_to_polyralg q).[threshold_ralg 4 105] != 0)%R.
Proof.
Admitted.

(* 4c. All chain entries evaluate to nonzero at the Cauchy bound
   after lifting to realalg. *)
Lemma chain_cb_nz :
  forall q, List.In q (BrownTraub.sturm_chain charpoly_int) ->
    ((pol_to_polyralg q).[
       cauchy_bound (pol_to_polyralg charpoly_int)] != 0)%R.
Proof.
Admitted.

(* 4d. The threshold 4/105 is below the Cauchy bound. The Cauchy
   bound of the degree-42 polynomial with huge coefficients is
   vastly larger than 4/105 ~ 0.038. *)
Lemma threshold_lt_cb :
  (threshold_ralg 4 105
     < cauchy_bound (pol_to_polyralg charpoly_int))%R.
Proof.
Admitted.

(* 4e. The lifted Sturm chain equals the abstract mods chain.
   This is mods_int_morph applied to (charpoly_int, pderiv charpoly_int),
   combined with pderiv_morph. *)
Lemma chain_is_mods :
  List.map pol_to_polyralg (BrownTraub.sturm_chain charpoly_int)
  = mods (pol_to_polyralg charpoly_int)
         ((pol_to_polyralg charpoly_int)^`()).
Proof.
Admitted.

(* 4f. No chain polynomial has a root weakly above the Cauchy bound.
   Follows from the Cauchy bound dominating all roots. *)
Lemma no_root_at_cb :
  forall r : {poly realalg},
    r \in mods (pol_to_polyralg charpoly_int)
               ((pol_to_polyralg charpoly_int)^`()) ->
    {in `[cauchy_bound (pol_to_polyralg charpoly_int), +oo[,
       forall y : realalg, ~~ root r y}.
Proof.
Admitted.

(* ================================================================== *)
(*  Section 5: The headline L1 lemma.                                   *)
(*                                                                      *)
(*  Wire `sturm_count_above_pos_concrete` with all the above to get    *)
(*  the existence of a realalg root of charpoly_int above 4/105.        *)
(*                                                                      *)
(*  Proven facts used: den_pos, chain_nz,                               *)
(*                     sturm_count_above_charpoly_pos.                  *)
(*  Admitted facts used: chain_lc_nz, chain_th_nz, chain_cb_nz,        *)
(*                       threshold_lt_cb, chain_is_mods, no_root_at_cb, *)
(*                       signs_at_x0_agree, signs_at_inf_agree.         *)
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
