(* ================================================================== *)
(*  theories/S1/Bridge.v                                                *)
(*                                                                      *)
(*  L1 / Sturm-bridge scaffolding.                                      *)
(*                                                                      *)
(*  This file bridges the concrete `list Z` Sturm machinery             *)
(*  (IntPoly.v / BrownTraub.v / SignChain.v) to the abstract            *)
(*  mathcomp-real-closed Sturm machinery (`mods`, `changes_horner`,     *)
(*  `rootsR`, `taq_taq_itv`) over `realalg`.                            *)
(*                                                                      *)
(*  The intended consumer is Cert.v's L1 admit `sturm_count_correct`.   *)
(*  We do NOT touch Cert.v here: a later sprint will rewire it to use   *)
(*  the stronger `sturm_count_above_pos` lemma proved below.            *)
(*                                                                      *)
(*  Structure:                                                          *)
(*    - Z_to_int             : stdlib Z -> mathcomp int helper.          *)
(*    - pol_to_polyralg      : lift of `pol = list Z` to                 *)
(*                             `{poly realalg}`, going through           *)
(*                             `pol_to_polyrat` from CharPoly.v.         *)
(*    - mods_int_morph       : [Admitted] `mods_int` agrees with         *)
(*                             abstract `mods` after lifting.            *)
(*    - variation_at_rat_morph                                           *)
(*                           : [Admitted] `variation_at_rat` agrees      *)
(*                             with abstract `changes_horner`.           *)
(*    - sturm_count_above_correct                                        *)
(*                           : [Admitted] our Sturm count equals the     *)
(*                             number of real roots above the threshold. *)
(*    - sturm_count_above_pos                                            *)
(*                           : [Proved modulo the above] a positive      *)
(*                             Sturm count yields an explicit realalg    *)
(*                             root above the threshold.                 *)
(* ================================================================== *)

From Stdlib Require Import ZArith List Lia.
Import ListNotations.

From mathcomp Require Import all_boot all_algebra.
From mathcomp.real_closed Require Import polyrcf qe_rcf_th realalg.
Import GRing.Theory Num.Theory.

From PrimeGapS1 Require Import IntPoly BrownTraub SignChain CharPoly.

Local Open Scope ring_scope.

(* `Z_to_int` is now exported from CharPoly.v; we re-use it directly. *)

(* ------------------------------------------------------------------ *)
(*  Lifting `pol = list Z` to `{poly realalg}`.                        *)
(*                                                                     *)
(*  We factor the lift through `pol_to_polyrat` (from CharPoly.v) so   *)
(*  that any future proof that pins down the behaviour of              *)
(*  `pol_to_polyrat` automatically lifts to `pol_to_polyralg`.         *)
(* ------------------------------------------------------------------ *)

Definition pol_to_polyralg (p : pol) : {poly realalg} :=
  map_poly (ratr : rat -> realalg) (pol_to_polyrat p).

(* The rational threshold `num/den` lifted to realalg. *)
Definition threshold_ralg (num den : Z) : realalg :=
  ((Z_to_int num)%:~R / (Z_to_int den)%:~R)%R.

(* ================================================================== *)
(*  L1 — the mods morphism.                                             *)
(*                                                                      *)
(*  Our `mods_int p q : list pol` from BrownTraub.v should agree with   *)
(*  the abstract `mods (lift p) (lift q) : seq {poly realalg}` from     *)
(*  qe_rcf_th.v.                                                        *)
(*                                                                      *)
(*  Proof sketch (future work):                                         *)
(*    1. Unfold `mods_int_loop` by induction on the fuel.               *)
(*    2. The base case is `p = 0` or `q = 0`; both sides are `[::]`.    *)
(*    3. The step case uses `mods_rec` and requires                     *)
(*       `next_mod_morph` : `pol_to_polyralg (next_mod p q)`            *)
(*                         = `next_mod (lift p) (lift q)`, which in     *)
(*       turn reduces to a compatibility of `prem` with `rmodp`.        *)
(*       This is the "scaling-by-lc^k then sign flip" calculation       *)
(*       and is the hardest piece.                                      *)
(* ================================================================== *)

Lemma mods_int_morph (p q : pol) :
  List.map pol_to_polyralg (mods_int p q)
  = mods (pol_to_polyralg p) (pol_to_polyralg q).
Proof.
Admitted.

(* ================================================================== *)
(*  L1 — the variation-count morphism.                                  *)
(*                                                                      *)
(*  Our `variation_at_rat c num den` (a `nat`) should agree with        *)
(*  `changes_horner (map lift c) (threshold_ralg num den)` (also a      *)
(*  `nat`) from qe_rcf_th.v — under the hypothesis that no chain entry  *)
(*  is the zero polynomial (which is always the case for the Brown-Traub
    Sturm chain: the recursion stops as soon as the degree drops to 0). *)
(*                                                                      *)
(*  Counter-example without the hypothesis: c = [[1]; []; [-1]].        *)
(*    variation_at_pinf c        = variation [1; 0; -1] = 1             *)
(*                                  (our `variation` skips the middle 0)*)
(*    changes_pinfty (lift c)    = changes [1; 0; -1] = 0               *)
(*                                  (mathcomp's `changes` does NOT skip)*)
(*                                                                      *)
(*  Strategy: show that on lists of nonzero entries (with parallel      *)
(*  sign information) both counts coincide with "count of adjacent      *)
(*  pairs whose product is negative", and then bridge the two sides     *)
(*  through a sign-matching assumption between `sgn_Z` and `sgz` of     *)
(*  the realalg leading coefficients / Horner evaluations.              *)
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
(* Helper: the core "no-zero" equivalence between our Z-valued         *)
(* `variation` and mathcomp's R-valued `changes`, stated on two        *)
(* parallel lists whose signs agree pointwise.                         *)
(*                                                                     *)
(* We work in `realDomainType` because mathcomp's `sgzM` (sign of a    *)
(* product) is only stated there; `realalg` is a realDomainType.       *)
(* ------------------------------------------------------------------ *)

Section VariationChangesBridge.

Variable R : rcfType.

(* Joint-sign predicate: `n` is nonzero in Z, `r` is nonzero in R,
   and they have the same sign. We phrase it via comparisons with 0,
   which are directly useful in the `variation` / `changes` fixpoints. *)
Definition sgn_matches (n : Z) (r : R) : Prop :=
  ((BinInt.Z.eq n BinInt.Z0) <-> (r = 0))
  /\ (BinInt.Z.lt n BinInt.Z0 <-> (r < 0)%R)
  /\ (BinInt.Z.lt BinInt.Z0 n <-> (0 < r)%R).

Lemma sgn_matches_Rnz n r : sgn_matches n r -> n <> BinInt.Z0 -> (r != 0)%R.
Proof. by case=> [H1 _] Hn; apply/eqP => Hr; apply: Hn; apply/H1. Qed.

Lemma sgn_matches_Znz n r : sgn_matches n r -> (r != 0)%R -> n <> BinInt.Z0.
Proof. by case=> [H1 _] /eqP Hr Hn; apply: Hr; apply/H1. Qed.

(* Two nonzero Z values have negative product iff their matched R
   counterparts do. *)
Lemma sgn_matches_prod (n1 n2 : Z) (r1 r2 : R) :
  sgn_matches n1 r1 -> n1 <> BinInt.Z0 ->
  sgn_matches n2 r2 -> n2 <> BinInt.Z0 ->
  BinInt.Z.ltb (BinInt.Z.mul n1 n2) BinInt.Z0 = (r1 * r2 < 0)%R.
Proof.
move=> H1 Hn1 H2 Hn2.
have Hnr1 : (r1 != 0)%R := sgn_matches_Rnz _ _ H1 Hn1.
have Hnr2 : (r2 != 0)%R := sgn_matches_Rnz _ _ H2 Hn2.
case: H1 => [_ [Hlt1 Hgt1]].
case: H2 => [_ [Hlt2 Hgt2]].
(* Split r1 into >0 or <0, similarly r2, via total order. *)
have Hr1 : ((0 < r1)%R \/ (r1 < 0)%R).
{ have : (0 : R) != r1 by rewrite eq_sym.
  by move/order.Order.TotalTheory.lt_total/orP; case=> H; [left|right]. }
have Hr2 : ((0 < r2)%R \/ (r2 < 0)%R).
{ have : (0 : R) != r2 by rewrite eq_sym.
  by move/order.Order.TotalTheory.lt_total/orP; case=> H; [left|right]. }
case: Hr1 => Hr1c; case: Hr2 => Hr2c.
- have Hn1pos : BinInt.Z.lt BinInt.Z0 n1 by apply/Hgt1.
  have Hn2pos : BinInt.Z.lt BinInt.Z0 n2 by apply/Hgt2.
  have Hpos : (0 < r1 * r2)%R by rewrite pmulr_rgt0.
  rewrite (order.Order.POrderTheory.lt_gtF Hpos).
  by apply/negP => /Z.ltb_lt; nia.
- have Hn1pos : BinInt.Z.lt BinInt.Z0 n1 by apply/Hgt1.
  have Hn2neg : BinInt.Z.lt n2 BinInt.Z0 by apply/Hlt2.
  have Hneg : (r1 * r2 < 0)%R by rewrite pmulr_rlt0.
  rewrite Hneg; apply/Z.ltb_lt; nia.
- have Hn1neg : BinInt.Z.lt n1 BinInt.Z0 by apply/Hlt1.
  have Hn2pos : BinInt.Z.lt BinInt.Z0 n2 by apply/Hgt2.
  have Hneg : (r1 * r2 < 0)%R by rewrite nmulr_rlt0.
  rewrite Hneg; apply/Z.ltb_lt; nia.
- have Hn1neg : BinInt.Z.lt n1 BinInt.Z0 by apply/Hlt1.
  have Hn2neg : BinInt.Z.lt n2 BinInt.Z0 by apply/Hlt2.
  have Hpos : (0 < r1 * r2)%R by rewrite nmulr_rgt0.
  rewrite (order.Order.POrderTheory.lt_gtF Hpos).
  by apply/negP => /Z.ltb_lt; nia.
Qed.

(* Parallel nonzero-list hypothesis for two lists of the same length. *)
Fixpoint sgn_matches_seq (sZ : list Z) (sR : seq R) : Prop :=
  match sZ, sR with
  | nil, nil => True
  | n :: sZ', r :: sR' => sgn_matches n r /\ sgn_matches_seq sZ' sR'
  | _, _ => False
  end.

Definition all_nonzero_Z (sZ : list Z) : Prop :=
  forall n, List.In n sZ -> n <> BinInt.Z0.

(* Core identity: with a sign-matching "previous" element [y / yR] that is
   nonzero, the one-step [variation_aux] matches mathcomp's [changes] on
   the combined list. *)
Lemma variation_aux_changes_nonzero
  (y : Z) (yR : R) (Hym : sgn_matches y yR) (Hy : y <> BinInt.Z0)
  (sZ : list Z) (sR : seq R)
  (Hnz : all_nonzero_Z sZ) (Hs : sgn_matches_seq sZ sR) :
  variation_aux (Some y) sZ = changes (yR :: sR).
Proof.
elim: sZ sR y yR Hym Hy Hnz Hs => [|x sZ' IH].
  move=> [|r sR'] y yR Hym Hy Hnz Hs /=.
  - by rewrite mulr0 preorder.Order.PreorderTheory.ltxx.
  - by case: Hs.
move=> [|r sR'] y yR Hym Hy Hnz Hs /=.
  by case: Hs.
case: Hs => Hxm Hs'.
  have Hx : x <> BinInt.Z0 by apply: Hnz; left.
  have Hxr : (r != 0)%R := sgn_matches_Rnz _ _ Hxm Hx.
  have Hxeq : BinInt.Z.eqb x BinInt.Z0 = false
    by apply/Z.eqb_neq.
  have Hyxeq : BinInt.Z.eqb (BinInt.Z.mul x y) BinInt.Z0 = false.
  { apply/Z.eqb_neq => Hprod.
    case/Z.mul_eq_0: Hprod => [Hx0|Hy0]; [exact: Hx|exact: Hy]. }
  rewrite /= Hxeq Hyxeq.
  rewrite (sgn_matches_prod x y r yR Hxm Hx Hym Hy).
  have Hnz' : all_nonzero_Z sZ'.
  { by move=> z Hz; apply: Hnz; right. }
  (* We want: [if r * yR < 0 then 1 else 0] + variation_aux (Some x) sZ'
     = [if yR * r < 0 then 1 else 0] + changes (r :: sR'). *)
  rewrite (IH sR' x r Hxm Hx Hnz' Hs').
  rewrite /= mulrC.
  by case: (yR * r < 0)%R.
Qed.

(* Initial form: variation on a nonzero list equals changes on the matched R list. *)
Lemma variation_changes_nonzero (sZ : list Z) (sR : seq R) :
  all_nonzero_Z sZ -> sgn_matches_seq sZ sR ->
  variation sZ = changes sR.
Proof.
case: sZ sR => [|x sZ'] [|r sR'] /=.
- done.
- by move=> _ [].
- by move=> _ [].
move=> Hnz [Hxm Hs'].
have Hx : x <> BinInt.Z0 by apply: Hnz; left.
have Hxr : (r != 0)%R := sgn_matches_Rnz _ _ Hxm Hx.
have Hxeq : BinInt.Z.eqb x BinInt.Z0 = false by apply/Z.eqb_neq.
rewrite /variation /= Hxeq /=.
have Hnz' : all_nonzero_Z sZ' by move=> z Hz; apply: Hnz; right.
exact: (variation_aux_changes_nonzero x r Hxm Hx sZ' sR' Hnz' Hs').
Qed.

End VariationChangesBridge.

(* ------------------------------------------------------------------ *)
(*  Sub-bridge helpers: "sign of `plead p` matches `sgz (lead_coef ...)`"*)
(*  and the analogous statement for Horner evaluation at a rational.    *)
(*                                                                     *)
(*  Both facts follow mechanically from `pol_to_polyrat`'s structural  *)
(*  definition and the injectivity of `ratr : rat -> realalg`.          *)
(* ------------------------------------------------------------------ *)

(* Structural cons-lemma for the rat-lifted polynomial. *)
Lemma pol_to_polyrat_cons (x : Z) (p : pol) :
  pol_to_polyrat (x :: p)
  = cons_poly ((Z_to_int x)%:~R : rat) (pol_to_polyrat p).
Proof. by []. Qed.

Lemma pol_to_polyrat_nil :
  pol_to_polyrat nil = 0 :> {poly rat}.
Proof. by []. Qed.

(* Cons-lemma for the realalg-lifted polynomial: goes through
   `map_poly` + `cons_poly_def`. *)
Lemma pol_to_polyralg_cons (x : Z) (p : pol) :
  pol_to_polyralg (x :: p)
  = pol_to_polyralg p * 'X + ((Z_to_int x)%:~R : realalg)%:P.
Proof.
rewrite /pol_to_polyralg pol_to_polyrat_cons cons_poly_def.
rewrite rmorphD rmorphM /= map_polyX map_polyC /=.
by rewrite ratr_int.
Qed.

Lemma pol_to_polyralg_nil :
  pol_to_polyralg nil = 0 :> {poly realalg}.
Proof. by rewrite /pol_to_polyralg pol_to_polyrat_nil rmorph0. Qed.

(* ------------------------------------------------------------------ *)
(*  Structural lemma used by the four helpers below.                    *)
(*                                                                      *)
(*  This is a small, local structural fact about `pol_to_polyralg` that *)
(*  connects the `{poly realalg}` leading coefficient with the integer  *)
(*  `plead` function.  It is the *only* remaining admit inside Bridge.v *)
(*  used by the four target helpers.                                    *)
(*                                                                      *)
(*  The proof goes by induction on `p`, with a case split on            *)
(*  `pol_to_polyralg rest = 0`.  The "structural" step (that all zero   *)
(*  entries yield the zero polynomial and vice versa) is the source of  *)
(*  the length — it is left for follow-up work since Bridge.v is not    *)
(*  imported by Cert.v, so this does NOT affect                         *)
(*  `Cert.maynard_eigenvalue_S1`'s axiom count.                         *)
(* ------------------------------------------------------------------ *)

Lemma lead_coef_pol_to_polyralg (p : pol) :
  lead_coef (pol_to_polyralg p)
  = ((Z_to_int (plead p))%:~R : realalg).
Proof. Admitted.

(* Symbolic sign-matching for a realalg element that comes from an int.
   We split on `n` into its three Z constructors and dispatch each sub-case
   by reducing to integer-to-real ordering lemmas `ltr0z` / `ltrz0`. *)
Lemma sgn_matches_int (n : Z) :
  sgn_matches realalg (sgn_Z n) ((Z_to_int n)%:~R : realalg).
Proof.
rewrite /sgn_matches /sgn_Z.
have Hpos_pos : forall q : positive, ((Z_to_int (Z.pos q))%:~R : realalg) > 0.
{ by move=> q; rewrite ltr0z /Z_to_int; apply/ltP/Pos2Nat.is_pos. }
have Hneg_neg : forall q : positive, ((Z_to_int (Z.neg q))%:~R : realalg) < 0.
{ by move=> q; rewrite ltrz0 /Z_to_int; case: (Pos.to_nat _). }
case: n => [|q|q] /=.
- split; last split.
  + split; first by []. by move=> _.
  + split; first by []. by rewrite order.Order.POrderTheory.ltxx.
  + split; first by []. by rewrite order.Order.POrderTheory.ltxx.
- split; last split.
  + split; first by [].
    move=> H; have := Hpos_pos q; by rewrite H order.Order.POrderTheory.ltxx.
  + split; first by [].
    move=> H; have := Hpos_pos q; by rewrite order.Order.POrderTheory.lt_gtF.
  + split; first by move=> _; exact: Hpos_pos.
    by [].
- split; last split.
  + split; first by [].
    move=> H; have := Hneg_neg q; by rewrite H order.Order.POrderTheory.ltxx.
  + split; first by move=> _; exact: Hneg_neg.
    by [].
  + split; first by [].
    move=> H; have := Hneg_neg q; by rewrite order.Order.POrderTheory.lt_gtF.
Qed.

(* Unconditional sign-matching for the leading coefficient. *)
Lemma sign_at_pinf_matches (p : pol) :
  sgn_matches _ (sign_at_pinf p) (lead_coef (pol_to_polyralg p)).
Proof.
rewrite /sign_at_pinf lead_coef_pol_to_polyralg.
exact: sgn_matches_int.
Qed.

Lemma sign_at_pinf_nz (p : pol) :
  (lead_coef (pol_to_polyralg p) != 0)%R -> sign_at_pinf p <> BinInt.Z0.
Proof.
move=> Hnz.
exact: (sgn_matches_Znz _ _ _ (sign_at_pinf_matches p) Hnz).
Qed.

(* Structural lemma: the realalg horner evaluation of the lifted polynomial
   at the lifted rational `num/den` has the same sign as the integer
   `peval_at_rat p num den`, provided `den > 0`.

   Proof sketch: `(pol_to_polyralg p).[num/den] = (peval_at_rat p num den)%:~R
   / (den^length p)%:~R`, where the numerator comes from the definition of
   `peval_at_rat_aux` which returns `den^d * p(num/den)`.  Since `den > 0`,
   the denominator is strictly positive and sign-invariant.

   This structural step is left for follow-up work — see the comment on
   `lead_coef_pol_to_polyralg` above. *)
Lemma horner_pol_to_polyralg_rat (p : pol) (num den : Z) :
  BinInt.Z.lt BinInt.Z0 den ->
  sgn_matches _ (peval_at_rat p num den)
    ((pol_to_polyralg p).[threshold_ralg num den]).
Proof. Admitted.

Lemma sign_at_rat_matches (p : pol) (num den : Z) :
  BinInt.Z.lt BinInt.Z0 den ->
  sgn_matches _ (sign_at_rat p num den)
    ((pol_to_polyralg p).[threshold_ralg num den]).
Proof.
move=> Hden.
have Hm := horner_pol_to_polyralg_rat p num den Hden.
rewrite /sign_at_rat /sgn_matches /sgn_Z.
case: Hm => [Hz [Hl Hg]]; split; last split.
- split.
  + case En : (peval_at_rat p num den) => [||q] // _.
    by apply/Hz.
  + move=> Heq. move/Hz in Heq. by rewrite Heq.
- split.
  + case En : (peval_at_rat p num den) => [||q] //= _.
    apply/Hl; rewrite En. by lia.
  + move=> Hr. move/Hl in Hr. case En : (peval_at_rat p num den) Hr => //=; lia.
- split.
  + case En : (peval_at_rat p num den) => [||q] //= _.
    apply/Hg; rewrite En. by lia.
  + move=> Hr. move/Hg in Hr. case En : (peval_at_rat p num den) Hr => //=; lia.
Qed.

Lemma sign_at_rat_nz (p : pol) (num den : Z) :
  BinInt.Z.lt BinInt.Z0 den ->
  ((pol_to_polyralg p).[threshold_ralg num den] != 0)%R ->
  sign_at_rat p num den <> BinInt.Z0.
Proof.
move=> Hd Hnz.
exact: (sgn_matches_Znz _ _ _ (sign_at_rat_matches p num den Hd) Hnz).
Qed.

(* ------------------------------------------------------------------ *)
(*  The two morphism lemmas, stated with a "no zero entries" guard.    *)
(*  Under that hypothesis our `variation` (which skips zeros) and      *)
(*  mathcomp's `changes` (which does not) agree, so the original       *)
(*  false equality becomes true.                                       *)
(* ------------------------------------------------------------------ *)

Lemma variation_at_pinf_morph (c : list pol)
  (Hnz : forall p, List.In p c ->
                   (lead_coef (pol_to_polyralg p) != 0)%R) :
  variation_at_pinf c = changes_pinfty (List.map pol_to_polyralg c).
Proof.
rewrite /variation_at_pinf /changes_pinfty.
(* Apply the generic bridge with the parallel sign-matching.
   Both sides are parallel maps over the same list `c`. *)
apply: (variation_changes_nonzero realalg
         (List.map sign_at_pinf c)
         (List.map lead_coef (List.map pol_to_polyralg c))).
- (* every entry of `map sign_at_pinf c` is nonzero *)
  move=> z /in_map_iff [p [<- Hpin]].
  exact: (sign_at_pinf_nz p (Hnz p Hpin)).
- (* sgn_matches holds pointwise across the two maps *)
  elim: c Hnz => [|p c' IH] Hnz //=.
  split.
  + exact: (sign_at_pinf_matches p).
  + apply: IH => q Hq; apply: Hnz; right; exact: Hq.
Qed.

Lemma variation_at_rat_morph
  (c : list pol) (num den : Z) (Hden : BinInt.Z.lt BinInt.Z0 den)
  (Hnz : forall p, List.In p c ->
                   ((pol_to_polyralg p).[threshold_ralg num den] != 0)%R) :
  variation_at_rat c num den
  = changes_horner (List.map pol_to_polyralg c) (threshold_ralg num den).
Proof.
rewrite /variation_at_rat /changes_horner.
apply: (variation_changes_nonzero realalg
         (List.map (fun p => sign_at_rat p num den) c)
         (List.map (fun p : {poly realalg} => p.[threshold_ralg num den])
                   (List.map pol_to_polyralg c))).
- move=> z /in_map_iff [p [<- Hpin]].
  exact: (sign_at_rat_nz p num den Hden (Hnz p Hpin)).
- elim: c Hnz => [|p c' IH] Hnz //=.
  split.
  + exact: (sign_at_rat_matches p num den Hden).
  + apply: IH => q Hq; apply: Hnz; right; exact: Hq.
Qed.

(* ================================================================== *)
(*  L1 — the main bridge.                                               *)
(*                                                                      *)
(*  `sturm_count_above (sturm_chain p) num den` equals the number of    *)
(*  real roots of the lifted polynomial strictly above the lifted       *)
(*  threshold.                                                          *)
(*                                                                      *)
(*  Proof sketch (future work):                                         *)
(*    1. Unfold `sturm_count_above` and `sturm_chain`.                  *)
(*    2. Rewrite both `variation_at_rat` and `variation_at_pinf`        *)
(*       using `variation_at_rat_morph` and `variation_at_pinf_morph`.  *)
(*    3. Rewrite `mods_int` by `mods_int_morph`.                        *)
(*    4. Use `taq_taq_itv` with `a := threshold`, `b := cauchy_bound`,  *)
(*       `q := 1`. This identifies the Sturm count with                 *)
(*       `taq (roots p a b) 1 = size (roots p a b)`.                    *)
(*    5. Observe `roots p (threshold) (+cauchy_bound)` equals           *)
(*       `filter (fun r => threshold < r) (rootsR p)` since any real    *)
(*       root lies within the Cauchy bound.                             *)
(*                                                                      *)
(*  Note: the correct statement of step (5) may require                 *)
(*  `half_open` vs `open` conventions; we use `strictly above` for      *)
(*  simplicity. The Cert.v consumer only asks for `<`, not `≤`.         *)
(* ================================================================== *)

(* NOTE (2026-04-09): the hypothesis `Hchain_nz` propagates the
   "no zero entries in the Sturm chain" invariant from the morphism
   lemmas above.  It is a semantically-trivial property of
   `BrownTraub.sturm_chain p` (the chain terminates when the degree
   drops to 0, so no chain entry is the zero polynomial); closing it
   structurally is a follow-up. *)
Lemma sturm_count_above_correct
  (p : pol) (num den : Z) (Hd : BinInt.Z.lt BinInt.Z0 den)
  (Hchain_nz : forall q, List.In q (sturm_chain p) -> q <> nil) :
  sturm_count_above (sturm_chain p) num den
  = size (List.filter
            (fun r : realalg => (threshold_ralg num den < r)%R)
            (rootsR (pol_to_polyralg p))).
Proof.
Admitted.

(* ================================================================== *)
(*  L1 consumer — existential form, suitable for Cert.v.                *)
(*                                                                      *)
(*  A strictly positive computational Sturm count yields the            *)
(*  existential of a realalg root above the threshold, which is what    *)
(*  Cert.v's `sturm_count_correct` actually needs.                      *)
(*                                                                      *)
(*  This lemma is proved outright (conditional on                       *)
(*  `sturm_count_above_correct`) — it is ~10 lines of list manipulation *)
(*  plus the standard "nonempty filter has a head" argument.            *)
(* ================================================================== *)

(* Helper: any element of a List.filter satisfies the predicate and
   is a member of the original list. We re-prove this rather than
   depend on List.filter_In's exact interface under MathComp's seq. *)
Lemma in_list_filter_inv {A : Type} (f : A -> bool) (l : list A) (x : A) :
  List.In x (List.filter f l) -> f x = true /\ List.In x l.
Proof.
elim: l => [//|a tl IH] /=.
case Ea : (f a) => /=.
- case => [<- | Htl].
  + by split; [exact: Ea | left].
  + by case: (IH Htl) => Hf Hin; split; [exact: Hf | right].
- move=> Htl. by case: (IH Htl) => Hf Hin; split; [exact: Hf | right].
Qed.

(* Helper: a realalg value in `rootsR p` (as a List.In) is a root of p.
   The clean version would be `rootsRP` + `roots_on_rootsR` but that
   requires `p != 0`; we keep this as a local Admitted side-lemma. *)
Lemma rootsR_in_root (P : {poly realalg}) (r : realalg) :
  List.In r (rootsR P) -> root P r.
Proof.
move=> Hin.
have HP : P != 0.
{ apply/eqP => HP0; rewrite HP0 rootsR0 /= in Hin; exact: Hin. }
have Hmem : r \in rootsR P.
{ elim: (rootsR P) Hin => [//|a tl IH] /=.
  case=> [<-|Htl]; first by rewrite inE eqxx.
  by rewrite inE (IH Htl) orbT. }
exact: (roots_on_root (roots_on_rootsR HP) Hmem).
Qed.

(* Same chain-nonzero caveat as `sturm_count_above_correct`: the
   caller must discharge `Hchain_nz` before invoking this lemma. *)
Lemma sturm_count_above_pos
  (p : pol) (num den : Z) (Hd : BinInt.Z.lt BinInt.Z0 den)
  (Hchain_nz : forall q, List.In q (sturm_chain p) -> q <> nil) :
  (0 < sturm_count_above (sturm_chain p) num den)%nat ->
  exists r : realalg,
    root (pol_to_polyralg p) r /\ (threshold_ralg num den < r)%R.
Proof.
move=> Hgt.
have Hsize :
  (0 < size (List.filter
               (fun r : realalg => (threshold_ralg num den < r)%R)
               (rootsR (pol_to_polyralg p))))%nat.
{ by rewrite -(sturm_count_above_correct p num den Hd Hchain_nz). }
(* Extract a head element from the nonempty filtered list. *)
case EL : (List.filter
             (fun r : realalg => (threshold_ralg num den < r)%R)
             (rootsR (pol_to_polyralg p))) Hsize => [//|r rest] _.
exists r.
have Hin : List.In r (List.filter
                        (fun r : realalg => (threshold_ralg num den < r)%R)
                        (rootsR (pol_to_polyralg p))).
{ by rewrite EL; left. }
case: (in_list_filter_inv _ _ _ Hin) => Hlt Hin2.
split; last exact: Hlt.
by apply: rootsR_in_root.
Qed.
