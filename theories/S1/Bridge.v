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

(* Auxiliary: Z -> realalg lifts nonzero integers to nonzero realalg. *)
Lemma Z_to_int_realalg_nz (x : Z) :
  x <> BinInt.Z0 -> ((Z_to_int x)%:~R : realalg) != 0.
Proof.
move=> Hx.
have Hsgn : sgn_Z x <> BinInt.Z0 by rewrite /sgn_Z; case: x Hx.
have Hs : sgn_matches realalg (sgn_Z x) ((Z_to_int x)%:~R : realalg)
  := sgn_matches_int x.
exact: (sgn_matches_Rnz _ _ _ Hs Hsgn).
Qed.

(* Strengthened induction: `plead_aux p acc`, lifted through `Z_to_int`,
   agrees with `lead_coef (pol_to_polyralg p)` when `pol_to_polyralg p`
   is nonzero, and with `(Z_to_int acc)%:~R` otherwise. *)
Lemma lead_coef_pol_to_polyralg_aux (p : pol) (acc : Z) :
  ((Z_to_int (plead_aux p acc))%:~R : realalg) =
  (if pol_to_polyralg p == 0 then ((Z_to_int acc)%:~R : realalg)
   else lead_coef (pol_to_polyralg p)).
Proof.
elim: p acc => [|x p IH] acc.
  by rewrite /= pol_to_polyralg_nil eqxx.
rewrite pol_to_polyralg_cons.
set p' := pol_to_polyralg p in IH *.
set c : realalg := ((Z_to_int x)%:~R)%R.
have Hstep : plead_aux (x :: p) acc =
             plead_aux p (if BinInt.Z.eqb x BinInt.Z0 then acc else x).
{ by simpl; case: (BinInt.Z.eqb x BinInt.Z0). }
rewrite Hstep.
case Hp' : (p' == 0).
- (* p' = 0: sum reduces to c%:P *)
  move/eqP: Hp' => Hp'.
  rewrite Hp' mul0r add0r.
  case Hx : (BinInt.Z.eqb x BinInt.Z0).
  + have Hxz : x = BinInt.Z0 by apply/Z.eqb_eq.
    have Hc0 : c = 0 by rewrite /c Hxz /Z_to_int /=; exact: mulr0n.
    rewrite Hc0 polyC0 eqxx.
    by rewrite IH Hp' eqxx.
  + have Hxnz : x <> BinInt.Z0 by move/Z.eqb_neq: Hx.
    have Hcnz : c != 0 := Z_to_int_realalg_nz x Hxnz.
    have Hcpnz : c%:P != 0 by rewrite polyC_eq0.
    rewrite (negbTE Hcpnz).
    rewrite lead_coefC.
    by rewrite IH Hp' eqxx.
- (* p' != 0: lead_coef comes from the 'X part *)
  move/negbT: Hp' => Hp'.
  have Hszp : (0 < size p')%N by rewrite lt0n size_poly_eq0.
  have HsMX : size (p' * 'X) = (size p').+1 by apply: size_mulX.
  have Hsz : size (p' * 'X + c%:P) = (size p').+1.
  { rewrite size_MXaddC (negbTE Hp') /=. by []. }
  have Hsum_nz : p' * 'X + c%:P != 0.
  { apply/eqP => H; have : size (p' * 'X + c%:P) = 0%N by rewrite H size_poly0.
    by rewrite Hsz. }
  rewrite (negbTE Hsum_nz).
  have Hsize_lt : (size (c%:P : {poly realalg}) < size ((p' * 'X)%R : {poly realalg}))%N.
  { rewrite HsMX ltnS.
    exact: (leq_trans (size_polyC_leq1 _) Hszp). }
  rewrite lead_coefDl // lead_coefMX.
  rewrite IH (negbTE Hp').
  by case: (BinInt.Z.eqb x BinInt.Z0).
Qed.

Lemma lead_coef_pol_to_polyralg (p : pol) :
  lead_coef (pol_to_polyralg p)
  = ((Z_to_int (plead p))%:~R : realalg).
Proof.
rewrite /plead.
have := lead_coef_pol_to_polyralg_aux p BinInt.Z0.
case Hp : (pol_to_polyralg p == 0).
- move/eqP: Hp => Hp0.
  rewrite Hp0 lead_coef0.
  have -> : ((Z_to_int BinInt.Z0)%:~R : realalg) = 0
    by rewrite /Z_to_int /=; exact: mulr0n.
  by move=> ->.
- by move=> ->.
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

(* ------------------------------------------------------------------ *)
(*  Bridge `Z_to_int` is a ring homomorphism (enough for our uses).    *)
(* ------------------------------------------------------------------ *)

Lemma Z_to_int_case (z : Z) :
  z = BinInt.Z0 \/
  (exists n : nat, (0 < n)%N /\ z = BinInt.Z.of_nat n /\ Z_to_int z = Posz n) \/
  (exists n : nat, (0 < n)%N /\ z = BinInt.Z.opp (BinInt.Z.of_nat n)
                   /\ Z_to_int z = (- Posz n)%R).
Proof.
case: z => [|p|p]; [by left|right; left|right; right].
- exists (Pos.to_nat p); split; [exact/ltP/Pos2Nat.is_pos|].
  split; [by rewrite positive_nat_Z|by []].
- exists (Pos.to_nat p); split; [exact/ltP/Pos2Nat.is_pos|].
  split; [by rewrite positive_nat_Z|].
  rewrite /Z_to_int /= NegzE.
  have Hp := Pos2Nat.is_pos p.
  case Hn : (Pos.to_nat p) => [|n]; first by lia.
  by rewrite subn1 /=.
Qed.

Lemma Z_to_int_of_nat (n : nat) :
  Z_to_int (BinInt.Z.of_nat n) = Posz n.
Proof. case: n => [//|n]; by rewrite /Z_to_int /= SuccNat2Pos.id_succ. Qed.

Lemma Z_to_int_opp_of_nat (n : nat) :
  Z_to_int (BinInt.Z.opp (BinInt.Z.of_nat n)) = (- Posz n)%R.
Proof.
case: n => [|n] /=; first by rewrite /Z_to_int /= oppr0.
rewrite /Z_to_int /= NegzE SuccNat2Pos.id_succ.
by rewrite subn1 /=.
Qed.

Lemma Z_to_int_mul (a b : Z) :
  Z_to_int (BinInt.Z.mul a b) = (Z_to_int a * Z_to_int b)%R.
Proof.
have [->|[[na [_ [-> ->]]]|[na [_ [-> ->]]]]] := Z_to_int_case a.
- by rewrite /= mul0r.
- have [->|[[nb [_ [-> ->]]]|[nb [_ [-> ->]]]]] := Z_to_int_case b.
  + by rewrite BinInt.Z.mul_0_r mulr0 /=.
  + by rewrite -Nat2Z.inj_mul Z_to_int_of_nat -PoszM.
  + rewrite BinInt.Z.mul_opp_r -Nat2Z.inj_mul Z_to_int_opp_of_nat.
    by rewrite mulrN -PoszM.
- have [->|[[nb [_ [-> ->]]]|[nb [_ [-> ->]]]]] := Z_to_int_case b.
  + by rewrite BinInt.Z.mul_0_r mulr0 /=.
  + rewrite BinInt.Z.mul_opp_l -Nat2Z.inj_mul Z_to_int_opp_of_nat.
    by rewrite mulNr -PoszM.
  + rewrite BinInt.Z.mul_opp_opp -Nat2Z.inj_mul Z_to_int_of_nat.
    by rewrite mulrNN -PoszM.
Qed.

Lemma nat_sub_Posz (n m : nat) :
  ((Posz n - Posz m)%R : int) =
  Z_to_int (BinInt.Z.sub (BinInt.Z.of_nat n) (BinInt.Z.of_nat m)).
Proof.
case Hcmp : (n <= m)%N.
- have -> : BinInt.Z.sub (BinInt.Z.of_nat n) (BinInt.Z.of_nat m)
          = BinInt.Z.opp (BinInt.Z.of_nat (m - n)).
  { rewrite Nat2Z.inj_sub; [lia|apply/leP; exact: Hcmp]. }
  rewrite Z_to_int_opp_of_nat.
  rewrite -(subzn Hcmp).
  by rewrite opprB.
- move/negbT: Hcmp; rewrite -ltnNge => Hlt.
  have Hle : (m <= n)%N := ltnW Hlt.
  have -> : BinInt.Z.sub (BinInt.Z.of_nat n) (BinInt.Z.of_nat m)
          = BinInt.Z.of_nat (n - m).
  { rewrite Nat2Z.inj_sub; [lia|apply/leP; exact: Hle]. }
  by rewrite Z_to_int_of_nat -(subzn Hle).
Qed.

Lemma Z_to_int_add (a b : Z) :
  Z_to_int (BinInt.Z.add a b) = (Z_to_int a + Z_to_int b)%R.
Proof.
have [->|[[na [_ [-> ->]]]|[na [_ [-> ->]]]]] := Z_to_int_case a.
- by rewrite BinInt.Z.add_0_l add0r.
- have [->|[[nb [_ [-> ->]]]|[nb [_ [-> ->]]]]] := Z_to_int_case b.
  + by rewrite BinInt.Z.add_0_r addr0 Z_to_int_of_nat.
  + by rewrite -Nat2Z.inj_add Z_to_int_of_nat -PoszD.
  + have -> : BinInt.Z.add (BinInt.Z.of_nat na) (BinInt.Z.opp (BinInt.Z.of_nat nb))
            = BinInt.Z.sub (BinInt.Z.of_nat na) (BinInt.Z.of_nat nb)
      by rewrite /BinInt.Z.sub.
    by rewrite -nat_sub_Posz.
- have [->|[[nb [_ [-> ->]]]|[nb [_ [-> ->]]]]] := Z_to_int_case b.
  + by rewrite BinInt.Z.add_0_r addr0 Z_to_int_opp_of_nat.
  + have -> : BinInt.Z.add (BinInt.Z.opp (BinInt.Z.of_nat na)) (BinInt.Z.of_nat nb)
            = BinInt.Z.sub (BinInt.Z.of_nat nb) (BinInt.Z.of_nat na)
      by rewrite /BinInt.Z.sub BinInt.Z.add_comm.
    by rewrite -nat_sub_Posz addrC.
  + rewrite -BinInt.Z.opp_add_distr -Nat2Z.inj_add Z_to_int_opp_of_nat.
    by rewrite -opprD PoszD.
Qed.

(* Lift to the realalg level. *)
Lemma Z_to_int_mul_ralg (a b : Z) :
  ((Z_to_int (BinInt.Z.mul a b))%:~R : realalg) =
  ((Z_to_int a)%:~R * (Z_to_int b)%:~R)%R.
Proof. by rewrite Z_to_int_mul intrM. Qed.

Lemma Z_to_int_add_ralg (a b : Z) :
  ((Z_to_int (BinInt.Z.add a b))%:~R : realalg) =
  ((Z_to_int a)%:~R + (Z_to_int b)%:~R)%R.
Proof. by rewrite Z_to_int_add intrD. Qed.

(* Auxiliary: positivity of `snd (peval_at_rat_aux p num den)` when `den > 0`. *)
Lemma peval_at_rat_aux_snd_pos (p : pol) (num den : Z) :
  BinInt.Z.lt BinInt.Z0 den ->
  BinInt.Z.lt BinInt.Z0 (snd (peval_at_rat_aux p num den)).
Proof.
Local Close Scope ring_scope.
move=> Hd.
elim: p => [//|a p IH] /=.
case Hp : (peval_at_rat_aux p num den) => [v dp].
rewrite Hp /= in IH. simpl. nia.
Qed.
Local Open Scope ring_scope.

(* Key identity over realalg: the realalg horner evaluation of the lifted
   polynomial at `num/den`, multiplied by the (lifted) denominator power,
   equals the (lifted) integer result of `peval_at_rat_aux`. *)
Lemma horner_pol_to_polyralg_aux_identity (p : pol) (num den : Z)
  (Hd : BinInt.Z.lt BinInt.Z0 den) :
  let (v, dp) := peval_at_rat_aux p num den in
  ((pol_to_polyralg p).[threshold_ralg num den] : realalg) *
     ((Z_to_int dp)%:~R : realalg) = ((Z_to_int v)%:~R : realalg).
Proof.
have Hden_ra_pos : ((Z_to_int den)%:~R : realalg) > 0.
{ have Hsgn : BinInt.Z.lt BinInt.Z0 (sgn_Z den)
    by rewrite /sgn_Z; case: den Hd => //.
  have Hds : sgn_matches realalg (sgn_Z den) ((Z_to_int den)%:~R : realalg)
    := sgn_matches_int den.
  by case: Hds => [_ [_ Hg]]; apply/Hg. }
have Hden_ra_nz : ((Z_to_int den)%:~R : realalg) != 0 by apply: lt0r_neq0.
elim: p => /=.
- rewrite pol_to_polyralg_nil horner0 mul0r /Z_to_int /=.
  symmetry; exact: mulr0z.
- move=> a p IH.
  case Hp : (peval_at_rat_aux p num den) => [v dp].
  rewrite Hp in IH.
  rewrite pol_to_polyralg_cons.
  rewrite hornerD hornerC hornerM hornerX.
  set t : realalg := threshold_ralg num den.
  set cr : realalg := ((Z_to_int a)%:~R)%R.
  set P : realalg := (pol_to_polyralg p).[t].
  set num_ra : realalg := ((Z_to_int num)%:~R)%R.
  set den_ra : realalg := ((Z_to_int den)%:~R)%R.
  set dp_ra : realalg := ((Z_to_int dp)%:~R)%R.
  (* t * den_ra = num_ra *)
  have Htden : (t * den_ra = num_ra)%R.
  { rewrite /t /threshold_ralg /num_ra /den_ra.
    by rewrite -mulrA mulVf // mulr1. }
  (* Key: reduce both sides to the same sum. *)
  rewrite Z_to_int_add_ralg !Z_to_int_mul_ralg.
  rewrite -/num_ra -/den_ra -/dp_ra -/cr.
  (* Goal: (P * t + cr) * (den_ra * dp_ra) = cr * (den_ra * dp_ra) + num_ra * (Z_to_int v)%:~R *)
  rewrite mulrDl addrC.
  congr (_ + _).
  (* (P * t) * (den_ra * dp_ra) = num_ra * (Z_to_int v)%:~R *)
  rewrite -(mulrA P t _) (mulrA t _ _) Htden.
  rewrite mulrA.
  (* (P * num_ra) * dp_ra = num_ra * (Z_to_int v)%:~R *)
  rewrite (mulrC P num_ra) -mulrA.
  by rewrite IH.
Qed.

(* Generic: sign-matching is preserved by multiplication by a positive
   realalg scalar. *)
Lemma sgn_matches_mul_pos_r (n : Z) (r s : realalg) :
  (0 < s)%R -> sgn_matches _ n (r * s) -> sgn_matches _ n r.
Proof.
move=> Hs [Hz [Hl Hg]].
have Hsnz : s != 0 by apply: lt0r_neq0.
have Hsinv : (0 < s^-1)%R by rewrite invr_gt0.
split; last split.
- split.
  + move=> Hnz.
    have : (r * s = 0)%R by apply/Hz.
    by move/eqP; rewrite mulf_eq0 (negbTE Hsnz) orbF => /eqP.
  + move=> Hr0; apply/Hz. rewrite Hr0 mul0r. by [].
- split.
  + move=> Hnl.
    have : (r * s < 0)%R by apply/Hl.
    by rewrite pmulr_llt0.
  + move=> Hrneg; apply/Hl.
    by rewrite pmulr_llt0.
- split.
  + move=> Hng.
    have : (0 < r * s)%R by apply/Hg.
    by rewrite pmulr_lgt0.
  + move=> Hrpos; apply/Hg.
    by rewrite pmulr_lgt0.
Qed.

(* Main: sign-matching of the integer peval and the realalg horner. *)
Lemma horner_pol_to_polyralg_rat (p : pol) (num den : Z) :
  BinInt.Z.lt BinInt.Z0 den ->
  sgn_matches _ (peval_at_rat p num den)
    ((pol_to_polyralg p).[threshold_ralg num den]).
Proof.
move=> Hd.
have Hid := horner_pol_to_polyralg_aux_identity p num den Hd.
have Hdp_pos := peval_at_rat_aux_snd_pos p num den Hd.
have Hgen : forall z, BinInt.Z.lt BinInt.Z0 z ->
  ((Z_to_int z)%:~R : realalg) > 0.
{ move=> z Hz.
  have Hsgn : BinInt.Z.lt BinInt.Z0 (sgn_Z z)
    by rewrite /sgn_Z; case: z Hz.
  have Hds : sgn_matches realalg (sgn_Z z) ((Z_to_int z)%:~R : realalg)
    := sgn_matches_int z.
  by case: Hds => [_ [_ Hg]]; apply/Hg. }
rewrite /peval_at_rat.
case Hp : (peval_at_rat_aux p num den) => [v dp].
rewrite Hp in Hid. rewrite Hp /= in Hdp_pos. simpl.
clear Hp.
set H := (pol_to_polyralg p).[_].
have Hdp_ra_pos : ((Z_to_int dp)%:~R : realalg) > 0 by exact: Hgen.
(* We want sgn_matches _ v H.
   By sgn_matches_mul_pos_r, it suffices: sgn_matches _ v (H * dp_ra),
   where dp_ra = (Z_to_int dp)%:~R.
   By Hid, H * dp_ra = (Z_to_int v)%:~R, and the sign of that w.r.t. v
   is sgn_matches_int (after reducing sgn_Z to Z.lt/eq).
   But sgn_matches_int gives `sgn_matches _ (sgn_Z v) (Z_to_int v)%:~R`,
   which is sgn_matches of `sgn_Z v`, not `v`. However the two are
   equivalent on v because `sgn_matches` only uses the comparisons with 0. *)
apply: (sgn_matches_mul_pos_r _ _ _ Hdp_ra_pos).
rewrite Hid. clear Hid H Hdp_ra_pos Hdp_pos Hgen.
(* Goal: sgn_matches _ v (Z_to_int v)%:~R.
   Prove by case on v. *)
have Hgen2 : forall z, sgn_matches realalg z ((Z_to_int z)%:~R : realalg).
{ move=> z; rewrite /sgn_matches.
  have Hpos_pos : forall q : positive, ((Z_to_int (Z.pos q))%:~R : realalg) > 0.
  { by move=> q; rewrite ltr0z /Z_to_int; apply/ltP/Pos2Nat.is_pos. }
  have Hneg_neg : forall q : positive, ((Z_to_int (Z.neg q))%:~R : realalg) < 0.
  { by move=> q; rewrite ltrz0 /Z_to_int; case: (Pos.to_nat _). }
  case: z => [|q|q].
  - split; last split.
    + by split => // _; rewrite /Z_to_int /= mulr0z.
    + by split => //; rewrite /Z_to_int /= mulr0z order.Order.POrderTheory.ltxx.
    + by split => //; rewrite /Z_to_int /= mulr0z order.Order.POrderTheory.ltxx.
  - split; last split.
    + split => //.
      move=> H; have := Hpos_pos q; by rewrite H order.Order.POrderTheory.ltxx.
    + split => //.
      move=> H; have := Hpos_pos q; by rewrite order.Order.POrderTheory.lt_gtF.
    + split; first by move=> _; exact: Hpos_pos.
      by [].
  - split; last split.
    + split => //.
      move=> H; have := Hneg_neg q; by rewrite H order.Order.POrderTheory.ltxx.
    + split; first by move=> _; exact: Hneg_neg.
      by [].
    + split => //.
      move=> H; have := Hneg_neg q; by rewrite order.Order.POrderTheory.lt_gtF. }
exact: Hgen2.
Qed.

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

(* Helper: `taq z 1 = #z` -- evaluation of the trivial Tarski query
   over a finite root list returns its cardinality. *)
Lemma natr_to_Posz (n : nat) : (n%:R : int) = Posz n.
Proof. by elim: n => [//|n IH]; rewrite -addn1 PoszD natrD /= IH. Qed.

Lemma taq_one (z : seq realalg) : taq z 1 = Posz (size z).
Proof.
unfold taq.
transitivity (\sum_(x <- z) (1%R : int)).
- by apply: eq_bigr => x _; rewrite hornerC sgz1.
- by rewrite big_const_seq count_predT iter_addr_0 natr_to_Posz.
Qed.

(* NOTE (2026-04-09): the hypothesis `Hchain_nz` propagates the
   "no zero entries in the Sturm chain" invariant from the morphism
   lemmas above.  It is a semantically-trivial property of
   `BrownTraub.sturm_chain p` (the chain terminates when the degree
   drops to 0, so no chain entry is the zero polynomial); closing it
   structurally is a follow-up.

   Additional hypotheses (`Habs_chain`, `Hpd`, `Hlc_nz`, `Hth_nz`,
   `Hcb_nz`, `Hbnd`) capture the abstract-level Sturm-bridge facts:
   the lifted Brown–Traub chain coincides with the abstract `mods`,
   our `pderiv` agrees with mathcomp's `^`()`, and the chain entries
   do not vanish in the relevant places. They are documented but not
   themselves proved here; their discharge is downstream work. *)

Lemma sturm_count_above_correct
  (p : pol) (num den : Z) (Hd : BinInt.Z.lt BinInt.Z0 den)
  (Hchain_nz : forall q, List.In q (sturm_chain p) -> q <> nil)
  (Hpd : pol_to_polyralg (pderiv p)
         = (pol_to_polyralg p)^`())
  (Habs_chain :
     List.map pol_to_polyralg (sturm_chain p)
     = mods (pol_to_polyralg p) ((pol_to_polyralg p)^`()))
  (Hlc_nz : forall q, List.In q (sturm_chain p) ->
                      (lead_coef (pol_to_polyralg q) != 0)%R)
  (Hth_nz : forall q, List.In q (sturm_chain p) ->
                      ((pol_to_polyralg q).[threshold_ralg num den] != 0)%R)
  (Hcb_nz : forall q, List.In q (sturm_chain p) ->
                      ((pol_to_polyralg q).[
                         cauchy_bound (pol_to_polyralg p)] != 0)%R)
  (Hbnd : (threshold_ralg num den
             < cauchy_bound (pol_to_polyralg p))%R)
  (* Bridge between mathcomp's `changes_pinfty` (lead-coef variation)
     and `changes_horner` evaluated at the Cauchy bound. Both are
     equal because, beyond the Cauchy bound, every chain entry has
     the same sign as its lead coefficient (sgp_pinftyP), and `changes`
     only depends on signs of products. *)
  (Hpinf_eq :
     changes_pinfty
        (mods (pol_to_polyralg p) ((pol_to_polyralg p)^`()))
     = changes_horner
        (mods (pol_to_polyralg p) ((pol_to_polyralg p)^`()))
        (cauchy_bound (pol_to_polyralg p)))
  (* Bridge between the half-open Sturm root list and the global root
     list, restricted to roots above the threshold. Holds because all
     real roots of `pol_to_polyralg p` lie strictly within `]-cb, cb[`
     by `root_in_cauchy_bound`. *)
  (Hroots_filt :
     roots (pol_to_polyralg p)
           (threshold_ralg num den)
           (cauchy_bound (pol_to_polyralg p))
     = List.filter
         (fun r : realalg => (threshold_ralg num den < r)%R)
         (rootsR (pol_to_polyralg p))) :
  sturm_count_above (sturm_chain p) num den
  = size (List.filter
            (fun r : realalg => (threshold_ralg num den < r)%R)
            (rootsR (pol_to_polyralg p))).
Proof.
(* Step 1: rewrite both variation counts via the morphism lemmas. *)
rewrite /sturm_count_above.
rewrite (variation_at_rat_morph _ _ _ Hd Hth_nz).
rewrite (variation_at_pinf_morph _ Hlc_nz).
(* Step 2: rewrite the lifted chain as `mods (lift p) (lift p)^`()`. *)
rewrite Habs_chain.
(* Step 3: identify the difference with `changes_itv_poly`, then with
   `changes_itv_mods`, then with `cindex` via `changes_itv_mods_cindex`. *)
set P := pol_to_polyralg p.
set a := threshold_ralg num den.
set b := cauchy_bound P.
(* Apply `changes_itv_mods_cindex`:
     changes_itv_mods a b P (P^`() * 1) = cindex a b (P^`() * 1) P.
   Note `changes_itv_mods a b p q = changes_itv_poly a b (mods p q)`,
   i.e. `changes_horner (mods p q) a - changes_horner (mods p q) b`.
   We use `q := 1`, so `mods P (P^`() * 1) = mods P (P^`())`. *)
have Heq1 : (P^`() * 1 = P^`())%R by rewrite mulr1.
have Hcim :
  ((changes_horner (mods P (P^`())) a)%:Z
     - (changes_horner (mods P (P^`())) b)%:Z)%R
  = taq (roots P a b) 1.
{ have Hab : (a < b)%R := Hbnd.
  (* Helper: every element of `List.map f l` corresponds to an element of l. *)
  have Hin_map : forall (T U : Type) (f : T -> U) (l : list T) (y : U),
    List.In y (List.map f l) -> exists2 x, List.In x l & y = f x.
  { move=> T U f l y.
    elim: l => [//|a' tl IH]; rewrite /=.
    case=> [<-|H]; first by exists a'; [left | by []].
    by case: (IH H) => x Hx ->; exists x; [right | by []]. }
  have all_in : forall (T : eqType) (P0 : pred T) (l : list T),
    (forall x, List.In x l -> P0 x) -> all P0 l.
  { move=> T P0 l Hp.
    elim: l Hp => [//|x tl IH] Hp /=.
    apply/andP; split; first by apply: Hp; left.
    by apply: IH => z Hz; apply: Hp; right. }
  have Ha : all (fun r : {poly realalg} => r.[a] != 0)
                (mods P (P^`() * 1)).
  { rewrite Heq1 -Habs_chain.
    apply: all_in => y Hy.
    case: (Hin_map _ _ _ _ _ Hy) => q Hq ->.
    by apply: Hth_nz. }
  have Hb' : all (fun r : {poly realalg} => r.[b] != 0)
                (mods P (P^`() * 1)).
  { rewrite Heq1 -Habs_chain.
    apply: all_in => y Hy.
    case: (Hin_map _ _ _ _ _ Hy) => q Hq ->.
    by apply: Hcb_nz. }
  have HT := taq_taq_itv Hab (p := P) (q := 1) Ha Hb'.
  rewrite HT /taq_itv /changes_itv_mods /changes_itv_poly Heq1.
  by []. }
(* Combine: variation_at_rat - variation_at_pinf
         = changes_horner a - changes_pinfty
         = changes_horner a - changes_horner b
         = cindex a b (P^`() * 1) P
         = taq (roots P a b) 1   [via taq_cindex]
         = #(roots P a b)        [via taq_one]
         = #(filter (>a) (rootsR P))   [roots p a b vs rootsR] *)
rewrite Hpinf_eq.
have Hsub : ((changes_horner (mods P (P^`())) a)%:Z
             - (changes_horner (mods P (P^`())) b)%:Z)%R
            = Posz (size (roots P a b)).
{ by rewrite Hcim taq_one. }
(* Convert int subtraction on the LHS to nat subtraction. *)
have Hge : (changes_horner (mods P (P^`())) b
            <= changes_horner (mods P (P^`())) a)%N.
{ have Hpos : (0 <= Posz (size (roots P a b)))%R by [].
  rewrite -Hsub subr_ge0 in Hpos.
  exact: Hpos. }
have Hnat_eq : (changes_horner (mods P (P^`())) a
                - changes_horner (mods P (P^`())) b)%N
             = size (roots P a b).
{ have HZ : Posz (changes_horner (mods P (P^`())) a
                  - changes_horner (mods P (P^`())) b)%N
            = Posz (size (roots P a b)).
  { rewrite -(subzn Hge); exact: Hsub. }
  by case: HZ. }
rewrite minusE Hnat_eq.
(* Now: size (roots P a b) = size (filter (>a) (rootsR P))
   directly via Hroots_filt. *)
by rewrite Hroots_filt.
Qed.

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
   caller must discharge `Hchain_nz` before invoking this lemma.
   The additional hypotheses bridging Brown–Traub's concrete chain to
   mathcomp's abstract `mods` (`Hpd`, `Habs_chain`, `Hlc_nz`, `Hth_nz`,
   `Hcb_nz`, `Hbnd`) are propagated verbatim from
   `sturm_count_above_correct`. *)
Lemma sturm_count_above_pos
  (p : pol) (num den : Z) (Hd : BinInt.Z.lt BinInt.Z0 den)
  (Hchain_nz : forall q, List.In q (sturm_chain p) -> q <> nil)
  (Hpd : pol_to_polyralg (pderiv p)
         = (pol_to_polyralg p)^`())
  (Habs_chain :
     List.map pol_to_polyralg (sturm_chain p)
     = mods (pol_to_polyralg p) ((pol_to_polyralg p)^`()))
  (Hlc_nz : forall q, List.In q (sturm_chain p) ->
                      (lead_coef (pol_to_polyralg q) != 0)%R)
  (Hth_nz : forall q, List.In q (sturm_chain p) ->
                      ((pol_to_polyralg q).[threshold_ralg num den] != 0)%R)
  (Hcb_nz : forall q, List.In q (sturm_chain p) ->
                      ((pol_to_polyralg q).[
                         cauchy_bound (pol_to_polyralg p)] != 0)%R)
  (Hbnd : (threshold_ralg num den
             < cauchy_bound (pol_to_polyralg p))%R)
  (Hpinf_eq :
     changes_pinfty
        (mods (pol_to_polyralg p) ((pol_to_polyralg p)^`()))
     = changes_horner
        (mods (pol_to_polyralg p) ((pol_to_polyralg p)^`()))
        (cauchy_bound (pol_to_polyralg p)))
  (Hroots_filt :
     roots (pol_to_polyralg p)
           (threshold_ralg num den)
           (cauchy_bound (pol_to_polyralg p))
     = List.filter
         (fun r : realalg => (threshold_ralg num den < r)%R)
         (rootsR (pol_to_polyralg p))) :
  (0 < sturm_count_above (sturm_chain p) num den)%nat ->
  exists r : realalg,
    root (pol_to_polyralg p) r /\ (threshold_ralg num den < r)%R.
Proof.
move=> Hgt.
have Hsize :
  (0 < size (List.filter
               (fun r : realalg => (threshold_ralg num den < r)%R)
               (rootsR (pol_to_polyralg p))))%nat.
{ by rewrite -(sturm_count_above_correct p num den Hd Hchain_nz
                 Hpd Habs_chain Hlc_nz Hth_nz Hcb_nz Hbnd
                 Hpinf_eq Hroots_filt). }
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
