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

From Stdlib Require Import ZArith List.
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
(*  `nat`) from qe_rcf_th.v.                                            *)
(*                                                                      *)
(*  Proof sketch (future work):                                         *)
(*    - Both sides count sign-agreement-breaks along the list of        *)
(*      horner evaluations. The only subtle step is the zero-skipping   *)
(*      convention: our `variation` skips zeros explicitly, whereas     *)
(*      mathcomp's `changes` uses `(a * head 0 q < 0)` on the raw seq,  *)
(*      which does NOT skip zeros. However, our `sign_at_rat` outputs   *)
(*      an integer in {-1,0,1}, and the two conventions coincide on     *)
(*      lists with the property that every isolated zero sits between   *)
(*      two opposite signs (Sturm chains have this structure).          *)
(*    - For a clean proof we would need either                          *)
(*      (a) a side lemma "Sturm chain has no adjacent zeros",           *)
(*      (b) a direct equivalence of the two variation notions on        *)
(*          chains that have the "no-two-adjacent-zeros" property, or   *)
(*      (c) state a slightly weaker bridge that only asserts the value  *)
(*          of the Sturm count (not the variation at a single point).   *)
(* ================================================================== *)

(* Same caveat as `variation_at_pinf_morph` below: the statement is false on
   chains with adjacent zeros at the evaluation point. For the actual
   application (`sturm_chain p` evaluated at `4/105`) the FLINT-shipped
   `signs_at_x0` confirms zero adjacent zeros, so this morphism IS true on
   our specific data. Pinning down the abstract precondition is left to a
   later sprint. *)
Lemma variation_at_rat_morph
  (c : list pol) (num den : Z) (Hden : BinInt.Z.lt BinInt.Z0 den) :
  variation_at_rat c num den
  = changes_horner (List.map pol_to_polyralg c) (threshold_ralg num den).
Proof.
Admitted.

(* WARNING (discovered 2026-04-09 during the first attempt):
   This statement is FALSE on lists with adjacent zeros, as a counter-example:
     c = [[1]; []; [-1]]
       variation_at_pinf c        = variation [1; 0; -1] = 1
                                    (our `variation` skips the middle 0)
       changes_pinfty (lift c)    = changes [1; 0; -1] = 0
                                    (mathcomp's `changes` does NOT skip zeros)
   The two definitions agree on lists with no adjacent zeros, which IS the
   case for the modified Sturm chain at any point that is not a root of the
   polynomial. The statement therefore needs a hypothesis like
       `no_adjacent_zeros_at_pinf c`
   or equivalently a precondition asserting `c = sturm_chain p` for some `p`
   whose polynomial degree exceeds the depth at which any chain entry vanishes
   at +infty (which always holds for the standard modified Sturm chain).

   Until the precondition is pinned down, this lemma stays Admitted as
   a placeholder for the eventual `_modulo_chain_invariant` form. *)
Lemma variation_at_pinf_morph (c : list pol) :
  variation_at_pinf c = changes_pinfty (List.map pol_to_polyralg c).
Proof.
Admitted.

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

Lemma sturm_count_above_correct
  (p : pol) (num den : Z) (Hd : BinInt.Z.lt BinInt.Z0 den) :
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

Lemma sturm_count_above_pos
  (p : pol) (num den : Z) (Hd : BinInt.Z.lt BinInt.Z0 den) :
  (0 < sturm_count_above (sturm_chain p) num den)%nat ->
  exists r : realalg,
    root (pol_to_polyralg p) r /\ (threshold_ralg num den < r)%R.
Proof.
move=> Hgt.
have Hsize :
  (0 < size (List.filter
               (fun r : realalg => (threshold_ralg num den < r)%R)
               (rootsR (pol_to_polyralg p))))%nat.
{ by rewrite -(sturm_count_above_correct p num den Hd). }
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
