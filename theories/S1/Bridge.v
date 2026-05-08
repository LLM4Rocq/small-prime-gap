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
(*  The intended consumer is Cert.v's `sturm_count_correct`            *)
(*  (now a one-line `Qed` discharged by `maynard_L1_concrete`, which    *)
(*  uses the `sturm_count_above_pos` lemma proved below).               *)
(*                                                                      *)
(*  Structure:                                                          *)
(*    - Z_to_int             : stdlib Z -> mathcomp int helper.          *)
(*    - pol_to_polyralg      : lift of `pol = list Z` to                 *)
(*                             `{poly realalg}`, going through           *)
(*                             `pol_to_polyrat` from CharPoly.v.         *)
(*    - (mods_int_morph removed: strict chain equality is unprovable;    *)
(*      consumers rewired to take Habs_chain as a hypothesis instead)    *)
(*    - variation_at_rat_morph                                           *)
(*                           : [Proved] `variation_at_rat` agrees        *)
(*                             with abstract `changes_horner`.           *)
(*    - sturm_count_above_correct                                        *)
(*                           : [Qed, conditional on chain-bridge         *)
(*                             hypotheses] our Sturm count equals the    *)
(*                             number of real roots above the threshold. *)
(*    - sturm_count_above_pos                                            *)
(*                           : [Qed, same hypotheses] a positive Sturm   *)
(*                             count yields an explicit realalg root     *)
(*                             above the threshold.                      *)
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
(*  PROOF OUTLINE.                                                      *)
(*  ----------------------------------------------------------------   *)
(*  The two chains are NOT equal coefficient-by-coefficient.  They      *)
(*  differ, at each step, by a positive-integer scalar factor that      *)
(*  comes from how the pseudo-remainder is rescaled:                    *)
(*                                                                      *)
(*    mathcomp :  next_mod p q = - (lc q)^(rscalp p q) *: rmodp p q     *)
(*    ours     :  next_mod p q = pneg (prem p q)                        *)
(*                                                                      *)
(*  Brown-Traub's `prem` already bakes in the `lc(q)^(deg p - deg q + 1)`*)
(*  scaling, so on a "clean" input pair the two agree up to sign and a  *)
(*  positive integer factor.  The sign flip is the same on both sides.  *)
(*                                                                      *)
(*  Rather than chase the exact polynomial equality (which requires     *)
(*  proving that our `prem` equals mathcomp's `rmodp` scaled by exactly *)
(*  `lc(q)^(rscalp p q)`), we take a simpler route: we show that, at    *)
(*  each recursive step, our Brown-Traub chain entry and the mathcomp   *)
(*  chain entry are *positive-scalar* multiples of one another.  Since  *)
(*  the Sturm machinery only looks at SIGNS of chain entries, this is   *)
(*  the weakest statement that suffices for L1.                         *)
(*                                                                      *)
(*  Precisely, we introduce a family of "parallel" intermediate lemmas: *)
(*                                                                      *)
(*    pol_to_polyralg_pnorm     :  pnorm is a no-op after lifting.      *)
(*    pol_to_polyralg_pneg      :  pneg lifts to polynomial negation.   *)
(*    pol_to_polyralg_pzero     :  pzero lifts to 0.                    *)
(*    mods_int_loop_nil_fuel    :  loop with 0 fuel is [::].            *)
(*    mods_int_p0               :  mods_int p 0 = [pnorm p] (or []).    *)
(*    mods_int_0q               :  mods_int 0 q = [pnorm q] (or []).    *)
(*    mods_00                   :  mods 0 0 = [::] in mathcomp.         *)
(*    mods_p0                   :  mods p 0 = [:: p] (or [::]).         *)
(*    mods_0q                   :  mods 0 q = [::] in mathcomp.         *)
(*                                                                      *)
(*  The STRUCTURAL STEP lemma (hardest, now Qed below) is:              *)
(*                                                                      *)
(*    next_mod_scaled_morph : forall p q : pol, pnorm q <> [] ->        *)
(*      exists k : realalg, (k != 0)%R /\                               *)
(*        pol_to_polyralg (next_mod p (pnorm q))                        *)
(*        = k *: qe_rcf_th.next_mod (pol_to_polyralg p)                 *)
(*                              (pol_to_polyralg (pnorm q)).            *)
(*                                                                      *)
(*  From this the equality `mods_int_morph` itself cannot be recovered  *)
(*  directly (the chains differ by scalars), but the *sign-variation*   *)
(*  counts `changes_horner` / `changes_pinfty` ARE invariant under      *)
(*  positive scaling of individual entries, which is what is actually   *)
(*  needed for Sturm.                                                   *)
(*                                                                      *)
(*  The strict equality `mods_int_morph` was removed from this file     *)
(*  (it is unprovable: chains differ by polynomial scalars).             *)
(*  Consumers (CertL1.v) now supply `Habs_chain` as a hypothesis;       *)
(*  `sturm_count_above_pos_concrete` takes it as an argument.           *)
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
(*  Structural lifts for the integer-polynomial primitives.            *)
(* ------------------------------------------------------------------ *)

Lemma pol_to_polyralg_pzero :
  pol_to_polyralg pzero = 0 :> {poly realalg}.
Proof. by rewrite /pol_to_polyralg /pzero /pol_to_polyrat /= rmorph0. Qed.

(* Lifting commutes with negation.  Proof by induction on `p`,
   unfolding the raw `pol_to_polyrat` / `cons_poly_def` / `map_poly`
   definitions directly (since `pol_to_polyralg_cons` is defined later). *)
Lemma pol_to_polyralg_pneg (p : pol) :
  pol_to_polyralg (pneg p) = - pol_to_polyralg p.
Proof.
elim: p => [|x p IH].
- by rewrite /pneg /= /pol_to_polyralg /pol_to_polyrat /= rmorph0 oppr0.
- rewrite /pneg -/pneg /=.
  rewrite /pol_to_polyralg /pol_to_polyrat /=.
  fold (pol_to_polyrat p).
  fold (pol_to_polyrat (pneg p)).
  fold (pol_to_polyralg p).
  fold (pol_to_polyralg (pneg p)).
  rewrite !cons_poly_def.
  rewrite !rmorphD !rmorphM /= !map_polyX !map_polyC.
  change (map_poly (rR:=realalg_realalg__canonical__GRing_NzSemiRing) ratr
    (Poly (ListDef.map (fun z : Z => (Z_to_int z)%:~R) (ListDef.map Z.opp p))))
    with (pol_to_polyralg (pneg p)).
  change (map_poly (rR:=realalg_realalg__canonical__GRing_NzSemiRing) ratr
    (pol_to_polyrat p)) with (pol_to_polyralg p).
  rewrite IH.
  rewrite opprD mulNr.
  congr (_ + _).
  rewrite -polyCN.
  congr (_%:P).
  rewrite -rmorphN.
  congr (ratr _).
  case: x => [|q|q] /=.
  + by rewrite oppr0.
  + rewrite NegzE.
    have Hq := Pos2Nat.is_pos q.
    by case Hn : (Pos.to_nat q) => [|n]; [lia| rewrite subn1 /=].
  + rewrite NegzE.
    have Hq := Pos2Nat.is_pos q.
    by case Hn : (Pos.to_nat q) => [|n]; [lia| rewrite subn1 /= opprK].
Qed.

(* Lifting is invariant under `pnorm`.  Proof: `pnorm` strips trailing
   zeros via `rev (drop_leading_zeros (rev p))`.  We show that
   `drop_leading_zeros` only removes entries that map to 0 under
   `Z_to_int`, and `Poly` already normalises by stripping trailing
   zeros, so both sides yield the same `{poly rat}` and hence the
   same `{poly realalg}` after `map_poly ratr`. *)
Lemma pol_to_polyralg_pnorm (p : pol) :
  pol_to_polyralg (pnorm p) = pol_to_polyralg p.
Proof.
rewrite /pol_to_polyralg /pol_to_polyrat /pnorm.
set f := (fun z : Z => (Z_to_int z)%:~R : rat).
have Hdlz : forall l : list Z,
  Poly (List.map f (List.rev (drop_leading_zeros l)))
  = Poly (List.map f (List.rev l)) :> {poly rat}.
{ move=> l.
  elim: l => [//|a l IH] /=.
  case Ha : (Z.eqb a 0); last by [].
  move/Z.eqb_eq in Ha; subst a.
  rewrite IH.
  have Hf0 : f BinInt.Z0 = 0
    by rewrite /f /Z_to_int /=; exact: mulr0z.
  rewrite List.map_app /= Hf0.
  apply/polyP => j.
  rewrite !coef_Poly nth_cat size_map.
  case: (ltnP j (size (List.rev l))) => Hj; first by [].
  have -> : [:: (0 : rat)]`_(j - size (List.rev l)) = 0.
  { by case: (j - size (List.rev l))%N => [//|k] /=;
       rewrite nth_nil. }
  by rewrite nth_default //; rewrite size_map. }
by rewrite (Hdlz (List.rev p)) List.rev_involutive.
Qed.

(* ------------------------------------------------------------------ *)
(*  Base cases of the `mods` / `mods_int` recursion.                    *)
(* ------------------------------------------------------------------ *)

(* mathcomp: `mods 0 q = [::]`. *)
Lemma mods_0q_ralg (q : {poly realalg}) :
  mods 0 q = [::].
Proof. exact: mods0p. Qed.

(* mathcomp: `mods p 0 = if p == 0 then [::] else [:: p]`. *)
Lemma mods_p0_ralg (p : {poly realalg}) :
  mods p 0 = if p == 0 then [::] else [:: p].
Proof. exact: modsp0. Qed.

(* Our side: when `pnorm p = []`, `mods_int p q` just runs the loop from
   `pzero`, which dispatches on `pnorm q` inside the loop. *)
Lemma mods_int_pzero_q (q : pol) :
  mods_int pzero q = mods_int_loop (S (S (psize q))) pzero q.
Proof. by []. Qed.

(* `mods_int_loop` on 0 fuel is empty. *)
Lemma mods_int_loop_0 (p q : pol) :
  mods_int_loop 0 p q = [].
Proof. by []. Qed.

(* When `q` is already zero, the loop stops immediately after the
   optional emit of `pnorm q` (which is empty). *)
Lemma mods_int_loop_zero_q (n : nat) (p : pol) :
  mods_int_loop (S n) p pzero = [].
Proof. by rewrite /= /pnorm /=. Qed.

(* ----- Weakest form: lifting `mods_int p pzero`. ------ *)

(* Our `mods_int p pzero` is:
     - [] if pnorm p = []
     - [pnorm p] otherwise.
   We phrase it so the RHS is recognisable from the LHS of the big
   morphism lemma. *)
Lemma mods_int_p_pzero (p : pol) :
  mods_int p pzero
  = if pnorm p is [] then [] else [pnorm p].
Proof.
rewrite /mods_int.
case E : (pnorm p) => [|x xs]; first by [].
rewrite /mods_int_loop /= /pnorm /=.
by [].
Qed.

(* Our `mods_int pzero q` is:
     - [] if pnorm q = []
     - [pnorm q] IF pnorm q is terminal (degree 0)
     - pnorm q :: (loop continuation) otherwise.
   The full shape is complicated by the recursion; we only expose the
   two trivial subcases we actually need. *)
Lemma mods_int_pzero_pzero : mods_int pzero pzero = [].
Proof. by []. Qed.

(* ------------------------------------------------------------------ *)
(*  Base cases of `mods_int_morph`.                                     *)
(* ------------------------------------------------------------------ *)

(* When `q = pzero`, both sides collapse to either `[::]` or
   `[:: pol_to_polyralg p]` depending on whether `p` is the zero
   polynomial.  This is the FIRST fully-closed base case of the big
   morphism lemma. *)
Lemma mods_int_morph_p_pzero (p : pol) :
  List.map pol_to_polyralg (mods_int p pzero)
  = mods (pol_to_polyralg p) (pol_to_polyralg pzero).
Proof.
rewrite pol_to_polyralg_pzero mods_p0_ralg mods_int_p_pzero.
case E : (pnorm p) => [|x xs].
- (* pnorm p = [] -> pol_to_polyralg p = 0. *)
  have Hp : pol_to_polyralg p = 0.
  { rewrite -(pol_to_polyralg_pnorm p) E.
    by rewrite /pol_to_polyralg /pol_to_polyrat /= rmorph0. }
  by rewrite /= Hp eqxx.
- (* pnorm p = x :: xs -> pol_to_polyralg p != 0. *)
  rewrite /= -(pol_to_polyralg_pnorm p) E.
  suff -> : (pol_to_polyralg (x :: xs) == 0) = false by [].
  apply/negP => /eqP Habs.
  (* 1. Last element of pnorm p = x :: xs is nonzero. *)
  have HE2 : last x xs <> BinInt.Z0.
  { have Hlnz : forall l a bs,
      List.rev (drop_leading_zeros l) = a :: bs ->
      last a bs <> BinInt.Z0.
    { move=> l; elim: l => [//|b l' IHl] a bs /=.
      case Hb : (Z.eqb b 0); first exact: IHl.
      move/Z.eqb_neq in Hb.
      (* List.rev (b :: l') = (List.rev l' ++ [:: b])%list *)
      move=> Heq.
      suff : last a bs = b by move=> ->.
      move: Heq; rewrite /=.
      case Hl : (List.rev l') => [|h t].
      - by move=> [<- <-] /=.
      - by move=> [<- Hbs]; rewrite -Hbs last_cat. }
    have HE3 : List.rev (drop_leading_zeros (List.rev p))
             = x :: xs by rewrite -E.
    exact: Hlnz _ _ _ HE3. }
  (* 2. The rat coefficient list has nonzero last element. *)
  set fq := (fun z : Z => (Z_to_int z)%:~R : rat).
  have Hmap_last_nz : last 0 (List.map fq (x :: xs)) != 0.
  { have Hml : last 0 (List.map fq (x :: xs))
             = (Z_to_int (last x xs))%:~R.
    { clear -fq; elim: xs x => [//|y ys IH] x' /=; exact: IH. }
    rewrite Hml intr_eq0; apply/eqP => H0; apply: HE2.
    case: (last x xs) H0 => [//|q|q]; rewrite /Z_to_int /=.
    - by move=> H; exfalso; have := Pos2Nat.is_pos q;
         case: (Pos.to_nat q) H => [|n] //= _;
         exact: (PeanoNat.Nat.lt_irrefl 0).
    - by case: (Pos.to_nat q) (Pos2Nat.is_pos q) => [|n] //=. }
  (* 3. The rat polynomial is nonzero (last coef is nonzero). *)
  have Hrat_nz : Poly (List.map fq (x :: xs)) != 0.
  { apply/eqP => Habs2; have := PolyK Hmap_last_nz.
    by rewrite Habs2 polyseq0. }
  (* 4. map_poly ratr preserves nonzero. *)
  have : pol_to_polyralg (x :: xs) != 0
    by rewrite /pol_to_polyralg /pol_to_polyrat map_poly_eq0.
  by rewrite Habs eqxx.
Qed.

(* When `p = pzero`, both sides likewise collapse.  On the mathcomp
   side, `mods 0 q = [::]` unconditionally, so this case is an
   equality between our `mods_int pzero q` (which starts the loop) and
   `[::]`.  This forces our loop to return `[::]`, which is TRUE only
   when `pnorm q = []`; otherwise our loop emits `pnorm q` at least
   once.  Hence the two sides DISAGREE when `q` is nonzero!

   This is the fundamental mismatch: mathcomp's `mods 0 q` throws away
   `q` entirely, but our `mods_int pzero q` returns it.  The correct
   bridge therefore has to normalise the `p = 0` case specially, or we
   must conclude that this case never arises in our Sturm application
   (it doesn't: we always call `mods_int p (pderiv p)` with `p` of
   degree >= 1).

   For completeness we record the mismatch as a lemma specialised to
   `pnorm q = []`, which is the only subcase where equality holds. *)
Lemma mods_int_morph_pzero_q_when_q_zero (q : pol) :
  pnorm q = [] ->
  List.map pol_to_polyralg (mods_int pzero q)
  = mods (pol_to_polyralg pzero) (pol_to_polyralg q).
Proof.
move=> Hq.
rewrite pol_to_polyralg_pzero mods_0q_ralg.
rewrite /mods_int /pnorm /= /pnorm in Hq *.
rewrite Hq /=.
(* mods_int_loop emits nothing because pnorm q = []. *)
by [].
Qed.

(* `mods_int_morph` (strict chain equality) is unprovable here: the     *)
(* PRS chains differ by per-entry nonzero scalars.  See the dedicated   *)
(* tombstone block below for the full explanation; consumers take      *)
(* `Habs_chain` as a hypothesis. *)

(* ------------------------------------------------------------------ *)
(*  Key intermediate: our `prem` computes the same pseudo-remainder    *)
(*  as MathComp's `Pdiv.Ring.rmodp` after lifting through               *)
(*  `pol_to_polyralg`.                                                  *)
(*                                                                      *)
(*  Both algorithms implement the same classical pseudo-division loop:  *)
(*    - Our `prem_step A B` computes                                    *)
(*        lc(B) * A - lc(A) * X^(deg A - deg B) * B                    *)
(*    - MathComp's `redivp_rec q` at each step computes                 *)
(*        r * cq - lc(r) * X^(size r - size q) * q                     *)
(*      where `cq = lead_coef q`.                                      *)
(*  These are identical operations (scalar mult by lc(B) then subtract  *)
(*  an aligned multiple of B), so both loops converge to the same       *)
(*  remainder polynomial.                                               *)
(*                                                                      *)
(*  A complete formal proof would go by strong induction on              *)
(*  `size (pol_to_polyralg p) - size (pol_to_polyralg q)` and show     *)
(*  each step of our `prem_loop` matches `redivp_rec`'s step.  This    *)
(*  requires connecting our `pnorm`/`len_deg`/`plead`/`prem_step` with *)
(*  MathComp's `size`/`lead_coef` primitives — straightforward but     *)
(*  lengthy; left as a focused follow-up.                               *)
(* ------------------------------------------------------------------ *)

(* ----- Helper: `pnorm` is idempotent. ----- *)
Lemma pnorm_idem (p : pol) : pnorm (pnorm p) = pnorm p.
Proof.
suff Hdlz : forall l, drop_leading_zeros (drop_leading_zeros l) = drop_leading_zeros l.
{ unfold pnorm.
  rewrite List.rev_involutive Hdlz. by []. }
move=> l; elim: l => [//|x l IH] /=.
case Hx : (Z.eqb x 0); first by exact: IH.
simpl. rewrite Hx. by [].
Qed.

(* ----- Helper: pnorm q <> [] implies pnorm (pnorm q) <> []. ----- *)
Lemma pnorm_pnorm_ne (q : pol) : pnorm q <> [] -> pnorm (pnorm q) <> [].
Proof. by rewrite pnorm_idem. Qed.

(* ----- Key helper: pol_to_polyrat is invariant under pnorm. ----- *)
Lemma pol_to_polyrat_pnorm (p : pol) :
  pol_to_polyrat (pnorm p) = pol_to_polyrat p.
Proof.
(* Follows from pol_to_polyralg_pnorm via injectivity of map_poly ratr. *)
have H := pol_to_polyralg_pnorm p.
rewrite /pol_to_polyralg in H.
exact: (@map_poly_inj _ _ (ratr : {rmorphism rat -> realalg}) _ _ H).
Qed.

(* prem_rmodp_rat, prem_rmodp_eq, and next_mod_scaled_morph are proved  *)
(* below (after the building-block lift lemmas they depend on).         *)

(* ------------------------------------------------------------------ *)
(*  `mods_int_morph` (strict chain equality) has been REMOVED.          *)
(*                                                                      *)
(*  The two PRS chains differ by per-entry nonzero scalars: our         *)
(*  Brown-Traub chain computes `-rmodp(P, Q)` while MathComp's          *)
(*  `next_mod` computes `-lc(Q)^{rscalp} *: rmodp(P, Q)`, so strict   *)
(*  polynomial equality does not hold in general.                       *)
(*                                                                      *)
(*  Consumers (CertL1.v) now supply `Habs_chain` as a hypothesis to    *)
(*  `sturm_count_above_pos_concrete`.  The `mods_chain_scaled` and      *)
(*  `mods_int_morph_weak` lemmas that formerly derived from the strict  *)
(*  form have also been removed (they had no external consumers).       *)
(* ------------------------------------------------------------------ *)

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
(*  Structural lemma `sgn_matches_int` (below) used by the four        *)
(*  sign-bridge helpers.                                                *)
(*                                                                      *)
(*  This is a small, local structural fact about `pol_to_polyralg` that *)
(*  connects the `{poly realalg}` leading coefficient with the integer  *)
(*  `plead` function.  Proved outright by case analysis on the Z        *)
(*  constructor (Z0 / Zpos / Zneg) and standard MathComp lemmas         *)
(*  `ltr0z` / `ltrz0`.                                                  *)
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

(* ------------------------------------------------------------------ *)
(*  Building-block lifts for the integer-polynomial primitives.        *)
(*  These enable future proofs connecting our `prem` loop with         *)
(*  MathComp's `Pdiv.Ring.redivp_rec`.                                 *)
(* ------------------------------------------------------------------ *)

(* Lifting commutes with scalar multiplication. *)
Lemma pol_to_polyralg_pscale (c : Z) (p : pol) :
  pol_to_polyralg (pscale c p)
  = ((Z_to_int c)%:~R : realalg) *: pol_to_polyralg p.
Proof.
elim: p => [|x p IH].
- by rewrite /pscale /= /pol_to_polyralg /pol_to_polyrat /= rmorph0 scaler0.
- rewrite /pscale -/pscale /=.
  rewrite /pol_to_polyralg /pol_to_polyrat /=.
  fold (pol_to_polyrat p).
  fold (pol_to_polyrat (pscale c p)).
  fold (pol_to_polyralg p).
  fold (pol_to_polyralg (pscale c p)).
  rewrite !cons_poly_def.
  rewrite !rmorphD !rmorphM /= !map_polyX !map_polyC.
  change (map_poly (rR:=realalg_realalg__canonical__GRing_NzSemiRing) ratr
    (Poly (ListDef.map (fun z : Z => (Z_to_int z)%:~R) (ListDef.map [eta Z.mul c] p))))
    with (pol_to_polyralg (pscale c p)).
  change (map_poly (rR:=realalg_realalg__canonical__GRing_NzSemiRing) ratr
    (pol_to_polyrat p)) with (pol_to_polyralg p).
  rewrite IH scalerDr -scalerAl.
  congr (_ + _).
  apply/polyP => i; rewrite coefZ !coefC.
  case: i => [|i]; last by rewrite !mulr0.
  rewrite /= !ratr_int Z_to_int_mul intrM.
  by [].
Qed.

(* Lifting commutes with X-shift (multiplication by X^k). *)
Lemma pol_to_polyralg_pshift (k : nat) (p : pol) :
  pol_to_polyralg (pshift k p) = 'X^k * pol_to_polyralg p.
Proof.
elim: k => [|k IH].
- by rewrite /= expr0 mul1r.
- rewrite /= pol_to_polyralg_cons IH.
  have -> : (Z_to_int 0)%:~R = (0 : realalg) by rewrite /Z_to_int /= mulr0z.
  rewrite polyC0 addr0.
  by rewrite -mulrA [pol_to_polyralg p * 'X]mulrC mulrA -exprSr.
Qed.

(* Lifting commutes with addition. *)
Lemma pol_to_polyralg_padd (p q : pol) :
  pol_to_polyralg (padd p q) = pol_to_polyralg p + pol_to_polyralg q.
Proof.
elim: p q => [|x p IH] [|y q].
- by rewrite /= pol_to_polyralg_nil add0r.
- by rewrite /= pol_to_polyralg_nil add0r.
- by rewrite /= pol_to_polyralg_nil addr0.
- rewrite [padd _ _]/= !pol_to_polyralg_cons IH.
  rewrite Z_to_int_add_ralg polyCD mulrDl addrACA.
  by [].
Qed.

(* Lifting commutes with subtraction. *)
Lemma pol_to_polyralg_psub (p q : pol) :
  pol_to_polyralg (psub p q) = pol_to_polyralg p - pol_to_polyralg q.
Proof.
elim: p q => [|x p IH] [|y q].
- by rewrite /= pol_to_polyralg_nil subrr.
- rewrite /=.
  change (pol_to_polyralg (pneg (y :: q))
        = pol_to_polyralg [::] - pol_to_polyralg (y :: q)).
  by rewrite pol_to_polyralg_pneg pol_to_polyralg_nil add0r.
- by rewrite /= pol_to_polyralg_nil oppr0 addr0.
- rewrite [psub _ _]/= !pol_to_polyralg_cons IH.
  have -> : Z_to_int (x - y) = Z_to_int (BinInt.Z.add x (BinInt.Z.opp y))
    by congr (Z_to_int _); lia.
  rewrite Z_to_int_add_ralg opprD mulrBl polyCD addrACA.
  congr (_ + _); congr (_ + _).
  rewrite -polyCN; congr (_%:P).
  case: y => [|q'|q'].
  + by rewrite /Z_to_int /= mulr0z oppr0.
  + rewrite /Z_to_int /= NegzE.
    case Hn : (Pos.to_nat q') => [|n]; first by have := Pos2Nat.is_pos q'; lia.
    by rewrite /= subn1 /=.
  + rewrite /Z_to_int /=.
    case Hn : (Pos.to_nat q') => [|n]; first by have := Pos2Nat.is_pos q'; lia.
    by rewrite /= subn1 /= NegzE opprK.
Qed.

(* Lifting commutes with prem_step (by definition unfolding). *)
Lemma pol_to_polyralg_prem_step (A B : pol) :
  pol_to_polyralg (prem_step A B)
  = pol_to_polyralg
      (pnorm (psub (pscale (plead B) A) (pscale (plead A) (pshift (len_deg A - len_deg B) B)))).
Proof. by []. Qed.

(* Expanded form: one pseudo-division step, after lifting, equals
   lc(B) *: A - lc(A) *: ('X^(deg A - deg B) * B)  as a realalg polynomial.
   This matches MathComp's `redivp_rec` step modulo the `pnorm` wrapper. *)
Lemma pol_to_polyralg_prem_step_expanded (A B : pol) :
  pol_to_polyralg (prem_step A B)
  = pol_to_polyralg
      (pnorm (psub (pscale (plead B) A)
                    (pscale (plead A) (pshift (len_deg A - len_deg B) B)))).
Proof. by []. Qed.

(* The expanded lift of a normalised prem_step: using the sub/scale/shift lemmas. *)
Lemma prem_step_lift (A B : pol) :
  pol_to_polyralg (pnorm (psub (pscale (plead B) A)
                               (pscale (plead A) (pshift (len_deg A - len_deg B) B))))
  = ((Z_to_int (plead B))%:~R : realalg) *: pol_to_polyralg A
    - ((Z_to_int (plead A))%:~R : realalg) *:
      ('X^(len_deg A - len_deg B) * pol_to_polyralg B).
Proof.
rewrite pol_to_polyralg_pnorm pol_to_polyralg_psub.
rewrite !pol_to_polyralg_pscale pol_to_polyralg_pshift.
by [].
Qed.

(* ------------------------------------------------------------------ *)
(*  Helpers and proof of `prem_rmodp_rat`.                              *)
(* ------------------------------------------------------------------ *)

Lemma pol_to_polyrat_pnorm_ne0 (p : pol) :
  pnorm p <> [::] -> pol_to_polyrat p != 0.
Proof.
move=> Hp.
rewrite -pol_to_polyrat_pnorm.
destruct (pnorm p) as [|x xs] eqn:HE; first by contradiction.
set fq := (fun z : Z => (Z_to_int z)%:~R : rat).
have HE2 : last x xs <> BinInt.Z0.
{ have Hlnz : forall l a bs,
    List.rev (drop_leading_zeros l) = a :: bs ->
    last a bs <> BinInt.Z0.
  { move=> l; elim: l => [//|b l' IHl] a bs /=.
    case Hb : (Z.eqb b 0); first exact: IHl.
    move/Z.eqb_neq in Hb.
    move=> Heq. suff : last a bs = b by move=> ->.
    move: Heq; rewrite /=.
    case Hl : (List.rev l') => [|h t].
    - by move=> [<- <-] /=.
    - by move=> [<- Hbs]; rewrite -Hbs last_cat. }
  have HE3 : List.rev (drop_leading_zeros (List.rev p))
           = x :: xs by rewrite -/pnorm -HE.
  exact: Hlnz _ _ _ HE3. }
have Hmap_last_nz : last 0 (List.map fq (x :: xs)) != 0.
{ have Hml : last 0 (List.map fq (x :: xs))
           = (Z_to_int (last x xs))%:~R.
  { clear -fq; elim: xs x => [//|y ys IH] x' /=; exact: IH. }
  rewrite Hml intr_eq0; apply/eqP => H0; apply: HE2.
  case: (last x xs) H0 => [//|q'|q']; rewrite /Z_to_int /=.
  - by move=> H; exfalso; have := Pos2Nat.is_pos q';
       case: (Pos.to_nat q') H => [|n] //= _;
       exact: (PeanoNat.Nat.lt_irrefl 0).
  - by case: (Pos.to_nat q') (Pos2Nat.is_pos q') => [|n] //=. }
apply/eqP => Habs.
have := PolyK Hmap_last_nz.
have Habs2 : Poly (List.map fq (x :: xs)) = 0.
{ move: Habs. rewrite /pol_to_polyrat /=. by []. }
rewrite Habs2 polyseq0. by [].
Qed.

Lemma redivp_rec_snd_indep (q : {poly rat}) (k1 k2 : nat)
  (qq1 qq2 r : {poly rat}) (n : nat) :
  (Pdiv.Ring.redivp_rec (R:=rat_rat__canonical__GRing_Field) q k1 qq1 r n).2
  = (Pdiv.Ring.redivp_rec (R:=rat_rat__canonical__GRing_Field) q k2 qq2 r n).2.
Proof.
elim: n r k1 k2 qq1 qq2 => [|n IH] r k1 k2 qq1 qq2 /=.
- by case: ifP.
- case: ifP => _; first by []. exact: IH.
Qed.

Lemma pol_to_polyrat_psub (p q : pol) :
  pol_to_polyrat (psub p q) = pol_to_polyrat p - pol_to_polyrat q.
Proof.
apply: (@map_poly_inj _ _ (ratr : {rmorphism rat -> realalg})).
rewrite rmorphB -!/(pol_to_polyralg _). exact: pol_to_polyralg_psub.
Qed.

Lemma pol_to_polyrat_pscale (c : Z) (p : pol) :
  pol_to_polyrat (pscale c p) = ((Z_to_int c)%:~R : rat) *: pol_to_polyrat p.
Proof.
apply: (@map_poly_inj _ _ (ratr : {rmorphism rat -> realalg})).
rewrite linearZ /= ratr_int -!/(pol_to_polyralg _). exact: pol_to_polyralg_pscale.
Qed.

Lemma pol_to_polyrat_pshift (k : nat) (p : pol) :
  pol_to_polyrat (pshift k p) = 'X^k * pol_to_polyrat p.
Proof.
apply: (@map_poly_inj _ _ (ratr : {rmorphism rat -> realalg})).
rewrite rmorphM /= map_polyXn -!/(pol_to_polyralg _). exact: pol_to_polyralg_pshift.
Qed.

Lemma lead_coef_pol_to_polyrat (p : pol) :
  lead_coef (pol_to_polyrat p) = ((Z_to_int (plead p))%:~R : rat).
Proof.
have H := lead_coef_pol_to_polyralg p. rewrite /pol_to_polyralg in H.
rewrite lead_coef_map /= in H.
have Hrhs : ((Z_to_int (plead p))%:~R : realalg) = ratr ((Z_to_int (plead p))%:~R : rat)
  by rewrite ratr_int.
rewrite Hrhs in H. move: H => /fmorph_inj. exact.
Qed.

Lemma length_pnorm_eq_size (p : pol) :
  List.length (pnorm p) = size (pol_to_polyrat p).
Proof.
rewrite -(pol_to_polyrat_pnorm p).
case Hl : (pnorm p) => [|x xs]; first by rewrite /pol_to_polyrat /= size_poly0.
set fq := (fun z : Z => (Z_to_int z)%:~R : rat).
suff Hmap_last_nz : last 0 (List.map fq (x :: xs)) != 0.
{ rewrite (_ : pol_to_polyrat (x :: xs) = Poly (List.map fq (x :: xs))); last by [].
  by rewrite (PolyK Hmap_last_nz) /= size_map. }
have HE2 : last x xs <> BinInt.Z0.
{ have Hlnz : forall l' a bs,
    List.rev (drop_leading_zeros l') = a :: bs ->
    last a bs <> BinInt.Z0.
  { move=> l'; elim: l' => [//|b l'' IHl] a bs /=.
    case Hb : (Z.eqb b 0); first exact: IHl.
    move/Z.eqb_neq in Hb.
    move=> Heq. suff : last a bs = b by move=> ->.
    move: Heq; rewrite /=.
    case Hl' : (List.rev l'') => [|h t].
    - by move=> [<- <-] /=.
    - by move=> [<- Hbs]; rewrite -Hbs last_cat. }
  have HE3 : List.rev (drop_leading_zeros (List.rev p)) = x :: xs
    by rewrite -Hl.
  exact: Hlnz _ _ _ HE3. }
have Hml : last 0 (List.map fq (x :: xs)) = (Z_to_int (last x xs))%:~R.
{ clear -fq; elim: xs x => [//|y ys IH] x' /=; exact: IH. }
rewrite Hml intr_eq0; apply/eqP => H0; apply: HE2.
case: (last x xs) H0 => [//|q'|q']; rewrite /Z_to_int /=.
- by move=> H; exfalso; have := Pos2Nat.is_pos q';
     case: (Pos.to_nat q') H => [|n] //= _;
     exact: (PeanoNat.Nat.lt_irrefl 0).
- by case: (Pos.to_nat q') (Pos2Nat.is_pos q') => [|n] //=.
Qed.

Lemma Nat_ltb_ltn (n m : nat) : Nat.ltb n m = (n < m)%N.
Proof.
case Hlt : (Nat.ltb n m).
- move/Nat.ltb_lt in Hlt. symmetry. apply/ltP. exact Hlt.
- symmetry. apply/negbTE/negP => /ltP Hm.
  have := proj2 (Nat.ltb_lt n m) Hm. by rewrite Hlt.
Qed.

Lemma prem_step_lift_rat (A B : pol) :
  pol_to_polyrat (prem_step A B) =
  pol_to_polyrat A * (lead_coef (pol_to_polyrat B))%:P
  - lead_coef (pol_to_polyrat A) *: 'X^(len_deg A - len_deg B) * pol_to_polyrat B.
Proof.
rewrite /prem_step pol_to_polyrat_pnorm pol_to_polyrat_psub.
rewrite !pol_to_polyrat_pscale pol_to_polyrat_pshift.
rewrite !lead_coef_pol_to_polyrat -mul_polyC.
rewrite mul_polyC scalerAl.
congr (_ - _).
{ by rewrite mulrC mul_polyC. }
Qed.

Lemma prem_rmodp_rat (p q : pol) :
  pnorm q <> [] ->
  pol_to_polyrat (prem p q)
  = Pdiv.Ring.rmodp (R:=rat_rat__canonical__GRing_Field)
      (pol_to_polyrat p) (pol_to_polyrat q).
Proof.
move=> Hq.
rewrite /Pdiv.Ring.rmodp /Pdiv.Ring.redivp unlock /Pdiv.Ring.redivp_expanded_def.
have Hqnz : pol_to_polyrat q != 0 := pol_to_polyrat_pnorm_ne0 q Hq.
rewrite (negbTE Hqnz).
rewrite /prem.
set A := pnorm p. set B := pnorm q.
have HBne : B <> [::] by exact: Hq.
destruct B as [|b0 bs] eqn:HBe; first by contradiction.
rewrite -(pol_to_polyrat_pnorm p) -/A.
rewrite -(pol_to_polyrat_pnorm q) -/B HBe.
have HAn : pnorm A = A by rewrite /A pnorm_idem.
have HBn : pnorm (b0 :: bs) = (b0 :: bs) by rewrite -HBe /B pnorm_idem.
have Hsize_A : List.length A = size (pol_to_polyrat A)
  by rewrite -length_pnorm_eq_size HAn.
rewrite -Hsize_A.
move: A HAn Hsize_A.
set Bq := (b0 :: bs).
have HBqsz : (0 < size (pol_to_polyrat Bq))%N.
{ rewrite lt0n size_poly_eq0 /Bq -HBe /B pol_to_polyrat_pnorm.
  exact: pol_to_polyrat_pnorm_ne0 _ Hq. }
have Hsize_Bq : List.length Bq = size (pol_to_polyrat Bq)
  by rewrite -length_pnorm_eq_size HBn.
have Hld_Bq : len_deg Bq = (size (pol_to_polyrat Bq)).-1
  by rewrite /len_deg -Hsize_Bq; case: (List.length Bq).
(* Strong induction on fuel; both prem_loop and redivp_rec use fuel *)
suff Hloop : forall fuel (A : pol),
  pnorm A = A ->
  List.length A = size (pol_to_polyrat A) ->
  (List.length A <= fuel)%coq_nat ->
  pol_to_polyrat
    (if Nat.ltb (len_deg A) (len_deg Bq) then A
     else prem_loop A Bq (S fuel))
  = (Pdiv.Ring.redivp_rec (R:=rat_rat__canonical__GRing_Field)
       (pol_to_polyrat Bq) 0 0 (pol_to_polyrat A) fuel).2.
{ move=> A0 HA0n HsA0. apply: (Hloop (List.length A0) A0 HA0n HsA0). lia. }
elim => [|fuel IHfuel] A0 HA0n HsA0 Hle.
- (* fuel = 0, so length A0 = 0, A0 = [] *)
  have HA00 : A0 = [::] by destruct A0 => //; simpl in Hle; lia.
  subst A0. rewrite /= /len_deg /=.
  case: (Nat.ltb 0 (len_deg Bq)).
  + rewrite /pol_to_polyrat /= size_poly0 HBqsz. by [].
  + rewrite /= /pol_to_polyrat /= size_poly0 HBqsz. by [].
- (* fuel = S fuel' *)
  destruct A0 as [|a0_hd a0_tl] eqn:HA0shape.
  { rewrite /= /len_deg /=.
    case: (Nat.ltb 0 (len_deg Bq)).
    + rewrite /pol_to_polyrat /= size_poly0 HBqsz. by [].
    + rewrite /= /pol_to_polyrat /= size_poly0 HBqsz. by []. }
  set AA := a0_hd :: a0_tl in HA0n HsA0 Hle |- *.
  have HAsz0 : (0 < size (pol_to_polyrat AA))%N by rewrite -HsA0 /AA /=.
  have Hld_AA : len_deg AA = (size (pol_to_polyrat AA)).-1
    by rewrite /len_deg -HsA0; case: (List.length AA).
  have Hld_cmp : (len_deg AA < len_deg Bq)%N
    = (size (pol_to_polyrat AA) < size (pol_to_polyrat Bq))%N.
  { rewrite Hld_AA Hld_Bq.
    move: HAsz0 HBqsz.
    case: (size (pol_to_polyrat AA)) => [//|sA] _.
    case: (size (pol_to_polyrat Bq)) => [//|sB] _.
    by []. }
  rewrite Nat_ltb_ltn Hld_cmp.
  have HlenAA : List.length AA = (List.length a0_tl).+1 by rewrite /AA /=.
  case Hlt : (size (pol_to_polyrat AA) < size (pol_to_polyrat Bq))%N.
  + by rewrite /= Hlt.
  + (* AA >= Bq: one step of prem_loop and redivp_rec *)
    rewrite /= Hlt.
    set A' := prem_step AA Bq.
    have HA'n : pnorm A' = A' by rewrite /A' /prem_step pnorm_idem.
    have HsA' : List.length A' = size (pol_to_polyrat A')
      by rewrite -length_pnorm_eq_size HA'n.
    (* Rewrite the RHS via redivp_rec_snd_indep to reset accumulators *)
    rewrite (redivp_rec_snd_indep _ _ 0 _ 0).
    have Hrstep2 : pol_to_polyrat A' =
      pol_to_polyrat AA * (lead_coef (pol_to_polyrat Bq))%:P -
      lead_coef (pol_to_polyrat AA) *:
      'X^(size (pol_to_polyrat AA) - size (pol_to_polyrat Bq)) *
      pol_to_polyrat Bq.
    { rewrite /A' prem_step_lift_rat.
      congr (_ - _ * _). congr (_ *: 'X^ _).
      rewrite Hld_AA Hld_Bq.
      move: HAsz0 HBqsz;
        case: (size (pol_to_polyrat AA)) => [//|sa] _;
        case: (size (pol_to_polyrat Bq)) => [//|sb] _ //. }
    rewrite -Hrstep2.
    (* Size decrease for IH application *)
    have Hle' : (List.length A' <= fuel)%coq_nat.
    { suff : (size (pol_to_polyrat A') < size (pol_to_polyrat AA))%N.
      { rewrite -HsA' -HsA0. move/ltP => ?. lia. }
      set rr := pol_to_polyrat AA.
      set qq := pol_to_polyrat Bq.
      rewrite Hrstep2.
      have HBqnz : qq != 0.
      { rewrite /qq /Bq -HBe /B pol_to_polyrat_pnorm.
        exact: pol_to_polyrat_pnorm_ne0 _ Hq. }
      have HAnz : rr != 0
        by rewrite /rr -size_poly_eq0; apply/eqP => HH;
           move: HAsz0; rewrite HH.
      have Hge : (size qq <= size rr)%N
        by move/negbT: Hlt; rewrite -leqNgt.
      have Hlcq_nz : lead_coef qq != 0 by rewrite lead_coef_eq0.
      have Hlcr_nz : lead_coef rr != 0 by rewrite lead_coef_eq0.
      set t1 := rr * (lead_coef qq)%:P.
      set t2 := lead_coef rr *: 'X^(_ - _) * qq.
      have Hcnz : (lead_coef qq)%:P != (0 : {poly rat})
        by rewrite polyC_eq0.
      have Hst1 : size t1 = size rr.
      { rewrite /t1 (size_mul HAnz Hcnz) size_polyC Hlcq_nz.
        by rewrite addn1. }
      have Hst2 : size t2 = size rr.
      { rewrite /t2 -scalerAl size_scale // (size_mul _ HBqnz);
          last by rewrite expf_neq0 // polyX_eq0.
        rewrite size_polyXn.
        move: HAsz0 HBqsz Hge;
          case: (size rr) => [//|sr] _;
          case: (size qq) => [//|sq] _;
          rewrite ltnS => Hle''.
        change (((sr - sq).+1 + sq.+1).-1 = sr.+1).
        rewrite addSn /= addnS subnK //. }
      have Hlc_eq : lead_coef t1 = lead_coef t2.
      { rewrite /t1 /t2 lead_coefM lead_coefC
                -scalerAl lead_coefZ lead_coefM lead_coefXn mul1r.
        by []. }
      rewrite -Hst1.
      apply: (leq_ltn_trans (n := (size t1).-1)).
      { apply/leq_sizeP => j Hj.
        rewrite coefB.
        case: (leqP (size t1) j) => Hjj.
        { have /leq_sizeP Ht1z := Hjj.
          rewrite (Ht1z j (leqnn _)).
          have Hjj2 : (size t2 <= j)%N by rewrite Hst2 -Hst1.
          have /leq_sizeP Ht2z := Hjj2.
          rewrite (Ht2z j (leqnn _)).
          by rewrite subrr. }
        { have Hjeq : j = (size t1).-1
            by apply/eqP; rewrite eqn_leq Hj /= -ltnS prednK ?Hjj // Hst1.
          subst j.
          have -> : t1`_(size t1).-1 = lead_coef t1 by rewrite lead_coefE.
          have -> : t2`_(size t1).-1 = lead_coef t2
            by rewrite lead_coefE Hst2 -Hst1.
          by rewrite Hlc_eq subrr. } }
      rewrite prednK ?Hst1 //. }
    (* Apply IH then show the prem_loop expressions match *)
    rewrite -(IHfuel A' HA'n HsA' Hle').
    congr (pol_to_polyrat _).
    rewrite Nat_ltb_ltn Hld_cmp Hlt.
    case Hlt' : (Nat.ltb (len_deg A') (len_deg Bq)).
    { by []. }
    rewrite /prem_loop -/prem_loop.
    destruct A' as [|a' atl'] eqn:HA'shape.
    { by case: (Nat.ltb _ _). }
    by rewrite Hlt'.
Qed.

Lemma prem_rmodp_eq (p q : pol) :
  pnorm q <> [] ->
  pol_to_polyralg (prem p q)
  = Pdiv.Ring.rmodp (pol_to_polyralg p) (pol_to_polyralg q).
Proof.
move=> Hq.
rewrite /pol_to_polyralg.
set pP := pol_to_polyrat p.
set pQ := pol_to_polyrat q.
have HNR : forall (r : {poly rat}),
  map_poly (rR:=realalg_realalg__canonical__GRing_NzSemiRing) ratr r
  = map_poly (rR:=realalg_realalg__canonical__GRing_NzRing) ratr r by [].
rewrite !HNR.
have Hmap := @redivp_map _ _ (ratr : {rmorphism rat -> realalg}) pP pQ.
have -> : Pdiv.Ring.rmodp (R:=realalg_realalg__canonical__GRing_NzRing)
  (map_poly (rR:=realalg_realalg__canonical__GRing_NzRing) ratr pP)
  (map_poly (rR:=realalg_realalg__canonical__GRing_NzRing) ratr pQ)
  = map_poly (rR:=realalg_realalg__canonical__GRing_NzRing) ratr
      (Pdiv.Ring.rmodp (R:=rat_rat__canonical__GRing_Field) pP pQ).
{ move: Hmap.
  rewrite Pdiv.Ring.redivp_def => [] [[] _ _ ->]. by []. }
congr (map_poly _).
exact: prem_rmodp_rat.
Qed.

Lemma next_mod_scaled_morph (p q : pol) :
  pnorm q <> [] ->
  exists k : realalg, (k != 0)%R /\
    pol_to_polyralg (next_mod p (pnorm q))
    = k *: qe_rcf_th.next_mod (pol_to_polyralg p)
                              (pol_to_polyralg (pnorm q)).
Proof.
move=> Hq.
set Q := pnorm q.
set P := pol_to_polyralg p.
set Ql := pol_to_polyralg Q.
set d := Pdiv.Ring.rscalp P Ql.
set lc_d := (lead_coef Ql ^+ d)%R.
have Hlc_nz : (lc_d != 0)%R := lc_expn_rscalp_neq0 P Ql.
rewrite /next_mod /qe_rcf_th.next_mod.
have HQnz : pnorm Q <> [::] by rewrite pnorm_idem.
rewrite pol_to_polyralg_pneg (prem_rmodp_eq _ _ HQnz)
        -/P -/Ql -/Q -/d -/lc_d.
have -> : Pdiv.Ring.rmodp (R:=realalg_realalg__canonical__Num_RealClosedField) P Ql
         = Pdiv.Ring.rmodp (R:=realalg_realalg__canonical__GRing_NzRing) P Ql
  by [].
set rm := Pdiv.Ring.rmodp (R:=realalg_realalg__canonical__GRing_NzRing) P Ql.
exists (lc_d^-1)%R; split; first by rewrite invr_eq0.
by rewrite scalerA mulrN mulVf // scaleN1r.
Qed.

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

