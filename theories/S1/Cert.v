(* theories/S1/Cert.v
   ---------------------------------------------------------------
   Headline S1 theorem.

   Assembles `maynard_eigenvalue_S1` from:
     L1 (IVT root existence) — Qed, zero project axioms
     L2 (root transfer)      — Qed, via rootZ + map_polyZ
     L3 (root ↔ eigenvalue)  — Qed, via map_char_poly

   charpoly_int_Dq_scaled is imported from CertL2.v (Qed there).
   Zero Admitted anywhere in the chain.
   --------------------------------------------------------------- *)

From Stdlib Require Import ZArith List.
Import ListNotations.

From mathcomp Require Import all_boot all_algebra.
From mathcomp.real_closed Require Import realalg.
Import GRing.Theory Num.Theory.

From PrimeGapS1 Require Import IntMat CharPoly Witness CertL1 CertL2.
From PrimeGapS1 Require Import MaynardVerify MaynardSpec MaynardSpecBridge.
From PrimeGapS1.MaynardVerify Require Import Def.

(* Re-open ring_scope AFTER Witness.v (which opens Z_scope). Every
   statement in this file lives in MathComp's ring_scope. *)
Open Scope ring_scope.

(* A_rat is defined in CertL2.v; imported via Require above. *)

(* ------------------------------------------------------------------
   L1 — an IVT (intermediate value theorem) argument on charpoly_int
   produces a realalg root strictly above ratr (4/105). The proof
   reads two vm_compute sign Qeds on charpoly_int directly
   (sign_at_rat 4 105 = -1, sign_at_pinf = 1) and feeds them to
   mathcomp-real-closed's `poly_ivtoo`.

   `charpoly_as_poly_realalg` is concretely defined as the lift of
   the FLINT-shipped `charpoly_int` to {poly realalg} via the
   `pol_to_polyrat` bridge from CharPoly.v followed by `map_poly ratr`.

   The lemma below is kept under the legacy name `sturm_count_correct`
   for downstream callers; its statement is purely "there exists a
   root > 4/105", and the proof is the IVT-based `maynard_L1_concrete`.
   ------------------------------------------------------------------ *)
Definition charpoly_as_poly_realalg : {poly realalg} :=
  map_poly (ratr : rat -> realalg) (pol_to_polyrat charpoly_int).

Lemma sturm_count_correct :
  exists lambda : realalg,
    root charpoly_as_poly_realalg lambda
    /\ (ratr (4%:Q / 105%:Q) : realalg) < lambda.
Proof. exact maynard_L1_concrete. Qed.

(* charpoly_int_Dq_scaled: imported from CertL2.v (Qed). *)

(* ------------------------------------------------------------------
   L2 — root transfer (Qed): a root of the shipped polynomial is also
   a root of `char_poly A_rat`.

   Proof: pol_to_polyrat charpoly_int = D_q *: char_poly A_rat
   (charpoly_int_Dq_scaled), so after map_poly ratr and rootZ with
   D_q != 0, roots are preserved.
   ------------------------------------------------------------------ *)
Lemma charpoly_root_transfer (lambda : realalg) :
  root charpoly_as_poly_realalg lambda ->
  root (map_poly (ratr : rat -> realalg) (char_poly A_rat)) lambda.
Proof.
  rewrite /charpoly_as_poly_realalg charpoly_int_Dq_scaled map_polyZ rootZ //.
  rewrite /ratr fmorph_eq0 intr_eq0.
  by apply: Z_to_int_neq0'; discriminate.
Qed.

(* ------------------------------------------------------------------
   L3 — "root of char poly" ↔ "eigenvalue". In the real proof this
   will be a one-liner combining `eigenvalue_root_char` with
   `map_char_poly`. We state it as the precise equivalence we use.
   ------------------------------------------------------------------ *)
Lemma eigenvalue_of_root_realalg (lambda : realalg) :
  root (map_poly (ratr : rat -> realalg) (char_poly A_rat)) lambda ->
  eigenvalue (map_mx (ratr : rat -> realalg) A_rat) lambda.
Proof.
  rewrite (map_char_poly (ratr : {rmorphism rat -> realalg})).
  by rewrite eigenvalue_root_char.
Qed.

(* ------------------------------------------------------------------
   The headline S1 theorem. Proof assembles L1, L2, L3.

   Note: the assembly is itself elementary — destruct L1, rewrite
   by L2, apply L3 — so we give it explicitly as tactics below.
   This is NOT a heavy proof; it is the contract of the S1 layer.
   ------------------------------------------------------------------ *)
Theorem maynard_eigenvalue_S1 :
  exists lambda : realalg,
    eigenvalue (map_mx (ratr : rat -> realalg) A_rat) lambda
    /\ (ratr (4%:Q / 105%:Q) : realalg) < lambda.
Proof.
  (* L1: get a realalg root of charpoly_as_poly_realalg above 4/105. *)
  destruct sturm_count_correct as [lambda [Hroot Hgt]].
  exists lambda; split; [| exact Hgt].
  (* L2: transfer root from shipped polynomial to char_poly A_rat. *)
  apply eigenvalue_of_root_realalg.
  exact (charpoly_root_transfer lambda Hroot).
Qed.

(* ==================================================================
   Headline trust contract: paper-form spec equals FLINT-shipped
   integer matrix, plus the eigenvalue bound.

   The bridge from the FLINT integer matrices `M1_int / M2_int` to
   the readable rat-level paper-form spec `MaynardSpec.M{1,2}_spec_ij`
   factors through a Z-level "computation-friendly" twin
   `m{1,2}_num_den_at`:

     M{1,2}_spec_ij   =   qfrac (m{1,2}_num_den_at)      [Qed, no Uint63]
                          via MaynardSpecBridge.M{1,2}_spec_rat_eq

     qfrac (m{1,2}_num_den_at)  =  M{1,2}_int[i,j] / D_M{1,2}
                          via the Z-level cross-multiplication
                          discharged by all_match_M{1,2}Z = true.

   The headline theorem `maynard_M105_certified` exposes the COMPOSED
   identity directly:
     M1_spec_ij i j  =  (mat_get M1_int i j) / D_M1     (as rat)
     M2_spec_ij i j  =  (mat_get M2_int i j) / D_M2
   plus the eigenvalue bound.  The Z-level checks
   `all_match_M{1,2}Z = true` move into the proof body as
   implementation steps; they remain available as standalone Qeds in
   MaynardVerify.v for anyone curious about *how* the verification
   proceeds.
   ================================================================== *)

(* ------------------------------------------------------------------
   Per-matrix rat-level identity: paper-form spec entry equals FLINT
   integer entry over the common denominator.

   Composes:
     - MaynardSpecBridge.M{1,2}_spec_rat_eq  (rat = qfrac of Z-pair)
     - MaynardVerify.M{1,2}_entry_match_in_grid  (per-entry from grid)
     - MaynardSpecBridge.qfrac_eq_div  (Z cross-mult -> rat division)
     - MaynardSpecBridge.{D_M{1,2}_pos, m{1,2}_num_den_at_den_pos}
   ------------------------------------------------------------------ *)

Lemma D_M1_pos : Z.lt 0 D_M1. Proof. by vm_compute. Qed.
Lemma D_M2_pos : Z.lt 0 D_M2. Proof. by vm_compute. Qed.

(* `Opaque` is re-declared here (does not propagate via Require) so
   the unifier doesn't expand `mat_get M{1,2}_int` during proofs that
   touch the per-entry booleans. *)
Opaque M1_entry_matchZ M2_entry_matchZ.

Lemma M1_spec_eq_int {i j} :
  (i < 42)%nat -> (j < 42)%nat ->
  M1_spec_ij i j = Z2rat (mat_get M1_int i j) / Z2rat D_M1.
Proof.
  move=> Hi Hj.
  rewrite M1_spec_rat_eq.
  have Hmatch : M1_entry_matchZ i j = true := M1_entry_match_in_grid Hi Hj.
  rewrite M1_entry_matchZ_E in Hmatch.
  move/Z.eqb_eq: Hmatch => Hcross.
  rewrite [m1_num_den_at i j]surjective_pairing.
  by apply: qfrac_eq_div;
    [exact: m1_num_den_at_den_pos | exact: D_M1_pos | exact: Hcross].
Qed.

Lemma M2_spec_eq_int {i j} :
  (i < 42)%nat -> (j < 42)%nat ->
  M2_spec_ij i j = Z2rat (mat_get M2_int i j) / Z2rat D_M2.
Proof.
  move=> Hi Hj.
  rewrite M2_spec_rat_eq.
  have Hmatch : M2_entry_matchZ i j = true := M2_entry_match_in_grid Hi Hj.
  rewrite M2_entry_matchZ_E in Hmatch.
  move/Z.eqb_eq: Hmatch => Hcross.
  rewrite [m2_num_den_at i j]surjective_pairing.
  by apply: qfrac_eq_div;
    [exact: m2_num_den_at_den_pos | exact: D_M2_pos | exact: Hcross].
Qed.

(* ------------------------------------------------------------------
   The headline theorem: two readable identities (paper-form spec =
   FLINT integer entry / common denominator) plus the eigenvalue
   bound.  The Z-level boolean checks `all_match_M{1,2}Z = true` and
   the rat<->Z bridges `M{1,2}_spec_rat_eq` are implementation
   details of the proof; they remain available as standalone Qeds in
   MaynardVerify and MaynardSpecBridge for auditors who want to
   trace the chain step-by-step.
   ------------------------------------------------------------------ *)
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

(* The S1 eigenvalue bound, rescaled from (A_rat, 4/105) to (M105, 4):
   if mu is an eigenvalue of A_rat above 4/105, then 105*mu is an
   eigenvalue of M105 = 105 *: A_rat above 4.  Pure realalg arithmetic. *)
Lemma maynard_eigenvalue_S1_M105 :
  exists lambda : realalg,
    eigenvalue (map_mx (ratr : rat -> realalg) M105) lambda /\ (4 < lambda).
Proof.
have [mu [Heig Hgt]] := maynard_eigenvalue_S1.
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
   The headline theorem, in the main-branch shape: the closed-form
   trust contract `matches_closed_forms M105` plus a real eigenvalue
   of M105 strictly above 4.  Stated over realalg (the real-closed
   field this IVT route lives in); the eigenvalue is genuinely real.
   ------------------------------------------------------------------ *)
Theorem maynard_M105_certified :
  matches_closed_forms M105 /\
  exists lambda : realalg,
    eigenvalue (map_mx (ratr : rat -> realalg) M105) lambda /\ (4 < lambda).
Proof.
split; [exact: matches_closed_forms_M105 | exact: maynard_eigenvalue_S1_M105].
Qed.
