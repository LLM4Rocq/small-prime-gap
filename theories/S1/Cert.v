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

(* Z embedded into rat via Z_to_int. *)
Definition zrat (z : Z) : rat := (Z_to_int z)%:~R.

(* ------------------------------------------------------------------
   Step 1 — denominator positivity.  D_M{1,2} are concrete positive
   Z; m{1,2}_num_den_at denominators are products of factorials.
   ------------------------------------------------------------------ *)

Lemma D_M1_pos : Z.lt 0 D_M1. Proof. vm_compute. reflexivity. Qed.
Lemma D_M2_pos : Z.lt 0 D_M2. Proof. vm_compute. reflexivity. Qed.

Lemma m1_num_den_den_pos bi ci bj cj :
  Z.lt 0 (m1_num_den bi ci bj cj).2.
Proof. exact: factZ_pos. Qed.

Lemma m1_num_den_at_den_pos i j : Z.lt 0 (m1_num_den_at i j).2.
Proof. exact: m1_num_den_den_pos. Qed.

Lemma qplus_den_pos (a b : Z * Z) :
  Z.lt 0 a.2 -> Z.lt 0 b.2 -> Z.lt 0 (qplus a b).2.
Proof.
  case: a => [na da]; case: b => [nb db] /= Ha Hb.
  exact: Z.mul_pos_pos.
Qed.

Lemma fold_left_qplus_den_pos {T : Type} (l : list T)
      (g : T -> Z * Z) (acc : Z * Z) :
  Z.lt 0 acc.2 ->
  (forall x, Z.lt 0 (g x).2) ->
  Z.lt 0 (List.fold_left (fun a x => qplus a (g x)) l acc).2.
Proof.
  elim: l acc => [//|x xs IH] acc Hacc Hg.
  apply: IH; [|exact: Hg].
  exact: qplus_den_pos Hacc (Hg x).
Qed.

Lemma m2_term_num_den_den_pos bi ci bj cj cp1 cp2 :
  Z.lt 0 (m2_term_num_den bi ci bj cj cp1 cp2).2.
Proof.
  apply: Z.mul_pos_pos; last exact: factZ_pos.
  apply: Z.mul_pos_pos; exact: factZ_pos.
Qed.

Lemma m2_num_den_den_pos bi ci bj cj :
  Z.lt 0 (m2_num_den bi ci bj cj).2.
Proof.
  rewrite /m2_num_den.
  have Hloop : forall (l : list nat) (acc : Z * Z),
    Z.lt 0 acc.2 ->
    Z.lt 0 (List.fold_left
            (fun a cp1 => List.fold_left
                            (fun b cp2 => qplus b
                              (m2_term_num_den bi ci bj cj cp1 cp2))
                            (List.seq 0 (S cj)) a)
            l acc).2.
  { elim => [//|cp1 cp1_rest IH] acc Hacc.
    apply: IH.
    apply: fold_left_qplus_den_pos => // cp2.
    exact: m2_term_num_den_den_pos. }
  apply: Hloop. by [].
Qed.

Lemma m2_num_den_at_den_pos i j : Z.lt 0 (m2_num_den_at i j).2.
Proof. exact: m2_num_den_den_pos. Qed.

(* ------------------------------------------------------------------
   Step 2 — extract a per-entry boolean from the 42x42-grid forallb.

   `Opaque M1_entry_matchZ M2_entry_matchZ` is necessary: the unifier
   would otherwise try to delta-reduce the per-entry boolean into the
   underlying `mat_get M1_int` call, expanding the 1764-cell FLINT
   matrix and exhausting memory.
   ------------------------------------------------------------------ *)

Lemma forallb_seq_in (n : nat) (f : nat -> bool) (i : nat) :
  List.forallb f (List.seq 0 n) = true ->
  (i < n)%nat -> f i = true.
Proof.
  move=> H Hi.
  rewrite -> List.forallb_forall in H.
  apply: H.
  apply: (proj2 (List.in_seq n 0 i)).
  split; [apply: Nat.le_0_l | apply/ltP; exact: Hi].
Qed.

Opaque M1_entry_matchZ M2_entry_matchZ.

Lemma M1_entry_match_in_grid i j :
  (i < 42)%nat -> (j < 42)%nat ->
  M1_entry_matchZ i j = true.
Proof.
  move=> Hi Hj.
  have HM := all_match_M1Z_true.
  rewrite /all_match_M1Z in HM.
  have H1 : forallb (M1_entry_matchZ i) (List.seq 0 42) = true.
  { exact: (@forallb_seq_in 42 _ i HM Hi). }
  exact: (@forallb_seq_in 42 _ j H1 Hj).
Qed.

Lemma M2_entry_match_in_grid i j :
  (i < 42)%nat -> (j < 42)%nat ->
  M2_entry_matchZ i j = true.
Proof.
  move=> Hi Hj.
  have HM := all_match_M2Z_true.
  rewrite /all_match_M2Z /M2_check_rows in HM.
  have H1 : forallb (M2_entry_matchZ i) (List.seq 0 42) = true.
  { exact: (@forallb_seq_in 42 _ i HM Hi). }
  exact: (@forallb_seq_in 42 _ j H1 Hj).
Qed.

(* ------------------------------------------------------------------
   Step 3 — cross-multiplication identity in Z lifts to rat equality
   between qfrac (a, b) and c / d.
   ------------------------------------------------------------------ *)

Lemma qfrac_eq_div (a b c d : Z) :
  Z.lt 0 b -> Z.lt 0 d ->
  BinInt.Z.mul a d = BinInt.Z.mul c b ->
  qfrac (a, b) = zrat c / zrat d.
Proof.
  move=> Hb Hd Heq.
  rewrite /qfrac /zrat /=.
  have Hbz : ((Z_to_int b)%:~R : rat) != 0 by exact: Z_to_int_pos_rat_neq0.
  have Hdz : ((Z_to_int d)%:~R : rat) != 0 by exact: Z_to_int_pos_rat_neq0.
  apply/eqP. rewrite eqr_div //.
  by rewrite -!intrM -!Z_to_int_mul Heq.
Qed.

(* ------------------------------------------------------------------
   Step 4 — the per-matrix rat-level identity.
   ------------------------------------------------------------------ *)

Lemma M1_spec_match_FLINT i j :
  (i < 42)%nat -> (j < 42)%nat ->
  M1_spec_ij i j = zrat (mat_get M1_int i j) / zrat D_M1.
Proof.
  move=> Hi Hj.
  rewrite (M1_spec_rat_eq i j).
  have Hentry := M1_entry_match_in_grid i j Hi Hj.
  Transparent M1_entry_matchZ.
  rewrite /M1_entry_matchZ in Hentry.
  Opaque M1_entry_matchZ.
  move/Z.eqb_eq: Hentry => Hcross.
  rewrite [m1_num_den_at i j]surjective_pairing.
  apply: qfrac_eq_div.
  - exact: m1_num_den_at_den_pos.
  - exact: D_M1_pos.
  - exact: Hcross.
Qed.

Lemma M2_spec_match_FLINT i j :
  (i < 42)%nat -> (j < 42)%nat ->
  M2_spec_ij i j = zrat (mat_get M2_int i j) / zrat D_M2.
Proof.
  move=> Hi Hj.
  rewrite (M2_spec_rat_eq i j).
  have Hentry := M2_entry_match_in_grid i j Hi Hj.
  Transparent M2_entry_matchZ.
  rewrite /M2_entry_matchZ in Hentry.
  Opaque M2_entry_matchZ.
  move/Z.eqb_eq: Hentry => Hcross.
  rewrite [m2_num_den_at i j]surjective_pairing.
  apply: qfrac_eq_div.
  - exact: m2_num_den_at_den_pos.
  - exact: D_M2_pos.
  - exact: Hcross.
Qed.

(* ------------------------------------------------------------------
   The headline theorem.  Two readable identities (paper-form spec =
   FLINT integer entry / common denominator) plus the eigenvalue
   bound.  The Z-level boolean check `all_match_M{1,2}Z = true` and
   the rat<->Z bridge `M{1,2}_spec_rat_eq` move into the proof body;
   they remain available as standalone Qeds.
   ------------------------------------------------------------------ *)
Theorem maynard_M105_certified :
  (forall i j : nat, (i < 42)%nat -> (j < 42)%nat ->
     M1_spec_ij i j = zrat (mat_get M1_int i j) / zrat D_M1) /\
  (forall i j : nat, (i < 42)%nat -> (j < 42)%nat ->
     M2_spec_ij i j = zrat (mat_get M2_int i j) / zrat D_M2) /\
  exists lambda : realalg,
    eigenvalue (map_mx (ratr : rat -> realalg) A_rat) lambda
    /\ (ratr (4%:Q / 105%:Q) : realalg) < lambda.
Proof.
  split; first exact: M1_spec_match_FLINT.
  split; first exact: M2_spec_match_FLINT.
  exact: maynard_eigenvalue_S1.
Qed.
