(* theories/S1/Cert.v
   ---------------------------------------------------------------
   Headline S1 theorem.

   Assembles `maynard_eigenvalue_S1` from:
     L1 (IVT root existence) — Qed, zero project axioms
     L2 (root transfer)      — Qed, via rootZ + map_polyZ
     L3 (root ↔ eigenvalue)  — Qed, via map_char_poly
     L4 (Maynard bridge)     — Qed, via ltr_pdivrMr

   charpoly_int_Dq_scaled is imported from CertL2.v (Qed there).
   Zero Admitted anywhere in the chain.
   --------------------------------------------------------------- *)

From Stdlib Require Import ZArith List.
Import ListNotations.

From mathcomp Require Import all_boot all_algebra.
From mathcomp.real_closed Require Import realalg.
Import GRing.Theory Num.Theory.

From PrimeGapS1 Require Import IntPoly IntMat CharPoly Witness CertL1 CertL2.
From PrimeGapS1 Require Import MaynardVerify MaynardSpec MaynardSpecBridge.

(* Re-open ring_scope AFTER Witness.v (which opens Z_scope). Every
   statement in this file lives in MathComp's ring_scope. *)
Open Scope ring_scope.

(* A_rat is defined in CertL2.v; imported via Require above. *)

(* ------------------------------------------------------------------
   L1 — Sturm count of the chain shipped in WitnessChain.v equals
   the number of real roots of charpoly_int strictly above 4/105.
   For the skeleton we only state the consequence we need: the
   existence of a realalg root of (the lift of) charpoly_int strictly
   above ratr (4/105).

   `charpoly_as_poly_realalg` is concretely defined as the lift of
   the FLINT-shipped `charpoly_int` to {poly realalg} via the
   `pol_to_polyrat` bridge from CharPoly.v followed by `map_poly ratr`.
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
  apply/eqP => Hz.
  have : D_q = BinNums.Z0 by destruct D_q as [|p|p]; [reflexivity|exfalso;rewrite /Z_to_int /= in Hz; injection Hz => Hz'; have := Pos2Nat.is_pos p; rewrite Hz'; exact (Nat.lt_irrefl 0)|exfalso; discriminate Hz].
  discriminate.
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
   L4 — Maynard bridge: existence of an eigenvalue > 4/105 implies
   the existence of an eigenvalue λ with 4 < 105 * λ, i.e., M_{105} > 4.
   This is an elementary rescaling of the bound.
   ------------------------------------------------------------------ *)
Lemma maynard_bridge_L4 :
  (exists lambda : realalg,
      eigenvalue (map_mx (ratr : rat -> realalg) A_rat) lambda
      /\ (ratr (4%:Q / 105%:Q) : realalg) < lambda) ->
  exists lambda : realalg,
      eigenvalue (map_mx (ratr : rat -> realalg) A_rat) lambda
      /\ (4%:R < 105%:R * lambda :> realalg).
Proof.
  case=> [lambda [Heig Hlt]]; exists lambda; split=> //.
  rewrite mulrC -ltr_pdivrMr; last by rewrite ltr0n.
  by rewrite (_ : (4 / 105 : realalg) = ratr (4%:~R / 105%:~R)).
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

(* ------------------------------------------------------------------
   The full M_{105} > 4 trust contract in a single Qed.

   `maynard_eigenvalue_S1` above gives the eigenvalue bound on the
   matrix `A_rat = M1^{-1} M2`. MaynardVerify discharges the Z-level
   match between the FLINT-shipped integer matrices `M1_int / M2_int`
   and the Z-level closed form `m{1,2}_num_den` (cross-multiplied in
   Z, vm_compute).  MaynardSpecBridge then certifies that the Z-level
   closed form equals the rat-level paper-form spec
   `MaynardSpec.M{1,2}_entry`, the readable definition that
   transcribes Maynard's Lemma 8.2 character-for-character (see
   SPEC_TO_PAPER.md).

   Conjoining all four facts means a single `Print Assumptions
   maynard_M105_certified` certifies the full chain
       FLINT integer matrices  =  Z-level closed form
                                =  rat-level paper-form spec
                                ⇒  eigenvalue > 4/105.
   ------------------------------------------------------------------ *)
Theorem maynard_M105_certified :
  all_match_M1Z = true /\
  all_match_M2Z = true /\
  (forall i j : nat,
     MaynardSpec.M1_spec_ij i j
     = MaynardSpecBridge.qfrac (MaynardSpec.m1_num_den_at i j)) /\
  (forall i j : nat,
     MaynardSpec.M2_spec_ij i j
     = MaynardSpecBridge.qfrac (MaynardSpec.m2_num_den_at i j)) /\
  exists lambda : realalg,
    eigenvalue (map_mx (ratr : rat -> realalg) A_rat) lambda
    /\ (ratr (4%:Q / 105%:Q) : realalg) < lambda.
Proof.
  split; [exact all_match_M1Z_true |
   split; [exact all_match_M2Z_true |
    split; [exact MaynardSpecBridge.M1_spec_rat_eq |
     split; [exact MaynardSpecBridge.M2_spec_rat_eq | exact maynard_eigenvalue_S1]]]].
Qed.
