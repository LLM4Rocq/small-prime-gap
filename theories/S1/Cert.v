(* theories/S1/Cert.v
   ---------------------------------------------------------------
   Headline S1 theorem — architecture skeleton.

   Purpose: state `maynard_eigenvalue_S1` (the §1 target of
   PLAN_S1.md) and its proof scaffold using the four bridge
   lemmas L1 (Sturm count), L2 (char_poly_int = char_poly),
   L3 (root ↔ eigenvalue), L4 (Maynard bridge). All load-bearing
   pieces are `Admitted` so that the S1 architecture type-checks
   end-to-end before the heavy proofs are written.

   Do NOT prove these lemmas here. This file is the contract the
   rest of the S1 pipeline compiles against.
   --------------------------------------------------------------- *)

From Stdlib Require Import ZArith List.
Import ListNotations.

From mathcomp Require Import all_boot all_algebra.
From mathcomp.real_closed Require Import realalg.
Import GRing.Theory Num.Theory.

From PrimeGapS1 Require Import IntPoly IntMat CharPoly Witness.

(* Re-open ring_scope AFTER Witness.v (which opens Z_scope). Every
   statement in this file lives in MathComp's ring_scope. *)
Open Scope ring_scope.

(* ------------------------------------------------------------------
   A_rat : the Maynard 42×42 rational matrix A := M1^{-1} * M2.
   Concretely defined via `mat_int_to_rat` from CharPoly.v on the
   integer-cleared data shipped by Witness.v.

   Note: `invmx` is total in MathComp — it returns 0 if the input
   is not invertible. The hypothesis `M1_rat \in unitmx` is needed
   only for downstream proofs that require the inverse to actually
   be a left/right inverse; the headline existence theorem does
   NOT use it (the assumption set of `maynard_eigenvalue_S1` does
   not include `A_rat_unitmx`).
   ------------------------------------------------------------------ *)
Definition A_rat : 'M[rat]_42 :=
  ((invmx (mat_int_to_rat M1_int D_M1 42))
     *m mat_int_to_rat M2_int D_M2 42)%R.

(* The SPD hypothesis M1 \in unitmx, required by invmx to make sense.
   Will be discharged by a `vm_compute`-free integer determinant check
   when the real definition of A_rat lands. *)
Lemma A_rat_unitmx : A_rat \in unitmx.
Admitted.

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
Admitted.

(* ------------------------------------------------------------------
   L2 — the integer-cleared shipped polynomial equals `char_poly A_rat`
   after lifting to realalg. The precise equational form (with the
   D^n scaling) lives in CharPoly.v (char_poly_int_correct). Here we
   only state the lifted version we actually need to chain L1 → L3. *)
Lemma charpoly_int_eq_charpoly :
  charpoly_as_poly_realalg
  = map_poly (ratr : rat -> realalg) (char_poly A_rat).
Admitted.

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
  (* L2: rewrite root ... into root of the lifted `char_poly A_rat`. *)
  apply eigenvalue_of_root_realalg.
  rewrite -charpoly_int_eq_charpoly.
  exact Hroot.
Qed.
