(* ==================================================================
   CRTPencilCheckExt.v

   Lift the pencil per-prime modular agreement over the 1210-prime
   set `crt_primes_pencil` (710 mainline + 500 extras) to a closed
   Z-equality between `D_pencil_int` (computed via fl_loop on
   `pencil_mat_int`) and `D_pencil_int_value` (shipped FLINT
   literal).

   The original `CRTPencilCheck.v` provides this for `det_M1_int`
   (using the 710-prime CRT product, which suffices for the 2044-bit
   M1 determinant).  Here we extend to `D_pencil_int` over the
   larger `crt_primes_pencil` product (~32500 bits, > 2 *
   |D_pencil_int_value|).
   ================================================================== *)

From Stdlib Require Import ZArith List Lia Bool Znumtheory.
Import ListNotations.
From Stdlib Require Import Uint63.

From mathcomp Require Import all_ssreflect.

From PrimeGapS1 Require Import IntMat IntPoly Witness CharPoly.
From PrimeGapS1 Require Import ModularArith CRTBridge CRTCheck CRTLift Fermat PrimeCheck.
From PrimeGapS1 Require Import AllRowsLenHelper.
From PrimeGapS1.CharPolyAgree Require Import Def.
From PrimeGapS1 Require Import Witness_PencilDet.
From PrimeGapS1 Require Import CertL2 CertPencilDef.
From PrimeGapS1 Require Import CRTPencilExtraPrimes.
From PrimeGapS1 Require Import CRTPencilExtra_PrimesProof.   (* extra_prime_at *)
From PrimeGapS1 Require Import CRTPencilExtraPrimesProof.    (* NoDup, valid, gt_43, product *)
From PrimeGapS1 Require Import CRTPencilExtraChecksProof.
From PrimeGapS1 Require Import CRTPencilChecksProof.   (* check_pencil_det_at *)
From PrimeGapS1 Require Import CRTPencilCheck.   (* mod_eq_to_divide, per_prime_div_pencil for 710 *)
From PrimeGapS1 Require Import CRTPencilPencilBound.

Open Scope Z_scope.

(* ================================================================== *)
(*  Per-prime modular agreement for the 500 EXTRA primes.              *)
(*  Same shape as `per_prime_mod_eq_pencil` in CRTPencilCheck.v but    *)
(*  parameterised on `crt_primes_pencil_valid` for primes in           *)
(*  crt_primes_pencil_extra.                                           *)
(* ================================================================== *)

Strategy opaque [char_poly_mod char_poly_int pencil_mat_int
                 fl_loop fl_mod_loop meye mzero
                 reduce_mat_Z fl_all_divisible].

Lemma per_prime_mod_eq_pencil_extra (p : Uint63.int) (Hin : In p crt_primes_pencil_extra) :
  List.map (Z_to_mod63 p) (char_poly_int pencil_mat_int) = char_poly_mod p pencil_mat_int.
Proof.
  have Hp_pencil : In p crt_primes_pencil
    by unfold crt_primes_pencil; apply List.in_or_app; right; exact Hin.
  apply char_poly_mod_sound.
  - exact (crt_primes_pencil_valid p Hp_pencil).
  - change (List.length pencil_mat_int) with (mat_dim pencil_mat_int).
    rewrite pencil_mat_int_dim.
    split; [exact pencil_mat_int_dim |
            exact (fun i Hi => pencil_mat_int_wf i Hi)].
  - change (List.length pencil_mat_int) with (mat_dim pencil_mat_int).
    rewrite pencil_mat_int_dim.
    have H43 := proj1 (Z.ltb_lt _ _) (extra_gt_43_at p Hin).
    apply Z.ltb_lt. lia.
  - change (List.length pencil_mat_int) with (mat_dim pencil_mat_int).
    rewrite pencil_mat_int_dim.
    apply fl_all_divisible_from_L2;
      [exact pencil_mat_int_dim |
       exact (fun i Hi => pencil_mat_int_wf i Hi)].
  - intros j Hj.
    have Hvp : valid_prime p := crt_primes_pencil_valid p Hp_pencil.
    have Hprime_nat : prime (Z.to_nat (Uint63.to_Z p)).
    { have Hcheck := extra_prime_at p Hin.
      exact (check_prime_Z_mc _ Hcheck). }
    apply fermat_Z; [case: Hvp; tauto | exact Hprime_nat | exact Hj].
Qed.

(* ================================================================== *)
(*  Per-prime divisibility for D_pencil_int over the 500 EXTRA primes  *)
(*  (same mod_eq_to_divide path as `per_prime_div_pencil` in           *)
(*  CRTPencilCheck.v).                                                 *)
(* ================================================================== *)

Lemma per_prime_div_pencil_extra (p : Uint63.int) :
  In p crt_primes_pencil_extra ->
  (Uint63.to_Z p | (D_pencil_int - D_pencil_int_value))%Z.
Proof.
  intros Hin.
  have Hp_pencil : In p crt_primes_pencil
    by unfold crt_primes_pencil; apply List.in_or_app; right; exact Hin.
  have Hagree : check_pencil_det_at p = true := check_pencil_det_extra_at p Hin.
  apply Uint63.eqb_spec in Hagree.
  have Hvp : valid_prime p := crt_primes_pencil_valid p Hp_pencil.
  have Hsound : List.map (Z_to_mod63 p) (char_poly_int pencil_mat_int)
              = char_poly_mod p pencil_mat_int
    := per_prime_mod_eq_pencil_extra p Hin.
  have HH : List.nth 0 (char_poly_mod p pencil_mat_int) 0%uint63
          = Z_to_mod63 p (List.nth 0 (char_poly_int pencil_mat_int) 0%Z).
  { rewrite -(Z_to_mod63_zero p Hvp) -Hsound. apply List.map_nth. }
  have Heq_mod_u : Z_to_mod63 p (List.nth 0 (char_poly_int pencil_mat_int) 0%Z)
                 = Z_to_mod63 p D_pencil_int_value.
  { transitivity (List.nth 0 (char_poly_mod p pencil_mat_int) 0%uint63);
    [exact (Logic.eq_sym HH) | exact Hagree]. }
  rewrite D_pencil_int_eq_nth.
  exact (mod_eq_to_divide p _ _ Hvp Heq_mod_u).
Qed.

Lemma per_prime_div_pencil_ext (p : Uint63.int) :
  In p crt_primes_pencil ->
  (Uint63.to_Z p | (D_pencil_int - D_pencil_int_value))%Z.
Proof.
  intros Hin. unfold crt_primes_pencil in Hin. apply List.in_app_or in Hin.
  destruct Hin as [Hin1|Hin2].
  - exact (per_prime_div_pencil p Hin1).
  - exact (per_prime_div_pencil_extra p Hin2).
Qed.

(* ================================================================== *)
(*  Assembly: D_pencil_int = D_pencil_int_value via small_multiple_zero. *)
(* ================================================================== *)

(* crt_primes_pencil_710 NoDup follows from crt_primes_pencil_NoDup. *)
Lemma crt_primes_pencil_NoDup_at_Z :
  NoDup (List.map Uint63.to_Z crt_primes_pencil).
Proof. exact crt_primes_pencil_NoDup. Qed.

Theorem D_pencil_int_eq : D_pencil_int = D_pencil_int_value.
Proof.
  cut ((D_pencil_int - D_pencil_int_value)%Z = 0%Z); [lia|].
  apply (small_multiple_zero _ crt_product_pencil).
  - unfold crt_product_pencil.
    apply all_primes_divide_product.
    + exact crt_primes_pencil_NoDup.
    + exact crt_primes_pencil_all_prime.
    + intros pz Hpz. apply List.in_map_iff in Hpz.
      destruct Hpz as [p [Hpeq Hin]]. subst pz.
      exact (per_prime_div_pencil_ext p Hin).
  - exact crt_product_pencil_pos.
  - apply Z.le_lt_trans with
      (2 * fl_coeff_bound 42 (max_abs_entry pencil_mat_int) +
       2 * Z.abs D_pencil_int_value)%Z;
      [|exact crt_bound_pencil_sufficient].
    have HA := D_pencil_int_abs_bound.
    have Hsub : (Z.abs (D_pencil_int - D_pencil_int_value)
                <= Z.abs D_pencil_int + Z.abs D_pencil_int_value)%Z.
    { have := Z.abs_triangle D_pencil_int (- D_pencil_int_value).
      by rewrite Z.abs_opp -Z.add_opp_r. }
    lia.
Qed.

(* Restore expand strategy so downstream files (CertPencil.v) can
   unfold these definitions as needed by mathcomp matrix elaboration. *)
Strategy expand [char_poly_mod char_poly_int pencil_mat_int
                 fl_loop fl_mod_loop meye mzero
                 reduce_mat_Z fl_all_divisible].
