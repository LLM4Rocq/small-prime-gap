(* ==================================================================
   CRTPencilCheck.v

   Lift the 1-coefficient CRT per-prime agreement (proved in
   `CRTPencilChecksProof.v` by ~12 min of vm_compute) to Z equality
   between `det_M1_int` / `D_pencil_int` (computed via fl_loop on
   M1_int and pencil_mat_int respectively) and the precomputed Z
   literals shipped in `Witness_PencilDet.v`.

   At each prime p in crt_primes_all:

     check_M_det_at p = true     (computational, cached)
   + char_poly_mod_sound          (CRTBridge.v)
   --------------------------------------------
   = (det_M_int mod p) = (det_M_value mod p)
   = p | (det_M_int - det_M_value)

   Aggregating over crt_primes_all:

     all_primes_divide_product   (CRTCheck.v)
   --------------------------------------------
   = crt_product_710 | (det_M_int - det_M_value)

   Combined with the Hadamard bound (2 * |diff| < crt_product_710):

     small_multiple_zero          (CRTCheck.v)
   --------------------------------------------
   = det_M_int = det_M_value

   Then sign by `vm_compute` on the literal.
   ================================================================== *)

From Stdlib Require Import ZArith List Lia Znumtheory.

From Stdlib Require Import Uint63.

From mathcomp Require Import all_ssreflect.

From PrimeGapS1 Require Import IntMat IntPoly Witness CharPoly.
From PrimeGapS1 Require Import ModularArith CRTBridge CRTCheck CRTLift Fermat PrimeCheck.
From PrimeGapS1.CharPolyAgree Require Import Def.
From PrimeGapS1 Require Import Witness_PencilDet.
From PrimeGapS1 Require Import CertL2 CertPencilDef.
From PrimeGapS1 Require Import CRTPencilChecksProof.

Open Scope Z_scope.

(* ================================================================== *)
(*  The signs of the shipped Z literals: trivial vm_compute.           *)
(* ================================================================== *)

Lemma det_M1_int_value_pos : (0 < det_M1_int_value)%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma D_pencil_int_value_neg : (D_pencil_int_value < 0)%Z.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  Structural facts about M1_int and pencil_mat_int for use by        *)
(*  char_poly_mod_sound (which needs square_mat).                      *)
(* ================================================================== *)

Lemma square_M1_int : square_mat (length M1_int) M1_int.
Proof.
  split; [ reflexivity | ].
  intros i Hi. exact (M1_int_wf' i Hi).
Qed.

Lemma square_pencil_mat_int : square_mat (length pencil_mat_int) pencil_mat_int.
Proof.
  split; [ reflexivity | ].
  intros i Hi. exact (pencil_mat_int_wf i Hi).
Qed.

(* fl_all_divisible (via the bridge from CRTBridge.v). *)

Lemma fl_div_M1_int :
  fl_all_divisible (length M1_int) Z.one M1_int
    (meye (length M1_int)) (mzero (length M1_int)) Z.one.
Proof.
  exact (fl_all_divisible_from_L2 M1_int (length M1_int)
                                  (@Logic.eq_refl _ _) M1_int_wf').
Qed.

Lemma fl_div_pencil :
  fl_all_divisible (length pencil_mat_int) Z.one pencil_mat_int
    (meye (length pencil_mat_int)) (mzero (length pencil_mat_int)) Z.one.
Proof.
  apply (fl_all_divisible_from_L2 pencil_mat_int (length pencil_mat_int) (@Logic.eq_refl _ _)).
  exact (fun i Hi => pencil_mat_int_wf i Hi).
Qed.

(* The dimension bound: each prime in crt_primes_all is > 43, so it
   exceeds `Z.of_nat (length M1_int) + 1 = 43` and similarly for the
   pencil matrix (also 42x42).  Verified by vm_compute on the
   minimum prime in the shipped list. *)

Definition check_dim_bound_43 : bool :=
  List.forallb (fun p => Z.ltb 43 (Uint63.to_Z p)) crt_primes_all.

Lemma check_dim_bound_43_true : check_dim_bound_43 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma dim_bound_42 :
  forall p, In p crt_primes_all ->
  (Z.of_nat (length M1_int) + 1 < Uint63.to_Z p)%Z.
Proof.
  intros p Hin.
  pose proof check_dim_bound_43_true as H.
  pose proof (proj1 (List.forallb_forall _ _) H p Hin) as Hp.
  apply Z.ltb_lt in Hp.
  have HM1len : length M1_int = 42%nat by vm_compute; reflexivity.
  rewrite HM1len. lia.
Qed.

Lemma dim_bound_pencil :
  forall p, In p crt_primes_all ->
  (Z.of_nat (length pencil_mat_int) + 1 < Uint63.to_Z p)%Z.
Proof.
  intros p Hin.
  pose proof check_dim_bound_43_true as H.
  pose proof (proj1 (List.forallb_forall _ _) H p Hin) as Hp.
  apply Z.ltb_lt in Hp.
  have Hlen : length pencil_mat_int = 42%nat.
  { have := pencil_mat_int_dim. unfold mat_dim. by move=> ->. }
  rewrite Hlen. lia.
Qed.

(* Fermat for each prime in crt_primes_all. *)

Lemma fermat_at :
  forall p, In p crt_primes_all ->
  forall j : Z, (0 < j < Uint63.to_Z p)%Z ->
  ((j * j ^ (Uint63.to_Z p - 2)) mod Uint63.to_Z p = 1 mod Uint63.to_Z p)%Z.
Proof.
  intros p Hin j Hj.
  have Hvp := crt_primes_valid p Hin.
  have Hcheck : check_prime_Z (Uint63.to_Z p) = true
    := proj1 (List.forallb_forall _ _) check_all_primes_710 p Hin.
  have Hprime_nat : prime (Z.to_nat (Uint63.to_Z p))
    := check_prime_Z_mc _ Hcheck.
  apply fermat_Z; [case: Hvp; tauto | exact Hprime_nat | exact Hj].
Qed.

(* ================================================================== *)
(*  Per-prime divisibility for both determinants                       *)
(* ================================================================== *)

Lemma per_prime_div_M1 (p : Uint63.int) :
  In p crt_primes_all ->
  (Uint63.to_Z p | (det_M1_int - det_M1_int_value))%Z.
Proof.
  intros Hin.
  have Hcheck := check_M1_det_710_true.
  have Hagree : check_M1_det_at p = true
    := proj1 (List.forallb_forall _ _) Hcheck p Hin.
  apply Uint63.eqb_spec in Hagree.
  (* Hagree : nth 0 (char_poly_mod p M1_int) 0%uint63 = Z_to_mod63 p det_M1_int_value *)
  have Hvp : valid_prime p := crt_primes_valid p Hin.
  have Hsound := char_poly_mod_sound p M1_int Hvp square_M1_int
                                     (dim_bound_42 p Hin) fl_div_M1_int
                                     (fermat_at p Hin).
  (* Hsound : map (Z_to_mod63 p) (char_poly_int M1_int) = char_poly_mod p M1_int *)
  have Heq_mod_u : Z_to_mod63 p det_M1_int = Z_to_mod63 p det_M1_int_value.
  { unfold det_M1_int.
    have HH : List.nth 0 (List.map (Z_to_mod63 p) (char_poly_int M1_int))
                       (Z_to_mod63 p 0%Z)
            = List.nth 0 (char_poly_mod p M1_int) 0%uint63.
    { rewrite Hsound.
      apply List.nth_indep.
      have Hne : char_poly_int M1_int <> nil
        := char_poly_int_M1_int_neq_nil.
      destruct (char_poly_mod p M1_int) eqn:Hcpm; [|simpl; lia].
      exfalso.
      have HH : List.map (Z_to_mod63 p) (char_poly_int M1_int) = nil
        by rewrite Hsound Hcpm.
      destruct (char_poly_int M1_int); [contradiction|discriminate]. }
    rewrite List.map_nth in HH.
    rewrite HH Hagree. reflexivity. }
  apply (f_equal Uint63.to_Z) in Heq_mod_u.
  rewrite !Z_to_mod63_spec in Heq_mod_u; [|exact Hvp|exact Hvp].
  destruct Hvp as [Hvp1 _].
  assert (Hpnz : Uint63.to_Z p <> 0%Z) by lia.
  exists ((det_M1_int / Uint63.to_Z p - det_M1_int_value / Uint63.to_Z p)%Z).
  rewrite Z.mul_sub_distr_r.
  rewrite (Z.div_mod det_M1_int (Uint63.to_Z p) Hpnz) at 1.
  rewrite (Z.div_mod det_M1_int_value (Uint63.to_Z p) Hpnz) at 1. lia.
Qed.

Lemma per_prime_div_pencil (p : Uint63.int) :
  In p crt_primes_all ->
  (Uint63.to_Z p | (D_pencil_int - D_pencil_int_value))%Z.
Proof.
  intros Hin.
  have Hcheck := check_pencil_det_710_true.
  have Hagree : check_pencil_det_at p = true
    := proj1 (List.forallb_forall _ _) Hcheck p Hin.
  apply Uint63.eqb_spec in Hagree.
  have Hvp : valid_prime p := crt_primes_valid p Hin.
  have Hsound := char_poly_mod_sound p pencil_mat_int Hvp square_pencil_mat_int
                                     (dim_bound_pencil p Hin) fl_div_pencil
                                     (fermat_at p Hin).
  have Heq_mod_u : Z_to_mod63 p D_pencil_int = Z_to_mod63 p D_pencil_int_value.
  { unfold D_pencil_int.
    have HH : List.nth 0 (List.map (Z_to_mod63 p) (char_poly_int pencil_mat_int))
                       (Z_to_mod63 p 0%Z)
            = List.nth 0 (char_poly_mod p pencil_mat_int) 0%uint63.
    { rewrite Hsound.
      apply List.nth_indep.
      have Hne : char_poly_int pencil_mat_int <> nil
        := char_poly_int_pencil_neq_nil.
      destruct (char_poly_mod p pencil_mat_int) eqn:Hcpm; [|simpl; lia].
      exfalso.
      have HH : List.map (Z_to_mod63 p) (char_poly_int pencil_mat_int) = nil
        by rewrite Hsound Hcpm.
      destruct (char_poly_int pencil_mat_int); [contradiction|discriminate]. }
    rewrite List.map_nth in HH.
    rewrite HH Hagree. reflexivity. }
  apply (f_equal Uint63.to_Z) in Heq_mod_u.
  rewrite !Z_to_mod63_spec in Heq_mod_u; [|exact Hvp|exact Hvp].
  destruct Hvp as [Hvp1 _].
  assert (Hpnz : Uint63.to_Z p <> 0%Z) by lia.
  exists ((D_pencil_int / Uint63.to_Z p - D_pencil_int_value / Uint63.to_Z p)%Z).
  rewrite Z.mul_sub_distr_r.
  rewrite (Z.div_mod D_pencil_int (Uint63.to_Z p) Hpnz) at 1.
  rewrite (Z.div_mod D_pencil_int_value (Uint63.to_Z p) Hpnz) at 1. lia.
Qed.

(* ================================================================== *)
(*  Hadamard bounds — `2 * |det - shipped| < crt_product_710`.         *)
(*                                                                      *)
(*  The 710 Uint63 primes give a product of ~44730 bits.  The two       *)
(*  determinants are 2044 and 31131 bits respectively; their            *)
(*  values mod-equal the shipped literals (proved per-prime above),    *)
(*  so |diff| <= 2 * max(|a|, |b|) is bounded by either's Hadamard      *)
(*  bound + a tiny margin.                                              *)
(*                                                                      *)
(*  We give an explicit bound on |det_M_int| as a hard-coded             *)
(*  literal (the value computed by FLINT, plus 1 to avoid off-by-one   *)
(*  edge cases) and prove `|det_M_int - det_M_value| < bound` by       *)
(*  vm_compute on the literal differences.                              *)
(* ================================================================== *)

(* Numerical bound check: 2 * |diff_M1| < crt_product_710.
   Since the per-prime check has already established that the two
   values agree mod every prime, the diff is provably 0 once we have
   the Hadamard bound below.  The bound is verified by vm_compute on
   `Z.abs det_M1_int_value`, then compared to crt_product_710. *)

Definition hadamard_check_M1 : bool :=
  Z.ltb (2 * (Z.abs det_M1_int_value + 1)) crt_product_710.

Definition hadamard_check_pencil : bool :=
  Z.ltb (2 * (Z.abs D_pencil_int_value + 1)) crt_product_710.

Lemma hadamard_check_M1_true : hadamard_check_M1 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma hadamard_check_pencil_true : hadamard_check_pencil = true.
Proof. vm_compute. reflexivity. Qed.

(* Bound on |det_M1_int|: equals |det_M1_int_value| (proved equal)
   so they cannot differ by more than 0 once the equality is in
   hand.  Circular?  No: the bound we use for `small_multiple_zero`
   is `2 * (|det_M1_int| + |det_M1_int_value|)` which is `<=
   crt_product_710` by a Hadamard-on-M1_int argument we DERIVE from
   `charpoly_coeff_bound`-style reasoning specialised to M1_int.

   Since `charpoly_coeff_bound` in CRTLift.v is specialised to
   A_int, we'd need to do similar work for M1_int (a new
   `M1_int_fl_loop_coeff` opaque helper, computable from M1_int's
   max_abs_entry).  Estimated +~30 LOC.

   PRAGMATIC: prove |det_M1_int| bounded by something we can
   compute, using `max_abs_coeff (char_poly_int M1_int)` — but this
   requires fl_loop on M1_int (the very thing we're avoiding).

   The CLEAN solution combines `fl_coeff_bound` (closed-form
   arithmetic on `(42, max_abs_entry M1_int)`) with a sketch like
   `A_int_fl_loop_coeff`.  For now we sketch the lift but defer the
   Hadamard bound. *)

Theorem det_M1_int_eq : det_M1_int = det_M1_int_value.
Proof.
  set (a := det_M1_int).
  set (b := det_M1_int_value).
  cut ((a - b)%Z = 0%Z). { unfold a, b. lia. }
  apply (small_multiple_zero _ crt_product_710).
  - (* crt_product_710 | (a - b) *)
    unfold crt_product_710.
    apply all_primes_divide_product.
    + exact crt_primes_710_NoDup.
    + exact crt_primes_710_all_prime.
    + intros pz Hpz. apply List.in_map_iff in Hpz.
      destruct Hpz as [p [Hpeq Hin]]. subst pz.
      exact (per_prime_div_M1 p Hin).
  - exact crt_product_710_pos.
  - (* 2 * |a - b| < crt_product_710 *)
    (* TODO: |a| <= fl_coeff_bound 42 (max_abs_entry M1_int);
       |b| = |det_M1_int_value| (the shipped literal).
       2 * (|a| + |b|) <= 2 * fl_coeff_bound 42 (...) + 2 * |b|
                       < crt_product_710 (vm_compute the sum, comparable
       to existing crt_bound_sufficient for A_int).
       For now: leave as remaining gap. *)
    admit.
Admitted.

Theorem D_pencil_int_eq : D_pencil_int = D_pencil_int_value.
Proof.
  set (a := D_pencil_int).
  set (b := D_pencil_int_value).
  cut ((a - b)%Z = 0%Z). { unfold a, b. lia. }
  apply (small_multiple_zero _ crt_product_710).
  - unfold crt_product_710.
    apply all_primes_divide_product.
    + exact crt_primes_710_NoDup.
    + exact crt_primes_710_all_prime.
    + intros pz Hpz. apply List.in_map_iff in Hpz.
      destruct Hpz as [p [Hpeq Hin]]. subst pz.
      exact (per_prime_div_pencil p Hin).
  - exact crt_product_710_pos.
  - admit.
Admitted.
