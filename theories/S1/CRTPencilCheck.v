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
From PrimeGapS1 Require Import AllRowsLenHelper.   (* forallb_all_rows_len *)
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
(*  Per-prime modular agreement via char_poly_mod_sound                *)
(*                                                                      *)
(*  Mirror of CRTLift.per_prime_mod_eq, specialised to M1_int and       *)
(*  pencil_mat_int.  Uses `change L with mat_dim M . rewrite *_dim`    *)
(*  to keep the unifier from expanding the concrete 42x42 matrices.    *)
(* ================================================================== *)

Strategy opaque [char_poly_mod char_poly_int M1_int M2_int pencil_mat_int
                 fl_loop fl_mod_loop mmat_eye mmat_zero meye mzero
                 reduce_mat_Z fl_all_divisible].

Lemma per_prime_mod_eq_M1 (p : Uint63.int) (Hin : In p crt_primes_all) :
  List.map (Z_to_mod63 p) (char_poly_int M1_int) = char_poly_mod p M1_int.
Proof.
  apply char_poly_mod_sound.
  - exact (crt_primes_valid p Hin).
  - change (List.length M1_int) with (mat_dim M1_int). rewrite M1_int_dim'.
    split; [exact M1_int_dim' | exact (forallb_all_rows_len 42%nat M1_int M1_int_rows_42)].
  - change (List.length M1_int) with (mat_dim M1_int). rewrite M1_int_dim'.
    apply Z.ltb_lt.
    exact (proj1 (List.forallb_forall _ _) check_dim_bound_43_true p Hin).
  - change (List.length M1_int) with (mat_dim M1_int). rewrite M1_int_dim'.
    apply fl_all_divisible_from_L2;
      [exact M1_int_dim' | exact M1_int_wf'].
  - exact (fermat_at p Hin).
Qed.

Lemma per_prime_mod_eq_pencil (p : Uint63.int) (Hin : In p crt_primes_all) :
  List.map (Z_to_mod63 p) (char_poly_int pencil_mat_int) = char_poly_mod p pencil_mat_int.
Proof.
  apply char_poly_mod_sound.
  - exact (crt_primes_valid p Hin).
  - change (List.length pencil_mat_int) with (mat_dim pencil_mat_int).
    rewrite pencil_mat_int_dim.
    split; [exact pencil_mat_int_dim |
            exact (fun i Hi => pencil_mat_int_wf i Hi)].
  - change (List.length pencil_mat_int) with (mat_dim pencil_mat_int).
    rewrite pencil_mat_int_dim.
    apply Z.ltb_lt.
    exact (proj1 (List.forallb_forall _ _) check_dim_bound_43_true p Hin).
  - change (List.length pencil_mat_int) with (mat_dim pencil_mat_int).
    rewrite pencil_mat_int_dim.
    apply fl_all_divisible_from_L2;
      [exact pencil_mat_int_dim |
       exact (fun i Hi => pencil_mat_int_wf i Hi)].
  - exact (fermat_at p Hin).
Qed.

(* Block kernel from reducing through char_poly_mod / char_poly_int on
   the concrete matrices when the per-prime equations are unfolded. *)
Strategy opaque [char_poly_mod char_poly_int M1_int pencil_mat_int].

(* ================================================================== *)
(*  Per-prime divisibility for both determinants                       *)
(* ================================================================== *)

(* Helper: Z_to_mod63 p 0 = 0%uint63.
   Uses BigZ machinery, so not definitionally equal — prove via Uint63 spec. *)
Lemma Z_to_mod63_zero (p : Uint63.int) :
  valid_prime p -> Z_to_mod63 p 0%Z = 0%uint63.
Proof.
  intros Hvp.
  apply Uint63.to_Z_inj.
  rewrite Z_to_mod63_spec; [|exact Hvp].
  rewrite Z.mod_0_l; [reflexivity|].
  destruct Hvp as [Hp1 _]. lia.
Qed.

(* Helper: mod-equality (as Uint63) implies Z-divisibility of the
   difference.  Generic in the two integers, so the rewrite engine
   doesn't unify against the heavy concrete `List.nth 0 (char_poly_int
   M1_int) 0%Z` term inside the matrix-specialised proofs below. *)
Lemma mod_eq_to_divide (p : Uint63.int) (z1 z2 : Z) :
  valid_prime p ->
  Z_to_mod63 p z1 = Z_to_mod63 p z2 ->
  (Uint63.to_Z p | (z1 - z2))%Z.
Proof.
  intros Hvp Heq.
  apply (f_equal Uint63.to_Z) in Heq.
  rewrite !Z_to_mod63_spec in Heq; [|exact Hvp|exact Hvp].
  destruct Hvp as [Hp1 _].
  apply Znumtheory.Zmod_divide; [lia|].
  rewrite Zminus_mod Heq Z.sub_diag.
  apply Z.mod_0_l; lia.
Qed.

(* Generic per-prime divisibility lift.  Given
   - the matrix M (e.g. M1_int or pencil_mat_int)
   - the shipped Z literal D (e.g. det_M1_int_value or D_pencil_int_value)
   - the sealed Z determinant D_int (e.g. det_M1_int or D_pencil_int)
   - the "D_int = nth 0 (char_poly_int M) 0" link
   - the per-prime modular sound bridge
   - the precomputed per-prime check passing,
   produce `p | (D_int - D)`. *)
Lemma per_prime_div_generic
  (M : mat) (D : Z) (D_int : Z) (p : Uint63.int)
  (Hint_eq : D_int = List.nth 0 (char_poly_int M) 0%Z)
  (Hvp     : valid_prime p)
  (Hsound  : List.map (Z_to_mod63 p) (char_poly_int M) = char_poly_mod p M)
  (Hagree  : List.nth 0 (char_poly_mod p M) 0%uint63 = Z_to_mod63 p D) :
  (Uint63.to_Z p | (D_int - D))%Z.
Proof.
  have HH : List.nth 0 (char_poly_mod p M) 0%uint63
          = Z_to_mod63 p (List.nth 0 (char_poly_int M) 0%Z).
  { rewrite -(Z_to_mod63_zero p Hvp) -Hsound. apply List.map_nth. }
  have Heq_mod_u : Z_to_mod63 p (List.nth 0 (char_poly_int M) 0%Z)
                 = Z_to_mod63 p D.
  { transitivity (List.nth 0 (char_poly_mod p M) 0%uint63);
    [exact (Logic.eq_sym HH) | exact Hagree]. }
  rewrite Hint_eq.
  exact (mod_eq_to_divide p _ _ Hvp Heq_mod_u).
Qed.

Lemma per_prime_div_M1 (p : Uint63.int) :
  In p crt_primes_all ->
  (Uint63.to_Z p | (det_M1_int - det_M1_int_value))%Z.
Proof.
  intros Hin.
  have Hagree : check_M1_det_at p = true
    := proj1 (List.forallb_forall _ _) check_M1_det_710_true p Hin.
  apply Uint63.eqb_spec in Hagree.
  exact (per_prime_div_generic M1_int det_M1_int_value det_M1_int p
           det_M1_int_eq_nth (crt_primes_valid p Hin)
           (per_prime_mod_eq_M1 p Hin) Hagree).
Qed.

Lemma per_prime_div_pencil (p : Uint63.int) :
  In p crt_primes_all ->
  (Uint63.to_Z p | (D_pencil_int - D_pencil_int_value))%Z.
Proof.
  intros Hin.
  have Hagree : check_pencil_det_at p = true
    := proj1 (List.forallb_forall _ _) check_pencil_det_710_true p Hin.
  apply Uint63.eqb_spec in Hagree.
  exact (per_prime_div_generic pencil_mat_int D_pencil_int_value D_pencil_int p
           D_pencil_int_eq_nth (crt_primes_valid p Hin)
           (per_prime_mod_eq_pencil p Hin) Hagree).
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

Lemma hadamard_check_M1_true : hadamard_check_M1 = true.
Proof. vm_compute. reflexivity. Qed.

(* NOTE: the pencil determinant is ~31131 bits, but the product of the
   710 shipped Uint63 primes is only ~21300 bits, so 2*|D_pencil_int_value|
   exceeds crt_product_710 and the 1-coefficient CRT lift cannot close
   `D_pencil_int = D_pencil_int_value` with the current prime set.
   Closing it requires ~330 additional primes (a ~25-min vm_compute
   recompile of CRTPencilChecksProof.v + a new bound check).  The
   det_M1_int side (2044 bits) closes cleanly below. *)

(* M1_int Hadamard bound — split into a sibling file `CRTPencilM1Bound.v`
   because the Qed-time kernel re-verification of these lemmas in this
   compilation unit was non-terminating (>30 min and growing RAM).  In
   isolation in `CRTPencilM1Bound.v` it compiles in ~10 seconds.  The
   underlying cause is not yet diagnosed but reproduces consistently
   here. *)
From PrimeGapS1 Require Import CRTPencilM1Bound.

(* ================================================================== *)
(*  Assembly: lift per-prime divisibility + Hadamard bound to Z.       *)
(* ================================================================== *)

Theorem det_M1_int_eq : det_M1_int = det_M1_int_value.
Proof.
  (* Mirror CRTLift.fl_eq_flint: introduce a, b via `set` to keep the
     kernel from reducing det_M1_int during Qed conversion checks. *)
  set (a := det_M1_int).
  set (b := det_M1_int_value).
  cut ((a - b)%Z = 0%Z); [unfold a, b; lia|].
  apply (small_multiple_zero _ crt_product_710).
  - unfold crt_product_710.
    apply all_primes_divide_product.
    + exact crt_primes_710_NoDup.
    + exact crt_primes_710_all_prime.
    + intros pz Hpz. apply List.in_map_iff in Hpz.
      destruct Hpz as [p [Hpeq Hin]]. subst pz.
      exact (per_prime_div_M1 p Hin).
  - exact crt_product_710_pos.
  - apply Z.le_lt_trans with
      (2 * fl_coeff_bound 42 (max_abs_entry M1_int) +
       2 * Z.abs det_M1_int_value)%Z;
      [|exact crt_bound_M1_sufficient].
    have HA := det_M1_int_abs_bound.
    have Hsub : (Z.abs (a - b) <= Z.abs a + Z.abs b)%Z.
    { have := Z.abs_triangle a (-b). by rewrite Z.abs_opp -Z.add_opp_r. }
    unfold a, b in *. lia.
Qed.

(* D_pencil_int_eq lives in CRTPencilCheckExt.v: it uses the
   1210-prime extension `crt_primes_pencil` (710 mainline + 500
   extras) to close the Hadamard bound, which the 710-prime product
   alone cannot bound (D_pencil_int is ~31131 bits, crt_product_710
   is only ~21300 bits). *)

(* Restore expand strategy on names used by downstream files so that
   mathcomp elaboration (e.g. in CertPencil.v) can fold/unfold these
   definitions as needed. *)
Strategy expand [char_poly_mod char_poly_int M1_int M2_int pencil_mat_int
                 fl_loop fl_mod_loop meye mzero
                 reduce_mat_Z fl_all_divisible].
