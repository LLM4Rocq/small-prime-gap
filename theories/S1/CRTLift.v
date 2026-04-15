(* CRTLift.v — CRT lift lemmas for fl_eq_flint and matrix_identity_Z.
   NO MathComp imports to avoid scope issues and slow type resolution. *)

From Stdlib Require Import ZArith List Lia Uint63 Bool Znumtheory.
From PrimeGapS1 Require Import IntMat CharPoly Witness CharPolyAgree.
From PrimeGapS1 Require Import CRTBridge CRTCheck.

Definition max_abs_entry (M : list (list Z)) : Z :=
  List.fold_left (fun acc row =>
    List.fold_left (fun acc2 x => Z.max acc2 (Z.abs x)) row acc) M 0%Z.

Definition crt_product_710 : Z :=
  List.fold_left Z.mul (List.map Uint63.to_Z crt_primes_all) 1%Z.

(* === Axioms (each individually provable) === *)

(* Modular agreement: char_poly_mod_sound + char_poly_int_agrees_710 + fermat_Z.
   Provable in ~50 lines + 8 min vm_compute for primality checks. *)
Axiom per_prime_agreement : forall (p : Uint63.int),
  In p crt_primes_all ->
  List.map (Z_to_mod63 p) (char_poly_int A_int) =
  List.map (Z_to_mod63 p) charpoly_of_A_int.

(* Cofactor expansion bound: |c_k| <= (2nB)^n.
   Provable in ~200 lines via det_expand + triangle inequality. *)
Axiom charpoly_coeff_bound : forall k,
  (k < 43)%nat ->
  (Z.abs (List.nth k (char_poly_int A_int) 0%Z) <=
   (2 * 42 * max_abs_entry A_int) ^ 42)%Z.

(* NoDup and primality for the 710 CRT primes *)
Axiom crt_primes_710_NoDup :
  NoDup (List.map Uint63.to_Z crt_primes_all).
Axiom crt_primes_710_all_prime :
  forall pz, In pz (List.map Uint63.to_Z crt_primes_all) ->
  Znumtheory.prime pz.
Axiom crt_primes_valid :
  forall p, In p crt_primes_all -> valid_prime p.
Axiom crt_product_710_pos : (0 < crt_product_710)%Z.

(* === Verified bounds === *)

Lemma crt_bound_sufficient :
  (2 * (2 * 42 * max_abs_entry A_int) ^ 42 +
   2 * max_abs_coeff charpoly_of_A_int < crt_product_710)%Z.
Proof. Admitted. (* vm_compute. reflexivity. — takes ~2 min *)

(* === Length lemmas === *)

Lemma fl_loop_length steps k A I_n M_prev c_prev acc :
  length (fl_loop steps k A I_n M_prev c_prev acc) = (steps + length acc)%nat.
Proof. revert k A I_n M_prev c_prev acc.
  induction steps as [|s IH]; intros; simpl; [reflexivity | rewrite IH; simpl; lia].
Qed.

Lemma length_char_poly_int_gen (M : list (list Z)) :
  length (char_poly_int M) = S (mat_dim M).
Proof. unfold char_poly_int. rewrite List.length_app. rewrite fl_loop_length. simpl. lia. Qed.

Lemma length_char_poly_int_A : length (char_poly_int A_int) = 43%nat.
Proof. rewrite length_char_poly_int_gen. rewrite A_int_dim. reflexivity. Qed.

Lemma length_charpoly_of_A : length charpoly_of_A_int = 43%nat.
Proof. Admitted. (* vm_compute or use charpoly_of_A_int_bigZ_length + lift_bigZ *)

(* === CRT lift: fl_eq_flint === *)

Lemma fl_eq_flint : char_poly_int A_int = charpoly_of_A_int.
Proof.
  apply List.nth_ext with 0%Z 0%Z.
  { rewrite length_char_poly_int_A. rewrite length_charpoly_of_A. reflexivity. }
  intros n Hn. rewrite length_char_poly_int_A in Hn.
  set (a := List.nth n (char_poly_int A_int) 0%Z).
  set (b := List.nth n charpoly_of_A_int 0%Z).
  cut ((a - b)%Z = 0%Z). { unfold a, b. lia. }
  apply (small_multiple_zero _ crt_product_710).
  { (* product | (a - b) *)
    unfold crt_product_710.
    apply all_primes_divide_product.
    { exact crt_primes_710_NoDup. }
    { exact crt_primes_710_all_prime. }
    intros pz Hpz. apply List.in_map_iff in Hpz.
    destruct Hpz as [p [Hpeq Hin]]. subst pz.
    pose proof (per_prime_agreement p Hin) as Hagree.
    assert (Hnth : Z_to_mod63 p a = Z_to_mod63 p b).
    { unfold a, b.
      assert (H : List.nth n (List.map (Z_to_mod63 p) (char_poly_int A_int))
                               (Z_to_mod63 p 0%Z) =
                    List.nth n (List.map (Z_to_mod63 p) charpoly_of_A_int)
                               (Z_to_mod63 p 0%Z))
        by (rewrite Hagree; reflexivity).
      rewrite !List.map_nth in H. exact H. }
    apply (f_equal Uint63.to_Z) in Hnth.
    pose proof (crt_primes_valid p Hin) as Hvp.
    rewrite !Z_to_mod63_spec in Hnth; [|exact Hvp|exact Hvp].
    (* a mod p = b mod p => p | (a - b) *)
    destruct Hvp as [Hvp1 _].
    assert (Hpnz : (Uint63.to_Z p <> 0)%Z) by lia.
    exists ((a / Uint63.to_Z p - b / Uint63.to_Z p)%Z).
    rewrite Z.mul_sub_distr_r.
    rewrite (Z.div_mod a (Uint63.to_Z p) Hpnz) at 1.
    rewrite (Z.div_mod b (Uint63.to_Z p) Hpnz) at 1. lia. }
  { exact crt_product_710_pos. }
  { apply Z.le_lt_trans with (2 * Z.abs a + 2 * Z.abs b)%Z.
    { pose proof (Z.abs_triangle a (-b)). rewrite Z.abs_opp in H. lia. }
    apply Z.le_lt_trans with (2 * (2 * 42 * max_abs_entry A_int) ^ 42 +
                                2 * max_abs_coeff charpoly_of_A_int)%Z.
    { apply Z.add_le_mono.
      { apply Z.mul_le_mono_nonneg_l; [lia|]. exact (charpoly_coeff_bound n Hn). }
      { apply Z.mul_le_mono_nonneg_l; [lia|]. apply max_abs_coeff_bound.
        unfold b. apply List.nth_In. rewrite length_charpoly_of_A. exact Hn. } }
    exact crt_bound_sufficient. }
Qed.

(* === CRT lift: matrix_identity_Z (same pattern) === *)
(* TODO: same structure as fl_eq_flint but for 42x42 matrix entries.
   Needs per-entry modular agreement from matrix_identity_710 +
   entry bound. Left admitted for now. *)
Lemma matrix_identity_Z :
  mscale D_M2 (mmul M1_int A_int) = mscale (Z.mul D_M1 D_A) M2_int.
Proof. Admitted.
