(* ===================================================================
   CharPolyAgree.v -- assembly of the 710-prime CRT cross-validation,
   plus the post-CRT bridge infrastructure.

   The 710-prime char-poly and matrix-identity checks are split across
   six chunks (CharPolyAgreeChunk_0..5.v) so `make -j` can run them in
   parallel.  This file imports those chunks and assembles the two
   headline Qeds via `crt_primes_all_split` + `forallb_app`.

   Definitions (modular polynomial primitives, the 710 prime list,
   `check_charpoly_one_prime_710`, `check_mat_identity_one_prime`,
   the chunk decomposition) live in CharPolyAgreeDef.v.
   =================================================================== *)

From Stdlib Require Import ZArith List Bool Uint63.
Import ListNotations.
Open Scope Z_scope.

From PrimeGapS1 Require Import IntPoly IntMat CharPoly Witness Recompose ModularArith.
From Bignums Require Import BigZ.
From PrimeGapS1 Require Export CharPolyAgreeDef.
From PrimeGapS1 Require Import
  CharPolyAgreeChunk_0 CharPolyAgreeChunk_1 CharPolyAgreeChunk_2
  CharPolyAgreeChunk_3 CharPolyAgreeChunk_4 CharPolyAgreeChunk_5.

(* ==================================================================
   Assembly: six chunks compose to the full 710-prime check.
   ================================================================== *)

Lemma char_poly_int_agrees_710 :
  check_charpoly_710 = true.
Proof.
  unfold check_charpoly_710.
  rewrite crt_primes_all_split.
  rewrite !List.forallb_app.
  rewrite char_poly_chunk_0, char_poly_chunk_1, char_poly_chunk_2,
          char_poly_chunk_3, char_poly_chunk_4, char_poly_chunk_5.
  reflexivity.
Qed.

Lemma matrix_identity_710 :
  check_mat_identity_710 = true.
Proof.
  unfold check_mat_identity_710.
  rewrite crt_primes_all_split.
  rewrite !List.forallb_app.
  rewrite matrix_identity_chunk_0, matrix_identity_chunk_1, matrix_identity_chunk_2,
          matrix_identity_chunk_3, matrix_identity_chunk_4, matrix_identity_chunk_5.
  reflexivity.
Qed.

From Stdlib Require Import Lia.

(* ==================================================================
   CRT BRIDGE INFRASTRUCTURE
   ================================================================== *)

(* ------------------------------------------------------------------
   1. M1 det nonzero check
   ------------------------------------------------------------------ *)

Definition check_M1_det_nz : bool :=
  negb (Uint63.eqb (List.hd 0 (char_poly_mod (List.hd 0 crt_primes_all) M1_int)) 0).

Lemma M1_det_nz_mod : check_M1_det_nz = true.
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------
   2. Size lemmas for charpoly_int and charpoly_of_A_int
   ------------------------------------------------------------------ *)

Lemma length_charpoly_int : length charpoly_int = 43%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma length_charpoly_of_A_int : length charpoly_of_A_int = 43%nat.
Proof. unfold charpoly_of_A_int, lift_bigZ. rewrite length_map. exact charpoly_of_A_int_bigZ_length. Qed.

(* ------------------------------------------------------------------
   3. Reflection lemma for scaling_Z
   ------------------------------------------------------------------ *)

Lemma check_scaling_coefs_sound k shipped intmat_cp :
  check_scaling_coefs k shipped intmat_cp = true ->
  forall j, (j < length shipped)%nat ->
    (j < length intmat_cp)%nat ->
    Z.mul (BigZ.to_Z (List.nth j shipped 0%bigZ))
          (BigZ.to_Z (BigZ.pow D_A_bigZ (BigZ.of_Z (Z.of_nat (42 - (k + j))))))
    = Z.mul (BigZ.to_Z D_q_bigZ) (BigZ.to_Z (List.nth j intmat_cp 0%bigZ)).
Proof.
  revert k intmat_cp.
  induction shipped as [| s ss IHss]; intros k intmat_cp Hcheck j Hj1 Hj2.
  - (* shipped = [] *)
    simpl in Hj1. lia.
  - (* shipped = s :: ss *)
    destruct intmat_cp as [| c cs].
    + (* intmat_cp = [] -- contradicts check = true *)
      cbn [check_scaling_coefs] in Hcheck. discriminate.
    + (* intmat_cp = c :: cs *)
      cbn [check_scaling_coefs] in Hcheck.
      apply andb_prop in Hcheck. destruct Hcheck as [Heqb Htail].
      destruct j as [| j'].
      * (* j = 0 *)
        cbn [List.nth].
        rewrite BigZ.spec_eqb in Heqb.
        rewrite Z.eqb_eq in Heqb.
        rewrite !BigZ.spec_mul in Heqb.
        replace (k + 0)%nat with k by lia.
        exact Heqb.
      * (* j = S j' *)
        cbn [List.nth length] in Hj1, Hj2 |- *.
        replace (k + S j')%nat with (S k + j')%nat by lia.
        apply IHss with (k := S k).
        -- exact Htail.
        -- lia.
        -- lia.
Qed.

Lemma scaling_Z_from_check (k : nat) : (k < 43)%nat ->
  Z.mul (List.nth k charpoly_int BinNums.Z0) (Z.pow D_A (Z.of_nat (42 - k)))
  = Z.mul D_q (List.nth k charpoly_of_A_int BinNums.Z0).
Proof.
  intros Hk.
  (* Get the BigZ-level result from check_scaling_coefs_sound *)
  pose proof (check_scaling_coefs_sound 0
    (List.map BigZ.of_Z charpoly_int) charpoly_of_A_int_bigZ
    charpoly_scaling_agrees k) as H.
  (* Satisfy the length conditions *)
  assert (Hlen1 : (k < length (List.map BigZ.of_Z charpoly_int))%nat).
  { rewrite length_map. rewrite length_charpoly_int. exact Hk. }
  assert (Hlen2 : (k < length charpoly_of_A_int_bigZ)%nat).
  { rewrite charpoly_of_A_int_bigZ_length. exact Hk. }
  specialize (H Hlen1 Hlen2).
  (* Simplify 0 + k to k *)
  replace (0 + k)%nat with k in H by lia.
  (* Rewrite H: nth of map BigZ.of_Z list *)
  change 0%bigZ with (BigZ.of_Z BinNums.Z0) in H.
  rewrite map_nth in H.
  (* Now H has BigZ.to_Z (BigZ.of_Z (nth k charpoly_int 0%Z)) on the left *)
  rewrite BigZ.spec_of_Z in H.
  (* Rewrite H: BigZ.pow -> Z.pow *)
  rewrite BigZ.spec_pow in H.
  rewrite BigZ.spec_of_Z in H.
  unfold D_A_bigZ in H.
  rewrite BigZ.spec_of_Z in H.
  (* Rewrite H: D_q_bigZ -> D_q *)
  unfold D_q_bigZ in H.
  rewrite BigZ.spec_of_Z in H.
  (* Rewrite the goal to expose BigZ.to_Z form on RHS *)
  change charpoly_of_A_int with (lift_bigZ charpoly_of_A_int_bigZ).
  unfold lift_bigZ.
  change BinNums.Z0 with (BigZ.to_Z 0%bigZ).
  rewrite map_nth.
  exact H.
Qed.

(* ------------------------------------------------------------------
   4. Row-length bridge
   ------------------------------------------------------------------ *)

Lemma forallb_all_rows_len n (M : list (list Z)) :
  forallb (fun row => Nat.eqb (length row) n) M = true ->
  all_rows_len n M.
Proof.
  intros Hfb.
  unfold all_rows_len. intros i Hi.
  rewrite forallb_forall in Hfb.
  assert (Hin : In (nth i M nil) M).
  { apply nth_In. exact Hi. }
  specialize (Hfb _ Hin).
  rewrite Nat.eqb_eq in Hfb.
  exact Hfb.
Qed.
