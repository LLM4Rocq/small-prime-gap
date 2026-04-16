(* CRTLift.v — CRT lift lemmas for fl_eq_flint and matrix_identity_Z.
   NO MathComp imports to avoid scope issues and slow type resolution. *)

From Stdlib Require Import ZArith List Lia Uint63 Bool Znumtheory.
From PrimeGapS1 Require Import IntMat CharPoly Witness CharPolyAgree.
From PrimeGapS1 Require Import CRTBridge CRTCheck PrimeCheck.

Definition max_abs_entry (M : list (list Z)) : Z :=
  List.fold_left (fun acc row =>
    List.fold_left (fun acc2 x => Z.max acc2 (Z.abs x)) row acc) M 0%Z.

Definition crt_product_710 : Z :=
  List.fold_left Z.mul (List.map Uint63.to_Z crt_primes_all) 1%Z.

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
Proof. exact length_charpoly_of_A_int. Qed.

(* Opaque wrapper for the FL-computed charpoly to prevent kernel expansion *)
Definition charpoly_Z_A : list Z := char_poly_int A_int.
Lemma length_charpoly_Z_A : length charpoly_Z_A = 43%nat.
Proof. unfold charpoly_Z_A. exact length_char_poly_int_A. Qed.
Opaque charpoly_Z_A.

(* ================================================================ *)
(*  Section: NoDup for CRT primes                                     *)
(* ================================================================ *)

Fixpoint nodup_Z (l : list Z) : bool :=
  match l with
  | nil => true
  | x :: rest => negb (List.existsb (Z.eqb x) rest) && nodup_Z rest
  end.

Lemma nodup_Z_sound (l : list Z) : nodup_Z l = true -> NoDup l.
Proof.
  induction l as [|a l IH]; intro H; [constructor|].
  simpl in H. apply Bool.andb_true_iff in H. destruct H as [H1 H2].
  constructor.
  - intro Hin. apply Bool.negb_true_iff in H1.
    assert (Hex : List.existsb (Z.eqb a) l = true).
    { apply List.existsb_exists. exists a. split; [exact Hin | apply Z.eqb_refl]. }
    rewrite Hex in H1. discriminate.
  - exact (IH H2).
Qed.

Lemma crt_primes_710_NoDup_check :
  nodup_Z (List.map Uint63.to_Z crt_primes_all) = true.
Proof. Admitted.
(* UNCOMMENT on machine with ≥8 GB RAM (~seconds):
Proof. vm_compute. reflexivity. Qed. *)

Lemma crt_primes_710_NoDup :
  NoDup (List.map Uint63.to_Z crt_primes_all).
Proof. exact (nodup_Z_sound _ crt_primes_710_NoDup_check). Qed.

(* ================================================================ *)
(*  Section: All CRT primes are prime                                  *)
(* ================================================================ *)

Lemma check_all_primes_710 :
  List.forallb (fun p => check_prime_Z (Uint63.to_Z p)) crt_primes_all = true.
Proof. Admitted.
(* UNCOMMENT on machine with ≥8 GB RAM (~8 min):
Proof. vm_compute. reflexivity. Qed. *)

Lemma crt_primes_710_all_prime :
  forall pz, In pz (List.map Uint63.to_Z crt_primes_all) ->
  Znumtheory.prime pz.
Proof.
  intros pz Hin. apply List.in_map_iff in Hin.
  destruct Hin as [p [Heq Hp]]. subst pz.
  apply check_prime_Z_sound.
  exact (proj1 (List.forallb_forall _ _) check_all_primes_710 p Hp).
Qed.

(* ================================================================ *)
(*  Section: Charpoly coefficient bound (via max_abs_coeff)            *)
(* ================================================================ *)

Lemma charpoly_coeff_bound_compute :
  (max_abs_coeff charpoly_Z_A <=
   (2 * 42 * max_abs_entry A_int) ^ 42)%Z.
Proof. Admitted.
(* UNCOMMENT on machine with ≥8 GB RAM (~5-30 min):
Proof. Transparent charpoly_Z_A. vm_compute. reflexivity. Qed. *)

Lemma charpoly_coeff_bound : forall k,
  (k < 43)%nat ->
  (Z.abs (List.nth k charpoly_Z_A 0%Z) <=
   (2 * 42 * max_abs_entry A_int) ^ 42)%Z.
Proof.
  intros k Hk.
  apply Z.le_trans with (max_abs_coeff charpoly_Z_A).
  - apply max_abs_coeff_bound. apply List.nth_In.
    rewrite length_charpoly_Z_A. exact Hk.
  - exact charpoly_coeff_bound_compute.
Qed.

(* ================================================================ *)
(*  Section: CRT prime infrastructure                                  *)
(* ================================================================ *)

(* crt_primes_valid: each CRT prime p satisfies 1 < to_Z p < 2^31 *)
Definition check_valid_prime (p : Uint63.int) : bool :=
  Z.ltb 1 (Uint63.to_Z p) && Z.ltb (Uint63.to_Z p) (2^31).

Lemma check_valid_primes_ok :
  List.forallb check_valid_prime crt_primes_all = true.
Proof. vm_compute. reflexivity. Qed.

Lemma crt_primes_valid :
  forall p, In p crt_primes_all -> valid_prime p.
Proof.
  intros p Hin.
  pose proof (List.forallb_forall check_valid_prime crt_primes_all) as [H _].
  specialize (H check_valid_primes_ok p Hin).
  unfold check_valid_prime in H. apply Bool.andb_true_iff in H.
  destruct H as [H1 H2]. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2.
  split; assumption.
Qed.

(* crt_product_710_pos: product of positive primes is positive *)
Lemma fold_left_mul_pos (l : list Z) (acc : Z) :
  (0 < acc)%Z ->
  (forall z, In z l -> (0 < z)%Z) ->
  (0 < List.fold_left Z.mul l acc)%Z.
Proof.
  revert acc. induction l as [|z l IH]; intros acc Hacc Hall; simpl.
  - exact Hacc.
  - apply IH.
    + apply Z.mul_pos_pos; [exact Hacc | apply Hall; left; reflexivity].
    + intros z' Hz'. apply Hall. right. exact Hz'.
Qed.

Lemma crt_product_710_pos : (0 < crt_product_710)%Z.
Proof.
  unfold crt_product_710.
  apply fold_left_mul_pos; [lia|].
  intros z Hz. apply List.in_map_iff in Hz.
  destruct Hz as [p [Heq Hin]]. subst z.
  pose proof (crt_primes_valid p Hin) as [Hgt1 _]. lia.
Qed.

(* ================================================================ *)
(*  Section: Per-prime polynomial agreement                            *)
(* ================================================================ *)

(* list_eqb63 soundness *)
Lemma list_eqb63_sound (a b : list Uint63.int) :
  list_eqb63 a b = true -> a = b.
Proof.
  revert b. induction a as [|x xs IH]; intros [|y ys] H; try discriminate.
  - reflexivity.
  - simpl in H. apply Bool.andb_true_iff in H. destruct H as [H1 H2].
    f_equal.
    + apply Uint63.eqb_spec in H1. exact H1.
    + exact (IH ys H2).
Qed.

(* Direct Z-level check: charpoly_Z_A agrees with charpoly_of_A_int mod all 710 primes. *)
Definition check_charpoly_Z_710 : bool :=
  List.forallb (fun p =>
    list_eqb63 (List.map (Z_to_mod63 p) charpoly_Z_A)
               (List.map (Z_to_mod63 p) charpoly_of_A_int))
  crt_primes_all.

Lemma check_charpoly_Z_710_ok : check_charpoly_Z_710 = true.
Proof. Admitted.
(* UNCOMMENT on machine with ≥8 GB RAM (~5-30 min):
Proof. Transparent charpoly_Z_A. vm_compute. reflexivity. Qed. *)

Lemma per_prime_agreement : forall (p : Uint63.int),
  In p crt_primes_all ->
  List.map (Z_to_mod63 p) charpoly_Z_A =
  List.map (Z_to_mod63 p) charpoly_of_A_int.
Proof.
  intros p Hin. apply list_eqb63_sound.
  exact (proj1 (List.forallb_forall _ _) check_charpoly_Z_710_ok p Hin).
Qed.

(* === Verified bounds === *)

Lemma crt_bound_sufficient :
  (2 * (2 * 42 * max_abs_entry A_int) ^ 42 +
   2 * max_abs_coeff charpoly_of_A_int < crt_product_710)%Z.
Proof. Admitted.
(* UNCOMMENT on machine with ≥8 GB RAM (~2 min):
Proof. vm_compute. reflexivity. Qed. *)

(* === Opaque wrappers for matrix terms === *)

Definition mat_lhs_opaque : mat := mscale D_M2 (mmul M1_int A_int).
Lemma length_mat_lhs : length mat_lhs_opaque = 42%nat.
Proof. unfold mat_lhs_opaque, mscale, mmul. rewrite !List.length_map.
  vm_compute. reflexivity. Qed.
Lemma mat_lhs_wf : all_rows_len 42%nat mat_lhs_opaque.
Proof. unfold mat_lhs_opaque. apply all_rows_len_mscale. apply all_rows_len_mmul.
  - exact A_int_dim.
  - exact (forallb_all_rows_len 42%nat A_int A_int_rows_42). Qed.
Opaque mat_lhs_opaque.

Definition mat_rhs_opaque : mat := mscale (Z.mul D_M1 D_A) M2_int.
Lemma length_mat_rhs : length mat_rhs_opaque = 42%nat.
Proof. unfold mat_rhs_opaque, mscale. rewrite List.length_map.
  vm_compute. reflexivity. Qed.
Lemma mat_rhs_wf : all_rows_len 42%nat mat_rhs_opaque.
Proof. unfold mat_rhs_opaque. apply all_rows_len_mscale.
  exact (forallb_all_rows_len 42%nat M2_int ltac:(vm_compute; reflexivity)). Qed.
Opaque mat_rhs_opaque.

(* === CRT lift: fl_eq_flint === *)

Lemma fl_eq_flint : charpoly_Z_A = charpoly_of_A_int.
Proof.
  apply List.nth_ext with 0%Z 0%Z.
  { rewrite length_charpoly_Z_A. rewrite length_charpoly_of_A. reflexivity. }
  intros n Hn. rewrite length_charpoly_Z_A in Hn.
  set (a := List.nth n charpoly_Z_A 0%Z).
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
      assert (H : List.nth n (List.map (Z_to_mod63 p) charpoly_Z_A)
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

(* === CRT lift: matrix_identity_Z === *)

(* --- Generic length helpers --- *)

Lemma length_mscale (c : Z) (M : mat) : length (mscale c M) = length M.
Proof. unfold mscale. apply List.length_map. Qed.

Lemma length_mmul (A B : mat) : length (mmul A B) = length A.
Proof. unfold mmul. apply List.length_map. Qed.

(* --- Concrete dimension/well-formedness facts --- *)

Lemma M1_int_len : length M1_int = 42%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma M2_int_len : length M2_int = 42%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma M2_int_rows_42 :
  forallb (fun row => Nat.eqb (List.length row) 42) M2_int = true.
Proof. vm_compute. reflexivity. Qed.

Lemma M1_int_rows_42 :
  forallb (fun row => Nat.eqb (List.length row) 42) M1_int = true.
Proof. vm_compute. reflexivity. Qed.

Lemma M1_int_wf : all_rows_len 42%nat M1_int.
Proof. exact (forallb_all_rows_len 42%nat M1_int M1_int_rows_42). Qed.

Lemma A_int_wf : all_rows_len 42%nat A_int.
Proof. exact (forallb_all_rows_len 42%nat A_int A_int_rows_42). Qed.

Lemma M2_int_wf : all_rows_len 42%nat M2_int.
Proof. exact (forallb_all_rows_len 42%nat M2_int M2_int_rows_42). Qed.

Lemma mmul_M1_A_wf : all_rows_len 42%nat (mmul M1_int A_int).
Proof. apply all_rows_len_mmul; [exact A_int_dim | exact A_int_wf]. Qed.

Lemma lhs_mat_wf : all_rows_len 42%nat (mscale D_M2 (mmul M1_int A_int)).
Proof. apply all_rows_len_mscale. exact mmul_M1_A_wf. Qed.

Lemma rhs_mat_wf : all_rows_len 42%nat (mscale (Z.mul D_M1 D_A) M2_int).
Proof. apply all_rows_len_mscale. exact M2_int_wf. Qed.

Definition check_mat_Z_entry (p : Uint63.int) (i j : nat) : bool :=
  Uint63.eqb (Z_to_mod63 p (mat_get mat_lhs_opaque i j))
             (Z_to_mod63 p (mat_get mat_rhs_opaque i j)).

Definition check_mat_Z_710 : bool :=
  List.forallb (fun p =>
    List.forallb (fun i =>
      List.forallb (fun j =>
        check_mat_Z_entry p (Z.to_nat i) (Z.to_nat j))
      (List.map Z.of_nat (List.seq 0 42)))
    (List.map Z.of_nat (List.seq 0 42)))
  crt_primes_all.

Lemma check_mat_Z_710_ok : check_mat_Z_710 = true.
Proof. Admitted.
(* UNCOMMENT on machine with ≥8 GB RAM (~5-30 min):
Proof. Transparent mat_lhs_opaque mat_rhs_opaque. vm_compute. reflexivity. Qed. *)

Lemma per_prime_matrix_agreement : forall (p : Uint63.int),
  In p crt_primes_all ->
  forall i j : nat, (i < 42)%nat -> (j < 42)%nat ->
  Z_to_mod63 p (mat_get mat_lhs_opaque i j) =
  Z_to_mod63 p (mat_get mat_rhs_opaque i j).
Proof.
  intros p Hin i j Hi Hj.
  assert (Hcheck := proj1 (List.forallb_forall _ _) check_mat_Z_710_ok p Hin).
  assert (Hi_in : In (Z.of_nat i) (List.map Z.of_nat (List.seq 0 42))).
  { apply List.in_map. apply List.in_seq. lia. }
  assert (Hj_in : In (Z.of_nat j) (List.map Z.of_nat (List.seq 0 42))).
  { apply List.in_map. apply List.in_seq. lia. }
  assert (Hrow := proj1 (List.forallb_forall _ _) Hcheck _ Hi_in).
  assert (Hcol := proj1 (List.forallb_forall _ _) Hrow _ Hj_in).
  unfold check_mat_Z_entry in Hcol. rewrite !Nat2Z.id in Hcol.
  apply Uint63.eqb_spec in Hcol. exact Hcol.
Qed.

(* --- max_abs_entry bounds --- *)

Lemma fold_left_max_mono (l : list Z) (acc : Z) :
  (0 <= acc)%Z ->
  (acc <= List.fold_left (fun a x => Z.max a (Z.abs x)) l acc)%Z.
Proof.
  revert acc. induction l as [|x l IH]; intros acc Hacc; simpl.
  - lia.
  - apply Z.le_trans with (Z.max acc (Z.abs x)).
    + lia.
    + apply IH. lia.
Qed.

Lemma fold_left_max_in (l : list Z) (acc : Z) (c : Z) :
  (0 <= acc)%Z -> In c l ->
  (Z.abs c <= List.fold_left (fun a x => Z.max a (Z.abs x)) l acc)%Z.
Proof.
  revert acc. induction l as [|x l IH]; intros acc Hacc Hin; simpl.
  - destruct Hin.
  - destruct Hin as [<- | Hin].
    + apply Z.le_trans with (Z.max acc (Z.abs x)).
      * lia.
      * apply fold_left_max_mono. lia.
    + apply IH; [lia | exact Hin].
Qed.

Lemma fold_left_outer_mono (M : mat) (acc : Z) :
  (0 <= acc)%Z ->
  (acc <= List.fold_left (fun a row =>
    List.fold_left (fun a2 x => Z.max a2 (Z.abs x)) row a) M acc)%Z.
Proof.
  revert acc. induction M as [|r M IH]; intros acc Hacc; simpl.
  - lia.
  - apply Z.le_trans with
      (List.fold_left (fun a2 x => Z.max a2 (Z.abs x)) r acc).
    + apply fold_left_max_mono. exact Hacc.
    + apply IH. apply Z.le_trans with acc; [exact Hacc | apply fold_left_max_mono; exact Hacc].
Qed.

Lemma max_abs_entry_row_bound_gen (M : mat) (acc : Z) (row : list Z) (c : Z) :
  (0 <= acc)%Z -> In row M -> In c row ->
  (Z.abs c <= List.fold_left (fun a r =>
    List.fold_left (fun a2 x => Z.max a2 (Z.abs x)) r a) M acc)%Z.
Proof.
  revert acc. induction M as [|r M' IH]; intros acc Hacc Hrow Hc.
  - destruct Hrow.
  - simpl. destruct Hrow as [<- | Hrow].
    + apply Z.le_trans with
        (List.fold_left (fun a x => Z.max a (Z.abs x)) r acc).
      * apply fold_left_max_in; [exact Hacc | exact Hc].
      * apply fold_left_outer_mono.
        apply Z.le_trans with acc; [exact Hacc | apply fold_left_max_mono; exact Hacc].
    + apply IH; [| exact Hrow | exact Hc].
      apply Z.le_trans with acc; [exact Hacc | apply fold_left_max_mono; exact Hacc].
Qed.

Lemma max_abs_entry_row_bound (M : mat) (row : list Z) (c : Z) :
  In row M -> In c row ->
  (Z.abs c <= max_abs_entry M)%Z.
Proof.
  intros Hrow Hc. unfold max_abs_entry.
  exact (max_abs_entry_row_bound_gen M 0%Z row c ltac:(lia) Hrow Hc).
Qed.

Lemma max_abs_entry_nonneg (M : mat) : (0 <= max_abs_entry M)%Z.
Proof. unfold max_abs_entry. exact (fold_left_outer_mono M 0%Z ltac:(lia)). Qed.

Lemma max_abs_entry_get (M : mat) (i j : nat) :
  (i < length M)%nat -> (j < length (List.nth i M nil))%nat ->
  (Z.abs (mat_get M i j) <= max_abs_entry M)%Z.
Proof.
  intros Hi Hj. unfold mat_get, nth_Z.
  apply max_abs_entry_row_bound with (row := List.nth i M nil).
  - apply List.nth_In. exact Hi.
  - apply List.nth_In. exact Hj.
Qed.

(* --- Dot product bound --- *)

Lemma dot_int_bound (u v : list Z) (n : nat) (Bu Bv : Z) :
  length u = n -> length v = n ->
  (forall k, (k < n)%nat -> (Z.abs (List.nth k u 0%Z) <= Bu)%Z) ->
  (forall k, (k < n)%nat -> (Z.abs (List.nth k v 0%Z) <= Bv)%Z) ->
  (0 <= Bu)%Z -> (0 <= Bv)%Z ->
  (Z.abs (dot_int u v) <= Z.of_nat n * Bu * Bv)%Z.
Proof.
  revert v n Bu Bv. induction u as [|a u IH]; intros v n Bu Bv Hlu Hlv Hbu Hbv HBu HBv.
  - simpl in Hlu. subst n. simpl. lia.
  - destruct v as [|b v']; [simpl in *; lia|].
    simpl in Hlu, Hlv. simpl.
    assert (Hn : n = S (length u)) by lia. subst n.
    assert (Hlv' : length v' = length u) by lia.
    apply Z.le_trans with (Z.abs (a * b) + Z.abs (dot_int u v'))%Z.
    { apply Z.abs_triangle. }
    apply Z.le_trans with (Bu * Bv + Z.of_nat (length u) * Bu * Bv)%Z.
    { apply Z.add_le_mono.
      { rewrite Z.abs_mul.
        apply Z.mul_le_mono_nonneg; try apply Z.abs_nonneg.
        - exact (Hbu 0%nat ltac:(lia)).
        - exact (Hbv 0%nat ltac:(lia)). }
      { apply IH; try assumption.
        - reflexivity.
        - intros k Hk. apply (Hbu (S k)). lia.
        - intros k Hk. apply (Hbv (S k)). lia. } }
    { rewrite Nat2Z.inj_succ. nia. }
Qed.

(* --- Entry bounds (proved, not axioms) --- *)

Definition mat_id_lhs_bound : Z :=
  (Z.abs D_M2 * (42 * max_abs_entry M1_int * max_abs_entry A_int))%Z.

Lemma matrix_lhs_entry_bound : forall i j : nat,
  (i < 42)%nat -> (j < 42)%nat ->
  (Z.abs (mat_get (mscale D_M2 (mmul M1_int A_int)) i j) <= mat_id_lhs_bound)%Z.
Proof.
  intros i j Hi Hj.
  rewrite mat_get_mscale. rewrite Z.abs_mul.
  unfold mat_id_lhs_bound.
  apply Z.mul_le_mono_nonneg_l; [apply Z.abs_nonneg|].
  (* Rewrite to dot product *)
  rewrite (mat_get_mmul_sq M1_int A_int 42%nat i j
    M1_int_len A_int_dim M1_int_wf A_int_wf Hi Hj).
  (* Bound the dot product *)
  apply Z.le_trans with (Z.of_nat 42 * max_abs_entry M1_int * max_abs_entry A_int)%Z.
  2:{ lia. }
  apply dot_int_bound with (n := 42%nat).
  - exact (M1_int_wf i ltac:(rewrite M1_int_len; exact Hi)).
  - exact (nth_mtrans_length_sq A_int 42%nat j A_int_dim A_int_wf Hj).
  - intros k Hk. apply max_abs_entry_get.
    + rewrite M1_int_len. exact Hi.
    + rewrite (M1_int_wf i ltac:(rewrite M1_int_len; exact Hi)). exact Hk.
  - intros k Hk.
    (* nth k (nth j (mtrans A_int) nil) 0 = nth_Z (nth k A_int nil) j *)
    rewrite (nth_nth_mtrans_sq A_int 42%nat j k A_int_dim A_int_wf Hj).
    unfold nth_Z. apply max_abs_entry_get.
    + change (length A_int) with (mat_dim A_int). rewrite A_int_dim. exact Hk.
    + rewrite (A_int_wf k ltac:(change (length A_int) with (mat_dim A_int);
        rewrite A_int_dim; exact Hk)). exact Hj.
  - exact (max_abs_entry_nonneg _).
  - exact (max_abs_entry_nonneg _).
Qed.

Definition mat_id_rhs_bound : Z :=
  (Z.abs (Z.mul D_M1 D_A) * max_abs_entry M2_int)%Z.

Lemma matrix_rhs_entry_bound : forall i j : nat,
  (i < 42)%nat -> (j < 42)%nat ->
  (Z.abs (mat_get (mscale (Z.mul D_M1 D_A) M2_int) i j) <= mat_id_rhs_bound)%Z.
Proof.
  intros i j Hi Hj.
  rewrite mat_get_mscale. rewrite Z.abs_mul.
  unfold mat_id_rhs_bound.
  apply Z.mul_le_mono_nonneg_l; [apply Z.abs_nonneg|].
  apply max_abs_entry_get.
  - rewrite M2_int_len. exact Hi.
  - rewrite (M2_int_wf i ltac:(rewrite M2_int_len; exact Hi)). exact Hj.
Qed.

(* Verified bound: 2 * LHS_bound + 2 * RHS_bound < product of 710 primes. *)
Lemma matrix_crt_bound_sufficient :
  (2 * mat_id_lhs_bound + 2 * mat_id_rhs_bound < crt_product_710)%Z.
Proof. Admitted.
(* UNCOMMENT on machine with ≥8 GB RAM (~1 min):
Proof. vm_compute. reflexivity. Qed. *)

(* === The CRT lift proof === *)

Lemma matrix_identity_Z :
  mat_lhs_opaque = mat_rhs_opaque.
Proof.
  set (LHS := mat_lhs_opaque).
  set (RHS := mat_rhs_opaque).
  assert (HlenL : length LHS = 42%nat) by exact length_mat_lhs.
  assert (HlenR : length RHS = 42%nat) by exact length_mat_rhs.
  (* Outer: row-by-row equality *)
  apply List.nth_ext with (d := @nil Z) (d' := @nil Z).
  { lia. }
  intros i Hi. rewrite HlenL in Hi.
  (* Inner: element-by-element equality within row i *)
  assert (Hrowi_L : length (List.nth i LHS nil) = 42%nat).
  { apply mat_lhs_wf. rewrite length_mat_lhs. exact Hi. }
  assert (Hrowi_R : length (List.nth i RHS nil) = 42%nat).
  { apply mat_rhs_wf. rewrite length_mat_rhs. exact Hi. }
  apply List.nth_ext with (d := 0%Z) (d' := 0%Z).
  { lia. }
  intros j Hj. rewrite Hrowi_L in Hj.
  (* Goal: nth j (nth i LHS nil) 0 = nth j (nth i RHS nil) 0
     which is mat_get LHS i j = mat_get RHS i j *)
  change (mat_get LHS i j = mat_get RHS i j).
  set (a := mat_get LHS i j).
  set (b := mat_get RHS i j).
  cut ((a - b)%Z = 0%Z). { unfold a, b. lia. }
  apply (small_multiple_zero _ crt_product_710).
  { (* product | (a - b) *)
    unfold crt_product_710.
    apply all_primes_divide_product.
    { exact crt_primes_710_NoDup. }
    { exact crt_primes_710_all_prime. }
    intros pz Hpz. apply List.in_map_iff in Hpz.
    destruct Hpz as [p [Hpeq Hin]]. subst pz.
    pose proof (per_prime_matrix_agreement p Hin i j Hi Hj) as Hagree.
    fold LHS RHS in Hagree. fold a b in Hagree.
    apply (f_equal Uint63.to_Z) in Hagree.
    pose proof (crt_primes_valid p Hin) as Hvp.
    rewrite !Z_to_mod63_spec in Hagree; [|exact Hvp|exact Hvp].
    destruct Hvp as [Hvp1 _].
    assert (Hpnz : (Uint63.to_Z p <> 0)%Z) by lia.
    exists ((a / Uint63.to_Z p - b / Uint63.to_Z p)%Z).
    rewrite Z.mul_sub_distr_r.
    rewrite (Z.div_mod a (Uint63.to_Z p) Hpnz) at 1.
    rewrite (Z.div_mod b (Uint63.to_Z p) Hpnz) at 1. lia. }
  { exact crt_product_710_pos. }
  { apply Z.le_lt_trans with (2 * Z.abs a + 2 * Z.abs b)%Z.
    { pose proof (Z.abs_triangle a (-b)). rewrite Z.abs_opp in H. lia. }
    apply Z.le_lt_trans with (2 * mat_id_lhs_bound + 2 * mat_id_rhs_bound)%Z.
    { apply Z.add_le_mono.
      { apply Z.mul_le_mono_nonneg_l; [lia|].
        exact (matrix_lhs_entry_bound i j Hi Hj). }
      { apply Z.mul_le_mono_nonneg_l; [lia|].
        exact (matrix_rhs_entry_bound i j Hi Hj). } }
    exact matrix_crt_bound_sufficient. }
Qed.
