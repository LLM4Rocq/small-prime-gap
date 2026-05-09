(* CRTLift.v — CRT lift lemmas for fl_eq_flint and matrix_identity_Z.
   NO MathComp imports to avoid scope issues and slow type resolution. *)

From Stdlib Require Import ZArith List Lia Uint63 Bool Znumtheory.
From PrimeGapS1 Require Import IntMat CharPoly Witness ModularArith CharPolyAgree.
From PrimeGapS1 Require Import CRTBridge CRTCheck Fermat PrimeCheck.

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

(* Generic structural lemmas about char_poly_int (no specific matrix) *)
Lemma char_poly_int_nth_lt (M : mat) (n k : nat) :
  mat_dim M = n -> (k < n)%nat ->
  List.nth k (char_poly_int M) 0%Z =
  List.nth k (fl_loop n Z.one M (meye n) (mzero n) Z.one nil) 0%Z.
Proof.
  intros Hd Hk. unfold char_poly_int. rewrite Hd.
  rewrite List.app_nth1; [reflexivity|rewrite fl_loop_length; simpl; lia].
Qed.

Lemma char_poly_int_nth_leading (M : mat) (n : nat) :
  mat_dim M = n ->
  List.nth n (char_poly_int M) 0%Z = Z.one.
Proof.
  intro Hd. unfold char_poly_int. rewrite Hd.
  rewrite List.app_nth2; [|rewrite fl_loop_length; simpl; lia].
  rewrite fl_loop_length. simpl.
  replace (n - (n + 0))%nat with 0%nat by lia. reflexivity.
Qed.

Lemma length_char_poly_int_A : length (char_poly_int A_int) = 43%nat.
Proof. rewrite length_char_poly_int_gen. rewrite A_int_dim. reflexivity. Qed.

Lemma length_charpoly_of_A : length charpoly_of_A_int = 43%nat.
Proof. exact length_charpoly_of_A_int. Qed.

(* Opaque wrapper for the FL-computed charpoly to prevent kernel expansion *)
Definition charpoly_Z_A : list Z := char_poly_int A_int.
Lemma length_charpoly_Z_A : length charpoly_Z_A = 43%nat.
Proof. unfold charpoly_Z_A. exact length_char_poly_int_A. Qed.

(* Bridge: opaque equation to use in proofs without triggering kernel unfold *)
Lemma charpoly_Z_A_eq : charpoly_Z_A = char_poly_int A_int.
Proof. reflexivity. Qed.

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
Proof. vm_compute. reflexivity. Qed.

Lemma crt_primes_710_NoDup :
  NoDup (List.map Uint63.to_Z crt_primes_all).
Proof. exact (nodup_Z_sound _ crt_primes_710_NoDup_check). Qed.

(* ================================================================ *)
(*  Section: All CRT primes are prime                                  *)
(* ================================================================ *)

Lemma check_all_primes_710 :
  List.forallb (fun p => check_prime_Z (Uint63.to_Z p)) crt_primes_all = true.
Proof. vm_compute. reflexivity. Qed.

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
(*  Section: Charpoly coefficient bound                                *)
(* ================================================================ *)

(* === FL coefficient bound via computable recurrence ===
   The FL loop computes c_k = -tr(A*M_k)/k. We bound |c_k| by tracking
   max_abs_entry(M_k) and |c_k| through the recurrence. The bound is
   COMPUTABLE from (n, B), so we check it against the CRT product by
   vm_compute — no MathComp det theory needed. *)

Fixpoint fl_bound_aux (remaining : nat) (k n B E_prev C_prev max_c : Z) : Z :=
  match remaining with
  | O => max_c
  | S s =>
    let E_k := (n * B * E_prev + Z.abs C_prev)%Z in
    let C_k := Z.div (n * n * B * E_k) k in
    fl_bound_aux s (k + 1) n B E_k C_k (Z.max max_c (Z.abs C_k))
  end.

Definition fl_coeff_bound (sz : nat) (B : Z) : Z :=
  fl_bound_aux sz 1 (Z.of_nat sz) B 0 1 1.

(* FL bound fits within CRT product — vm_compute, ~2 min *)
Lemma fl_crt_bound :
  (2 * fl_coeff_bound 42 (max_abs_entry A_int) +
   2 * max_abs_coeff charpoly_of_A_int < crt_product_710)%Z.
Proof. apply Z.ltb_lt. vm_compute. reflexivity. Qed.

(* --- max_abs_entry infrastructure --- *)

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
    + apply IH. apply Z.le_trans with acc;
        [exact Hacc | apply fold_left_max_mono; exact Hacc].
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
        apply Z.le_trans with acc;
          [exact Hacc | apply fold_left_max_mono; exact Hacc].
    + apply IH; [| exact Hrow | exact Hc].
      apply Z.le_trans with acc;
        [exact Hacc | apply fold_left_max_mono; exact Hacc].
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

Lemma fold_left_zmax_le (l : list Z) (acc B : Z) :
  (acc <= B)%Z -> (forall x, In x l -> (Z.abs x <= B)%Z) ->
  (List.fold_left (fun a x => Z.max a (Z.abs x)) l acc <= B)%Z.
Proof.
  revert acc. induction l as [|x l IH]; intros acc Hacc Hall; simpl; [exact Hacc|].
  apply IH; [|intros y Hy; exact (Hall y (or_intror Hy))].
  pose proof (Hall x (or_introl eq_refl)). lia.
Qed.

Lemma fold_left_zmax_outer_le (M : mat) (acc B : Z) :
  (acc <= B)%Z ->
  (forall row, In row M -> forall x, In x row -> (Z.abs x <= B)%Z) ->
  (List.fold_left (fun a row =>
    List.fold_left (fun a2 x => Z.max a2 (Z.abs x)) row a) M acc <= B)%Z.
Proof.
  revert acc. induction M as [|r M IH]; intros acc Hacc Hall; simpl; [exact Hacc|].
  apply IH; [|intros row Hr x Hx; exact (Hall row (or_intror Hr) x Hx)].
  apply fold_left_zmax_le; [exact Hacc|exact (Hall r (or_introl eq_refl))].
Qed.

Lemma max_abs_entry_le_bound (M : mat) (B : Z) :
  (0 <= B)%Z ->
  (forall i j, (i < length M)%nat -> (j < length (List.nth i M nil))%nat ->
    (Z.abs (mat_get M i j) <= B)%Z) ->
  (max_abs_entry M <= B)%Z.
Proof.
  intros HB Hentry. unfold max_abs_entry.
  apply fold_left_zmax_outer_le; [lia|].
  intros row Hrow x Hx.
  apply List.In_nth with (d := nil) in Hrow. destruct Hrow as [i [Hi Hri]].
  apply List.In_nth with (d := 0%Z) in Hx. destruct Hx as [j [Hj Hxj]].
  subst. exact (Hentry i j Hi Hj).
Qed.

Lemma fold_left_zmax_zrow_0 (n : nat) :
  List.fold_left (fun (a : Z) (x : Z) => Z.max a (Z.abs x)) (zrow n) 0%Z = 0%Z.
Proof.
  induction n as [|k IH]; [reflexivity|].
  simpl zrow. simpl fold_left. replace (Z.max 0 0) with 0%Z by lia. exact IH.
Qed.

Lemma max_abs_entry_mzero_aux (r c : nat) :
  max_abs_entry (mzero_aux r c) = 0%Z.
Proof.
  unfold max_abs_entry. induction r as [|k IH]; [reflexivity|].
  simpl mzero_aux. simpl fold_left. rewrite fold_left_zmax_zrow_0. exact IH.
Qed.

Lemma max_abs_entry_mzero (n : nat) : max_abs_entry (mzero n) = 0%Z.
Proof. exact (max_abs_entry_mzero_aux n n). Qed.

(* --- Generic length helpers (needed for bounds below) --- *)

Lemma length_mscale (c : Z) (M : mat) : length (mscale c M) = length M.
Proof. unfold mscale. apply List.length_map. Qed.

Lemma length_mmul (A B : mat) : length (mmul A B) = length A.
Proof. unfold mmul. apply List.length_map. Qed.

(* --- Matrix operation bounds (simple, provable from entry-level reasoning) --- *)

Lemma max_abs_entry_meye_le (n : nat) : (max_abs_entry (meye n) <= 1)%Z.
Proof.
  apply max_abs_entry_le_bound; [lia|].
  intros i j Hi Hj.
  unfold meye in Hi. rewrite meye_aux_len in Hi.
  destruct (Nat.eq_dec i j) as [<-|Hne].
  - rewrite mat_get_meye_eq; [simpl; lia | exact Hi].
  - rewrite mat_get_meye_neq; [simpl; lia | exact Hi | exact Hne].
Qed.

Lemma max_abs_entry_mscale_le (c : Z) (M : mat) :
  (max_abs_entry (mscale c M) <= Z.abs c * max_abs_entry M)%Z.
Proof.
  apply max_abs_entry_le_bound.
  - apply Z.mul_nonneg_nonneg; [apply Z.abs_nonneg | apply max_abs_entry_nonneg].
  - intros i j Hi Hj.
    rewrite length_mscale in Hi.
    assert (Hj' : (j < length (List.nth i M nil))%nat).
    { unfold mscale in Hj.
      rewrite (List.nth_indep _ nil (vscale c nil)) in Hj;
        [|rewrite List.length_map; exact Hi].
      rewrite List.map_nth in Hj. rewrite length_vscale in Hj. exact Hj. }
    rewrite mat_get_mscale. rewrite Z.abs_mul.
    apply Z.mul_le_mono_nonneg_l; [apply Z.abs_nonneg|].
    apply max_abs_entry_get; [exact Hi | exact Hj'].
Qed.

Lemma max_abs_entry_madd_le (A B : mat) (n : nat) :
  mat_dim A = n -> mat_dim B = n -> all_rows_len n A -> all_rows_len n B ->
  (max_abs_entry (madd A B) <= max_abs_entry A + max_abs_entry B)%Z.
Proof.
  intros HdA HdB HrA HrB.
  apply max_abs_entry_le_bound.
  - pose proof (max_abs_entry_nonneg A). pose proof (max_abs_entry_nonneg B). lia.
  - intros i j Hi Hj.
    assert (HlenAB : length A = length B) by (unfold mat_dim in *; lia).
    assert (Hi' : (i < length A)%nat).
    { unfold mat_dim in *. rewrite mat_dim_madd_eq in Hi;
        [exact Hi | exact HlenAB]. }
    assert (Hj' : (j < n)%nat).
    { assert (Htmp : all_rows_len n (madd A B))
        by (apply all_rows_len_madd; [exact HlenAB | exact HrA | exact HrB]).
      assert (Hi'' : (i < length (madd A B))%nat)
        by (rewrite mat_dim_madd_eq; [exact Hi' | exact HlenAB]).
      rewrite (Htmp i Hi'') in Hj. exact Hj. }
    rewrite (mat_get_madd A B n i j HlenAB HrA HrB Hi').
    apply Z.le_trans with (Z.abs (mat_get A i j) + Z.abs (mat_get B i j))%Z.
    + apply Z.abs_triangle.
    + apply Z.add_le_mono.
      * apply max_abs_entry_get; [exact Hi' | rewrite (HrA i Hi'); exact Hj'].
      * apply max_abs_entry_get;
          [unfold mat_dim in *; lia |
           rewrite (HrB i ltac:(unfold mat_dim in *; lia)); exact Hj'].
Qed.

Lemma max_abs_entry_mmul_le (A B : mat) (n : nat) :
  mat_dim A = n -> mat_dim B = n -> all_rows_len n A -> all_rows_len n B ->
  (max_abs_entry (mmul A B) <= Z.of_nat n * max_abs_entry A * max_abs_entry B)%Z.
Proof.
  intros HdA HdB HrA HrB.
  apply max_abs_entry_le_bound.
  - apply Z.mul_nonneg_nonneg; [|apply max_abs_entry_nonneg].
    apply Z.mul_nonneg_nonneg; [lia|apply max_abs_entry_nonneg].
  - intros i j Hi Hj.
    assert (Hi' : (i < n)%nat)
      by (rewrite length_mmul in Hi; unfold mat_dim in HdA; lia).
    assert (Hj' : (j < n)%nat).
    { assert (Hwf : all_rows_len n (mmul A B))
        by (apply all_rows_len_mmul; [exact HdB | exact HrB]).
      assert (Hi'' : (i < length (mmul A B))%nat)
        by (rewrite length_mmul; unfold mat_dim in HdA; lia).
      rewrite (Hwf i Hi'') in Hj. exact Hj. }
    unfold mat_dim in HdA, HdB.
    rewrite (mat_get_mmul_sq A B n i j HdA HdB HrA HrB Hi' Hj').
    apply dot_int_bound with (n := n).
    + rewrite (HrA i ltac:(lia)). reflexivity.
    + rewrite (nth_mtrans_length_sq B n j HdB HrB Hj'). exact HdB.
    + intros k Hk. apply max_abs_entry_get;
        [lia | rewrite (HrA i ltac:(lia)); exact Hk].
    + intros k Hk.
      rewrite (nth_nth_mtrans_sq B n j k HdB HrB Hj').
      unfold nth_Z. apply max_abs_entry_get;
        [lia | rewrite (HrB k ltac:(lia)); exact Hj'].
    + exact (max_abs_entry_nonneg A).
    + exact (max_abs_entry_nonneg B).
Qed.

Lemma abs_mtrace_aux_le (M_orig : mat) (M' : mat) :
  forall (i : nat),
    (forall k, (k < length M')%nat ->
      (Z.abs (mat_get M' k (k + i)) <= max_abs_entry M_orig)%Z) ->
    (Z.abs (mtrace_aux i M') <= Z.of_nat (length M') * max_abs_entry M_orig)%Z.
Proof.
  induction M' as [|row M' IH]; intros i Hget.
  - simpl. lia.
  - simpl mtrace_aux. simpl length.
    apply Z.le_trans with (Z.abs (nth_Z row i) + Z.abs (mtrace_aux (S i) M'))%Z.
    + apply Z.abs_triangle.
    + assert (Hget0 : (Z.abs (nth_Z row i) <= max_abs_entry M_orig)%Z).
      { specialize (Hget 0%nat ltac:(simpl; lia)). simpl in Hget.
        replace (0 + i)%nat with i in Hget by lia. exact Hget. }
      assert (HIH : (Z.abs (mtrace_aux (S i) M') <=
        Z.of_nat (length M') * max_abs_entry M_orig)%Z).
      { apply IH. intros k Hk.
        specialize (Hget (S k) ltac:(simpl; lia)). simpl in Hget.
        replace (k + S i)%nat with (S (k + i)) by lia. exact Hget. }
      rewrite Nat2Z.inj_succ. pose proof (max_abs_entry_nonneg M_orig). nia.
Qed.

Lemma abs_mtrace_le (M : mat) (n : nat) :
  mat_dim M = n -> all_rows_len n M ->
  (Z.abs (mtrace M) <= Z.of_nat n * max_abs_entry M)%Z.
Proof.
  intros Hdim Hwf. unfold mtrace, mat_dim in *. rewrite <- Hdim.
  apply abs_mtrace_aux_le. intros k Hk.
  replace (k + 0)%nat with k by lia.
  apply max_abs_entry_get; [lia | rewrite (Hwf k Hk); lia].
Qed.

(* --- Divisibility helper for FL loop bound --- *)

Lemma Z_abs_div_exact (a k : Z) :
  (0 < k)%Z -> (k | a)%Z -> (Z.abs (Z.div a k) = Z.div (Z.abs a) k)%Z.
Proof.
  intros Hk [q Hq]. subst a.
  rewrite Z.div_mul; [|lia].
  assert (Hkabs : Z.abs k = k) by lia. rewrite Z.abs_mul, Hkabs.
  rewrite Z_div_mult_full; [reflexivity | lia].
Qed.

Lemma Z_abs_div_le (a k B : Z) :
  (0 < k)%Z -> (k | a)%Z -> (Z.abs a <= B)%Z ->
  (Z.abs (Z.div a k) <= Z.div B k)%Z.
Proof.
  intros Hk Hdiv Hle.
  rewrite Z_abs_div_exact; [| exact Hk | exact Hdiv].
  apply Z.div_le_mono; lia.
Qed.

(* --- FL loop induction --- *)

Lemma fl_loop_coeff_bound (steps : nat) (k : Z) (A I_n M_prev : mat)
  (c_prev : Z) (acc : list Z) (n : nat) (B E_prev C_prev max_c : Z) :
  mat_dim A = n -> all_rows_len n A ->
  I_n = meye n ->
  mat_dim M_prev = n -> all_rows_len n M_prev ->
  (0 < k)%Z ->
  (max_abs_entry A <= B)%Z -> (0 <= B)%Z ->
  (max_abs_entry M_prev <= E_prev)%Z -> (0 <= E_prev)%Z ->
  (Z.abs c_prev <= C_prev)%Z ->
  (forall c, In c acc -> (Z.abs c <= max_c)%Z) ->
  (0 <= max_c)%Z ->
  fl_all_divisible steps k A I_n M_prev c_prev ->
  forall c, In c (fl_loop steps k A I_n M_prev c_prev acc) ->
  (Z.abs c <= fl_bound_aux steps k (Z.of_nat n) B E_prev C_prev max_c)%Z.
Proof.
  revert k M_prev c_prev acc E_prev C_prev max_c.
  induction steps as [|s IH]; intros k M_prev c_prev acc E_prev C_prev max_c
    HdA HrA HIn HdM HrM Hk HaB HB HaE HE HaC Hacc Hmc Hdiv c Hc.
  - simpl in Hc. exact (Hacc c Hc).
  - simpl in Hc, Hdiv.
    set (AMprev := mmul A M_prev) in *.
    set (M_k := madd AMprev (mscale c_prev I_n)) in *.
    set (AMk := mmul A M_k) in *.
    set (tr := mtrace AMk) in *.
    set (c_new := Z.div (Z.opp tr) k) in *.
    destruct Hdiv as [Hdiv_tr Hdiv_rest].
    assert (HdI : mat_dim I_n = n) by (subst I_n; apply mat_dim_meye).
    assert (HrI : all_rows_len n I_n) by (subst I_n; apply all_rows_len_meye).
    assert (HdAMprev : mat_dim AMprev = n)
      by (unfold AMprev; rewrite mat_dim_mmul_eq; exact HdA).
    assert (HrAMprev : all_rows_len n AMprev)
      by (unfold AMprev; apply all_rows_len_mmul; [exact HdM | exact HrM]).
    assert (HdMk : mat_dim M_k = n).
    { unfold M_k. rewrite mat_dim_madd_eq;
        [exact HdAMprev | rewrite mat_dim_mscale_eq; lia]. }
    assert (HrMk : all_rows_len n M_k).
    { unfold M_k. apply all_rows_len_madd.
      - rewrite mat_dim_mscale_eq. lia.
      - exact HrAMprev.
      - apply all_rows_len_mscale. exact HrI. }
    set (E_k := (Z.of_nat n * B * E_prev + Z.abs C_prev)%Z).
    assert (HaEk : (max_abs_entry M_k <= E_k)%Z).
    { unfold E_k, M_k.
      apply Z.le_trans with
        (max_abs_entry AMprev + max_abs_entry (mscale c_prev I_n))%Z.
      { apply (max_abs_entry_madd_le _ _ n);
          [exact HdAMprev | rewrite mat_dim_mscale_eq; exact HdI |
           exact HrAMprev | apply all_rows_len_mscale; exact HrI]. }
      apply Z.add_le_mono.
      { apply Z.le_trans with
          (Z.of_nat n * max_abs_entry A * max_abs_entry M_prev)%Z.
        { apply (max_abs_entry_mmul_le _ _ n);
            [exact HdA | exact HdM | exact HrA | exact HrM]. }
        apply Z.le_trans with (Z.of_nat n * B * max_abs_entry M_prev)%Z.
        { apply Z.mul_le_mono_nonneg_r;
            [apply max_abs_entry_nonneg |
             apply Z.mul_le_mono_nonneg_l; [lia | exact HaB]]. }
        apply Z.mul_le_mono_nonneg_l;
          [pose proof (max_abs_entry_nonneg A); nia | exact HaE]. }
      { apply Z.le_trans with (Z.abs c_prev * max_abs_entry I_n)%Z;
          [apply max_abs_entry_mscale_le |].
        apply Z.le_trans with (Z.abs c_prev * 1)%Z.
        { apply Z.mul_le_mono_nonneg_l; [apply Z.abs_nonneg |].
          subst I_n. apply max_abs_entry_meye_le. }
        rewrite Z.mul_1_r.
        apply Z.le_trans with C_prev; [exact HaC | lia]. } }
    set (C_k := Z.div (Z.of_nat n * Z.of_nat n * B * E_k) k).
    assert (HaCk : (Z.abs c_new <= C_k)%Z).
    { unfold c_new, C_k.
      apply Z_abs_div_le; [exact Hk | |].
      - destruct Hdiv_tr as [q Hq]. exists (-q)%Z. unfold tr. lia.
      - rewrite Z.abs_opp. unfold tr, AMk.
        assert (HdAMk : mat_dim (mmul A M_k) = n)
          by (rewrite mat_dim_mmul_eq; exact HdA).
        assert (HrAMk : all_rows_len n (mmul A M_k))
          by (apply all_rows_len_mmul; [exact HdMk | exact HrMk]).
        apply Z.le_trans with (Z.of_nat n * max_abs_entry (mmul A M_k))%Z;
          [apply abs_mtrace_le; [exact HdAMk | exact HrAMk] |].
        apply Z.le_trans with
          (Z.of_nat n * (Z.of_nat n * max_abs_entry A * max_abs_entry M_k))%Z.
        { apply Z.mul_le_mono_nonneg_l; [lia |].
          apply (max_abs_entry_mmul_le _ _ n);
            [exact HdA | exact HdMk | exact HrA | exact HrMk]. }
        apply Z.le_trans with (Z.of_nat n * (Z.of_nat n * B * E_k))%Z.
        { apply Z.mul_le_mono_nonneg_l; [lia |].
          apply Z.le_trans with
            (Z.of_nat n * B * max_abs_entry M_k)%Z.
          { apply Z.mul_le_mono_nonneg_r;
              [apply max_abs_entry_nonneg |
               apply Z.mul_le_mono_nonneg_l; [lia | exact HaB]]. }
          apply Z.mul_le_mono_nonneg_l;
            [pose proof (max_abs_entry_nonneg A); nia | exact HaEk]. }
        nia. }
    apply (IH (k + 1) M_k c_new (c_new :: acc) E_k C_k
              (Z.max max_c (Z.abs C_k))
              HdA HrA HIn HdMk HrMk ltac:(lia) HaB HB HaEk).
    + unfold E_k. pose proof (max_abs_entry_nonneg A).
      pose proof (Z.abs_nonneg C_prev). nia.
    + exact HaCk.
    + intros c' [<- | Hin]; [lia | pose proof (Hacc c' Hin); lia].
    + lia.
    + exact Hdiv_rest.
    + exact Hc.
Qed.

(* --- Assembly: FL coefficients bounded --- *)

Lemma fl_bound_aux_mono (steps : nat) (k n B E C mc : Z) :
  (0 <= mc)%Z ->
  (mc <= fl_bound_aux steps k n B E C mc)%Z.
Proof.
  revert k E C mc. induction steps as [|s IH]; intros k E C mc Hmc; simpl.
  - lia.
  - apply Z.le_trans with (Z.max mc (Z.abs (n * n * B * (n * B * E + Z.abs C) / k)))%Z.
    + lia.
    + apply IH. lia.
Qed.

(* Prevent kernel from expanding fl_all_divisible on concrete 42x42 matrix *)
Opaque fl_all_divisible.

(* Helper: specialize fl_all_divisible_from_L2 to A_int as a separate Qed.
   This makes the divisibility fact OPAQUE when used in charpoly_coeff_bound,
   preventing kernel reduction on the huge proof term. *)
Lemma A_int_fl_all_divisible :
  fl_all_divisible 42 Z.one A_int (meye 42) (mzero 42) Z.one.
Proof.
  apply fl_all_divisible_from_L2;
    [exact A_int_dim | exact (forallb_all_rows_len 42%nat A_int A_int_rows_42)].
Qed.

(* Helper: specialize fl_loop_coeff_bound to our A_int FL loop as a separate Qed. *)
Lemma A_int_fl_loop_coeff (k : nat) (Hk : (k < 42)%nat) :
  (Z.abs (List.nth k (fl_loop 42 Z.one A_int (meye 42) (mzero 42) Z.one nil) 0%Z)
   <= fl_bound_aux 42 1 (Z.of_nat 42) (max_abs_entry A_int) 0 1 1)%Z.
Proof.
  apply (fl_loop_coeff_bound 42 Z.one A_int (meye 42) (mzero 42) Z.one
            nil 42 (max_abs_entry A_int) 0 1 1).
  + exact A_int_dim.
  + exact (forallb_all_rows_len 42%nat A_int A_int_rows_42).
  + reflexivity.
  + exact (mat_dim_mzero 42).
  + apply all_rows_len_mzero.
  + reflexivity.
  + reflexivity.
  + apply max_abs_entry_nonneg.
  + rewrite max_abs_entry_mzero. reflexivity.
  + reflexivity.
  + reflexivity.
  + intros c' Hc'. destruct Hc'.
  + lia.
  + apply A_int_fl_all_divisible.
  + apply List.nth_In. rewrite fl_loop_length. simpl. exact Hk.
Qed.

Lemma charpoly_coeff_bound : forall k,
  (k < 43)%nat ->
  (Z.abs (List.nth k charpoly_Z_A 0%Z) <=
   fl_coeff_bound 42 (max_abs_entry A_int))%Z.
Proof.
  intros k Hk.
  rewrite charpoly_Z_A_eq.
  destruct (Nat.eq_dec k 42) as [->|Hne].
  - (* k = 42: leading coefficient is 1 *)
    rewrite (char_poly_int_nth_leading A_int 42 A_int_dim). simpl.
    unfold fl_coeff_bound. apply fl_bound_aux_mono. lia.
  - (* k < 42: coefficient from fl_loop, use pre-proved opaque helper *)
    assert (Hk' : (k < 42)%nat) by lia.
    rewrite (char_poly_int_nth_lt A_int 42 k A_int_dim Hk').
    unfold fl_coeff_bound.
    exact (A_int_fl_loop_coeff k Hk').
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

(* === Per-prime polynomial agreement via deductive chain ===
   1. char_poly_mod_sound: Z FL mod p = char_poly_mod p (fast Uint63 FL)
   2. char_poly_int_agrees_710: char_poly_mod p = shipped (bigZ) [existing Qed]
   3. BigZ/Z bridge: shipped (bigZ) = shipped (Z) [vm_compute below]     *)

(* Step 3: BigZ/Z bridge — vm_compute, ~3 min *)
Definition f_bigZ_bridge (p : Uint63.int) : bool :=
  list_eqb63 (List.map (bigZ_to_mod63 p) charpoly_of_A_int_bigZ)
             (List.map (Z_to_mod63 p) charpoly_of_A_int).

Lemma bigZ_bridge_710 : List.forallb f_bigZ_bridge crt_primes_all = true.
Proof. vm_compute. reflexivity. Qed.

Lemma per_prime_bigZ_eq p (Hin : In p crt_primes_all) :
  List.map (bigZ_to_mod63 p) charpoly_of_A_int_bigZ =
  List.map (Z_to_mod63 p) charpoly_of_A_int.
Proof. exact (list_eqb63_sound _ _ (proj1 (List.forallb_forall _ _) bigZ_bridge_710 p Hin)). Qed.

(* Step 2: from char_poly_int_agrees_710 (Qed in CharPolyAgree.v).
   Closed via named-predicate pattern mirroring matrix_per_prime. *)
Lemma check_charpoly_as_forallb :
  check_charpoly_710 = List.forallb check_charpoly_one_prime_710 crt_primes_all.
Proof. reflexivity. Qed.

Lemma shipped_per_prime (p : Uint63.int) (Hin : In p crt_primes_all) :
  check_charpoly_one_prime_710 p = true.
Proof.
  assert (H : List.forallb check_charpoly_one_prime_710 crt_primes_all = true).
  { rewrite <- check_charpoly_as_forallb. exact char_poly_int_agrees_710. }
  exact ((proj1 (List.forallb_forall _ _) H) p Hin).
Qed.

(* Strategy opaque [list_eqb63 ...] is essential here. Without it, the kernel
   tries to iota-reduce list_eqb63 X Y during conversion, which forces WHNF
   of X = char_poly_mod p A_int, which triggers 42 iterations of FL over the
   concrete 42x42 matrix — hanging >25 min. With list_eqb63 opaque, the
   conversion stops at syntactic match on the list_eqb63 head. *)
Strategy opaque [list_eqb63 char_poly_mod A_int charpoly_of_A_int_bigZ
                 bigZ_to_mod63 reduce_mat_Z mmat_eye mmat_zero fl_mod_loop].
Lemma per_prime_shipped_eq p (Hin : In p crt_primes_all) :
  char_poly_mod p A_int = List.map (bigZ_to_mod63 p) charpoly_of_A_int_bigZ.
Proof.
  apply list_eqb63_sound. exact (shipped_per_prime p Hin).
Qed.
Strategy transparent [list_eqb63 char_poly_mod A_int charpoly_of_A_int_bigZ
                      bigZ_to_mod63 reduce_mat_Z mmat_eye mmat_zero fl_mod_loop].

(* Step 1: char_poly_mod_sound — deductive, fast Qed *)
Lemma check_primes_gt_43 :
  List.forallb (fun p0 => Z.ltb 43 (Uint63.to_Z p0)) crt_primes_all = true.
Proof. vm_compute. reflexivity. Qed.

Lemma per_prime_mod_eq p (Hvp : valid_prime p) (Hin : In p crt_primes_all) :
  List.map (Z_to_mod63 p) (char_poly_int A_int) = char_poly_mod p A_int.
Proof.
  apply char_poly_mod_sound.
  - exact Hvp.
  - change (List.length A_int) with (mat_dim A_int). rewrite A_int_dim.
    split; [exact A_int_dim | exact (forallb_all_rows_len 42%nat A_int A_int_rows_42)].
  - change (List.length A_int) with (mat_dim A_int). rewrite A_int_dim.
    apply Z.ltb_lt.
    exact (proj1 (List.forallb_forall _ _) check_primes_gt_43 p Hin).
  - change (List.length A_int) with (mat_dim A_int). rewrite A_int_dim.
    apply fl_all_divisible_from_L2;
      [exact A_int_dim | exact (forallb_all_rows_len 42%nat A_int A_int_rows_42)].
  - apply fermat_Z; [destruct Hvp as [Hvp1 _]; exact Hvp1 |].
    apply Zprime_to_ssrprime; [destruct Hvp as [Hvp1 _]; exact Hvp1 |].
    exact (crt_primes_710_all_prime _ (List.in_map _ _ _ Hin)).
Qed.

(* Use opaque bridge lemma to avoid kernel reducing char_poly_int A_int. *)
Lemma per_prime_agreement p (Hin : In p crt_primes_all) :
  List.map (Z_to_mod63 p) charpoly_Z_A =
  List.map (Z_to_mod63 p) charpoly_of_A_int.
Proof.
  rewrite charpoly_Z_A_eq.
  rewrite (per_prime_mod_eq p (crt_primes_valid p Hin) Hin).
  rewrite (per_prime_shipped_eq p Hin).
  exact (per_prime_bigZ_eq p Hin).
Qed.

(* === Verified bounds === *)

Lemma crt_bound_sufficient :
  (2 * fl_coeff_bound 42 (max_abs_entry A_int) +
   2 * max_abs_coeff charpoly_of_A_int < crt_product_710)%Z.
Proof. exact fl_crt_bound. Qed.

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
    apply Z.le_lt_trans with (2 * fl_coeff_bound 42 (max_abs_entry A_int) +
                                2 * max_abs_coeff charpoly_of_A_int)%Z.
    { apply Z.add_le_mono.
      { apply Z.mul_le_mono_nonneg_l; [lia|]. exact (charpoly_coeff_bound n Hn). }
      { apply Z.mul_le_mono_nonneg_l; [lia|]. apply max_abs_coeff_bound.
        unfold b. apply List.nth_In. rewrite length_charpoly_of_A. exact Hn. } }
    exact crt_bound_sufficient. }
Qed.

(* === CRT lift: matrix_identity_Z === *)

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

(* === Per-prime matrix agreement via deductive chain ===
   Uses matrix_identity_710 + mscale_mod_sound + mmul_mod_sound.
   All Uint63 modular, no Z-level matrix computation. *)

(* mmat_eqb is unsound for length-mismatch (uses combine which truncates).
   Don't use mmat_eqb_sound; use these per-entry extraction lemmas instead. *)
Lemma mmat_eqb_get_row (M1 M2 : list (list Uint63.int)) (i : nat) :
  mmat_eqb M1 M2 = true ->
  (i < length M1)%nat ->
  List.forallb (fun '(a, b) => Uint63.eqb a b)
    (List.combine (List.nth i M1 nil) (List.nth i M2 nil)) = true.
Proof.
  revert i M2. induction M1 as [|r1 rs1 IH]; intros i M2 H Hi.
  - simpl in Hi. lia.
  - destruct M2 as [|r2 rs2]; [simpl in H; discriminate|].
    simpl in H. apply Bool.andb_true_iff in H.
    destruct i as [|i'].
    + simpl. exact (proj1 H).
    + simpl. apply IH; [exact (proj2 H) | simpl in Hi; lia].
Qed.

Lemma forallb_combine_get (l1 l2 : list Uint63.int) (j : nat) :
  List.forallb (fun '(a, b) => Uint63.eqb a b) (List.combine l1 l2) = true ->
  (j < length l1)%nat -> (j < length l2)%nat ->
  Uint63.eqb (List.nth j l1 0%uint63) (List.nth j l2 0%uint63) = true.
Proof.
  revert j l2. induction l1 as [|a l1' IH]; intros j l2 H H1 H2.
  - simpl in H1. lia.
  - destruct l2 as [|b l2']; [simpl in H2; lia|].
    simpl in H. apply Bool.andb_true_iff in H.
    destruct j as [|j'].
    + simpl. exact (proj1 H).
    + simpl. apply IH; [exact (proj2 H) | simpl in H1; lia | simpl in H2; lia].
Qed.

Lemma mmat_eqb_get (M1 M2 : list (list Uint63.int)) (i j : nat) :
  mmat_eqb M1 M2 = true ->
  (i < length M1)%nat ->
  (j < length (List.nth i M1 nil))%nat ->
  (j < length (List.nth i M2 nil))%nat ->
  List.nth j (List.nth i M1 nil) 0%uint63 =
  List.nth j (List.nth i M2 nil) 0%uint63.
Proof.
  intros H Hi Hj1 Hj2.
  apply Uint63.eqb_spec.
  apply forallb_combine_get; [|exact Hj1|exact Hj2].
  apply mmat_eqb_get_row; [exact H|exact Hi].
Qed.

Lemma reduce_mat_Z_get (p : Uint63.int) (M : mat) (i j : nat) :
  (i < length M)%nat -> (j < length (List.nth i M nil))%nat ->
  List.nth j (List.nth i (List.map (List.map (Z_to_mod63 p)) M) nil)
    (Z_to_mod63 p 0%Z) =
  Z_to_mod63 p (mat_get M i j).
Proof.
  intros Hi Hj. unfold mat_get, nth_Z.
  rewrite (List.nth_indep _ nil (List.map (Z_to_mod63 p) nil));
    [|rewrite List.length_map; exact Hi].
  rewrite List.map_nth.
  apply List.map_nth.
Qed.

(* Bridge: check_mat_identity_710 as a forallb (provable by reflexivity because
   check_mat_identity_one_prime is a named function, not an inline lambda) *)
Lemma check_mat_identity_as_forallb :
  check_mat_identity_710 = List.forallb check_mat_identity_one_prime crt_primes_all.
Proof. reflexivity. Qed.

(* Per-prime matrix check via the bridge *)
Lemma matrix_per_prime (p : Uint63.int) (Hin : In p crt_primes_all) :
  check_mat_identity_one_prime p = true.
Proof.
  assert (H : List.forallb check_mat_identity_one_prime crt_primes_all = true).
  { rewrite <- check_mat_identity_as_forallb. exact matrix_identity_710. }
  exact ((proj1 (List.forallb_forall _ _) H) p Hin).
Qed.

(* Well-formedness helpers for mmat_scale/mmat_mul outputs *)
Lemma mmat_scale_length p c A : length (mmat_scale p c A) = length A.
Proof. unfold mmat_scale. apply List.length_map. Qed.

Lemma mmat_mul_length p A B : length (mmat_mul p A B) = length A.
Proof. unfold mmat_mul. apply List.length_map. Qed.

Lemma mmat_scale_row_length p c A i :
  length (List.nth i (mmat_scale p c A) nil) = length (List.nth i A nil).
Proof.
  unfold mmat_scale.
  destruct (Nat.lt_ge_cases i (length A)) as [Hlt|Hge].
  - rewrite (List.nth_indep _ nil (mmat_vscale p c nil));
      [|rewrite List.length_map; exact Hlt].
    rewrite List.map_nth. unfold mmat_vscale. apply List.length_map.
  - rewrite List.nth_overflow with (l := List.map _ A);
      [|rewrite List.length_map; lia].
    rewrite List.nth_overflow with (l := A); [simpl; reflexivity|lia].
Qed.

Lemma mmat_mul_row_length p A B i :
  (i < length A)%nat ->
  length (List.nth i (mmat_mul p A B) nil) = length (mmat_trans B).
Proof.
  intros Hi. unfold mmat_mul.
  remember (fun row : list Uint63.int =>
             List.map (fun col : list Uint63.int => dot_mod p row col) (mmat_trans B))
    as f eqn:Heqf.
  rewrite (List.nth_indep _ nil (f nil)); [|rewrite List.length_map; exact Hi].
  rewrite List.map_nth. subst f. simpl. apply List.length_map.
Qed.

(* Helpers for mmat_trans_fuel length *)
Lemma mmat_tails_preserves (M : list (list Uint63.int)) (r' : list Uint63.int) :
  In r' (mmat_tails M) ->
  exists r, In r M /\ (r = nil /\ r' = nil \/ exists a, r = a :: r').
Proof.
  induction M as [|r0 rs IH]; intros Hin; simpl in Hin.
  - contradiction.
  - destruct r0 as [|a r00]; simpl in Hin.
    + destruct Hin as [Heq|Hin].
      * exists nil. split; [left; reflexivity|left; split; [reflexivity|auto]].
      * destruct (IH Hin) as [r [Hin' Hp]].
        exists r. split; [right; exact Hin'|exact Hp].
    + destruct Hin as [Heq|Hin].
      * subst r00. exists (a :: r'). split; [left; reflexivity|right; exists a; reflexivity].
      * destruct (IH Hin) as [r [Hin' Hp]].
        exists r. split; [right; exact Hin'|exact Hp].
Qed.

Lemma length_mmat_trans_fuel_wellformed (fuel : nat) (M : list (list Uint63.int)) :
  M <> nil ->
  (forall r, In r M -> (fuel <= length r)%nat) ->
  length (mmat_trans_fuel fuel M) = fuel.
Proof.
  revert M. induction fuel as [|f IH]; intros M HMne Hlen; simpl.
  - reflexivity.
  - destruct M as [|r0 rs]; [contradiction|].
    assert (Hr0_len : (S f <= length r0)%nat) by (apply Hlen; left; reflexivity).
    destruct r0 as [|a r0']; [simpl in Hr0_len; lia|].
    simpl. f_equal.
    apply IH.
    + destruct rs; simpl; discriminate.
    + intros r Hr. simpl in Hr. destruct Hr as [<-|Hr].
      * simpl in Hr0_len. lia.
      * destruct (mmat_tails_preserves _ _ Hr) as [r_orig [Hin_orig Hp]].
        assert (Horig_len : (S f <= length r_orig)%nat)
          by (apply Hlen; right; exact Hin_orig).
        destruct Hp as [[-> ->]|[b ->]]; simpl in *; lia.
Qed.

(* Per-prime matrix agreement via deductive chain.
   Strategy opaque [mmat_eqb check_mat_identity_one_prime ...] prevents
   the kernel from reducing mmat_eqb during conversion, which would
   otherwise trigger WHNF descent into the 42x42 matrix operations
   (same pattern as per_prime_shipped_eq). *)
Strategy opaque [mmat_eqb
                 Z_to_mod63 list_eqb63 char_poly_mod fl_mod_loop].
Lemma per_prime_matrix_agreement p (Hin : In p crt_primes_all)
  i j (Hi : (i < 42)%nat) (Hj : (j < 42)%nat) :
  Z_to_mod63 p (mat_get mat_lhs_opaque i j) =
  Z_to_mod63 p (mat_get mat_rhs_opaque i j).
Proof.
  pose proof (matrix_per_prime p Hin) as Heq.
  unfold check_mat_identity_one_prime in Heq.
  assert (Hvp : valid_prime p) by exact (crt_primes_valid p Hin).
  rewrite <- (reduce_mat_Z_get p mat_lhs_opaque i j).
  2:{ rewrite length_mat_lhs. exact Hi. }
  2:{ rewrite (mat_lhs_wf i ltac:(rewrite length_mat_lhs; exact Hi)). exact Hj. }
  rewrite <- (reduce_mat_Z_get p mat_rhs_opaque i j).
  2:{ rewrite length_mat_rhs. exact Hi. }
  2:{ rewrite (mat_rhs_wf i ltac:(rewrite length_mat_rhs; exact Hi)). exact Hj. }
  Transparent mat_lhs_opaque mat_rhs_opaque.
  unfold mat_lhs_opaque, mat_rhs_opaque.
  Opaque mat_lhs_opaque mat_rhs_opaque.
  rewrite (mscale_mod_sound p D_M2 (mmul M1_int A_int) Hvp).
  rewrite (mscale_mod_sound p (Z.mul D_M1 D_A) M2_int Hvp).
  rewrite (mmul_mod_sound p M1_int A_int Hvp).
  2:{ intros k Hk. rewrite (M1_int_wf k ltac:(rewrite M1_int_len in *; exact Hk)).
      change 42%nat with (mat_dim A_int). symmetry. exact A_int_dim. }
  2:{ intros k Hk. change (length A_int) with (mat_dim A_int) in Hk. rewrite A_int_dim in Hk.
      rewrite (A_int_wf k ltac:(change (length A_int) with (mat_dim A_int);
        rewrite A_int_dim; exact Hk)).
      change 42%nat with (mat_dim A_int). symmetry. exact A_int_dim. }
  (* Well-formedness of the resulting LHS row (length = 42) *)
  assert (HlhsRow : length (List.nth i
    (mmat_scale p (Z_to_mod63 p D_M2)
      (mmat_mul p (List.map (List.map (Z_to_mod63 p)) M1_int)
                  (List.map (List.map (Z_to_mod63 p)) A_int))) nil) = 42%nat).
  { rewrite mmat_scale_row_length. rewrite mmat_mul_row_length.
    2:{ rewrite List.length_map, M1_int_len. exact Hi. }
    unfold mmat_trans.
    set (A' := List.map (List.map (Z_to_mod63 p)) A_int).
    assert (HA'len : length A' = 42%nat).
    { unfold A'. rewrite List.length_map.
      change (length A_int) with (mat_dim A_int). exact A_int_dim. }
    destruct A' as [|r0 rs0] eqn:EA'.
    - simpl in HA'len. lia.
    - (* mmat_trans_fuel uses fuel = length r0.
         We show length r0 = 42 and all rows have length >= 42. *)
      assert (Hr0_def : r0 = List.map (Z_to_mod63 p) (List.nth 0 A_int nil)).
      { assert (Hnth : List.nth 0 (r0 :: rs0) nil = r0) by reflexivity.
        rewrite <- Hnth. rewrite <- EA'. unfold A'.
        rewrite (List.nth_indep _ nil (List.map (Z_to_mod63 p) nil));
          [|rewrite List.length_map; change (length A_int) with (mat_dim A_int);
            rewrite A_int_dim; lia].
        apply List.map_nth. }
      assert (Hr0_len : length r0 = 42%nat).
      { rewrite Hr0_def, List.length_map.
        rewrite (A_int_wf 0%nat); [reflexivity|].
        change (length A_int) with (mat_dim A_int). rewrite A_int_dim. lia. }
      rewrite Hr0_len.
      apply length_mmat_trans_fuel_wellformed; [discriminate|].
      intros r Hr. simpl in Hr. destruct Hr as [<-|Hr].
      + lia.
      + (* r in rs0; rs0 is in A' \ r0 *)
        assert (HrA' : In r A') by (rewrite EA'; right; exact Hr).
        unfold A' in HrA'. apply List.in_map_iff in HrA'.
        destruct HrA' as [row [Hreq Hrow]]. subst r.
        rewrite List.length_map. apply List.In_nth with (d := nil) in Hrow.
        destruct Hrow as [k [Hk Hrk]]. subst row.
        rewrite (A_int_wf k ltac:(change (length A_int) with (mat_dim A_int);
          rewrite A_int_dim; change (length A_int) with (mat_dim A_int) in Hk;
          rewrite A_int_dim in Hk; exact Hk)).
        lia. }
  assert (HrhsRow : length (List.nth i
    (mmat_scale p (Z_to_mod63 p (D_M1 * D_A)%Z)
      (List.map (List.map (Z_to_mod63 p)) M2_int)) nil) = 42%nat).
  { rewrite mmat_scale_row_length.
    rewrite (List.nth_indep _ nil (List.map (Z_to_mod63 p) nil));
      [|rewrite List.length_map, M2_int_len; exact Hi].
    rewrite List.map_nth. rewrite List.length_map.
    apply M2_int_wf. rewrite M2_int_len. exact Hi. }
  rewrite (List.nth_indep _ (Z_to_mod63 p 0) 0%uint63); [|rewrite HlhsRow; exact Hj].
  symmetry.
  rewrite (List.nth_indep _ (Z_to_mod63 p 0) 0%uint63); [|rewrite HrhsRow; exact Hj].
  symmetry.
  apply mmat_eqb_get.
  - exact Heq.
  - rewrite mmat_scale_length, mmat_mul_length, List.length_map, M1_int_len. exact Hi.
  - rewrite HlhsRow. exact Hj.
  - rewrite HrhsRow. exact Hj.
Qed.
Strategy transparent [mmat_eqb
                      Z_to_mod63 list_eqb63 char_poly_mod fl_mod_loop].

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
Proof. vm_compute. reflexivity. Qed.

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
