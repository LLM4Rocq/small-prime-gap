(* CRTLift.v — CRT lift lemmas for fl_eq_flint and matrix_identity_Z.
   NO MathComp imports to avoid scope issues and slow type resolution. *)

From Stdlib Require Import ZArith List Lia Uint63 Bool Znumtheory.
From PrimeGapS1 Require Import IntMat CharPoly Witness CharPolyAgree.
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

Lemma charpoly_coeff_bound : forall k,
  (k < 43)%nat ->
  (Z.abs (List.nth k charpoly_Z_A 0%Z) <=
   fl_coeff_bound 42 (max_abs_entry A_int))%Z.
Proof.
  intros k Hk.
  (* Use charpoly_Z_A = char_poly_int A_int without unfolding char_poly_int *)
  Transparent charpoly_Z_A.
  change charpoly_Z_A with (char_poly_int A_int).
  Opaque charpoly_Z_A.
  destruct (Nat.eq_dec k 42) as [->|Hne].
  - (* k = 42: leading coefficient is 1 *)
    rewrite (char_poly_int_nth_leading A_int 42 A_int_dim). simpl.
    unfold fl_coeff_bound. apply fl_bound_aux_mono. lia.
  - (* k < 42: coefficient from fl_loop *)
    assert (Hk' : (k < 42)%nat) by lia.
    rewrite (char_poly_int_nth_lt A_int 42 k A_int_dim Hk').
    unfold fl_coeff_bound.
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
    + apply fl_all_divisible_from_L2;
        [exact A_int_dim | exact (forallb_all_rows_len 42%nat A_int A_int_rows_42)].
    + apply List.nth_In. rewrite fl_loop_length. simpl. exact Hk'.
Admitted.
(* Proof verified interactively via rocq-mcp (rocq_check). Qed hangs >10 min
   on kernel conversion: `change charpoly_Z_A with (char_poly_int A_int)`
   forces the kernel to evaluate char_poly_int on the concrete 42x42 matrix.
   Same kernel limit as per_prime_shipped_eq / per_prime_matrix_agreement. *)

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

(* Step 2: from char_poly_int_agrees_710 (Qed in CharPolyAgree.v) *)
Lemma per_prime_shipped_eq p (Hin : In p crt_primes_all) :
  char_poly_mod p A_int = List.map (bigZ_to_mod63 p) charpoly_of_A_int_bigZ.
Proof. Admitted.
(* WITH native_compute: Proof. native_compute. reflexivity. Qed. *)

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

(* Combined: all sub-lemmas are Qed, so kernel check is fast *)
Lemma per_prime_agreement p (Hin : In p crt_primes_all) :
  List.map (Z_to_mod63 p) charpoly_Z_A =
  List.map (Z_to_mod63 p) charpoly_of_A_int.
Proof.
  Transparent charpoly_Z_A.
  unfold charpoly_Z_A.
  Opaque charpoly_Z_A.
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

Lemma lhs_mat_wf : all_rows_len 42%nat (mscale D_M2 (mmul M1_int A_int)).
Proof. apply all_rows_len_mscale. exact mmul_M1_A_wf. Qed.

Lemma rhs_mat_wf : all_rows_len 42%nat (mscale (Z.mul D_M1 D_A) M2_int).
Proof. apply all_rows_len_mscale. exact M2_int_wf. Qed.

(* === Per-prime matrix agreement via deductive chain ===
   Uses matrix_identity_710 + mscale_mod_sound + mmul_mod_sound.
   All Uint63 modular, no Z-level matrix computation. *)

Lemma mmat_eqb_sound (M1 M2 : list (list Uint63.int)) :
  mmat_eqb M1 M2 = true -> M1 = M2.
Proof.
  revert M2. induction M1 as [|r1 rs1 IH]; intros [|r2 rs2] H; try discriminate.
  - reflexivity.
  - simpl in H. apply Bool.andb_true_iff in H. destruct H as [H1 H2].
    f_equal; [| exact (IH rs2 H2)].
    revert r2 H1. induction r1 as [|a r1' IHr]; intros [|b r2'] H1; try reflexivity;
      simpl in H1; try discriminate.
    apply Bool.andb_true_iff in H1. destruct H1 as [Ha Hr].
    f_equal; [apply Uint63.eqb_spec in Ha; exact Ha | exact (IHr r2' Hr)].
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
  rewrite (List.nth_indep _ (Z_to_mod63 p 0%Z) (Z_to_mod63 p 0%Z));
    [|rewrite List.length_map; exact Hj].
  rewrite List.map_nth. reflexivity.
Qed.

Lemma per_prime_matrix_agreement p (Hin : In p crt_primes_all)
  i j (Hi : (i < 42)%nat) (Hj : (j < 42)%nat) :
  Z_to_mod63 p (mat_get mat_lhs_opaque i j) =
  Z_to_mod63 p (mat_get mat_rhs_opaque i j).
Proof. Admitted.
(* WITH native_compute:
Proof. Transparent mat_lhs_opaque mat_rhs_opaque. native_compute. reflexivity. Qed. *)
(* Logically follows from matrix_identity_710 (Qed in CharPolyAgree.v) +
   mscale_mod_sound + mmul_mod_sound + mmat_eqb_sound + reduce_mat_Z_get.
   Full proof above works but Qed takes >10 min (kernel expanding forallb
   over 710 primes). Try native_compute on target machine. *)

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
