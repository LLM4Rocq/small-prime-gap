(**md**************************************************************************)
(** # Bound.v — coefficient-bound infrastructure for char_poly_int

 Pure-Z port of the COEFFICIENT-BOUND half of pencil:theories/S1/CRTLift.v
 (Uint63 / CRT-product / prime-checking parts dropped), together with the
 generic Hadamard-style coefficient bound from
 pencil:theories/S1/CRTPencilHadamardGeneric.v, generalised here to ALL
 coefficients of char_poly_int M (not just the constant term).

 Main results:
 - max_abs_entry and its arithmetic (mmul/madd/mscale/mtrace/meye/mzero).
 - dot_int_bound, Z_abs_div_*.
 - fl_bound_aux / fl_coeff_bound and the loop bound fl_loop_coeff_bound:
   every coefficient produced by the FL loop is bounded by fl_bound_aux.
 - char_poly_int_coeff_bound: for a square matrix M,
   forall k, |nth k (char_poly_int M)|
     <= fl_coeff_bound (length M) (max_abs_entry M).

 Axiom-free: computation only over stdlib Z; no Uint63 / native_compute. *)

From Stdlib Require Import ZArith List Lia.
From PrimeGapS1 Require Import IntMat CharPoly FLDiv.
Import ListNotations.
Local Open Scope Z_scope.

(* ================================================================ *)
(*  max_abs_entry and char_poly_int length / index structure         *)
(* ================================================================ *)

Definition max_abs_entry (M : list (list Z)) : Z :=
  List.fold_left (fun acc row =>
    List.fold_left (fun acc2 x => Z.max acc2 (Z.abs x)) row acc) M 0%Z.

Lemma fl_loop_length steps k A I_n M_prev c_prev acc :
  length (fl_loop steps k A I_n M_prev c_prev acc) = (steps + length acc)%nat.
Proof.
  revert k A I_n M_prev c_prev acc.
  induction steps as [|s IH]; intros; simpl;
    [reflexivity | rewrite IH; simpl; lia].
Qed.

Lemma length_char_poly_int_gen (M : mat) :
  length (char_poly_int M) = S (mat_dim M).
Proof.
  unfold char_poly_int. rewrite List.length_app. rewrite fl_loop_length. simpl.
  lia.
Qed.

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
  replace (n - (n + 0))%nat with 0%nat by lia.
  reflexivity.
Qed.

(* ================================================================ *)
(*  FL coefficient bound via computable recurrence                    *)
(*                                                                    *)
(*  The FL loop computes c_k = -tr(A*M_k)/k. We bound |c_k| by        *)
(*  tracking max_abs_entry(M_k) and |c_k| through the recurrence.      *)
(* ================================================================ *)

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
  revert v n Bu Bv.
  induction u as [|a u IH];
    intros v n Bu Bv Hlu Hlv Hbu Hbv HBu HBv.
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
  revert acc.
  induction l as [|x l IH]; intros acc Hacc Hall; simpl; [exact Hacc|].
  apply IH; [|intros y Hy; exact (Hall y (or_intror Hy))].
  pose proof (Hall x (or_introl eq_refl)). lia.
Qed.

Lemma fold_left_zmax_outer_le (M : mat) (acc B : Z) :
  (acc <= B)%Z ->
  (forall row, In row M -> forall x, In x row -> (Z.abs x <= B)%Z) ->
  (List.fold_left (fun a row =>
    List.fold_left (fun a2 x => Z.max a2 (Z.abs x)) row a) M acc <= B)%Z.
Proof.
  revert acc.
  induction M as [|r M IH]; intros acc Hacc Hall; simpl; [exact Hacc|].
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

(* --- Matrix operation bounds --- *)

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
  - apply Z.mul_nonneg_nonneg;
      [apply Z.abs_nonneg | apply max_abs_entry_nonneg].
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
  - pose proof (max_abs_entry_nonneg A).
    pose proof (max_abs_entry_nonneg B).
    lia.
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
  (max_abs_entry (mmul A B)
   <= Z.of_nat n * max_abs_entry A * max_abs_entry B)%Z.
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

(* --- Divisibility helpers for FL loop bound --- *)

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

Lemma fl_bound_aux_mono (steps : nat) (k n B E C mc : Z) :
  (0 <= mc)%Z ->
  (mc <= fl_bound_aux steps k n B E C mc)%Z.
Proof.
  revert k E C mc. induction steps as [|s IH]; intros k E C mc Hmc; simpl.
  - lia.
  - apply Z.le_trans with
      (Z.max mc (Z.abs (n * n * B * (n * B * E + Z.abs C) / k)))%Z.
    + lia.
    + apply IH. lia.
Qed.

(* ================================================================ *)
(*  Generic Hadamard-style bound on ALL coefficients of char_poly    *)
(* ================================================================ *)

Section GenericBound.

Variable M : mat.
Hypothesis M_rows :
  forall i, (i < length M)%nat -> length (List.nth i M nil) = length M.

Local Lemma gen_mat_dim : mat_dim M = length M.
Proof. reflexivity. Qed.

Local Lemma gen_fl_all_divisible :
  fl_all_divisible
    (length M) Z.one M (meye (length M)) (mzero (length M)) Z.one.
Proof.
  apply fl_all_divisible_from_L2; [exact gen_mat_dim | exact M_rows].
Qed.

Local Lemma gen_fl_loop_coeff (k : nat) (Hk : (k < length M)%nat) :
  (Z.abs (List.nth k
            (fl_loop (length M) Z.one M (meye (length M))
               (mzero (length M)) Z.one nil) 0%Z)
   <= fl_bound_aux (length M) 1 (Z.of_nat (length M))
        (max_abs_entry M) 0 1 1)%Z.
Proof.
  apply (fl_loop_coeff_bound (length M) Z.one M (meye (length M))
           (mzero (length M)) Z.one nil (length M) (max_abs_entry M) 0 1 1).
  + exact gen_mat_dim.
  + exact M_rows.
  + reflexivity.
  + exact (mat_dim_mzero (length M)).
  + apply all_rows_len_mzero.
  + reflexivity.
  + reflexivity.
  + apply max_abs_entry_nonneg.
  + rewrite max_abs_entry_mzero. reflexivity.
  + reflexivity.
  + reflexivity.
  + intros c' Hc'. destruct Hc'.
  + lia.
  + apply gen_fl_all_divisible.
  + apply List.nth_In. rewrite fl_loop_length. simpl. lia.
Qed.

(* For every coefficient index k (the In-form generic Hadamard bound). *)
Lemma char_poly_int_coeff_bound :
  forall k,
    (Z.abs (List.nth k (char_poly_int M) 0%Z)
       <= fl_coeff_bound (length M) (max_abs_entry M))%Z.
Proof.
  intro k. unfold fl_coeff_bound.
  destruct (Nat.lt_ge_cases k (length M)) as [Hk | Hk].
  - (* in-range coefficient: read off the FL loop *)
    rewrite (char_poly_int_nth_lt M (length M) k gen_mat_dim Hk).
    exact (gen_fl_loop_coeff k Hk).
  - destruct (Nat.eq_dec k (length M)) as [-> | Hne].
    + (* leading coefficient is 1 *)
      rewrite (char_poly_int_nth_leading M (length M) gen_mat_dim).
      change (Z.abs Z.one) with 1%Z.
      apply fl_bound_aux_mono. lia.
    + (* out of range: coefficient is 0 *)
      assert (Hov : (length (char_poly_int M) <= k)%nat).
      { rewrite length_char_poly_int_gen. rewrite gen_mat_dim. lia. }
      rewrite (List.nth_overflow _ _ Hov).
      change (Z.abs 0) with 0%Z.
      apply Z.le_trans with 1%Z; [lia | apply fl_bound_aux_mono; lia].
Qed.

End GenericBound.

(* Axiom-free: [Print Assumptions char_poly_int_coeff_bound] reports
   "Closed under the global context". *)
