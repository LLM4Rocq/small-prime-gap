# Closing the remaining CRTLift admits

**0 axioms. 10 admits in CRTLift.v, 2 admits in CertL2.v.**

The 10 CRTLift admits are:
- 6 matrix operation bounds (Z-level, no MathComp)
- 2 FL structural proofs (Z-level induction)
- 2 kernel Qed limits (logically proved, Rocq kernel too slow)

## Proved helper: `max_abs_entry_le_bound`

All matrix bounds use this converse of `max_abs_entry_get`:

```coq
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
```

## 1. `max_abs_entry_mzero`

```coq
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
```

## 2. `max_abs_entry_meye_le`

```coq
Lemma max_abs_entry_meye_le (n : nat) : (max_abs_entry (meye n) <= 1)%Z.
Proof.
  apply max_abs_entry_le_bound; [lia|].
  intros i j Hi Hj. unfold mat_get, nth_Z.
  (* meye entries are 0 or 1 from eye_row *)
  admit. (* Need: |nth j (nth i (meye_aux n n) nil) 0| <= 1
            Follows from eye_row having entries 0 and 1. *)
Admitted.
```

Needs helper about `eye_row` entries being 0 or 1.

## 3. `max_abs_entry_mscale_le`

```coq
Lemma max_abs_entry_mscale_le (c : Z) (M : mat) :
  (max_abs_entry (mscale c M) <= Z.abs c * max_abs_entry M)%Z.
Proof.
  apply max_abs_entry_le_bound.
  { apply Z.mul_nonneg_nonneg; [apply Z.abs_nonneg|exact (max_abs_entry_nonneg M)]. }
  intros i j Hi Hj.
  rewrite length_mscale in Hi. (* mscale preserves length *)
  rewrite mat_get_mscale. rewrite Z.abs_mul.
  apply Z.mul_le_mono_nonneg_l; [apply Z.abs_nonneg|].
  apply max_abs_entry_get; [exact Hi|].
  (* Need: j < length (nth i M nil) *)
  (* Derive from Hj + mscale row length = original row length *)
  admit.
Admitted.
```

Needs `length_mscale` (already proved in CRTLift.v) and row length relation.

## 4. `max_abs_entry_madd_le`

```coq
(* Helper: nth of vadd *)
Lemma nth_vadd (xs ys : list Z) (j : nat) :
  (j < length xs)%nat -> length xs = length ys ->
  List.nth j (vadd xs ys) 0%Z = (List.nth j xs 0%Z + List.nth j ys 0%Z)%Z.
Proof.
  revert ys j. induction xs as [|x xs IH]; intros [|y ys] [|j] Hj Hlen;
    simpl in *; try lia; try reflexivity. apply IH; lia.
Qed.

Lemma max_abs_entry_madd_le (A B : mat) (n : nat) :
  mat_dim A = n -> mat_dim B = n -> all_rows_len n A -> all_rows_len n B ->
  (max_abs_entry (madd A B) <= max_abs_entry A + max_abs_entry B)%Z.
Proof.
  intros HdA HdB HwA HwB.
  apply max_abs_entry_le_bound.
  { pose proof (max_abs_entry_nonneg A). pose proof (max_abs_entry_nonneg B). lia. }
  intros i j Hi Hj.
  (* mat_get (madd A B) i j = A[i][j] + B[i][j] for well-formed matrices *)
  (* Then triangle inequality *)
  admit.
Admitted.
```

Needs helper for `mat_get (madd A B)` and well-formedness propagation.

## 5. `max_abs_entry_mmul_le`

```coq
Lemma max_abs_entry_mmul_le (A B : mat) (n : nat) :
  mat_dim A = n -> mat_dim B = n -> all_rows_len n A -> all_rows_len n B ->
  (max_abs_entry (mmul A B) <= Z.of_nat n * max_abs_entry A * max_abs_entry B)%Z.
Proof.
  intros HdA HdB HwA HwB.
  apply max_abs_entry_le_bound.
  { apply Z.mul_nonneg_nonneg; [|exact (max_abs_entry_nonneg B)].
    apply Z.mul_nonneg_nonneg; [lia|exact (max_abs_entry_nonneg A)]. }
  intros i j Hi Hj.
  (* Use mat_get_mmul_sq + dot_int_bound *)
  rewrite (mat_get_mmul_sq A B n i j HdA HdB HwA HwB
    ltac:(rewrite length_mmul, HdA in Hi; exact Hi)
    ltac:(admit)). (* j < n from Hj + row length *)
  apply dot_int_bound with (n := n);
    [apply HwA; rewrite HdA in Hi; exact Hi
    |apply nth_mtrans_length_sq; assumption
    |intros k Hk; apply max_abs_entry_get; [rewrite HdA; lia|rewrite (HwA _ ltac:(rewrite HdA; lia)); exact Hk]
    |intros k Hk; rewrite nth_nth_mtrans_sq; [unfold nth_Z; apply max_abs_entry_get|..]; admit
    |exact (max_abs_entry_nonneg A)
    |exact (max_abs_entry_nonneg B)].
Admitted.
```

## 6. `abs_mtrace_le`

```coq
Lemma abs_mtrace_le (M : mat) (n : nat) :
  mat_dim M = n -> all_rows_len n M ->
  (Z.abs (mtrace M) <= Z.of_nat n * max_abs_entry M)%Z.
Proof.
  intros Hd Hw. unfold mtrace.
  (* mtrace_aux i M = sum of M[i+k][i+k] for k = 0..length(M)-i-1 *)
  (* Triangle inequality + max_abs_entry_get *)
  admit.
Admitted.
```

## 7. `fl_loop_coeff_bound`

See the induction structure in the test file above. The key steps per iteration:
1. Bound `max_abs_entry M_k` using madd + mmul + mscale + meye bounds
2. Bound `|c_new|` using mtrace + mmul bounds + `Z.div` monotonicity
3. Update acc invariant
4. Apply IH with updated bounds

Well-formedness propagates via `all_rows_len_madd`, `all_rows_len_mmul`,
`all_rows_len_mscale`, `all_rows_len_meye` (all Qed in CharPoly.v).

## 8. `charpoly_coeff_bound`

```coq
Lemma charpoly_coeff_bound : forall k,
  (k < 43)%nat ->
  (Z.abs (List.nth k charpoly_Z_A 0%Z) <=
   fl_coeff_bound 42 (max_abs_entry A_int))%Z.
Proof.
  intros k Hk.
  change charpoly_Z_A with (char_poly_int A_int).
  unfold char_poly_int. rewrite A_int_dim.
  destruct (Nat.eq_dec k 42) as [->|Hne].
  - (* k = 42: leading coefficient 1 *)
    rewrite List.nth_middle; [|rewrite fl_loop_length; simpl; lia].
    simpl. unfold fl_coeff_bound. simpl. lia.
  - (* k < 42: from fl_loop *)
    assert (Hk' : (k < 42)%nat) by lia.
    rewrite List.app_nth1; [|rewrite fl_loop_length; simpl; lia].
    apply fl_loop_coeff_bound with
      (n := 42%nat) (B := max_abs_entry A_int)
      (E_prev := 0%Z) (C_prev := 1%Z) (max_c := 1%Z);
      try exact A_int_dim;
      try exact (forallb_all_rows_len 42%nat A_int A_int_rows_42);
      try reflexivity; try lia.
    + exact (all_rows_len_meye 42%nat : all_rows_len 42 (meye 42)).
    + admit. (* mat_dim (mzero 42) = 42 *)
    + exact (all_rows_len_mzero 42%nat : all_rows_len 42 (mzero 42)).
    + rewrite max_abs_entry_mzero. lia.
    + intros c Hc. destruct Hc.
    + apply List.nth_In. rewrite fl_loop_length. simpl. lia.
Admitted.
```

## Summary

The 6 matrix bounds + 2 FL proofs total ~180 lines. Each is a standard
Z-level argument using `max_abs_entry_le_bound` (converse of
`max_abs_entry_get`), `dot_int_bound`, and fold_left properties.

No MathComp, no heavy computation, no kernel performance issues.
