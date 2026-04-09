(* theories/S1/CharPolyHelpers.v
   ---------------------------------------------------------------
   Step 1 bridge lemmas for CharPoly.v relating `list (list Z)` matrix
   operations to MathComp 'M[rat]_n operations through
     `mat_int_to_rat _ 1 n`
   from CharPoly.v.

   This is a leaf file (no other file depends on it). CharPoly.v is
   kept untouched: the corresponding Admitted statements there are
   shadowed by the versions proved here for use in downstream work.
   --------------------------------------------------------------- *)

From Stdlib Require Import ZArith List Lia.
Import ListNotations.

From mathcomp Require Import all_boot all_algebra.
Import GRing.Theory.

From PrimeGapS1 Require Import IntPoly IntMat CharPoly.

(* We intentionally keep the default scope as `nat_scope` (which is
   ssreflect's nat on `all_boot`). We reopen ring_scope inside each
   ring-level lemma body. Z constants are written as Z0 / Zpos xH to
   avoid the `%Z` delimiter clash with mathcomp's int_scope. *)

(* ==================================================================
   Tiny helpers about the integer->mathcomp int conversion.
   ================================================================== *)

Lemma Z_to_int_0 : Z_to_int Z0 = 0%R.
Proof. reflexivity. Qed.

Lemma Z_to_int_1 : Z_to_int (Zpos xH) = 1%R.
Proof. reflexivity. Qed.

(* ==================================================================
   STEP 1 lemmas
   ================================================================== *)

(* ------- (1) mat_int_to_rat (mzero n) = 0 ----------------------- *)

(* mat_get (mzero n) i j = 0 when both indices are in range. *)
Lemma nth_Z_zrow (n i : nat) : nth_Z (zrow n) i = Z0.
Proof.
  revert i. induction n as [|k IH]; intros [|i]; simpl; try reflexivity.
  apply IH.
Qed.

Lemma nth_mzero_aux_is_zrow (rows cols : nat) (i : nat) (d : list Z) :
  (i < rows)%coq_nat ->
  List.nth i (mzero_aux rows cols) d = zrow cols.
Proof.
  revert i. induction rows as [|k IH]; intros [|i] H; simpl.
  - exfalso; lia.
  - exfalso; lia.
  - reflexivity.
  - apply IH. lia.
Qed.

Lemma mat_get_mzero (n i j : nat) :
  mat_get (mzero n) i j = Z0.
Proof.
  unfold mat_get, mzero, nth_Z.
  destruct (Compare_dec.lt_dec i n) as [Hlt|Hge].
  - rewrite (nth_mzero_aux_is_zrow n n i nil Hlt).
    change (List.nth j (zrow n) Z0) with (nth_Z (zrow n) j).
    apply nth_Z_zrow.
  - assert (Hge' : Nat.le (List.length (mzero_aux n n)) i).
    { rewrite mzero_aux_len. apply Nat.nlt_ge; exact Hge. }
    rewrite (List.nth_overflow _ _ Hge').
    simpl. destruct j; reflexivity.
Qed.

Lemma mat_int_to_rat_mzero (n : nat) :
  mat_int_to_rat (mzero n) 1 n = 0%R.
Proof.
  apply/matrixP => i j.
  rewrite /mat_int_to_rat !mxE.
  rewrite mat_get_mzero Z_to_int_0.
  rewrite /= mul0r.
  reflexivity.
Qed.

(* ------- (2) mat_int_to_rat (mscale c A) ----------------------- *)

Lemma nth_Z_vscale (c : Z) (xs : list Z) (j : nat) :
  nth_Z (vscale c xs) j = BinInt.Z.mul c (nth_Z xs j).
Proof.
  revert j. induction xs as [|x xs IH]; intros [|j]; simpl.
  - unfold nth_Z; simpl. rewrite BinInt.Z.mul_0_r. reflexivity.
  - unfold nth_Z; simpl. rewrite BinInt.Z.mul_0_r. reflexivity.
  - reflexivity.
  - apply IH.
Qed.

Lemma nth_map_vscale (c : Z) (A : mat) (i : nat) (d : list Z) :
  (i < length A)%coq_nat ->
  List.nth i (List.map (vscale c) A) d = vscale c (List.nth i A d).
Proof.
  revert i. induction A as [|a A IH]; intros [|i] H; simpl.
  - exfalso; simpl in H; lia.
  - exfalso; simpl in H; lia.
  - reflexivity.
  - apply IH. simpl in H; lia.
Qed.

Lemma mat_get_mscale (c : Z) (A : mat) (i j : nat) :
  mat_get (mscale c A) i j = BinInt.Z.mul c (mat_get A i j).
Proof.
  unfold mat_get, mscale.
  destruct (Compare_dec.lt_dec i (length A)) as [Hlt|Hge].
  - rewrite (nth_map_vscale _ _ _ _ Hlt).
    apply nth_Z_vscale.
  - rewrite List.nth_overflow; [| rewrite length_map; lia].
    rewrite (List.nth_overflow A); [| lia].
    simpl. unfold nth_Z. destruct j; simpl; rewrite BinInt.Z.mul_0_r; reflexivity.
Qed.

Lemma Z_to_int_neg_pos (p : positive) :
  Z_to_int (Zneg p) = (- (Posz (Pos.to_nat p)))%R.
Proof.
  unfold Z_to_int.
  have Hp := Pos2Nat.is_pos p.
  destruct (Pos.to_nat p) as [|k] eqn:Ek; [exfalso; lia|].
  have ->: (k.+1 - 1 = k)%N by rewrite subn1.
  by rewrite NegzE.
Qed.

Lemma Z_to_int_pos_pos (p : positive) :
  Z_to_int (Zpos p) = Posz (Pos.to_nat p).
Proof. reflexivity. Qed.

Lemma Z_to_int_mul (a b : Z) :
  Z_to_int (BinInt.Z.mul a b) = ((Z_to_int a) * (Z_to_int b))%R.
Proof.
  destruct a as [|pa|pa]; destruct b as [|pb|pb];
    try (change (Z_to_int 0) with (0%R : int)); try reflexivity;
    try (rewrite mul0r; reflexivity);
    try (rewrite mulr0; reflexivity).
  - (* Zpos pa * Zpos pb *)
    change (BinInt.Z.mul (Zpos pa) (Zpos pb)) with (Zpos (pa * pb)%positive).
    rewrite !Z_to_int_pos_pos. rewrite Pos2Nat.inj_mul. by rewrite PoszM.
  - (* Zpos pa * Zneg pb *)
    change (BinInt.Z.mul (Zpos pa) (Zneg pb)) with (Zneg (pa * pb)%positive).
    rewrite !Z_to_int_neg_pos Z_to_int_pos_pos.
    rewrite Pos2Nat.inj_mul. rewrite PoszM.
    by rewrite mulrN.
  - (* Zneg pa * Zpos pb *)
    change (BinInt.Z.mul (Zneg pa) (Zpos pb)) with (Zneg (pa * pb)%positive).
    rewrite !Z_to_int_neg_pos Z_to_int_pos_pos.
    rewrite Pos2Nat.inj_mul. rewrite PoszM.
    by rewrite mulNr.
  - (* Zneg pa * Zneg pb *)
    change (BinInt.Z.mul (Zneg pa) (Zneg pb)) with (Zpos (pa * pb)%positive).
    rewrite !Z_to_int_neg_pos Z_to_int_pos_pos.
    rewrite Pos2Nat.inj_mul. rewrite PoszM.
    by rewrite mulrNN.
Qed.

(* `Z_to_int (Z.pos_sub pa pb) = Pos.to_nat pa - Pos.to_nat pb`. *)
Lemma Z_pos_sub_int (pa pb : positive) :
  Z_to_int (Z.pos_sub pa pb) = (Posz (Pos.to_nat pa) - Posz (Pos.to_nat pb))%R.
Proof.
  have Hd := Z.pos_sub_discr pa pb.
  destruct (Z.pos_sub pa pb) as [|k|k].
  - subst. by rewrite subrr.
  - rewrite Z_to_int_pos_pos. rewrite Hd Pos2Nat.inj_add PoszD.
    by rewrite addrAC subrr add0r.
  - rewrite Z_to_int_neg_pos. rewrite Hd Pos2Nat.inj_add PoszD.
    rewrite opprD.
    have ->: (Posz (Pos.to_nat pa) + (- Posz (Pos.to_nat pa) - Posz (Pos.to_nat k)) = - Posz (Pos.to_nat k))%R
      by rewrite addrA addrN add0r.
    reflexivity.
Qed.

(* Additivity of Z_to_int. *)
Lemma Z_to_int_add (a b : Z) :
  Z_to_int (BinInt.Z.add a b) = ((Z_to_int a) + (Z_to_int b))%R.
Proof.
  destruct a as [|pa|pa]; destruct b as [|pb|pb]; simpl BinInt.Z.add.
  - by rewrite addr0.
  - by rewrite add0r.
  - by rewrite add0r.
  - by rewrite addr0.
  - rewrite !Z_to_int_pos_pos.
    rewrite Pos2Nat.inj_add. by rewrite PoszD.
  - rewrite Z_pos_sub_int Z_to_int_pos_pos Z_to_int_neg_pos.
    by [].
  - by rewrite addr0.
  - rewrite Z_pos_sub_int Z_to_int_neg_pos Z_to_int_pos_pos.
    by rewrite addrC.
  - rewrite !Z_to_int_neg_pos.
    rewrite Pos2Nat.inj_add PoszD. by rewrite opprD.
Qed.

Lemma mat_int_to_rat_mscale (c : Z) (A : mat) (n : nat) :
  mat_int_to_rat (mscale c A) 1 n
  = ((Z_to_int c)%:~R *: mat_int_to_rat A 1 n)%R.
Proof.
  apply/matrixP => i j.
  rewrite /mat_int_to_rat !mxE.
  rewrite mat_get_mscale.
  rewrite Z_to_int_mul.
  rewrite intrM.
  rewrite mulrA.
  reflexivity.
Qed.

(* ------- (3) mat_int_to_rat (meye n) = 1%:M ----------------------- *)

Lemma nth_eye_row_eq (n i : nat) :
  (i < n)%coq_nat ->
  nth_Z (eye_row n i) i = BinInt.Zpos xH.
Proof.
  revert i. induction n as [|k IH]; intros [|i] H; simpl.
  - exfalso; lia.
  - exfalso; lia.
  - reflexivity.
  - apply IH. lia.
Qed.

Lemma nth_eye_row_neq (n i j : nat) :
  i <> j ->
  nth_Z (eye_row n i) j = Z0.
Proof.
  revert i j. induction n as [|k IH]; intros i j H; simpl.
  - unfold nth_Z. destruct j; reflexivity.
  - destruct i as [|i]; destruct j as [|j]; simpl.
    + exfalso; apply H; reflexivity.
    + apply nth_Z_zrow.
    + reflexivity.
    + apply IH. intros E; apply H. f_equal. exact E.
Qed.

Lemma nth_meye_aux (n i k : nat) (d : list Z) :
  (i < k)%coq_nat -> (k <= n)%coq_nat ->
  List.nth i (meye_aux n k) d = eye_row n i.
Proof.
  revert i. induction k as [|k IH]; intros i H Hk; simpl.
  - exfalso; lia.
  - destruct (Nat.eq_dec i k) as [->|Hne].
    + rewrite List.app_nth2; rewrite meye_aux_len; [| lia].
      rewrite Nat.sub_diag. reflexivity.
    + assert (Hik : (i < k)%coq_nat) by lia.
      rewrite List.app_nth1; rewrite ?meye_aux_len; [| lia].
      apply IH; lia.
Qed.

Lemma mat_get_meye_eq (n i : nat) :
  (i < n)%coq_nat ->
  mat_get (meye n) i i = BinInt.Zpos xH.
Proof.
  intros H. unfold mat_get, meye.
  rewrite (nth_meye_aux n i n nil); try lia.
  apply nth_eye_row_eq; exact H.
Qed.

Lemma mat_get_meye_neq (n i j : nat) :
  (i < n)%coq_nat -> i <> j ->
  mat_get (meye n) i j = Z0.
Proof.
  intros Hi Hij. unfold mat_get, meye.
  rewrite (nth_meye_aux n i n nil); try lia.
  apply nth_eye_row_neq; exact Hij.
Qed.

Lemma mat_int_to_rat_meye (n : nat) :
  mat_int_to_rat (meye n) 1 n = (1%:M)%R.
Proof.
  apply/matrixP => i j.
  rewrite /mat_int_to_rat !mxE.
  case: (eqVneq i j) => [->|Hne].
  - have Hj : (nat_of_ord j < n)%coq_nat by apply/ltP; apply: ltn_ord.
    rewrite (mat_get_meye_eq n j Hj).
    rewrite Z_to_int_1.
    rewrite /= divr1.
    reflexivity.
  - have Hi : (nat_of_ord i < n)%coq_nat by apply/ltP; apply: ltn_ord.
    have Hne' : (nat_of_ord i) <> (nat_of_ord j).
    { move=> E. move/eqP: Hne => Hne. apply: Hne. apply: val_inj. exact: E. }
    rewrite (mat_get_meye_neq n i j Hi Hne').
    rewrite Z_to_int_0.
    rewrite /= mul0r.
    reflexivity.
Qed.

(* ------- (4) mat_int_to_rat (madd A B) --------------------- *)

Lemma nth_Z_vadd (xs ys : list Z) (j : nat) :
  List.length xs = List.length ys ->
  nth_Z (vadd xs ys) j = BinInt.Z.add (nth_Z xs j) (nth_Z ys j).
Proof.
  revert ys j. induction xs as [|x xs IH]; intros [|y ys] j Hlen;
    simpl in Hlen; try discriminate; simpl.
  - unfold nth_Z; destruct j; simpl; reflexivity.
  - destruct j; simpl; [reflexivity|].
    assert (Hlen' : List.length xs = List.length ys) by (inversion Hlen; reflexivity).
    specialize (IH ys j Hlen'). exact IH.
Qed.

Lemma nth_madd (A B : mat) (i : nat) :
  List.length A = List.length B ->
  List.nth i (madd A B) nil = vadd (List.nth i A nil) (List.nth i B nil).
Proof.
  revert B i. induction A as [|a A IH]; intros [|b B] i Hlen;
    simpl in Hlen; try discriminate; simpl.
  - destruct i; simpl; reflexivity.
  - destruct i; simpl; [reflexivity|].
    assert (Hlen' : List.length A = List.length B) by (inversion Hlen; reflexivity).
    specialize (IH B i Hlen'). exact IH.
Qed.

(* To bridge to mat_get we also need that row lengths match.
   The S1 workload only uses `madd` where both matrices are square
   n x n, so we expose a square-matrix corollary.  The general
   per-row length hypothesis is tracked via an extra predicate. *)

Definition all_rows_len (n : nat) (A : mat) : Prop :=
  forall i, (i < List.length A)%coq_nat ->
            List.length (List.nth i A nil) = n.

Lemma mat_get_madd (A B : mat) (n : nat) (i j : nat) :
  List.length A = List.length B ->
  all_rows_len n A -> all_rows_len n B ->
  (i < List.length A)%coq_nat ->
  mat_get (madd A B) i j = BinInt.Z.add (mat_get A i j) (mat_get B i j).
Proof.
  intros Hlen HA HB Hi. unfold mat_get.
  rewrite (nth_madd A B i Hlen).
  assert (HAlen : List.length (List.nth i A nil) = n) by (apply HA; exact Hi).
  assert (HBlen : List.length (List.nth i B nil) = n).
  { apply HB. rewrite <- Hlen. exact Hi. }
  apply nth_Z_vadd. rewrite HAlen HBlen. reflexivity.
Qed.

(* Bridge lemma for `madd`.  The hypotheses `all_rows_len n A/B` are
   the structural well-formedness conditions that the input matrices
   are honest n x n grids; they are not part of CharPoly.v's public
   API (which would require editing CharPoly.v) but are added here
   so that the lemma can actually be discharged.  Downstream callers
   carry the same square-matrix invariants and can supply them. *)
Lemma mat_int_to_rat_madd (A B : mat) (n : nat) :
  mat_dim A = n -> mat_dim B = n ->
  all_rows_len n A -> all_rows_len n B ->
  mat_int_to_rat (madd A B) 1 n
  = (mat_int_to_rat A 1 n + mat_int_to_rat B 1 n)%R.
Proof.
  intros HdimA HdimB HrowA HrowB.
  unfold mat_dim in HdimA, HdimB.
  apply/matrixP => i j.
  rewrite /mat_int_to_rat !mxE.
  have Hlen : List.length A = List.length B by rewrite HdimA HdimB.
  have Hi : (nat_of_ord i < List.length A)%coq_nat.
  { rewrite HdimA. apply/ltP; exact: ltn_ord. }
  rewrite (mat_get_madd A B n i j Hlen HrowA HrowB Hi).
  rewrite Z_to_int_add intrD.
  change (Z_to_int 1) with (1%R : int).
  rewrite /=. by rewrite !divr1.
Qed.

(* ------- (5) trace ------------------------------------------ *)

(* The diagonal sum of A as an `int`-valued sum.  Generalised to an
   offset `k` so that the recursion in `mtrace_aux` can be unwound by
   structural induction on the matrix. *)
Lemma mtrace_aux_diag_sum (A : mat) (k : nat) :
  Z_to_int (mtrace_aux k A)
  = (\sum_(i < length A) Z_to_int (mat_get A i (k + i)%coq_nat))%R.
Proof.
  revert k. induction A as [|row rest IH]; intros k; simpl.
  - by rewrite big_ord0.
  - rewrite Z_to_int_add. rewrite big_ord_recl.
    rewrite Nat.add_0_r.
    have Hhead : nth_Z row k = mat_get (row :: rest) (nat_of_ord (ord0 : 'I_(length rest).+1)) k
      by rewrite /mat_get /=.
    rewrite Hhead. f_equal.
    rewrite (IH k.+1).
    apply: eq_bigr => i _.
    rewrite /mat_get /=. rewrite /bump /=.
    have Heq: (k + i)%coq_nat.+1 = (k + (1 + i))%coq_nat
      by rewrite /= Nat.add_succ_r.
    rewrite Heq. reflexivity.
Qed.

Lemma mtrace_int_to_rat (A : mat) (n : nat) :
  mat_dim A = n ->
  ((Z_to_int (mtrace A))%:~R : rat)
  = (\tr (mat_int_to_rat A 1 n))%R.
Proof.
  intros Hdim. unfold mtrace.
  rewrite mtrace_aux_diag_sum.
  rewrite raddf_sum /=.
  rewrite /mxtrace.
  unfold mat_dim in Hdim. rewrite Hdim.
  apply: eq_bigr => i _.
  rewrite /mat_int_to_rat mxE.
  change (Z_to_int 1) with (1%R : int).
  rewrite /= divr1. reflexivity.
Qed.

(* ------- (6) mmul ------------------------------------------- *)

(* Bridge lemmas for `mmul`.  The proof strategy:
   1. Reduce `mat_get (mmul A B) i j` to a `dot_int` over row_i(A) and a
      column of `mtrans B`.
   2. Show that under the well-formedness assumption `all_rows_len n B`,
      for any `j < n`, the j-th column of `mtrans B` behaves like
      `col_at j B := map (fun row => nth_Z row j) B` for indexing purposes.
   3. Lift the `dot_int` to a `\sum_(k<n)` over rat via `Z_to_int_add`,
      `Z_to_int_mul`, `intrD`, `intrM`.
*)

(* ---------- generic list helpers ---------- *)

Lemma nth_Z_oob (xs : list Z) (i : nat) :
  (List.length xs <= i)%coq_nat -> nth_Z xs i = Z0.
Proof.
  intros H. unfold nth_Z. apply List.nth_overflow. exact H.
Qed.

(* ---------- structural facts about mtrans ---------- *)

(* Shape of `tails m`. *)
Lemma length_tails (m : mat) : List.length (tails m) = List.length m.
Proof.
  induction m as [|row rest IH]; simpl; [reflexivity|].
  destruct row; simpl; rewrite IH; reflexivity.
Qed.

Lemma nth_tails (m : mat) (k : nat) :
  List.nth k (tails m) nil = List.tl (List.nth k m nil).
Proof.
  revert k. induction m as [|row rest IH]; intros k; simpl.
  - destruct k; simpl; reflexivity.
  - destruct row as [|x xs]; destruct k as [|k']; simpl.
    + reflexivity.
    + apply IH.
    + reflexivity.
    + apply IH.
Qed.

Lemma nth_heads (m : mat) (k : nat) :
  List.nth k (heads m) Z0 = nth_Z (List.nth k m nil) 0.
Proof.
  revert k. induction m as [|row rest IH]; intros k; simpl.
  - destruct k; reflexivity.
  - destruct row as [|x xs]; destruct k as [|k']; simpl; try reflexivity.
    + apply IH.
    + apply IH.
Qed.

Lemma length_heads (m : mat) : List.length (heads m) = List.length m.
Proof.
  induction m as [|row rest IH]; simpl; [reflexivity|].
  destruct row; simpl; rewrite IH; reflexivity.
Qed.

(* `mtrans_fuel` length: is at most the fuel. *)
Lemma length_mtrans_fuel (f : nat) (m : mat) :
  (List.length (mtrans_fuel f m) <= f)%coq_nat.
Proof.
  revert m. induction f as [|f IH]; intros m; simpl.
  - apply Nat.le_refl.
  - destruct (all_empty m); simpl.
    + apply Nat.le_0_l.
    + apply le_n_S. apply IH.
Qed.

(* Under "all rows have length >= f", `mtrans_fuel f m` has exactly f rows. *)
Fixpoint all_rows_at_least (k : nat) (m : mat) : Prop :=
  match m with
  | nil => True
  | r :: rest => (k <= List.length r)%coq_nat /\ all_rows_at_least k rest
  end.

Lemma all_rows_at_least_0 (m : mat) : all_rows_at_least 0 m.
Proof. induction m as [|r rest IH]; simpl; [exact I|]. split; [lia|exact IH]. Qed.

Lemma all_rows_at_least_tails (k : nat) (m : mat) :
  all_rows_at_least (S k) m -> all_rows_at_least k (tails m).
Proof.
  induction m as [|r rest IH]; intros H; simpl; [exact I|].
  destruct H as [Hr Hrest]. destruct r as [|x r']; simpl in *.
  - lia.
  - split; [lia|]. apply IH. exact Hrest.
Qed.

Lemma all_empty_false_of_Sk (k : nat) (m : mat) :
  m <> nil -> all_rows_at_least (S k) m -> all_empty m = false.
Proof.
  intros Hne H. destruct m as [|r rest].
  - exfalso; apply Hne; reflexivity.
  - simpl. destruct H as [Hr _]. destruct r as [|x r']; simpl in *.
    + lia.
    + reflexivity.
Qed.

Lemma length_mtrans_fuel_exact (f : nat) (m : mat) :
  m <> nil -> all_rows_at_least f m ->
  List.length (mtrans_fuel f m) = f.
Proof.
  revert m. induction f as [|f IH]; intros m Hne Hall; simpl.
  - reflexivity.
  - rewrite (all_empty_false_of_Sk f m Hne Hall). simpl.
    f_equal. apply IH.
    + destruct m as [|r rest]; [exfalso; apply Hne; reflexivity|].
      simpl. destruct r as [|x r']; simpl.
      * destruct Hall as [Hr _]. simpl in Hr. lia.
      * intros E; discriminate.
    + apply all_rows_at_least_tails. exact Hall.
Qed.

(* The nth row of `mtrans_fuel f m` has length `length m`
   (the number of rows of m). *)
Lemma length_nth_mtrans_fuel (f : nat) (m : mat) (j : nat) :
  (j < f)%coq_nat -> all_rows_at_least f m ->
  List.length (List.nth j (mtrans_fuel f m) nil) = List.length m.
Proof.
  revert m j. induction f as [|f IH]; intros m j Hj Hall; simpl.
  - lia.
  - destruct m as [|r rest] eqn:Em.
    + simpl. destruct j; reflexivity.
    + have Hne: (r :: rest) <> nil by intros E; discriminate.
      rewrite <- Em in *.
      rewrite (all_empty_false_of_Sk f m Hne Hall).
      destruct j as [|j']; simpl.
      * apply length_heads.
      * rewrite IH; [| lia | apply all_rows_at_least_tails; exact Hall].
        apply length_tails.
Qed.

(* The entry at row j, column k of `mtrans_fuel f m` is `nth_Z (nth k m nil) j`
   (i.e. transposed indexing).  Proved under the shape hypothesis. *)
Lemma nth_nth_mtrans_fuel (f : nat) (m : mat) (j k : nat) :
  (j < f)%coq_nat -> all_rows_at_least f m ->
  List.nth k (List.nth j (mtrans_fuel f m) nil) Z0
  = nth_Z (List.nth k m nil) j.
Proof.
  revert m j k. induction f as [|f IH]; intros m j k Hj Hall.
  - lia.
  - simpl.
    destruct m as [|r rest] eqn:Em.
    + simpl. unfold nth_Z. destruct j; destruct k; simpl; reflexivity.
    + have Hne : (r :: rest) <> nil by intros E; discriminate.
      rewrite <- Em in *.
      rewrite (all_empty_false_of_Sk f m Hne Hall).
      destruct j as [|j']; simpl.
      * (* head row: heads m *)
        rewrite nth_heads.
        (* Goal: nth_Z (nth k m nil) 0 = nth_Z (nth k m nil) 0 *)
        reflexivity.
      * (* recursive: row j' of tails m *)
        rewrite IH; [| lia | apply all_rows_at_least_tails; exact Hall].
        rewrite nth_tails.
        (* Goal: nth_Z (tl (nth k m nil)) j' = nth_Z (nth k m nil) (S j') *)
        unfold nth_Z.
        destruct (List.nth k m nil) as [|x xs]; simpl.
        -- destruct j'; reflexivity.
        -- reflexivity.
Qed.

(* Convert `all_rows_len n m` into `all_rows_at_least n m`. *)
Lemma all_rows_len_to_at_least (n : nat) (m : mat) :
  all_rows_len n m -> all_rows_at_least n m.
Proof.
  induction m as [|r rest IH]; simpl; [intros _; exact I|].
  intros H. split.
  - have H0 : List.length (List.nth 0 (r :: rest) nil) = n
      by (apply H; simpl; lia).
    simpl in H0. rewrite H0. apply Nat.le_refl.
  - apply IH. intros i Hi.
    have := H (S i). simpl. intros HH. apply HH. lia.
Qed.

(* `mtrans B` for an n x n square B.  Packaged forms. *)
Lemma length_mtrans_sq (B : mat) (n : nat) :
  List.length B = n -> all_rows_len n B ->
  List.length (mtrans B) = n.
Proof.
  intros Hdim Hrow.
  unfold mtrans. destruct B as [|r rest] eqn:EB.
  - simpl in Hdim. subst. reflexivity.
  - have Hrlen : List.length r = n.
    { have H0 : List.length (List.nth 0 (r :: rest) nil) = n
        by (apply Hrow; simpl; lia).
      simpl in H0. exact H0. }
    rewrite Hrlen.
    apply length_mtrans_fuel_exact.
    + intros E; discriminate.
    + exact (all_rows_len_to_at_least n (r :: rest) Hrow).
Qed.

Lemma nth_mtrans_length_sq (B : mat) (n : nat) (j : nat) :
  List.length B = n -> all_rows_len n B -> (j < n)%coq_nat ->
  List.length (List.nth j (mtrans B) nil) = List.length B.
Proof.
  intros Hdim Hrow Hj.
  unfold mtrans. destruct B as [|r rest] eqn:EB.
  - simpl in Hdim. subst. lia.
  - have Hrlen : List.length r = n.
    { have H0 : List.length (List.nth 0 (r :: rest) nil) = n
        by (apply Hrow; simpl; lia).
      simpl in H0. exact H0. }
    rewrite Hrlen.
    apply length_nth_mtrans_fuel; [lia|].
    exact (all_rows_len_to_at_least n (r :: rest) Hrow).
Qed.

Lemma nth_nth_mtrans_sq (B : mat) (n : nat) (j k : nat) :
  List.length B = n -> all_rows_len n B -> (j < n)%coq_nat ->
  List.nth k (List.nth j (mtrans B) nil) Z0
  = nth_Z (List.nth k B nil) j.
Proof.
  intros Hdim Hrow Hj.
  unfold mtrans. destruct B as [|r rest] eqn:EB.
  - simpl in Hdim. subst. lia.
  - have Hrlen : List.length r = n.
    { have H0 : List.length (List.nth 0 (r :: rest) nil) = n
        by (apply Hrow; simpl; lia).
      simpl in H0. exact H0. }
    rewrite Hrlen.
    rewrite nth_nth_mtrans_fuel; [reflexivity| lia|].
    exact (all_rows_len_to_at_least n (r :: rest) Hrow).
Qed.

(* ---------- dot_int as a mathcomp big-sum over rat ---------- *)

(* `dot_int xs ys` lifted to rat equals a big-sum over nat of the
   product of entries.  We lift through `Z_to_int` + `intrM` + `intrD`. *)
Lemma Z_to_int_dot_int_sum (xs ys : list Z) (n : nat) :
  (List.length xs <= n)%coq_nat ->
  ((Z_to_int (dot_int xs ys))%:~R : rat)
  = (\sum_(k < n)
       ((Z_to_int (nth_Z xs k))%:~R * (Z_to_int (nth_Z ys k))%:~R))%R.
Proof.
  revert ys n. induction xs as [|x xs IH]; intros ys n Hlen; simpl.
  - (* dot_int nil _ = 0; all terms vanish since nth_Z nil k = 0. *)
    rewrite /=.
    change (Z_to_int Z0) with (0%R : int).
    rewrite /=.
    have -> : ((0%R : int)%:~R : rat) = 0%R by rewrite /= mulr0z.
    symmetry.
    rewrite big1; [reflexivity|].
    intros k _.
    have -> : nth_Z nil (nat_of_ord k) = Z0
      by (unfold nth_Z; destruct (nat_of_ord k); reflexivity).
    change (Z_to_int Z0) with (0%R : int).
    have -> : ((0%R : int)%:~R : rat) = 0%R by rewrite /= mulr0z.
    by rewrite mul0r.
  - (* xs = x :: xs'; ys = nil or y :: ys' *)
    destruct ys as [|y ys']; simpl.
    + (* dot_int _ nil = 0 *)
      change (Z_to_int Z0) with (0%R : int).
      have -> : ((0%R : int)%:~R : rat) = 0%R by rewrite /= mulr0z.
      symmetry.
      rewrite big1; [reflexivity|].
      intros k _.
      have -> : nth_Z nil (nat_of_ord k) = Z0
        by (unfold nth_Z; destruct (nat_of_ord k); reflexivity).
      change (Z_to_int Z0) with (0%R : int).
      have -> : ((0%R : int)%:~R : rat) = 0%R by rewrite /= mulr0z.
      by rewrite mulr0.
    + (* x * y + dot_int xs' ys' *)
      rewrite Z_to_int_add Z_to_int_mul intrD intrM.
      destruct n as [|n']; simpl in Hlen; [lia|].
      rewrite big_ord_recl /=.
      rewrite (IH ys' n'); [| lia].
      by [].
Qed.

(* ---------- main mmul bridge ---------- *)

Lemma mat_get_mmul_sq (A B : mat) (n : nat) (i j : nat) :
  List.length A = n -> List.length B = n ->
  all_rows_len n A -> all_rows_len n B ->
  (i < n)%coq_nat -> (j < n)%coq_nat ->
  mat_get (mmul A B) i j
  = dot_int (List.nth i A nil) (List.nth j (mtrans B) nil).
Proof.
  intros HdimA HdimB HrowA HrowB Hi Hj.
  unfold mat_get, mmul.
  set Bt := mtrans B.
  have HBt_len : List.length Bt = n by apply length_mtrans_sq.
  have Hi' : (i < List.length A)%coq_nat by lia.
  (* Switch default for outer map via nth_indep then apply map_nth. *)
  rewrite (List.nth_indep _ nil (map (fun col => dot_int nil col) Bt));
    [| rewrite length_map; exact Hi'].
  rewrite (List.map_nth (fun row => map (fun col => dot_int row col) Bt) A nil i).
  set row := List.nth i A nil.
  unfold nth_Z.
  have Hjlt : (j < List.length Bt)%coq_nat by lia.
  rewrite (List.nth_indep _ Z0 (dot_int row nil));
    [| rewrite length_map; exact Hjlt].
  rewrite (List.map_nth (fun col => dot_int row col) Bt nil j).
  reflexivity.
Qed.

(* Main bridge lemma.  NOTE (signature change): we added the two
   well-formedness hypotheses `all_rows_len n A` and `all_rows_len n B`.
   These are the structural invariants that A and B are honest n x n
   grids; our `madd` bridge lemma above already carries the same extra
   hypotheses, so callers downstream (who hold square-matrix invariants
   anyway) can supply them. *)
Lemma mat_int_to_rat_mmul (A B : mat) (n : nat) :
  mat_dim A = n -> mat_dim B = n ->
  all_rows_len n A -> all_rows_len n B ->
  mat_int_to_rat (mmul A B) 1 n
  = (mat_int_to_rat A 1 n *m mat_int_to_rat B 1 n)%R.
Proof.
  intros HdimA HdimB HrowA HrowB.
  unfold mat_dim in HdimA, HdimB.
  apply/matrixP => i j.
  rewrite /mat_int_to_rat !mxE.
  have Hi : (nat_of_ord i < n)%coq_nat by apply/ltP; apply: ltn_ord.
  have Hj : (nat_of_ord j < n)%coq_nat by apply/ltP; apply: ltn_ord.
  rewrite (mat_get_mmul_sq A B n i j HdimA HdimB HrowA HrowB Hi Hj).
  change (Z_to_int 1) with (1%R : int).
  rewrite /= divr1.
  (* Rewrite mxE inside the big-sum on RHS.  We have to manually clear
     the (Z_to_int 1)%:~R = 1 factors inside the `under` body. *)
  have E1 : ((Z_to_int 1)%:~R : rat) = 1%R by [].
  under eq_bigr => k _ do (rewrite !mxE; rewrite E1; rewrite !divr1).
  have Hrowi_len : List.length (List.nth (nat_of_ord i) A nil) = n
    by apply HrowA; lia.
  rewrite (Z_to_int_dot_int_sum _ _ n); [| lia].
  apply: eq_bigr => k _.
  have Hk : (nat_of_ord k < n)%coq_nat by apply/ltP; apply: ltn_ord.
  have HBkj : nth_Z (List.nth (nat_of_ord j) (mtrans B) nil) (nat_of_ord k)
            = mat_get B (nat_of_ord k) (nat_of_ord j).
  { unfold nth_Z.
    rewrite (nth_nth_mtrans_sq B n (nat_of_ord j) (nat_of_ord k) HdimB HrowB Hj).
    reflexivity. }
  rewrite HBkj.
  (* Remaining: nth_Z (nth i A nil) k = mat_get A i k is definitional. *)
  reflexivity.
Qed.
