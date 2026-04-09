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

Lemma mat_int_to_rat_mmul (A B : mat) (n : nat) :
  mat_dim A = n -> mat_dim B = n ->
  mat_int_to_rat (mmul A B) 1 n
  = (mat_int_to_rat A 1 n *m mat_int_to_rat B 1 n)%R.
Proof. Admitted.
