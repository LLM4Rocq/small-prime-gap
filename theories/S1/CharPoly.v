(* theories/S1/CharPoly.v
   ---------------------------------------------------------------
   Integer-cleared characteristic polynomial — Faddeev-LeVerrier.

   This file gives a hand-rolled implementation of the Faddeev-
   LeVerrier algorithm over `list (list Z)` matrices, returning a
   `pol` (low-to-high `list Z`) whose value at lambda is
   det(lambda*I_n - A). The leading coefficient is 1 and the result
   is monic of degree `mat_dim A`.

   This Definition assumes the input is a square matrix. If so,
   all integer divisions by `k` performed during the recurrence are
   exact (a classical identity from the Faddeev-LeVerrier proof;
   proof postponed to a later sprint), and `Z.div` returns the
   correct rational value.

   Dependencies:
   - PrimeGapS1.IntPoly (list Z polynomial library, by another agent)
   - PrimeGapS1.IntMat  (list (list Z) matrix library, by another agent)
   - MathComp algebra   (for the abstract `char_poly` spec).

   ===============================================================
   PROOF OUTLINE for `char_poly_int_correct`  (L2, PLAN_S1.md)
   ===============================================================

   Goal:
     pol_to_polyrat (char_poly_int M) = char_poly (mat_int_to_rat M 1 n)

   --- Proof chain ---

   Step 0 [Qed]:
     Structural trivia (meye_aux_len, mat_dim_meye, mzero_aux_len,
     mat_dim_mzero) — proved by list induction.

   Step 1 [Qed]:
     All 6 bridge lemmas (mat_int_to_rat_meye/mzero/mmul/madd/mscale,
     mtrace_int_to_rat) are fully proved.

   Steps 2-3 [Qed modulo Z_rem_of_intr_eq]:
     FL loop invariant (fl_invariant_L2) — Qed for the inductive step
       under hypotheses; wrapper Admitted pending fl_divisibility_L2.
     FL = char_poly (fl_loop_rat_is_char_poly_L2) — Qed via
       adj_coef_jacobi (Jacobi's formula proved from Leibniz).

   Step 4 [Admitted]:
     char_poly_int_correct — assembly of Steps 1-3.

   Current status:
     Step 0: Qed.
     Step 1: Qed.
     Steps 2-3: mostly Qed; fl_divisibility_L2 Admitted.
     Step 4: Admitted (assembly).
   --------------------------------------------------------------- *)

From Stdlib Require Import ZArith List Lia.
Import ListNotations.
Open Scope Z_scope.

From mathcomp Require Import all_boot all_algebra.
From mathcomp.algebra_tactics Require Import ring lra.
Import GRing.Theory.

From PrimeGapS1 Require Import IntPoly IntMat.

(* ==================================================================
   Faddeev-LeVerrier recurrence over `mat` = `list (list Z)`.

   Recurrence (Wikipedia convention):

     M_0   := 0
     c_n   := 1
     for k = 1, 2, ..., n:
         M_k     := A * M_{k-1} + c_{n-k+1} * I
         c_{n-k} := -(1/k) * trace(A * M_k)

   Final characteristic polynomial (monic):

     p(lambda) = lambda^n + c_{n-1} lambda^{n-1} + ... + c_1 lambda + c_0
               = det(lambda*I - A)

   Output format (`pol` low-to-high):

     [c_0; c_1; ...; c_{n-1}; 1]

   Key identity used to justify `Z.div` (proof deferred):
   at every step, `trace(A * M_k)` is divisible by `k` over Z.
   ================================================================== *)

(* One iteration of Faddeev-LeVerrier.
   - `steps`  : remaining iterations (starts at n, decreases by 1)
   - `k`      : current iteration index as Z (starts at 1)
   - `A`      : the input matrix (constant across iterations)
   - `I_n`    : identity matrix of the right size (constant)
   - `M_prev` : the matrix M_{k-1} from the previous step (starts at mzero n)
   - `c_prev` : the scalar c_{n-(k-1)} = c_{n-k+1} (starts at 1)
   - `acc`    : accumulated low-to-high coefficient list

   The accumulator is built in the correct low-to-high order:
   after the first iteration `acc` is [c_{n-1}], after the second
   [c_{n-2}; c_{n-1}], ..., after n iterations [c_0; c_1; ...; c_{n-1}].
*)
Fixpoint fl_loop
  (steps : nat) (k : Z)
  (A I_n : mat)
  (M_prev : mat) (c_prev : Z)
  (acc : list Z) : list Z :=
  match steps with
  | O => acc
  | S s =>
      let AMprev := mmul A M_prev in
      let M_k    := madd AMprev (mscale c_prev I_n) in
      let AMk    := mmul A M_k in
      let tr     := mtrace AMk in
      (* c_new = -(trace(A*M_k)) / k  (exact integer division). *)
      let c_new  := Z.div (Z.opp tr) k in
      fl_loop s (k + 1) A I_n M_k c_new (c_new :: acc)
  end.

(* ------------------------------------------------------------------
   The characteristic polynomial of an integer square matrix.

   Signature: `mat -> pol`. The matrix is taken at face value (no
   implicit denominator): `peval (char_poly_int A) lambda = det(lambda*I - A)`
   over Z, for any square `A`.

   Cert.v does not call `char_poly_int` directly (it only mentions
   it in comments and uses `char_poly_int_correct` / `mat_int_to_rat`
   / `pol_to_polyrat` through opaque bridges), so we are free to
   expose the cleaner 1-argument signature. The bridging names
   below keep the public API expected by PLAN_S1.md.
   ------------------------------------------------------------------ *)
Definition char_poly_int (A : mat) : pol :=
  let n := mat_dim A in
  let I_n := meye n in
  let coeffs := fl_loop n Z.one A I_n (mzero n) Z.one [] in
  coeffs ++ [Z.one].

(* ==================================================================
   Bridging definitions — concrete (no longer Admitted).

   These functions are plumbing between our `list Z`-based computational
   layer and MathComp's `'M[rat]_n` / `{poly rat}` spec layer. They are
   total, ring-homomorphic in the obvious way, and never invoked under
   `vm_compute` (only at the type level by the spec / proofs).
   ================================================================== *)

(* stdlib Z -> mathcomp int. *)
Definition Z_to_int (z : Z) : int :=
  match z with
  | Z0     => 0%R
  | Zpos p => Posz (Pos.to_nat p)
  | Zneg p => Negz (Pos.to_nat p - 1)
  end.

(* Lift an `mat` of integers plus a denominator D to an 'M[rat]_n.
   Semantics: `mat_int_to_rat M D n (i, j) = (M_int[i][j])%:Q / D%:Q`.
   Out-of-range entries default to 0 via `mat_get`. *)
Definition mat_int_to_rat (M : mat) (D : Z) (n : nat) : 'M[rat]_n :=
  \matrix_(i, j)
    ((Z_to_int (mat_get M (nat_of_ord i) (nat_of_ord j)))%:~R
       / (Z_to_int D)%:~R)%R.

(* Lift a `pol = list Z` to a `{poly rat}` by coefficient-wise
   embedding Z -> rat. *)
Definition pol_to_polyrat (p : pol) : {poly rat} :=
  Poly (List.map (fun z => (Z_to_int z)%:~R : rat) p).

(* ==================================================================
   STEP 0 — structural trivia about our concrete list-of-list matrices.

   These are all proved by direct list induction.  They feed into the
   Step 1 bridge lemmas below, which in turn feed `char_poly_int_correct`.
   ================================================================== *)

Lemma meye_aux_len (n i : nat) : length (meye_aux n i) = i.
Proof.
  induction i as [|k IH]; simpl; [reflexivity|].
  rewrite length_app. simpl. rewrite IH. apply Nat.add_1_r.
Qed.

Lemma mat_dim_meye (n : nat) : mat_dim (meye n) = n.
Proof. unfold mat_dim, meye. apply meye_aux_len. Qed.

Lemma mzero_aux_len (rows cols : nat) : length (mzero_aux rows cols) = rows.
Proof. induction rows as [|k IH]; simpl; [reflexivity|]. now rewrite IH. Qed.

Lemma mat_dim_mzero (n : nat) : mat_dim (mzero n) = n.
Proof. unfold mat_dim, mzero. apply mzero_aux_len. Qed.

(* ==================================================================
   STEP 1 — bridge lemmas.

   These relate `list (list Z)` matrix operations to MathComp
   'M[rat]_n operations through `mat_int_to_rat _ 1 n`.
   ================================================================== *)

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

Lemma nth_Z_oob (xs : list Z) (i : nat) :
  (List.length xs <= i)%coq_nat -> nth_Z xs i = Z0.
Proof.
  intros H. unfold nth_Z. apply List.nth_overflow. exact H.
Qed.

(* ---------- structural facts about mtrans ---------- *)

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

Lemma length_mtrans_fuel (f : nat) (m : mat) :
  (List.length (mtrans_fuel f m) <= f)%coq_nat.
Proof.
  revert m. induction f as [|f IH]; intros m; simpl.
  - apply Nat.le_refl.
  - destruct (all_empty m); simpl.
    + apply Nat.le_0_l.
    + apply le_n_S. apply IH.
Qed.

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
      * rewrite nth_heads. reflexivity.
      * rewrite IH; [| lia | apply all_rows_at_least_tails; exact Hall].
        rewrite nth_tails.
        unfold nth_Z.
        destruct (List.nth k m nil) as [|x xs]; simpl.
        -- destruct j'; reflexivity.
        -- reflexivity.
Qed.

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

Lemma Z_to_int_dot_int_sum (xs ys : list Z) (n : nat) :
  (List.length xs <= n)%coq_nat ->
  ((Z_to_int (dot_int xs ys))%:~R : rat)
  = (\sum_(k < n)
       ((Z_to_int (nth_Z xs k))%:~R * (Z_to_int (nth_Z ys k))%:~R))%R.
Proof.
  revert ys n. induction xs as [|x xs IH]; intros ys n Hlen; simpl.
  - rewrite /=.
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
  - destruct ys as [|y ys']; simpl.
    + change (Z_to_int Z0) with (0%R : int).
      have -> : ((0%R : int)%:~R : rat) = 0%R by rewrite /= mulr0z.
      symmetry.
      rewrite big1; [reflexivity|].
      intros k _.
      have -> : nth_Z nil (nat_of_ord k) = Z0
        by (unfold nth_Z; destruct (nat_of_ord k); reflexivity).
      change (Z_to_int Z0) with (0%R : int).
      have -> : ((0%R : int)%:~R : rat) = 0%R by rewrite /= mulr0z.
      by rewrite mulr0.
    + rewrite Z_to_int_add Z_to_int_mul intrD intrM.
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
  reflexivity.
Qed.

(* ==================================================================
   STEPS 2-3 — FL reference loop, Newton's identity, Jacobi's formula,
   FL invariant, and supporting L2 proofs.
   ================================================================== *)

Set Implicit Arguments.
Unset Strict Implicit.

(* Iterative FL state: returns (M_k, c_k) after k steps of the
   Faddeev-LeVerrier recurrence on integer matrix A.
   - fl_state A 0 = (mzero n, 1)    where n = mat_dim A
   - fl_state A (k+1) = one FL step from fl_state A k            *)
Fixpoint fl_state (k : nat) (A : mat) : mat * Z :=
  let n := mat_dim A in
  let I_n := meye n in
  match k with
  | O => (mzero n, Zpos xH)
  | S k' =>
    let '(M_prev, c_prev) := fl_state k' A in
    let M_k := madd (mmul A M_prev) (mscale c_prev I_n) in
    let tr := mtrace (mmul A M_k) in
    let c_new := BinInt.Z.div (BinInt.Z.opp tr) (BinInt.Z.of_nat (S k')) in
    (M_k, c_new)
  end.

Definition fl_M_int_k (A : mat) (k : nat) : mat := fst (fl_state k A).
Definition fl_c_int_k (A : mat) (k : nat) : Z := snd (fl_state k A).
Unset Printing Implicit Defensive.

(* ==================================================================
   1. fl_loop_rat — the rational-side reference Faddeev-LeVerrier loop.
   ================================================================== *)

Section FLRat.

Variable (n : nat).
Variable (A : 'M[rat]_n).

Definition fl_step_rat (k : nat) (prev : 'M[rat]_n * rat)
  : 'M[rat]_n * rat :=
  let M_prev := fst prev in
  let c_prev := snd prev in
  let M_k := (A *m M_prev + c_prev *: (1%:M))%R in
  let tr_AMk := (\tr (A *m M_k))%R in
  let c_new := (- tr_AMk / (k%:R))%R in
  (M_k, c_new).

Fixpoint fl_loop_rat (k : nat) : 'M[rat]_n * rat :=
  match k with
  | O   => (0%R, 1%R)
  | S k' => fl_step_rat (S k') (fl_loop_rat k')
  end.

Definition fl_M_rat (k : nat) : 'M[rat]_n := fst (fl_loop_rat k).
Definition fl_c_rat (k : nat) : rat := snd (fl_loop_rat k).

End FLRat.

(* ==================================================================
   2. fl_invariant_L2 — the loop invariant bridge.
   ================================================================== *)

Lemma Z_to_int_opp (a : Z) :
  Z_to_int (BinInt.Z.opp a) = (- Z_to_int a)%R.
Proof.
  destruct a as [|pa|pa]; simpl BinInt.Z.opp.
  - by rewrite oppr0.
  - by rewrite Z_to_int_neg_pos Z_to_int_pos_pos.
  - by rewrite Z_to_int_neg_pos Z_to_int_pos_pos opprK.
Qed.

Lemma Z_div_exact_rat (a d : Z) :
  d <> Z0 ->
  BinInt.Z.rem a d = Z0 ->
  ((Z_to_int (BinInt.Z.div a d))%:~R : rat)
  = ((Z_to_int a)%:~R / (Z_to_int d)%:~R)%R.
Proof.
  intros Hd Hrem.
  have Hdvd : (d | a)%Z by apply (BinInt.Z.rem_divide a d Hd); exact Hrem.
  destruct Hdvd as [q Hq]. subst a.
  rewrite BinInt.Z.div_mul; [|exact Hd].
  rewrite Z_to_int_mul intrM.
  rewrite mulfK.
  - reflexivity.
  - apply/eqP => Habs. apply Hd.
    destruct d as [|pd|pd]; [reflexivity| |]; exfalso.
    + rewrite Z_to_int_pos_pos /= in Habs. revert Habs. rewrite /intmul /=.
      have Hpos := Pos2Nat.is_pos pd.
      destruct (Pos.to_nat pd) as [|m] eqn:E.
      { exfalso; exact (Nat.lt_irrefl 0 Hpos). }
      clear Hpos E. move=> H.
      have Hgt0 : (0 < (m.+1%:R : rat))%R by apply/Num.Theory.ltr0Sn.
      rewrite H in Hgt0. discriminate Hgt0.
    + rewrite Z_to_int_neg_pos /= in Habs. revert Habs. rewrite rmorphN /= /intmul /=.
      have Hpos := Pos2Nat.is_pos pd.
      destruct (Pos.to_nat pd) as [|m] eqn:E.
      { exfalso; exact (Nat.lt_irrefl 0 Hpos). }
      clear Hpos E.
      move=> H. have : (- (m.+1%:R : rat) = 0)%R by exact H.
      move/eqP. rewrite oppr_eq0 => /eqP H2.
      have Hgt0 : (0 < (m.+1%:R : rat))%R by apply/Num.Theory.ltr0Sn.
      rewrite H2 in Hgt0. discriminate Hgt0.
Qed.

Lemma Z_to_int_of_nat (nn : nat) :
  Z_to_int (BinInt.Z.of_nat nn) = Posz nn.
Proof. case: nn => [//|nn]; by rewrite /Z_to_int /= SuccNat2Pos.id_succ. Qed.

Lemma Z_to_int_1_rat : ((Z_to_int (Zpos xH))%:~R : rat) = 1%R.
Proof.
  rewrite Z_to_int_1.
  by rewrite /intmul /=.
Qed.

Section FL_Invariant_Proof.

Variable M : mat.
Variable sz : nat.

Let A := mat_int_to_rat M 1 sz.

Variable fl_M : nat -> mat.
Variable fl_c : nat -> Z.

Hypothesis fl_base_M : fl_M 0 = mzero sz.
Hypothesis fl_base_c : fl_c 0 = Zpos xH.

Hypothesis fl_step_M : forall k, (k < sz)%N ->
  fl_M k.+1 = madd (mmul M (fl_M k)) (mscale (fl_c k) (meye sz)).

Hypothesis fl_step_c : forall k, (k < sz)%N ->
  fl_c k.+1 = BinInt.Z.div
                (BinInt.Z.opp (mtrace (mmul M (fl_M k.+1))))
                (BinInt.Z.of_nat k.+1).

Hypothesis fl_M_dim : forall k, (k <= sz)%N -> mat_dim (fl_M k) = sz.
Hypothesis fl_M_rows : forall k, (k <= sz)%N -> all_rows_len sz (fl_M k).

Hypothesis M_dim : mat_dim M = sz.
Hypothesis M_rows : all_rows_len sz M.

Hypothesis meye_rows : all_rows_len sz (meye sz).

Hypothesis fl_div : forall k, (k < sz)%N ->
  BinInt.Z.rem (mtrace (mmul M (fl_M k.+1)))
               (BinInt.Z.of_nat k.+1) = Z0.

Hypothesis mmul_dim : forall A' B' : mat,
  mat_dim A' = sz -> mat_dim B' = sz -> mat_dim (mmul A' B') = sz.
Hypothesis mmul_rows : forall A' B' : mat,
  mat_dim A' = sz -> mat_dim B' = sz ->
  all_rows_len sz A' -> all_rows_len sz B' ->
  all_rows_len sz (mmul A' B').
Hypothesis mscale_dim : forall c (A' : mat), mat_dim A' = sz -> mat_dim (mscale c A') = sz.
Hypothesis mscale_rows : forall c (A' : mat),
  all_rows_len sz A' -> all_rows_len sz (mscale c A').

Lemma fl_invariant_L2_gen (k : nat) :
  (k <= sz)%N ->
  mat_int_to_rat (fl_M k) 1 sz = fl_M_rat A k
  /\
  ((Z_to_int (fl_c k))%:~R : rat) = fl_c_rat A k.
Proof.
  elim: k => [|k IH] Hle.
  - rewrite fl_base_M fl_base_c.
    split.
    + rewrite mat_int_to_rat_mzero. reflexivity.
    + exact Z_to_int_1_rat.
  - have Hk_le : (k <= sz)%N by apply: ltnW.
    have Hk_lt : (k < sz)%N by exact Hle.
    have [IHmat IHcoeff] := IH Hk_le.
    rewrite /fl_M_rat /fl_c_rat /= -/fl_loop_rat.
    rewrite -/(fl_M_rat A k) -/(fl_c_rat A k).
    rewrite -IHmat -IHcoeff.
    split.
    + rewrite (fl_step_M Hk_lt).
      rewrite (mat_int_to_rat_madd
                 (mmul M (fl_M k)) (mscale (fl_c k) (meye sz)) sz
                 (mmul_dim M_dim (fl_M_dim Hk_le))
                 (mscale_dim (fl_c k) (mat_dim_meye sz))
                 (mmul_rows M_dim (fl_M_dim Hk_le) M_rows (fl_M_rows Hk_le))
                 (@mscale_rows (fl_c k) (meye sz) meye_rows)).
      rewrite (mat_int_to_rat_mmul M (fl_M k) sz M_dim (fl_M_dim Hk_le)
                 M_rows (fl_M_rows Hk_le)).
      rewrite mat_int_to_rat_mscale mat_int_to_rat_meye.
      reflexivity.
    + rewrite (fl_step_c Hk_lt).
      have Hkp : BinInt.Z.of_nat k.+1 <> Z0.
      { rewrite Nat2Z.inj_succ. lia. }
      have Hdiv_opp :
        Z.rem (BinInt.Z.opp (mtrace (mmul M (fl_M k.+1))))
              (BinInt.Z.of_nat k.+1) = Z0
        by rewrite Z.rem_opp_l // fl_div.
      rewrite (@Z_div_exact_rat _ _ Hkp Hdiv_opp).
      rewrite Z_to_int_opp rmorphN /=.
      rewrite SuccNat2Pos.id_succ -pmulrn.
      congr (_ / _)%R. congr (- _)%R.
      have HMk1_dim : mat_dim (fl_M k.+1) = sz
        by apply fl_M_dim; exact Hle.
      have HMk1_rows : all_rows_len sz (fl_M k.+1)
        by apply fl_M_rows; exact Hle.
      have Hmmul_dim : mat_dim (mmul M (fl_M k.+1)) = sz
        by exact (mmul_dim M_dim HMk1_dim).
      rewrite (mtrace_int_to_rat (mmul M (fl_M k.+1)) sz Hmmul_dim).
      rewrite (mat_int_to_rat_mmul M (fl_M k.+1) sz M_dim HMk1_dim
                 M_rows HMk1_rows).
      rewrite (fl_step_M Hk_lt).
      rewrite (mat_int_to_rat_madd
                 (mmul M (fl_M k)) (mscale (fl_c k) (meye sz)) sz
                 (mmul_dim M_dim (fl_M_dim Hk_le))
                 (mscale_dim (fl_c k) (mat_dim_meye sz))
                 (mmul_rows M_dim (fl_M_dim Hk_le) M_rows (fl_M_rows Hk_le))
                 (@mscale_rows (fl_c k) (meye sz) meye_rows)).
      rewrite (mat_int_to_rat_mmul M (fl_M k) sz M_dim (fl_M_dim Hk_le)
                 M_rows (fl_M_rows Hk_le)).
      rewrite mat_int_to_rat_mscale mat_int_to_rat_meye.
      reflexivity.
Qed.

End FL_Invariant_Proof.

(* ==================================================================
   4. fl_loop_rat_is_char_poly_L2 — the abstract identity.
   ================================================================== *)

Section FL_CharPoly_Core.

Variable (n : nat).
Variable (B : 'M[rat]_n.+1).

Let cp := char_poly B.

Lemma fl_M_expansion (k : nat) :
  (k <= n.+1)%N ->
  fl_M_rat B k =
    (\sum_(j < k) fl_c_rat B j *: B ^+ (k - j.+1))%R.
Proof.
  elim: k => [|k IH] Hk.
  - by rewrite big_ord0.
  - rewrite /fl_M_rat /= -/fl_loop_rat /fl_step_rat /=.
    rewrite -/(fl_M_rat B k) -/(fl_c_rat B k).
    have Hk' : (k <= n.+1)%N by exact (ltnW Hk).
    rewrite (IH Hk').
    rewrite mulmx_sumr.
    rewrite big_ord_recr /=.
    rewrite subnn expr0.
    congr (_ + _)%R.
    apply eq_bigr => j _.
    rewrite -scalemxAr.
    congr (_ *: _)%R.
    have Hj : (j < k)%N by exact (ltn_ord j).
    change (B *m B ^+ (k - j.+1))%R with (B * B ^+ (k - j.+1))%R.
    rewrite -exprS.
    congr (B ^+ _)%R.
    rewrite subSn //.
Qed.

Fixpoint adj_coef (l : nat) : 'M[rat]_(n.+1) :=
  match l with
  | O => 1%:M
  | l'.+1 => (B *m adj_coef l' + (cp)`_(n - l') *: 1%:M)%R
  end.

Let Hlead_cp : ((cp)`_n.+1 = 1 :> rat)%R.
Proof.
  have /monicP := char_poly_monic B.
  by rewrite /lead_coef (size_char_poly B).
Qed.

Lemma adj_coef_formula (l : nat) :
  (l <= n.+1)%N ->
  adj_coef l = (\sum_(m < l.+1) (cp)`_(n.+1 - l + m) *: B ^+ m)%R.
Proof.
  elim: l => [|l IH] Hl.
  - by rewrite big_ord_recl big_ord0 /= subn0 addn0 Hlead_cp expr0 addr0
               scale1r.
  - rewrite /= (IH (ltnW Hl)) mulmx_sumr.
    have Hpos : (0 < n.+1 - l)%N by rewrite subn_gt0.
    have Heq : (n.+1 - l).-1 = (n - l)%N by rewrite -subnS.
    rewrite big_ord_recl /= addn0 expr0.
    rewrite [RHS]big_ord_recl /= addn0 expr0.
    have -> : (n.+1 - l.+1)%N = (n - l)%N by rewrite subnS -Heq.
    rewrite [LHS]addrC addrA -[LHS]addrA.
    congr (_ + _)%R.
    rewrite [RHS]big_ord_recl /= /bump /= addn0.
    have -> : (n - l + 1)%N = (n.+1 - l)%N.
    { rewrite addn1 -Heq. by rewrite prednK. }
    congr (_ + _)%R.
    { by rewrite -scalemxAr mulmx1. }
    apply eq_bigr => [[m Hm]] _ /=.
    rewrite -scalemxAr.
    change (B *m B ^+ (1 + m))%R with (B * B ^+ (1 + m))%R.
    rewrite -exprS.
    have -> : (n - l + (1 + (1 + m)))%N = (n.+1 - l + (1 + m))%N.
    { by rewrite addnA addn1 -Heq prednK. }
    done.
Qed.

Lemma adj_coef_trace (l : nat) :
  (l <= n.+1)%N ->
  mxtrace (adj_coef l) =
    (\sum_(m < l.+1) (cp)`_(n.+1 - l + m) * mxtrace (B ^+ m))%R.
Proof.
  move=> Hl. rewrite (adj_coef_formula Hl) raddf_sum /=.
  apply eq_bigr => m _. by rewrite mxtraceZ.
Qed.

Lemma adj_coef_jacobi (l : nat) :
  (l <= n)%N ->
  mxtrace (adj_coef l) = ((n.+1 - l)%:R * (cp)`_(n.+1 - l))%R.
Proof.
  move=> Hl.
  suff Hsuff : (mxtrace (adj_coef l) = (deriv cp)`_(n - l))%R.
  { rewrite Hsuff coef_deriv.
    have Hnl2 : (n - l).+1 = (n.+1 - l)%N by lia.
    by rewrite Hnl2 mulr_natl. }
  set P := char_poly_mx B.
  pose Q := fun k : nat => map_mx (coefp k) (\adj P)%R : 'M[rat]_(n.+1).
  have Hcoef_eq : forall k : nat, (k <= n)%N ->
    (Q k - B *m Q k.+1 = cp`_k.+1 *: 1%:M :> 'M_(n.+1))%R.
  { move=> k Hk. apply/matrixP => i j. rewrite !mxE.
    have Hmma := mul_mx_adj P.
    have : ((P *m \adj P)%R i j = ((\det P)%:M)%R i j)%R by rewrite Hmma.
    rewrite !mxE.
    move=> Hprod.
    have Hcoef := congr1 (coefp k.+1) Hprod.
    rewrite /= in Hcoef.
    rewrite coef_sum coefMn in Hcoef.
    have HP : forall i0 j0 : 'I_n.+1, P i0 j0 = ((i0 == j0)%:R *: 'X - (B i0 j0)%:P)%R.
    { move=> i0 j0. rewrite /P /char_poly_mx mxE !mxE. by rewrite scaler_nat. }
    have Hcoef2 : forall i0 : 'I_n.+1,
      ((P i i0 * ((\adj P)%R) i0 j)`_k.+1 =
       (i == i0)%:R * (((\adj P)%R) i0 j)`_k - B i i0 * (((\adj P)%R) i0 j)`_k.+1)%R.
    { move=> i0. rewrite (HP i i0) mulrBl coefB -scalerAl coefZ coefXM /= coefCM.
      done. }
    rewrite (eq_bigr _ (fun i0 _ => Hcoef2 i0)) sumrB in Hcoef.
    rewrite mulr_natr -Hcoef.
    congr (_ - _)%R.
    - rewrite (bigD1 i) //= eqxx mul1r big1 ?addr0.
      + by rewrite mxE.
      + move=> i0 /negbTE Hi. by rewrite eq_sym Hi mul0r.
    - apply eq_bigr => i0 _. by rewrite /Q mxE. }
  have HQn : Q n = (1%:M)%R.
  { apply/matrixP => i j. rewrite /Q mxE !mxE /cofactor.
    case Hij: (i == j).
    - rewrite (eqP Hij).
      have -> : ((-1 : {poly rat}) ^+ (j + j) = 1)%R
        by rewrite addnn -mul2n mulnC exprM sqrr_sign.
      rewrite mul1r row'_col'_char_poly_mx -/(char_poly _).
      have /monicP := char_poly_monic (row' j (col' j B)).
      by rewrite /lead_coef (size_char_poly (row' j (col' j B))) /= => ->.
    - rewrite /coefp. apply nth_default. rewrite size_Msign.
      apply: (leq_trans (size_sum _ _ _)). apply/bigmax_leqP => s _. rewrite size_Msign.
      apply: (leq_trans (size_poly_prod_leq _ _)).
      rewrite card_ord /=.
      have Hentry_size : forall (k0 : 'I_n) (l0 : 'I_n),
        (size (row' j (col' i P) k0 l0) <= 2)%N.
        move=> k0 l0. rewrite mxE mxE /P /char_poly_mx !mxE.
        case: (lift j k0 == lift i l0); rewrite /=.
        - by rewrite mulr1n size_XsubC.
        - rewrite mulr0n sub0r size_opp size_polyC. by case: (_ == _).
      have Hij' : j != i.
        apply/eqP => Habs. move: Hij. by rewrite eq_sym Habs eqxx.
      have [k0 Hk0 _] := unlift_some Hij'.
      have Hspecial : forall (l0 : 'I_n),
        (size (row' j (col' i P) k0 l0) <= 1)%N.
        move=> l0. rewrite mxE mxE /P /char_poly_mx !mxE -Hk0.
        have -> : (i == lift i l0) = false by rewrite eq_liftF.
        rewrite /= mulr0n sub0r size_opp size_polyC. by case: (_ == _).
      have Hk0bound := Hspecial (perm.fun_of_perm.body s k0).
      rewrite (bigD1 k0) //=.
      have Hrest_bound : (\sum_(i0 < n | i0 != k0) size (row' j (col' i P) i0 (perm.fun_of_perm.body s i0)) <= \sum_(i0 < n | i0 != k0) 2%N)%N.
        apply: leq_sum => i0 _. exact: Hentry_size.
      rewrite sum_nat_const cardC1 card_ord in Hrest_bound.
      have Hn : (0 < n)%N by exact: (leq_ltn_trans (leq0n k0) (ltn_ord k0)).
      set a := size _. set b := (\sum_(i0 < n | i0 != k0) size _)%N.
      move=> /=. move: Hk0bound Hrest_bound Hn.
      move=> Ha Hb Hn2.
      have Hab : (a + b <= 1 + n.-1 * 2)%N by apply: leq_add.
      have: ((1 + n.-1 * 2).+1 - n <= n)%N.
        move: Hn2. case: (n) => [|n'] //=. move=> _. lia.
      lia. }
  have Hadj_eq : forall l' : nat, (l' <= n)%N ->
    Q (n - l')%N = adj_coef l' :> 'M_(n.+1).
  { elim => [|l' IHl'] Hl'.
    - by rewrite subn0 HQn.
    - have Hl'n : (l' <= n)%N := ltnW Hl'.
      have Hk : (n - l'.+1 <= n)%N by lia.
      have Hstep := Hcoef_eq (n - l'.+1)%N Hk.
      have Hsucc : (n - l'.+1).+1 = (n - l')%N by lia.
      have Hcp_idx : (n - l'.+1).+1 = (n - l')%N by lia.
      rewrite Hsucc (IHl' Hl'n) in Hstep.
      have -> : adj_coef l'.+1 = (B *m adj_coef l' + cp`_(n - l') *: 1%:M)%R by done.
      by rewrite -Hstep addrC addrNK. }
  have jacobi : (deriv (\det P) = \sum_(k : 'I_n.+1) \det (row' k (col' k P)))%R.
  { have deriv_prod_seq : forall (T : eqType) (s : seq T) (F : T -> {poly rat}),
      uniq s ->
      deriv (\prod_(i <- s) F i) =
      (\sum_(k <- s) deriv (F k) * \prod_(i <- s | i != k) F i)%R.
    { move=> T s F. elim: s => [|a s IHs] Huniq.
      - by rewrite !big_nil derivC.
      - have Ha : a \notin s by move: Huniq => /= /andP [].
        have Hs : uniq s by move: Huniq => /= /andP [].
        rewrite big_cons /= derivM (IHs Hs) [RHS]big_cons /=.
        have Hfilt : (\prod_(j <- s | j != a) F j = \prod_(j <- s) F j)%R.
          rewrite -big_filter. congr (\big[_/_]_(j <- _) F j)%R.
          apply/all_filterP/allP => i Hi.
          apply/negP => /eqP Habs. subst. by rewrite Hi in Ha.
        have -> : (\prod_(i <- a :: s | i != a) F i)%R = (\prod_(j <- s) F j)%R
          by rewrite big_cons /= eq_refl Hfilt.
        congr (_ + _)%R.
        rewrite big_distrr /= big_seq_cond [RHS]big_seq_cond.
        apply eq_bigr => k /andP [Hkin _].
        rewrite mulrCA. congr (_ * _)%R.
        rewrite big_cons /=.
        have -> : (a != k) = true by apply/eqP => Habs; subst; rewrite Hkin in Ha.
        done. }
    rewrite /determinant raddf_sum /=.
    under eq_bigr => s _.
      rewrite derivM.
      have -> : ((-1 : {poly rat}) ^+ perm.odd_perm s)^`()%R = 0%R.
        by case: (perm.odd_perm s); rewrite /= ?expr1 ?expr0 ?derivN ?derivC ?oppr0.
      rewrite mul0r add0r.
      rewrite deriv_prod_seq; first last.
        exact: index_enum_uniq.
      rewrite mulr_sumr.
      over.
    rewrite exchange_big /=.
    apply eq_bigr => k _.
    have Hderiv_entry : forall i j : 'I_n.+1,
      deriv (P i j) = ((i == j)%:R : rat)%:P%R.
    { move=> i j. rewrite /P /char_poly_mx !mxE.
      rewrite derivB derivC subr0 derivMn derivX.
      by rewrite polyCMn polyC1. }
    under eq_bigr => s _.
      rewrite Hderiv_entry.
      over.
    rewrite (eq_bigr (fun s =>
      if perm.fun_of_perm.body s k == k then
        (-1) ^+ perm.odd_perm s * \prod_(i < n.+1 | i != k) P i (perm.fun_of_perm.body s i)
      else 0))%R; last first.
    { move=> s _.
      case Hsk: (perm.fun_of_perm.body s k == k).
      - by rewrite (eqP Hsk) eqxx /= polyC1 mul1r.
      - have -> : (k == perm.fun_of_perm.body s k) = false by rewrite eq_sym Hsk.
        by rewrite /= polyC0 mul0r mulr0. }
    rewrite -big_mkcond /=.
    under eq_bigr => s Hs.
      rewrite (eq_bigl (fun i0 => k != i0)); last by move=> x; rewrite eq_sym.
      over.
    rewrite -expand_cofactor /cofactor.
    have -> : ((-1 : {poly rat}) ^+ (k + k) = 1)%R
      by rewrite addnn -mul2n mulnC exprM sqrr_sign.
    by rewrite mul1r. }
  have Hdiag : forall k : 'I_n.+1,
    ((\adj P) k k = char_poly (row' k (col' k B)))%R.
  { move=> k. rewrite mxE /cofactor.
    have -> : ((-1 : {poly rat}) ^+ (k + k) = 1)%R
      by rewrite addnn -mul2n mulnC exprM sqrr_sign.
    by rewrite mul1r /char_poly row'_col'_char_poly_mx. }
  have -> : cp = (\det P)%R by done.
  rewrite jacobi coef_sum /mxtrace.
  apply eq_bigr => k _.
  rewrite row'_col'_char_poly_mx /char_poly.
  rewrite -(Hadj_eq l Hl) /Q mxE.
  by rewrite Hdiag /char_poly.
Qed.

Lemma char_poly_newton (k : nat) :
  (1 <= k)%N -> (k <= n.+1)%N ->
  (\sum_(j < k) (cp)`_(n.+1 - j) * \tr (B ^+ (k - j)))%R
  = (- (k%:R * (cp)`_(n.+1 - k)))%R.
Proof.
  move=> Hk1 Hkle.
  have Hsize : size cp = n.+2 := size_char_poly B.
  have Hlead : ((cp)`_n.+1 = 1 :> rat)%R.
  { have /monicP := char_poly_monic B. by rewrite /lead_coef Hsize. }
  have HCH := Cayley_Hamilton B : horner_mx B cp = 0%R.
  have HCH_mx : (\sum_(i < n.+2) (cp)`_i *: B ^+ i)%R = 0%R :> 'M_(n.+1).
  { suff -> : (\sum_(i < n.+2) (cp)`_i *: B ^+ i)%R = horner_mx B cp
      by exact HCH.
    rewrite /horner_mx /horner_morph /=.
    rewrite (@horner_coef_wide _ n.+2 (map_poly scalar_mx cp) B).
    - apply eq_bigr => i _. rewrite coef_map /=. by rewrite -mul_scalar_mx.
    - rewrite (size_map_poly_id0 _); first by rewrite Hsize.
      have /monicP := char_poly_monic B. rewrite /lead_coef Hsize /= => ->.
      exact: oner_neq0. }
  have CH_trace : forall m : nat,
    (\sum_(i < n.+2) (cp)`_i * \tr (B ^+ (i + m)))%R = 0%R.
  { move=> m.
    have : (\sum_(i < n.+2) (cp)`_i *: B ^+ i *m B ^+ m)%R = 0%R
      by rewrite -mulmx_suml HCH_mx mul0mx.
    move/(congr1 (@mxtrace _ _)). rewrite mxtrace0 raddf_sum /=.
    suff H : forall i : 'I_n.+2,
      mxtrace ((cp)`_i *: B ^+ i *m B ^+ m)%R =
        ((cp)`_i * mxtrace (B ^+ (i + m)))%R.
    { move=> Hsum. by rewrite -(eq_bigr _ (fun i _ => H i)) Hsum. }
    move=> i. by rewrite -scalemxAl mxtraceZ exprD. }
  case: (ltnP k n.+1) => Hk.
  - have Hkn : (k <= n)%N by rewrite -ltnS.
    have Hkn1 : (k <= n.+1)%N := Hkle.
    have HNt := adj_coef_trace Hkn1.
    have HNj := adj_coef_jacobi Hkn.
    have Hcomb : (\sum_(m < k.+1) cp`_(n.+1 - k + m) * \tr (B ^+ m))%R
                 = ((n.+1 - k)%:R * cp`_(n.+1 - k))%R
      by rewrite -HNj HNt.
    rewrite big_ord_recl /= expr0 mxtrace_scalar addn0 in Hcomb.
    have Hsum : (\sum_(i < k) cp`_(n.+1 - k + bump 0 i)
                    * \tr (B ^+ bump 0 i))%R
                = (- (k%:R * cp`_(n.+1 - k)))%R.
    { apply (addrI (cp`_(n.+1 - k) * n.+1%:R)%R).
      rewrite Hcomb.
      have -> : (k%:R * (cp`_(n.+1 - k) : rat))%R
                = ((cp`_(n.+1 - k) : rat) * k%:R)%R by rewrite mulrC.
      rewrite -mulrBr -natrB //.
      by rewrite mulrC. }
    rewrite -Hsum (reindex_inj rev_ord_inj).
    apply eq_bigr => [[i Hi]] _ /=.
    rewrite /bump /= !add1n.
    have Hi3 : (i.+1 <= k)%N by done.
    rewrite subKn // subnBA //.
    congr (_ * _)%R. congr (cp`_ _)%R.
    by rewrite addnC -addnBA // addnC.
  - have Hk_eq : k = n.+1 by apply/eqP; rewrite eqn_leq Hkle Hk.
    subst k.
    have HCH0 := CH_trace 0%N.
    rewrite big_ord_recr /= Hlead mul1r in HCH0.
    rewrite big_ord_recl /= expr0 mxtrace_scalar addn0 in HCH0.
    rewrite big_ord_recl /= Hlead mul1r subn0.
    rewrite (reindex_inj rev_ord_inj).
    have Hsum_eq :
      (\sum_(j < n) cp`_(n.+1 - bump 0 (rev_ord j))
          * \tr (B ^+ (n.+1 - bump 0 (rev_ord j))))%R
      = (\sum_(i < n) cp`_(bump 0 i)
            * \tr (B ^+ (bump 0 i + 0)))%R.
    { apply eq_bigr => [[j Hj]] _ /=.
      rewrite /bump /= !add1n addn0.
      rewrite subnSK //.
      rewrite subSn; last by apply leq_subr.
      by rewrite subKn; last exact (ltnW Hj). }
    rewrite Hsum_eq addrC.
    apply (addrI (cp`_0 * n.+1%:R)%R).
    by rewrite addrA HCH0 subnn mulrC subrr.
Qed.

Lemma fl_trace_identity (k : nat) :
  (1 <= k)%N -> (k <= n.+1)%N ->
  (k%:R * fl_c_rat B k)%R =
    (- \sum_(j < k) fl_c_rat B j * \tr (B ^+ (k - j)))%R.
Proof.
  move=> Hk1 Hk.
  destruct k as [|k']; first by rewrite ltnn in Hk1.
  rewrite /fl_c_rat /= -/fl_loop_rat /fl_step_rat /=.
  rewrite -/(fl_M_rat B k') -/(fl_c_rat B k').
  rewrite mulrC -mulrA.
  rewrite mulVf; last first.
  { apply/eqP => Habs.
    have := @Num.Theory.ltr0Sn _ k'.
    move=> /(_ rat). rewrite Habs. by move=> []. }
  rewrite mulr1.
  congr (- _)%R.
  rewrite mulmxDr mxtraceD.
  rewrite -(scalemxAr (fl_c_rat B k') B (1%:M : 'M_n.+1)) mulmx1 mxtraceZ.
  rewrite big_ord_recr /= subSn // subnn expr1.
  congr (_ + _)%R.
  have Hk' : (k' <= n.+1)%N by exact (ltnW Hk).
  rewrite (fl_M_expansion Hk').
  rewrite mulmx_sumr mulmx_sumr raddf_sum.
  apply eq_bigr => j _.
  rewrite /matrix_mxtrace__canonical__Algebra_Additive /=.
  rewrite -(scalemxAr (fl_c_rat B j) B).
  rewrite -(scalemxAr (fl_c_rat B j) B).
  rewrite mxtraceZ.
  congr (_ * _)%R.
  change (B *m (B *m B ^+ (k' - j.+1)))%R with (B * (B * B ^+ (k' - j.+1)))%R.
  rewrite -exprS.
  change (B * B ^+ (k' - j))%R with (B *m B ^+ (k' - j))%R.
  change (B *m B ^+ (k' - j))%R with (B * B ^+ (k' - j))%R.
  rewrite -exprS.
  congr (\tr (B ^+ _))%R.
  have Hj : (j < k')%N by exact (ltn_ord j).
  rewrite subSn //; last exact (ltnW Hj).
  by rewrite subnS prednK // subn_gt0.
Qed.

Lemma fl_c_rat_eq_char_poly (k : nat) :
  (k <= n.+1)%N ->
  fl_c_rat B k = ((cp)`_(n.+1 - k))%R.
Proof.
  elim/ltn_ind: k => k IH Hk.
  destruct k as [|k'].
  - rewrite subn0 /fl_c_rat /=.
    have /monicP := char_poly_monic B.
    rewrite /lead_coef (size_char_poly B).
    by move=> ->.
  - have Hk'1 : (1 <= k'.+1)%N by done.
    have Hk'le : (k'.+1 <= n.+1)%N by exact Hk.
    have Hfl := fl_trace_identity Hk'1 Hk'le.
    have Hnewton := char_poly_newton Hk'1 Hk'le.
    have Hsums_eq :
      (\sum_(j < k'.+1) fl_c_rat B j * \tr (B ^+ (k'.+1 - j)))%R =
      (\sum_(j < k'.+1) (cp)`_(n.+1 - j) * \tr (B ^+ (k'.+1 - j)))%R.
    { apply eq_bigr => j _. congr (_ * _)%R.
      apply IH.
      - exact (ltn_ord j).
      - exact (ltnW (leq_trans (ltn_ord j) Hk'le)). }
    have Hkne0 : (k'.+1%:R : rat) != 0%R.
    { apply/eqP => Habs.
      have := @Num.Theory.ltr0Sn _ k'.
      move=> /(_ rat). rewrite Habs. by move=> []. }
    apply (mulfI Hkne0).
    rewrite Hfl Hsums_eq Hnewton subSS opprK. reflexivity.
Qed.

End FL_CharPoly_Core.

Lemma fl_loop_rat_is_char_poly_L2 (sz : nat) (B : 'M[rat]_sz) :
  let cs := map (fl_c_rat B) (rev (iota 1 sz)) in
  Poly (rcons cs 1%R) = char_poly B.
Proof.
  destruct sz as [|n].
  - rewrite /= /char_poly.
    have -> : B = (0 : 'M_0)%R by apply/matrixP => i; case: i => [].
    rewrite det_mx00 cons_poly_def mul0r add0r. reflexivity.
  - rewrite /=.
    set cs := map _ _.
    set q := char_poly B.
    have Hsize_cs : size cs = n.+1.
    { by rewrite size_map size_rev /= size_iota. }
    have Hlast : last 1%R (rcons cs 1%R) != 0%R.
    { rewrite last_rcons. exact GRing.oner_neq0. }
    have Hsize_q : size q = n.+2.
    { exact (size_char_poly B). }
    apply/polyP => i.
    rewrite coef_Poly.
    case: (ltnP i n.+2) => Hi.
    + case: (ltnP i n.+1) => Hi2.
      * rewrite nth_rcons Hsize_cs Hi2.
        rewrite (nth_map 0%N); last by rewrite size_rev /= size_iota.
        rewrite nth_rev; last by rewrite /= size_iota.
        rewrite /= size_iota -/(iota 1 n.+1).
        rewrite nth_iota; last by rewrite ltn_subrL.
        rewrite add1n subSS.
        rewrite /q fl_c_rat_eq_char_poly.
        { congr (_`_ _)%R. rewrite subSS subKn //. }
        { rewrite ltnS. exact (leq_subr i n). }
      * have Hieq : i = n.+1 by apply/eqP; rewrite eqn_leq Hi2 -ltnS Hi.
        subst i.
        rewrite nth_rcons Hsize_cs ltnn eqxx.
        have /monicP := char_poly_monic B.
        by rewrite /lead_coef /q Hsize_q /= => ->.
    + rewrite nth_default; last by rewrite size_rcons Hsize_cs.
      rewrite nth_default //. rewrite Hsize_q. exact Hi.
Qed.

(* ==================================================================
   5. Base case helper.
   ================================================================== *)

Lemma fl_base_case_mat (sz : nat) :
  let A := mat_int_to_rat (mzero sz) 1 sz in
  mat_int_to_rat (mzero sz) 1 sz = fl_M_rat A 0.
Proof.
  simpl. rewrite mat_int_to_rat_mzero. reflexivity.
Qed.

Lemma fl_base_case_coeff (sz : nat) :
  let A := mat_int_to_rat (mzero sz) 1 sz in
  ((Z_to_int (Zpos xH))%:~R : rat) = fl_c_rat A 0.
Proof.
  simpl. exact Z_to_int_1_rat.
Qed.

(* ==================================================================
   6. Well-formedness lemmas for integer matrix operations.
   ================================================================== *)

Lemma length_zrow (n : nat) : List.length (zrow n) = n.
Proof. induction n as [|k IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma length_vscale (c : Z) (xs : list Z) : List.length (vscale c xs) = List.length xs.
Proof. unfold vscale. apply List.length_map. Qed.

Lemma length_vadd (xs ys : list Z) :
  List.length xs = List.length ys ->
  List.length (vadd xs ys) = List.length xs.
Proof.
  revert ys; induction xs as [|x xs' IH]; intros ys Hlen; simpl.
  - destruct ys; simpl in Hlen; [reflexivity | discriminate].
  - destruct ys as [|y ys']; simpl in Hlen; [discriminate |].
    simpl. f_equal. apply IH. lia.
Qed.

Lemma mat_dim_mscale_eq (c : Z) (A : mat) : mat_dim (mscale c A) = mat_dim A.
Proof. unfold mat_dim, mscale. rewrite List.length_map. reflexivity. Qed.

Lemma mat_dim_mmul_eq (A B : mat) : mat_dim (mmul A B) = mat_dim A.
Proof. unfold mat_dim, mmul. rewrite List.length_map. reflexivity. Qed.

Lemma mat_dim_madd_eq (A B : mat) :
  mat_dim A = mat_dim B ->
  mat_dim (madd A B) = mat_dim A.
Proof.
  unfold mat_dim. revert B; induction A as [|a A' IH]; intros B Hlen; simpl.
  - destruct B; simpl in Hlen; [reflexivity | discriminate].
  - destruct B as [|b B']; [discriminate |].
    simpl. f_equal. apply IH. simpl in Hlen. lia.
Qed.

Lemma all_rows_len_mscale (n : nat) (c : Z) (A : mat) :
  all_rows_len n A -> all_rows_len n (mscale c A).
Proof.
  unfold all_rows_len, mscale. intros HA i Hi.
  rewrite List.length_map in Hi.
  rewrite (List.map_nth _ _ nil) /=.
  rewrite length_vscale. exact (HA i Hi).
Qed.

Lemma all_rows_len_madd (n : nat) (A B : mat) :
  mat_dim A = mat_dim B ->
  all_rows_len n A -> all_rows_len n B ->
  all_rows_len n (madd A B).
Proof.
  unfold all_rows_len, mat_dim.
  revert B; induction A as [|a A' IH]; intros B Hlen HA HB i Hi.
  - destruct B; simpl in *; lia.
  - destruct B as [|b B']; [discriminate |].
    simpl in Hi |- *. destruct i as [|i'].
    + simpl. rewrite length_vadd.
      * exact (HA 0%nat ltac:(simpl; lia)).
      * have Ha : length a = n := HA 0%nat ltac:(simpl; lia).
        have Hb : length b = n := HB 0%nat ltac:(simpl; lia).
        rewrite Ha Hb. reflexivity.
    + apply (IH B' ltac:(simpl in Hlen; lia)
               (fun j Hj => HA (S j) ltac:(simpl; lia))
               (fun j Hj => HB (S j) ltac:(simpl; lia))).
      lia.
Qed.

Lemma all_rows_len_mzero_aux (r c : nat) :
  all_rows_len c (mzero_aux r c).
Proof.
  unfold all_rows_len. induction r as [|k IH]; simpl; intros i Hi.
  - lia.
  - destruct i as [|i']; simpl.
    + apply length_zrow.
    + apply IH. lia.
Qed.

Lemma all_rows_len_mzero (n : nat) : all_rows_len n (mzero n).
Proof. exact: all_rows_len_mzero_aux. Qed.

Lemma length_eye_row (n i : nat) : List.length (eye_row n i) = n.
Proof.
  revert i; induction n as [|k IH]; intros i; simpl.
  - reflexivity.
  - destruct i; simpl; f_equal.
    + apply length_zrow.
    + apply IH.
Qed.

Lemma all_rows_len_meye_aux (n i : nat) :
  all_rows_len n (meye_aux n i).
Proof.
  unfold all_rows_len. induction i as [|k IH]; simpl; intros j Hj.
  - lia.
  - rewrite List.length_app in Hj. simpl in Hj.
    destruct (Nat.lt_ge_cases j (List.length (meye_aux n k))) as [Hlt|Hge].
    + rewrite List.app_nth1; [exact (IH j Hlt) | lia].
    + have Heq : j = List.length (meye_aux n k) by lia.
      subst j. rewrite List.app_nth2; [| lia].
      rewrite Nat.sub_diag. simpl. apply length_eye_row.
Qed.

Lemma all_rows_len_meye (n : nat) : all_rows_len n (meye n).
Proof. exact: all_rows_len_meye_aux. Qed.

Lemma all_rows_len_mmul (n : nat) (A B : mat) :
  mat_dim B = n -> all_rows_len n B ->
  all_rows_len n (mmul A B).
Proof.
  intros HdimB HrowB. unfold all_rows_len, mmul, mat_dim in *.
  induction A as [|row rest IH]; simpl; intros i Hi.
  - lia.
  - destruct i as [|i']; simpl.
    + rewrite List.length_map.
      exact (length_mtrans_sq B n HdimB HrowB).
    + apply IH. lia.
Qed.

(* ==================================================================
   7. FL state well-formedness and recurrence properties.
   ================================================================== *)

Lemma fl_M_int_k_wf (M : mat) (sz : nat) (k : nat) :
  mat_dim M = sz -> all_rows_len sz M ->
  (k <= sz)%N ->
  mat_dim (fl_M_int_k M k) = sz /\ all_rows_len sz (fl_M_int_k M k).
Proof.
  intros Hdim Hrows Hle. unfold fl_M_int_k.
  induction k as [|k' IH].
  - simpl. rewrite Hdim. split; [apply mat_dim_mzero | apply all_rows_len_mzero].
  - have Hle' : (k' <= sz)%N by exact (ltnW Hle).
    have [IHdim IHrows] := IH Hle'.
    simpl. case E: (fl_state k' M) => [M_prev c_prev] /=.
    have HMprev_dim : mat_dim M_prev = sz.
    { have H0d : mat_dim (fst (fl_state k' M)) = sz by exact IHdim.
      rewrite E /= in H0d. exact H0d. }
    have HMprev_rows : all_rows_len sz M_prev.
    { have H0r : all_rows_len sz (fst (fl_state k' M)) by exact IHrows.
      rewrite E /= in H0r. exact H0r. }
    split.
    + rewrite mat_dim_madd_eq.
      * rewrite mat_dim_mmul_eq. exact Hdim.
      * rewrite mat_dim_mmul_eq Hdim mat_dim_mscale_eq.
        symmetry. exact (mat_dim_meye sz).
    + apply all_rows_len_madd.
      * rewrite mat_dim_mmul_eq Hdim mat_dim_mscale_eq.
        symmetry. exact (mat_dim_meye sz).
      * exact (all_rows_len_mmul HMprev_dim HMprev_rows).
      * apply all_rows_len_mscale. rewrite Hdim. apply all_rows_len_meye.
Qed.

Lemma fl_M_int_k_dim (M : mat) (sz : nat) (k : nat) :
  mat_dim M = sz -> all_rows_len sz M ->
  (k <= sz)%N -> mat_dim (fl_M_int_k M k) = sz.
Proof. intros; exact (fl_M_int_k_wf H H0 H1).1. Qed.

Lemma fl_M_int_k_rows (M : mat) (sz : nat) (k : nat) :
  mat_dim M = sz -> all_rows_len sz M ->
  (k <= sz)%N -> all_rows_len sz (fl_M_int_k M k).
Proof. intros; exact (fl_M_int_k_wf H H0 H1).2. Qed.

Lemma fl_M_int_k_base (M : mat) :
  fl_M_int_k M 0 = mzero (mat_dim M).
Proof. reflexivity. Qed.

Lemma fl_c_int_k_base (M : mat) :
  fl_c_int_k M 0 = Zpos xH.
Proof. reflexivity. Qed.

Lemma fl_state_step (M : mat) (k : nat) :
  fl_state (S k) M =
    let '(M_prev, c_prev) := fl_state k M in
    let I_n := meye (mat_dim M) in
    let M_k := madd (mmul M M_prev) (mscale c_prev I_n) in
    let tr := mtrace (mmul M M_k) in
    (M_k, BinInt.Z.div (BinInt.Z.opp tr) (BinInt.Z.of_nat (S k))).
Proof. simpl. reflexivity. Qed.

Lemma fl_M_int_k_step (M : mat) (k : nat) :
  fl_M_int_k M (S k) = madd (mmul M (fl_M_int_k M k))
                             (mscale (fl_c_int_k M k) (meye (mat_dim M))).
Proof.
  unfold fl_M_int_k, fl_c_int_k. simpl.
  destruct (fl_state k M) as [M_prev c_prev] eqn:E. simpl. reflexivity.
Qed.

Lemma fl_c_int_k_step (M : mat) (k : nat) :
  fl_c_int_k M (S k) = BinInt.Z.div
                          (BinInt.Z.opp (mtrace (mmul M (fl_M_int_k M (S k)))))
                          (BinInt.Z.of_nat (S k)).
Proof.
  unfold fl_c_int_k, fl_M_int_k. simpl.
  destruct (fl_state k M) as [M_prev c_prev] eqn:E. simpl. reflexivity.
Qed.

(* ==================================================================
   8. fl_c_rat_is_int — char poly coefficients of integer matrices
      are integers (via map_char_poly from MathComp).
   ================================================================== *)

Lemma fl_c_rat_is_int (sz : nat) (M : mat) (k : nat) :
  let A_rat := mat_int_to_rat M 1 sz in
  (k <= sz)%N ->
  exists z : int, fl_c_rat A_rat k = (z%:~R : rat)%R.
Proof.
  move=> A_rat Hk.
  destruct sz as [|n].
  - have Hk0 : k = 0%N by apply/eqP; rewrite -leqn0.
    subst k. exists 1%R. by rewrite /fl_c_rat /= /intmul /=.
  - pose A_int : 'M[int]_n.+1 :=
      (\matrix_(i, j) Z_to_int (mat_get M (nat_of_ord i) (nat_of_ord j)))%R.
    have Hmap : A_rat = map_mx (intr : int -> rat) A_int.
    { apply/matrixP => i j. rewrite !mxE /=.
      change (Z_to_int 1) with (1%R : int). by rewrite divr1. }
    have Hcp : char_poly A_rat = map_poly (intr : int -> rat) (char_poly A_int).
    { rewrite Hmap. rewrite map_char_poly. reflexivity. }
    have Hcoef := @fl_c_rat_eq_char_poly n A_rat k Hk.
    rewrite Hcoef Hcp coef_map. by eexists.
Qed.

(* ==================================================================
   9. fl_invariant_L2 and fl_divisibility_L2 — proved via combined
      induction using fl_c_rat_is_int (integrality from map_char_poly).
   ================================================================== *)

Lemma intr_injective_rat (a b : int) :
  (a%:~R : rat)%R = (b%:~R : rat)%R -> a = b.
Proof.
  move=> H. apply/eqP.
  have H3 : ((a%:~R : rat)%R == (b%:~R : rat)%R) by apply/eqP.
  rewrite eqr_int in H3. exact H3.
Qed.

Lemma Z_to_int_injective (x y : Z) : Z_to_int x = Z_to_int y -> x = y.
Proof.
  destruct x as [|px|px], y as [|py|py]; rewrite /Z_to_int //; intro Hxy;
    try (exfalso; have := Pos2Nat.is_pos px; have := Pos2Nat.is_pos py; lia);
    try (exfalso; have := Pos2Nat.is_pos px; lia);
    try (exfalso; have := Pos2Nat.is_pos py; lia).
  - f_equal. apply Pos2Nat.inj. injection Hxy => Hnat. exact Hnat.
  - f_equal. apply Pos2Nat.inj. injection Hxy => Hnat.
    have := Pos2Nat.is_pos px. have := Pos2Nat.is_pos py. lia.
Qed.

Lemma Z_rem_of_intr_eq (a : Z) (k : nat) (z : int) :
  (0 < k)%N ->
  ((Z_to_int a)%:~R : rat)%R = (- ((k%:R : rat) * (z%:~R : rat)))%R ->
  Z.rem a (Z.of_nat k) = Z0.
Proof.
  intros Hk Heq.
  have Hint : Z_to_int a = (- (Posz k * z))%R.
  { apply intr_injective_rat. rewrite rmorphN rmorphM /=.
    rewrite -pmulrn. exact Heq. }
  apply Z.rem_divide.
  - destruct k; [inversion Hk | lia].
  - set w := (match z with Posz n => Z.of_nat n
                          | Negz n => Z.neg (Pos.of_succ_nat n) end).
    exists (Z.opp w).
    apply Z_to_int_injective. rewrite Z_to_int_mul Z_to_int_opp Z_to_int_of_nat.
    rewrite Hint.
    f_equal. rewrite mulrC. subst w. destruct z as [n|n].
    + by rewrite Z_to_int_of_nat mulNr mulrC.
    + rewrite Z_to_int_neg_pos SuccNat2Pos.id_succ mulNr mulrC. ring.
Qed.

Lemma fl_combined (M : mat) (sz : nat) :
  let A := mat_int_to_rat M 1 sz in
  mat_dim M = sz -> all_rows_len sz M ->
  forall k : nat, (k <= sz)%N ->
    (mat_int_to_rat (fl_M_int_k M k) 1 sz = fl_M_rat A k
     /\ ((Z_to_int (fl_c_int_k M k))%:~R : rat) = fl_c_rat A k)
    /\ ((0 < k)%N ->
         Z.rem (mtrace (mmul M (fl_M_int_k M k))) (Z.of_nat k) = Z0).
Proof.
  move=> A Hdim Hrows.
  elim => [|k IH] Hle.
  - split; [split |].
    + rewrite /fl_M_int_k /= Hdim. rewrite mat_int_to_rat_mzero. reflexivity.
    + rewrite /fl_c_int_k /=. exact Z_to_int_1_rat.
    + move=> Habs. by rewrite ltnn in Habs.
  - have Hle' : (k <= sz)%N := ltnW Hle.
    have [[IHmat IHcoef] IHdiv] := IH Hle'.
    have HMk_dim := fl_M_int_k_dim Hdim Hrows Hle'.
    have HMk_rows := fl_M_int_k_rows Hdim Hrows Hle'.
    have HMk1_dim := fl_M_int_k_dim Hdim Hrows Hle.
    have HMk1_rows := fl_M_int_k_rows Hdim Hrows Hle.
    have Hmat :
      mat_int_to_rat (fl_M_int_k M k.+1) 1 sz = fl_M_rat A k.+1.
    { rewrite (fl_M_int_k_step M k) Hdim.
      rewrite /fl_M_rat /= -/fl_loop_rat /fl_step_rat /=.
      rewrite -/(fl_M_rat A k) -/(fl_c_rat A k).
      rewrite -IHmat -IHcoef.
      rewrite mat_int_to_rat_madd;
        [ | rewrite mat_dim_mmul_eq; exact Hdim
          | rewrite mat_dim_mscale_eq; exact (mat_dim_meye sz)
          | exact (all_rows_len_mmul HMk_dim HMk_rows)
          | apply all_rows_len_mscale; apply all_rows_len_meye ].
      rewrite (mat_int_to_rat_mmul M (fl_M_int_k M k) sz Hdim HMk_dim
                 Hrows HMk_rows).
      rewrite mat_int_to_rat_mscale mat_int_to_rat_meye.
      reflexivity. }
    have Hmmul_dim : mat_dim (mmul M (fl_M_int_k M k.+1)) = sz
      by rewrite mat_dim_mmul_eq; exact Hdim.
    have Htrace_eq : ((Z_to_int (mtrace (mmul M (fl_M_int_k M k.+1))))%:~R : rat)
                     = mxtrace (A *m fl_M_rat A k.+1)%R.
    { rewrite (mtrace_int_to_rat _ sz Hmmul_dim).
      rewrite (mat_int_to_rat_mmul M (fl_M_int_k M k.+1) sz Hdim HMk1_dim
                 Hrows HMk1_rows).
      by rewrite Hmat. }
    have Hdiv : Z.rem (mtrace (mmul M (fl_M_int_k M k.+1)))
                      (Z.of_nat k.+1) = Z0.
    { destruct sz as [|n].
      { exfalso. move: Hle. by rewrite leqn0 => /eqP. }
      have Hkle : (k.+1 <= n.+1)%N := Hle.
      have [z Hz] := @fl_c_rat_is_int n.+1 M k.+1 Hkle.
      have Hfl2 : (k.+1%:R * fl_c_rat A k.+1)%R
                  = (- mxtrace (A *m fl_M_rat A k.+1))%R.
      { rewrite /fl_c_rat /= -/fl_loop_rat /fl_step_rat /=.
        rewrite -/(fl_M_rat A k) -/(fl_c_rat A k).
        rewrite mulrC -mulrA mulVf; last first.
        { apply/eqP => Habs.
          have := @Num.Theory.ltr0Sn _ k.
          move=> /(_ rat). rewrite Habs. by move=> []. }
        by rewrite mulr1. }
      have Htrace_rat :
        mxtrace (A *m fl_M_rat A k.+1)%R = (- (k.+1%:R * z%:~R) : rat)%R.
      { have -> : mxtrace (A *m fl_M_rat A k.+1)%R
                  = (- (k.+1%:R * fl_c_rat A k.+1))%R by lra.
        by rewrite Hz. }
      have Htrace_int :
        ((Z_to_int (mtrace (mmul M (fl_M_int_k M k.+1))))%:~R : rat)
        = (- (k.+1%:R * z%:~R) : rat)%R
        by rewrite Htrace_eq Htrace_rat.
      exact (Z_rem_of_intr_eq (ltn0Sn k) Htrace_int). }
    split; [split |]; first exact Hmat.
    + rewrite (fl_c_int_k_step M k).
      have Hkp : BinInt.Z.of_nat k.+1 <> Z0
        by destruct k; lia.
      have Hdiv_opp :
        Z.rem (BinInt.Z.opp (mtrace (mmul M (fl_M_int_k M k.+1))))
              (BinInt.Z.of_nat k.+1) = Z0
        by rewrite Z.rem_opp_l // Hdiv.
      rewrite (@Z_div_exact_rat _ _ Hkp Hdiv_opp).
      rewrite Z_to_int_opp rmorphN /=.
      rewrite SuccNat2Pos.id_succ -pmulrn.
      congr (_ / _)%R. congr (- _)%R.
      rewrite (mtrace_int_to_rat (mmul M (fl_M_int_k M k.+1)) sz Hmmul_dim).
      rewrite (mat_int_to_rat_mmul M (fl_M_int_k M k.+1) sz Hdim HMk1_dim
                 Hrows HMk1_rows).
      rewrite Hmat.
      rewrite /fl_c_rat /= -/fl_loop_rat /fl_step_rat /=.
      rewrite -/(fl_M_rat A k) -/(fl_c_rat A k).
      reflexivity.
    + intros _. exact Hdiv.
Qed.

Lemma fl_invariant_L2 (M : mat) (sz : nat) (k : nat) :
  let A := mat_int_to_rat M 1 sz in
  mat_dim M = sz ->
  all_rows_len sz M ->
  (k <= sz)%N ->
  mat_int_to_rat (fl_M_int_k M k) 1 sz
    = fl_M_rat A k
  /\
  ((Z_to_int (fl_c_int_k M k))%:~R : rat)
    = fl_c_rat A k.
Proof.
  move=> A Hdim Hrows Hle.
  exact (fl_combined Hdim Hrows Hle).1.
Qed.

Lemma fl_divisibility_L2 (M : mat) (sz : nat) (k : nat) :
  mat_dim M = sz ->
  all_rows_len sz M ->
  (1 <= k)%N -> (k <= sz)%N ->
  Z.rem (mtrace (mmul M (fl_M_int_k M k))) (Z.of_nat k) = Z0.
Proof.
  move=> Hdim Hrows Hk1 Hle.
  exact ((fl_combined Hdim Hrows Hle).2 Hk1).
Qed.

Lemma fl_loop_eq_fl_state (A : mat) (steps j : nat) (acc : list Z) :
  fl_loop steps (Z.of_nat (S j)) A (meye (mat_dim A))
          (fl_M_int_k A j) (fl_c_int_k A j) acc
  = rev (map (fl_c_int_k A) (iota (S j) steps)) ++ acc.
Proof.
  revert j acc. induction steps as [|s IH] => j acc.
  - simpl. reflexivity.
  - simpl fl_loop.
    rewrite -(fl_M_int_k_step A j).
    rewrite -(fl_c_int_k_step A j).
    replace (Z.pos (PosDef.Pos.of_succ_nat j + 1)) with (Z.of_nat j.+2) by lia.
    rewrite /= rev_cons -cats1 -catA /=.
    exact (IH j.+1 (fl_c_int_k A j.+1 :: acc)).
Qed.

(* ------------------------------------------------------------------
   L2 (PLAN_S1.md section 3) — the load-bearing correctness lemma.

   `char_poly_int M` computes `det(lambda*I - M)` for an integer matrix M.
   `mat_int_to_rat M 1 n` lifts M to `'M[rat]_n` with denominator 1
   (i.e., each entry is just `Z_to_int M[i][j] : rat`).

   With D = 1, the two sides agree directly:
     pol_to_polyrat (char_poly_int M) = char_poly (mat_int_to_rat M 1 n)
   ------------------------------------------------------------------ *)
Lemma char_poly_int_correct
  (M : mat) (n : nat)
  (sq : mat_dim M = n)
  (wf : forall i, (i < List.length M)%coq_nat ->
          List.length (List.nth i M nil) = n) :
  pol_to_polyrat (char_poly_int M) = char_poly (mat_int_to_rat M 1 n).
Proof.
  rewrite <- (fl_loop_rat_is_char_poly_L2 (mat_int_to_rat M 1 n)).
  rewrite /char_poly_int sq.
  have Hwf : all_rows_len n M by exact wf.
  have Hfl_eq : fl_loop n Z.one M (meye n) (mzero n) Z.one [::]
            = rev (map (fl_c_int_k M) (iota 1 n)).
  { have -> : mzero n = fl_M_int_k M 0 by rewrite fl_M_int_k_base sq.
    have -> : meye n = meye (mat_dim M) by rewrite sq.
    replace Z.one with (fl_c_int_k M 0) by (rewrite fl_c_int_k_base; reflexivity).
    replace (fl_c_int_k M 0) with (Z.of_nat 1) at 1 by (rewrite fl_c_int_k_base; reflexivity).
    by rewrite (fl_loop_eq_fl_state M n 0 []) /= cats0. }
  rewrite Hfl_eq /pol_to_polyrat.
  congr (Poly _).
  rewrite List.map_app /= Z_to_int_1_rat -map_rev -cats1.
  congr (_ ++ _).
  have Heq_lists : forall ks : seq nat,
    (forall k, k \in ks -> (k <= n)%N) ->
    ListDef.map (fun z : Z => (Z_to_int z)%:~R%R)
      [seq fl_c_int_k M i | i <- ks]
    = [seq fl_c_rat (mat_int_to_rat M 1 n) i | i <- ks].
  { induction ks as [|k ks' IHks'] => Hbnd; first reflexivity.
    simpl. f_equal.
    - exact (fl_invariant_L2 sq Hwf (Hbnd k (mem_head k ks'))).2.
    - apply IHks' => j Hj. apply Hbnd. by rewrite in_cons Hj orbT. }
  apply Heq_lists.
  intros k Hk. rewrite mem_rev mem_iota in Hk.
  move/andP : Hk => [_ Hlt].
  rewrite addnC addn1 ltnS in Hlt. exact Hlt.
Qed.

(* ==================================================================
   Sanity tests — must reduce under vm_compute.
   ================================================================== *)

(* 2x2: [[1;2];[3;4]]
     lambda^2 - 5 lambda - 2 = (1*4 - 2*3) - 5 lambda + lambda^2
   Low-to-high: [-2; -5; 1]. *)
Example char_poly_2x2_test :
  char_poly_int [[1; 2]; [3; 4]] = [-2; -5; 1].
Proof. vm_compute. reflexivity. Qed.

(* 3x3: I_3
     (lambda - 1)^3 = lambda^3 - 3 lambda^2 + 3 lambda - 1.
   Low-to-high: [-1; 3; -3; 1]. *)
Example char_poly_eye_3_test :
  char_poly_int (meye 3) = [-1; 3; -3; 1].
Proof. vm_compute. reflexivity. Qed.

(* 3x3 diagonal: diag(2,3,5)
     (lambda - 2)(lambda - 3)(lambda - 5)
     = lambda^3 - 10 lambda^2 + 31 lambda - 30.
   Low-to-high: [-30; 31; -10; 1]. *)
Example char_poly_3x3_test :
  char_poly_int [[2; 0; 0]; [0; 3; 0]; [0; 0; 5]] = [-30; 31; -10; 1].
Proof. vm_compute. reflexivity. Qed.

(* ==================================================================
   Performance test: 10x10 identity.

   (lambda - 1)^10 has coefficients (low-to-high) given by the
   binomial coefficients with alternating signs:
     (-1)^{10-k} * C(10, k), for k = 0, 1, ..., 10.

     k=0:  +C(10,0)  =    1  (sign (-1)^10)    ... wait, the constant
                                                   term of (x-1)^10 is (-1)^10 = 1.
   Let us expand (lambda - 1)^10 directly:
     sum_{k=0}^{10} C(10,k) lambda^k (-1)^{10-k}.
   k = 0 : (-1)^10 *   1 =    1
   k = 1 : (-1)^9  *  10 =  -10
   k = 2 : (-1)^8  *  45 =   45
   k = 3 : (-1)^7  * 120 = -120
   k = 4 : (-1)^6  * 210 =  210
   k = 5 : (-1)^5  * 252 = -252
   k = 6 : (-1)^4  * 210 =  210
   k = 7 : (-1)^3  * 120 = -120
   k = 8 : (-1)^2  *  45 =   45
   k = 9 : (-1)^1  *  10 =  -10
   k = 10: (-1)^0  *   1 =    1
   Low-to-high coefficient list therefore is
     [1; -10; 45; -120; 210; -252; 210; -120; 45; -10; 1]. *)
Example char_poly_eye_10_perf :
  char_poly_int (meye 10)
  = [1; -10; 45; -120; 210; -252; 210; -120; 45; -10; 1].
Proof. vm_compute. reflexivity. Qed.
