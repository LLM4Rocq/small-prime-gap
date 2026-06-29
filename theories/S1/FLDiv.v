(**md
# FLDiv

Pure-`Z` helpers for the Faddeev-LeVerrier CRT certificate.

This file collects the *integer-only* (no `Uint63`) infrastructure that the
CRT-over-`Z` characteristic-polynomial certificate needs:

| name                       | meaning                              |
|----------------------------|--------------------------------------|
| `square_mat`               | `n`x`n` integer matrix predicate     |
| `square_mat_mmul`          | `square_mat` preserved under `mmul`  |
| `square_mat_mscale`        | `square_mat` preserved under `mscale`|
| `square_mat_madd`          | `square_mat` preserved under `madd`  |
| `fl_all_divisible`         | step-by-step FL divisibility         |
| `fl_all_divisible_from_L2` | `fl_all_divisible` from `..._L2`     |

These are relocated, verbatim and `Uint63`-free, from the pencil branch's
`CRTBridge.v`.  Only stdlib `Z` arithmetic is used; no
`PrimInt63` / `native_compute` / `Axiom` / `Parameter` appears here.
*)

From Stdlib Require Import ZArith List Lia.
From PrimeGapS1 Require Import IntMat CharPoly.
Import ListNotations.
Local Open Scope Z_scope.

(* ================================================================== *)
(* Section 1: Structural length lemmas                                 *)
(* ================================================================== *)

Local Lemma heads_length (M : list (list Z)) :
  List.length (heads M) = List.length M.
Proof.
  induction M as [|row rest IH]; [reflexivity|].
  simpl. destruct row; simpl; f_equal; exact IH.
Qed.

Local Lemma tails_length (M : list (list Z)) :
  List.length (tails M) = List.length M.
Proof.
  induction M as [|row rest IH]; [reflexivity|].
  simpl. destruct row; simpl; f_equal; exact IH.
Qed.

Local Lemma tails_row_len (M : list (list Z)) (j : nat) :
  (j < List.length M)%nat ->
  List.length (List.nth j (tails M) []) =
  (List.length (List.nth j M []) - 1)%nat.
Proof.
  revert j. induction M as [|row rest IH]; intros j Hj.
  - simpl in Hj. lia.
  - destruct j.
    + simpl. destruct row; simpl; lia.
    + simpl. destruct row; simpl; simpl in Hj; apply IH; lia.
Qed.

Local Lemma mtrans_fuel_length (fuel : nat) (M : list (list Z)) :
  M <> nil ->
  (forall j, (j < List.length M)%nat ->
    (fuel <= List.length (List.nth j M []))%nat) ->
  List.length (mtrans_fuel fuel M) = fuel.
Proof.
  revert M. induction fuel as [|f IH]; intros M Hne Hwf.
  - reflexivity.
  - simpl. destruct M as [|row rest]; [contradiction|].
    assert (Hrow : (S f <= List.length row)%nat)
      by (specialize (Hwf 0%nat); simpl in Hwf; apply Hwf; simpl; lia).
    destruct row as [|x xs]; [simpl in Hrow; lia|].
    simpl. f_equal. apply IH.
    + simpl. discriminate.
    + intros j Hj. simpl in Hj. rewrite tails_length in Hj.
      destruct j; simpl; [simpl in Hrow; lia|].
      rewrite tails_row_len; [|lia].
      specialize (Hwf (S j) Hj). simpl in Hwf. lia.
Qed.

Local Lemma mtrans_length_sq (M : list (list Z)) (n : nat) :
  (0 < n)%nat -> mat_dim M = n ->
  (forall j, (j < n)%nat -> List.length (List.nth j M []) = n) ->
  List.length (mtrans M) = n.
Proof.
  intros Hn Hdim Hwf. unfold mtrans.
  destruct M as [|row rest]; [simpl in Hdim; lia|].
  simpl. assert (Hrow : List.length row = n).
  { apply (Hwf 0%nat). unfold mat_dim in Hdim. simpl in Hdim. lia. }
  rewrite <- Hrow. apply mtrans_fuel_length.
  - discriminate.
  - intros j Hj. unfold mat_dim in Hdim. simpl in Hdim.
    destruct j; simpl; [lia|].
    simpl in Hj. specialize (Hwf (S j)). simpl in Hwf.
    rewrite Hwf; [lia | lia].
Qed.

Local Lemma vscale_length (c : Z) (xs : list Z) :
  List.length (vscale c xs) = List.length xs.
Proof. unfold vscale. apply List.length_map. Qed.

Local Lemma vadd_length (xs ys : list Z) :
  List.length xs = List.length ys ->
  List.length (vadd xs ys) = List.length xs.
Proof.
  revert ys. induction xs as [|x xs' IH]; intros [|y ys'] Hlen;
    simpl in *; try lia.
  f_equal. apply IH. lia.
Qed.

Local Lemma mmul_length (A B : list (list Z)) :
  List.length (mmul A B) = List.length A.
Proof. unfold mmul. rewrite List.length_map. reflexivity. Qed.

Local Lemma mscale_length (c : Z) (A : list (list Z)) :
  List.length (IntMat.mscale c A) = List.length A.
Proof. unfold IntMat.mscale. rewrite List.length_map. reflexivity. Qed.

Local Lemma madd_length (A B : list (list Z)) :
  List.length A = List.length B ->
  List.length (madd A B) = List.length A.
Proof.
  revert B. induction A as [|ra A' IH]; intros [|rb B'] Hlen;
    simpl in *; try lia.
  f_equal. apply IH. lia.
Qed.

(* ================================================================== *)
(* Section 2: square_mat and its preservation                          *)
(* ================================================================== *)

Definition square_mat (n : nat) (M : list (list Z)) : Prop :=
  mat_dim M = n /\
  forall i, (i < n)%nat -> List.length (List.nth i M []) = n.

Local Lemma mmul_nth_length (A B : list (list Z)) (n : nat) (i : nat) :
  (0 < n)%nat -> square_mat n A -> square_mat n B ->
  (i < n)%nat ->
  List.length (List.nth i (mmul A B) []) = n.
Proof.
  intros Hn [HdA HwA] [HdB HwB] Hi. unfold mmul.
  set (f := fun row => map (fun col => dot_int row col) (mtrans B)).
  assert (Heq : nth i (map f A) [] = f (nth i A [])).
  { transitivity (nth i (map f A) (f [])).
    - apply List.nth_indep. rewrite List.length_map. unfold mat_dim in HdA. lia.
    - apply List.map_nth. }
  rewrite Heq. unfold f. rewrite List.length_map.
  apply mtrans_length_sq; [exact Hn | exact HdB | exact HwB].
Qed.

Local Lemma mscale_nth_length (c : Z) (A : list (list Z)) (n : nat) (i : nat) :
  square_mat n A -> (i < n)%nat ->
  List.length (List.nth i (IntMat.mscale c A) []) = n.
Proof.
  intros [Hd Hw] Hi. unfold IntMat.mscale.
  change (@nil Z) with (vscale c (@nil Z)).
  rewrite List.map_nth. rewrite vscale_length. apply Hw. exact Hi.
Qed.

Local Lemma madd_nth_length (A B : list (list Z)) (n : nat) (i : nat) :
  List.length A = List.length B ->
  (forall j, (j < List.length A)%nat -> List.length (List.nth j A []) = n) ->
  (forall j, (j < List.length B)%nat -> List.length (List.nth j B []) = n) ->
  (i < List.length A)%nat ->
  List.length (List.nth i (madd A B) []) = n.
Proof.
  revert B i. induction A as [|ra A' IH]; intros [|rb B'] i Hlen HwA HwB Hi;
    simpl in *; try lia.
  destruct i; simpl.
  - rewrite vadd_length; [apply (HwA 0%nat); lia|].
    rewrite (HwA 0%nat); [|lia]. rewrite (HwB 0%nat); [|lia]. reflexivity.
  - apply IH with (B := B'); try lia.
    + intros j Hj. apply (HwA (S j)). lia.
    + intros j Hj. apply (HwB (S j)). lia.
Qed.

Lemma square_mat_mmul (n : nat) (A B : list (list Z)) :
  (0 < n)%nat -> square_mat n A -> square_mat n B ->
  square_mat n (mmul A B).
Proof.
  intros Hn HsA HsB. split.
  - unfold mat_dim. rewrite mmul_length. destruct HsA; exact H.
  - intros i Hi. exact (mmul_nth_length A B n i Hn HsA HsB Hi).
Qed.

Lemma square_mat_mscale (n : nat) (c : Z) (A : list (list Z)) :
  square_mat n A -> square_mat n (IntMat.mscale c A).
Proof.
  intros Hs. split.
  - unfold mat_dim. rewrite mscale_length. destruct Hs; exact H.
  - intros i Hi. exact (mscale_nth_length c A n i Hs Hi).
Qed.

Lemma square_mat_madd (n : nat) (A B : list (list Z)) :
  square_mat n A -> square_mat n B ->
  square_mat n (madd A B).
Proof.
  intros [HdA HwA] [HdB HwB]. split.
  - unfold mat_dim.
    rewrite madd_length; [exact HdA | unfold mat_dim in *; lia].
  - intros i Hi.
    apply madd_nth_length;
      [unfold mat_dim in *; lia | | | unfold mat_dim in HdA; lia].
    + intros j Hj. apply HwA. unfold mat_dim in HdA; lia.
    + intros j Hj. apply HwB. unfold mat_dim in HdB; lia.
Qed.

(* ================================================================== *)
(* Section 3: FL step-by-step divisibility predicate                   *)
(* ================================================================== *)

(* FL divisibility at every step *)
Fixpoint fl_all_divisible (steps : nat) (k : Z) (A I_n M_prev : list (list Z))
    (c_prev : Z) : Prop :=
  match steps with
  | O => True
  | S s =>
    let M_k := madd (mmul A M_prev) (IntMat.mscale c_prev I_n) in
    let tr := mtrace (mmul A M_k) in
    (k | tr)%Z /\
    fl_all_divisible s (k + 1) A I_n M_k (Z.div (Z.opp tr) k)
  end.

(* ================================================================== *)
(* Section 4: fl_all_divisible from fl_divisibility_L2                  *)
(*                                                                     *)
(* Bridge between the step-by-step fl_all_divisible above and          *)
(* CharPoly's fl_divisibility_L2 (which proves divisibility at any     *)
(* step index using Newton's identities).                              *)
(* ================================================================== *)

(* The FL loop intermediate states match fl_state from CharPoly.v.
   fl_all_divisible tracks: at step j, (j | trace(A * M_j)).
   fl_divisibility_L2 proves: for any k <= n, k | trace(M * fl_M_int_k(M,k)).
   The connection: M_j in fl_all_divisible = fl_M_int_k(A, j).

   This bridge requires showing by induction that fl_all_divisible's
   M_prev/c_prev match fl_M_int_k/fl_c_int_k at each step.
   The proof uses fl_state's definition (which mirrors fl_all_divisible). *)

Lemma fl_all_divisible_from_L2 (M : list (list Z)) (n : nat) :
  mat_dim M = n ->
  (forall i, (i < List.length M)%nat -> List.length (List.nth i M []) = n) ->
  fl_all_divisible n Z.one M (meye n) (mzero n) Z.one.
Proof.
  intros Hdim Hwf.
  (* The FL loop starts with M_prev = mzero n, c_prev = 1, k = 1.
     At each step j (1-indexed): M_j = madd(mmul M M_{j-1})(mscale c_{j-1} I),
     and we need j | trace(mmul M M_j).
     This matches fl_state j M = (fl_M_int_k M j, fl_c_int_k M j),
     and fl_divisibility_L2 gives Z.rem(trace(mmul M (fl_M_int_k M j)))(j) = 0.
     The bridge is by induction showing the states agree. *)
  cut (forall steps j, (j + steps <= n)%nat ->
    fl_all_divisible steps (Z.of_nat (S j)) M (meye (mat_dim M))
      (fst (fl_state j M)) (snd (fl_state j M))).
  { intros H. rewrite <- Hdim in *.
    exact (H (mat_dim M) 0%nat (Nat.le_refl _)). }
  induction steps as [|s IH]; intros j Hj.
  - exact I.
  - simpl. split.
    + destruct (fl_state j M) as [Mj cj] eqn:HFS.
      simpl fst. simpl snd.
      (* Now create Hdiv with the destructed form *)
      pose proof (@fl_divisibility_L2 M n (S j) Hdim Hwf) as Hdiv.
      assert (H1 : is_true (ssrnat.leq 1 (S j))) by reflexivity.
      assert (H2 : is_true (ssrnat.leq (S j) n))
        by (unfold is_true, ssrnat.leq; apply Nat.eqb_eq;
            unfold ssrnat.subn; lia).
      specialize (Hdiv H1 H2).
      unfold fl_M_int_k in Hdiv. simpl fl_state in Hdiv.
      rewrite HFS in Hdiv. simpl fst in Hdiv.
      apply Z.rem_divide in Hdiv; [exact Hdiv|lia].
    + replace (Z.of_nat (S j) + 1)%Z with (Z.of_nat (S (S j))) by lia.
      specialize (IH (S j) ltac:(lia)).
      destruct (fl_state j M) as [Mj cj] eqn:HFS.
      simpl fst in *. simpl snd in *. rewrite HFS in IH. simpl in IH.
      replace (Z.pos (Pos.of_succ_nat j + 1)) with
        (Z.pos (Pos.succ (Pos.of_succ_nat j))) by lia.
      exact IH.
Qed.

(* ================================================================== *)
(* Axiom audit                                                         *)
(* ================================================================== *)
Print Assumptions fl_all_divisible_from_L2.
Print Assumptions square_mat_mmul.
Print Assumptions square_mat_mscale.
Print Assumptions square_mat_madd.
