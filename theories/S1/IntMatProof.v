(* ===================================================================
   IntMatProof.v — bridging our hand-rolled `det_int` (from IntMat.v)
   to MathComp's `\det : 'M[rat]_n -> rat` via the lift `mat_int_to_rat`
   from CharPoly.v.

   The goal: prove

     Lemma det_int_correct (M : mat) (n : nat) (sq : mat_dim M = n) :
       ((Z_to_int (det_int M))%:~R : rat) = (\det (mat_int_to_rat M 1 n))%R.

   This is the analogue of `char_poly_int_correct` for the bare
   determinant, and is the missing piece needed to discharge
   `A_rat_unitmx` in Cert.v by an integer-determinant vm_compute
   check on M1_int.

   =====================================================================
   Status (scaffolding sprint)
   =====================================================================

   Closed:
     - det_int_zero_dim              (0 x 0 base case, Qed)
     - det_int_laplace_zero_dim      (0 x 0 Laplace case, Qed)
     - det_int_correct_zero          (0 x 0 bridge, Qed)
     - det_int_one                   (1 x 1 Bareiss case, Qed)
     - det_int_laplace_one           (1 x 1 Laplace case, Qed)
     - Z_to_int_{add,sub,mul,opp,...}_loc  (local homomorphism
                                      rewrites, Qed)
     - det_int_laplace_two           (concrete 2x2 formula a*d - b*c,
                                      Qed)
     - det_int_laplace_correct_two_shape   (2 x 2 bridge on the
                                      concrete shape [[a;b];[c;d]],
                                      Qed — this is the main new
                                      result of the scaffolding sprint)

   Closed (Wave 10 — minor-commutes-with-lift sprint):
     - nth_Z_drop_nth                (drop_nth/nth_Z bump shift, Qed)
     - map_drop_nth_nth              (map (drop_nth j) commutes with
                                      nth, Qed)
     - mat_get_minor                 (list-level minor projection, Qed)
     - mat_int_to_rat_minor          (the main minor-commutes-with-lift
                                      lemma, Target A, Qed)
     - mat_dim_minor_mat             (dimension of a minor, Qed)
     - mat_int_to_rat_get            (pointwise read of the lift, Qed)
     - det_int_laplace_correct_step  (Target B, the inductive step
                                      assuming [det_int_laplace_expand]
                                      and the IH, Qed)
     - det_int_laplace_correct       (Target C, full induction on n,
                                      now Qed; depends only on
                                      [det_int_laplace_expand] which is
                                      Admitted)
     - det_int_correct               (main bridge, now Qed; depends on
                                      [det_int_laplace_eq_det_int] and
                                      [det_int_laplace_expand])
     - mat_int_to_rat_unitmx         (downstream corollary, now Qed)

   Partial / Admitted:
     - det_int_laplace_eq_det_int    (Bareiss = Laplace under no-swap
                                      condition + well-formedness,
                                      Admitted; the original
                                      unconditioned statement was
                                      UNSOUND due to a fuel bug in
                                      det_int on matrices needing
                                      row-swaps)
     - det_int_laplace_expand        (first-row Laplace expansion of
                                      [det_int_laplace] in MathComp
                                      \sum form, Admitted; the only
                                      remaining piece needed by the
                                      [det_int_laplace_correct] chain)

   New helpers:
     - Z_to_int_inj                  (injectivity of Z_to_int, Qed)
     - bareiss_no_swap               (predicate: all Bareiss pivots
                                      nonzero, Definition)

   =====================================================================
   Proof outline (Approach A — cofactor expansion)
   =====================================================================

   We split the problem through the auxiliary `det_int_laplace` from
   IntMat.v (the Laplace expansion along the first row of our list-of-
   list representation) because it connects *directly* to MathComp's
   `expand_det_row`:

     (\det M)%R = \sum_j M i0 j * cofactor M i0 j               (MC)

   (with `i0 := ord0`).

   Step A.  det_int M = det_int_laplace M   (for square M).
     This is a self-contained statement about our list implementation:
     Bareiss elimination and cofactor expansion agree on the integers.
     We will prove it later by the Bareiss invariant "the running
     sub-matrix has determinant (current pivot) * det(input)". For now
     it is Admitted.

   Step B.  det_int_laplace_correct :
        mat_dim M = n ->
        ((Z_to_int (det_int_laplace M))%:~R : rat)
           = (\det (mat_int_to_rat M 1 n))%R.
     Proof by strong induction on `n`:

       n = 0 : both sides are 1. Closed by `det_mx00` / reduction of
               `det_int_laplace []`.

       n = 1 : both sides equal the single entry. Closed by
               `det_mx11` / reduction of `det_int_laplace [[a]]`.

       n = k.+1, k >= 1 :
         - Rewrite the LHS by unfolding `det_int_laplace` on a cons
           cell, pulling out the first-row Laplace expansion
               \sum_{j < n} (-1)^j * (row 0)[j] * det_int_laplace (minor 0 j M)
         - Rewrite the RHS by `expand_det_row _ ord0`, yielding
               \sum_{j : 'I_n} M i0 j * cofactor M i0 j
         - Unfold `cofactor` on the MathComp side to
               (-1)^{0+j} * \det (row'^j (col'^ord0 M))
         - The key bridging lemma is:
               mat_int_to_rat (minor_mat j M) 1 k
                 = row' ord0 (col' (widen_ord ... j) (mat_int_to_rat M 1 n))
           which says the list-level minor lifts exactly to the
           MathComp-level minor. Modulo index bookkeeping, this is
           pointwise by `mat_getE`.
         - Apply the induction hypothesis on `det_int_laplace (minor_mat j M)`
           to turn it into `\det (minor on the rat side)`, giving the
           same cofactor sum on both sides.
         - Close by `big_sum` extensionality; the `(-1)^j` terms match.

   Step C.  det_int_correct := trans [A] [B].

   The whole chain compiles; only the two Admitted leaves (Step A and
   the cofactor induction in Step B) remain for a later sprint.
   =================================================================== *)

From Stdlib Require Import ZArith List Lia.
Import ListNotations.
Open Scope Z_scope.

From mathcomp Require Import all_boot all_algebra.
Import GRing.Theory.

From PrimeGapS1 Require Import IntPoly IntMat CharPoly.

(* ===================================================================
   0 x 0 trivia — directly closed.
   =================================================================== *)

(** `det_int` on the empty matrix is 1 (reduces by its definition). *)
Lemma det_int_zero_dim : det_int [::] = BinInt.Z.one.
Proof. reflexivity. Qed.

(** `det_int_laplace` on the empty matrix is 1. *)
Lemma det_int_laplace_zero_dim : det_int_laplace [::] = BinInt.Z.one.
Proof. reflexivity. Qed.

(** The 0 x 0 case of the main bridge: both sides are 1. *)
Lemma det_int_correct_zero (M : mat) (sq : mat_dim M = 0%nat) :
  ((Z_to_int (det_int M))%:~R : rat) = (\det (mat_int_to_rat M 1 0))%R.
Proof.
  (* LHS: mat_dim M = 0 forces M = nil, so det_int M = 1,
     Z_to_int 1 = 1, (1)%:~R = 1. *)
  have hM : M = [::].
  { by case: M sq => //=. }
  rewrite hM /=.
  (* RHS: the empty 'M_0 has \det = 1 by det_mx00. *)
  rewrite det_mx00.
  reflexivity.
Qed.

(* ===================================================================
   1 x 1 base case — stub, Admitted.
   =================================================================== *)

(** The 1 x 1 case of our `det_int` (Bareiss) gives the single
    entry.  The proof is by case analysis on whether the pivot `a`
    is zero: in both branches bareiss_loop reduces to `a`. *)
Lemma det_int_one (a : Z) : det_int [[a]] = a.
Proof.
  change (det_int [[a]])
    with (bareiss_loop 1 BinInt.Z.one BinInt.Z.one [[a]]).
  simpl bareiss_loop.
  destruct (BinInt.Z.eqb a BinInt.Z0) eqn:Ha.
  - apply BinInt.Z.eqb_eq in Ha. subst a. reflexivity.
  - simpl hd_Z. apply BinInt.Z.mul_1_l.
Qed.

(** Laplace determinant of a 1 x 1 list-representation matrix: it
    reduces to the single entry via concrete computation. *)
Lemma det_int_laplace_one (a : Z) :
  det_int_laplace [[a]] = a.
Proof.
  (* Unfold the Laplace expansion on the concrete list shape [[a]].
     Only one term survives; the minor is the 0 x 0 matrix, whose
     determinant is 1 by definition, and the sign for j = 0 is +1. *)
  cbv - [BinInt.Z.mul BinInt.Z.add].
  rewrite BinInt.Z.mul_1_l BinInt.Z.mul_1_r BinInt.Z.add_0_r.
  reflexivity.
Qed.

(* ===================================================================
   Main intermediate lemmas.
   =================================================================== *)

(* -------------------------------------------------------------------
   Z_to_int injectivity — needed for the bridge-based proof.
   -------------------------------------------------------------------- *)
Local Lemma Z_to_int_inj : forall a b : Z, Z_to_int a = Z_to_int b -> a = b.
Proof.
  move=> [|pa|pa] [|pb|pb] //=; move=> H.
  - (* 0 = Posz (Pos.to_nat pb) -> contradiction *)
    exfalso. have Hpb := Pos2Nat.is_pos pb.
    have : Posz 0 = Posz (Pos.to_nat pb) by exact H.
    move=> []. lia.
  - (* Posz (Pos.to_nat pa) = 0 -> contradiction *)
    exfalso. have Hpa := Pos2Nat.is_pos pa.
    have : Posz (Pos.to_nat pa) = Posz 0 by exact H.
    move=> []. lia.
  - (* Posz pa = Posz pb *)
    have H2 : Posz (Pos.to_nat pa) = Posz (Pos.to_nat pb) by exact H.
    have H3 : Pos.to_nat pa = Pos.to_nat pb by injection H2.
    by rewrite (Pos2Nat.inj _ _ H3).
  - (* Negz (pa-1) = Negz (pb-1) *)
    injection H => Hkk.
    have Hpa := Pos2Nat.is_pos pa.
    have Hpb := Pos2Nat.is_pos pb.
    have H3 : Pos.to_nat pa = Pos.to_nat pb.
    { move: Hkk; destruct (Pos.to_nat pa) eqn:Epa;
        destruct (Pos.to_nat pb) eqn:Epb;
        [lia|lia|lia|]; rewrite !subn1 /=; lia. }
    by rewrite (Pos2Nat.inj _ _ H3).
Qed.

(* -------------------------------------------------------------------
   Bareiss no-swap predicate: the Bareiss loop never needs to swap
   rows.  This holds when all "effective pivots" (first elements of
   the current first row at each elimination step) are nonzero.
   For SPD matrices, all leading principal minors are positive,
   so all pivots are nonzero and no swapping is ever triggered.
   -------------------------------------------------------------------- *)
Fixpoint bareiss_no_swap (fuel : nat) (prev : Z) (M : mat) : Prop :=
  match fuel with
  | O => True
  | S fuel' =>
    match M with
    | nil => True
    | row :: rest =>
      hd_Z row <> BinInt.Z0 /\
      match rest with
      | nil => True
      | _ => bareiss_no_swap fuel' (hd_Z row)
               (bareiss_step prev row rest)
      end
    end
  end.

(** Step A: Bareiss-based `det_int` agrees with cofactor-based
    `det_int_laplace` on well-formed square matrices that never
    require row-swapping during the Bareiss loop.

    The general Bareiss correctness argument requires the
    fraction-free Gaussian elimination identity:
      prev^|rest| * det(bareiss_step prev row rest)
        = (hd_Z row)^{|rest|-1} * det(row :: rest)
    which is a multi-day proof involving matrix multi-linearity.
    We therefore condition on [bareiss_no_swap] (the Bareiss loop
    never encounters a zero pivot), which holds for SPD matrices
    and specifically for our target M1_int.

    **NOTE**: The original unconditioned statement was UNSOUND:
    `det_int` has a fuel bug where each row-swap consumes a fuel
    unit, so `det_int [[0;1];[1;0]]` incorrectly returns 0 instead
    of -1.  The [bareiss_no_swap] condition avoids this class of
    matrices.  *)
Lemma det_int_laplace_eq_det_int (M : mat) (n : nat) :
  mat_dim M = n ->
  Forall (fun row => length row = n) M ->
  bareiss_no_swap (mat_dim M) BinInt.Z.one M ->
  det_int_laplace M = det_int M.
Proof.
  move=> Hdim HF Hns.
  elim: n M Hdim HF Hns => [|[|n'] IH] M Hdim HF Hns.
  - (* n = 0: M = nil *)
    destruct M as [|]; [reflexivity | discriminate].
  - (* n = 1: M = [[a]] *)
    destruct M as [|row rest]; [discriminate|].
    destruct rest as [|r2 rest']; [|simpl in Hdim; discriminate].
    inversion HF as [|? ? Hrowlen]; subst.
    destruct row as [|a row']; [simpl in Hrowlen; discriminate|].
    destruct row' as [|b row'']; [|simpl in Hrowlen; lia].
    rewrite det_int_laplace_one det_int_one. reflexivity.
  - (* n = n'.+2: general inductive case.
       The proof requires the Bareiss fraction-free elimination identity
         prev^|rest| * det_int_laplace(bareiss_step prev row rest)
           = (hd_Z row)^{|rest|-1} * det_int_laplace(row :: rest)
       applied at prev = 1 for the first step, then inductively with
       the updated prev = hd_Z row for subsequent steps.
       This is a multi-day formalization involving multi-linear algebra
       on the determinant under row operations.  See the module-level
       comment for a full proof sketch. *)
    admit.
Admitted.

(** Step B: the Laplace-expanded integer determinant equals MathComp's
    abstract `\det` after lifting through `mat_int_to_rat`.

    Sketch (induction on n):
      - Base n = 0: `det_int_laplace [::] = 1` and `\det (M : 'M_0) = 1`
        by [det_mx00].  Closed above via [det_int_correct_zero].
      - Base n = 1: the single entry matches on both sides via
        [det_mx11] and our [det_int_laplace_one].
      - Base n = 2: closed below as [det_int_laplace_correct_two] by
        direct cofactor expansion of the abstract 2x2 determinant against
        the concrete 2x2 Laplace formula [a d - b c].
      - Step n = k.+2 (k >= 1): rewrite the LHS by Laplace on the
        first row of the list representation; rewrite the RHS by
        [expand_det_row _ ord0]; pair up summands via a minor-lifting
        lemma
           mat_int_to_rat (minor_mat j M) 1 k
              = row' ord0 (col' j_ord (mat_int_to_rat M 1 n))
        and then apply the induction hypothesis under the bigop. *)

(* -------------------------------------------------------------------
   Local helpers on Z_to_int: we re-prove the tiny additive / sign
   facts we need for the 2x2 case here so we do not depend on
   [CharPolyHelpers] (which another agent is editing concurrently).
   -------------------------------------------------------------------- *)

Local Lemma Z_to_int_0 : Z_to_int 0 = 0%R.
Proof. reflexivity. Qed.

Local Lemma Z_to_int_1 : Z_to_int 1 = 1%R.
Proof. reflexivity. Qed.

Local Lemma Z_to_int_neg_pos_loc (p : positive) :
  Z_to_int (Zneg p) = (- (Posz (Pos.to_nat p)))%R.
Proof.
  unfold Z_to_int.
  have Hp := Pos2Nat.is_pos p.
  destruct (Pos.to_nat p) as [|k] eqn:Ek; [exfalso; lia|].
  have ->: (k.+1 - 1 = k)%N by rewrite subn1.
  by rewrite NegzE.
Qed.

Local Lemma Z_to_int_pos_pos_loc (p : positive) :
  Z_to_int (Zpos p) = Posz (Pos.to_nat p).
Proof. reflexivity. Qed.

Local Lemma Z_to_int_mul_loc (a b : Z) :
  Z_to_int (BinInt.Z.mul a b) = ((Z_to_int a) * (Z_to_int b))%R.
Proof.
  destruct a as [|pa|pa]; destruct b as [|pb|pb];
    try (change (Z_to_int 0) with (0%R : int)); try reflexivity;
    try (rewrite mul0r; reflexivity);
    try (rewrite mulr0; reflexivity).
  - change (BinInt.Z.mul (Zpos pa) (Zpos pb)) with (Zpos (pa * pb)%positive).
    rewrite !Z_to_int_pos_pos_loc. rewrite Pos2Nat.inj_mul. by rewrite PoszM.
  - change (BinInt.Z.mul (Zpos pa) (Zneg pb)) with (Zneg (pa * pb)%positive).
    rewrite !Z_to_int_neg_pos_loc Z_to_int_pos_pos_loc.
    rewrite Pos2Nat.inj_mul. rewrite PoszM. by rewrite mulrN.
  - change (BinInt.Z.mul (Zneg pa) (Zpos pb)) with (Zneg (pa * pb)%positive).
    rewrite !Z_to_int_neg_pos_loc Z_to_int_pos_pos_loc.
    rewrite Pos2Nat.inj_mul. rewrite PoszM. by rewrite mulNr.
  - change (BinInt.Z.mul (Zneg pa) (Zneg pb)) with (Zpos (pa * pb)%positive).
    rewrite !Z_to_int_neg_pos_loc Z_to_int_pos_pos_loc.
    rewrite Pos2Nat.inj_mul. rewrite PoszM. by rewrite mulrNN.
Qed.

Local Lemma Z_pos_sub_int_loc (pa pb : positive) :
  Z_to_int (Z.pos_sub pa pb)
  = (Posz (Pos.to_nat pa) - Posz (Pos.to_nat pb))%R.
Proof.
  have Hd := Z.pos_sub_discr pa pb.
  destruct (Z.pos_sub pa pb) as [|k|k].
  - subst. by rewrite subrr.
  - rewrite Z_to_int_pos_pos_loc. rewrite Hd Pos2Nat.inj_add PoszD.
    by rewrite addrAC subrr add0r.
  - rewrite Z_to_int_neg_pos_loc. rewrite Hd Pos2Nat.inj_add PoszD.
    rewrite opprD.
    have ->: (Posz (Pos.to_nat pa) + (- Posz (Pos.to_nat pa)
              - Posz (Pos.to_nat k)) = - Posz (Pos.to_nat k))%R
      by rewrite addrA addrN add0r.
    reflexivity.
Qed.

Local Lemma Z_to_int_add_loc (a b : Z) :
  Z_to_int (BinInt.Z.add a b) = ((Z_to_int a) + (Z_to_int b))%R.
Proof.
  destruct a as [|pa|pa]; destruct b as [|pb|pb]; simpl BinInt.Z.add.
  - by rewrite addr0.
  - by rewrite add0r.
  - by rewrite add0r.
  - by rewrite addr0.
  - rewrite !Z_to_int_pos_pos_loc. rewrite Pos2Nat.inj_add. by rewrite PoszD.
  - rewrite Z_pos_sub_int_loc Z_to_int_pos_pos_loc Z_to_int_neg_pos_loc.
    by [].
  - by rewrite addr0.
  - rewrite Z_pos_sub_int_loc Z_to_int_neg_pos_loc Z_to_int_pos_pos_loc.
    by rewrite addrC.
  - rewrite !Z_to_int_neg_pos_loc.
    rewrite Pos2Nat.inj_add PoszD. by rewrite opprD.
Qed.

Local Lemma Z_to_int_opp_loc (a : Z) :
  Z_to_int (BinInt.Z.opp a) = (- Z_to_int a)%R.
Proof.
  destruct a as [|pa|pa]; simpl BinInt.Z.opp.
  - by rewrite oppr0.
  - by rewrite Z_to_int_neg_pos_loc Z_to_int_pos_pos_loc.
  - by rewrite Z_to_int_neg_pos_loc Z_to_int_pos_pos_loc opprK.
Qed.

Local Lemma Z_to_int_sub_loc (a b : Z) :
  Z_to_int (BinInt.Z.sub a b) = ((Z_to_int a) - (Z_to_int b))%R.
Proof.
  unfold BinInt.Z.sub. by rewrite Z_to_int_add_loc Z_to_int_opp_loc.
Qed.

(* -------------------------------------------------------------------
   The concrete 2x2 Laplace determinant has the expected closed form.
   -------------------------------------------------------------------- *)
Lemma det_int_laplace_two (a b c d : Z) :
  det_int_laplace [[a; b]; [c; d]]
  = BinInt.Z.sub (BinInt.Z.mul a d) (BinInt.Z.mul b c).
Proof.
  (* Unfold the definition on the concrete 2x2 shape. *)
  cbv - [BinInt.Z.mul BinInt.Z.add BinInt.Z.sub BinInt.Z.opp].
  (* Simplify the fuel-driven expansion by hand. *)
  ring.
Qed.

(* -------------------------------------------------------------------
   The concrete 3x3 Laplace determinant has the expected closed form.
   -------------------------------------------------------------------- *)
Lemma det_int_laplace_three (a b c d e f g h i : Z) :
  det_int_laplace [[a; b; c]; [d; e; f]; [g; h; i]]
  = BinInt.Z.add
      (BinInt.Z.sub
         (BinInt.Z.mul a (BinInt.Z.sub (BinInt.Z.mul e i) (BinInt.Z.mul f h)))
         (BinInt.Z.mul b (BinInt.Z.sub (BinInt.Z.mul d i) (BinInt.Z.mul f g))))
      (BinInt.Z.mul c (BinInt.Z.sub (BinInt.Z.mul d h) (BinInt.Z.mul e g))).
Proof.
  cbv - [BinInt.Z.mul BinInt.Z.add BinInt.Z.sub BinInt.Z.opp].
  ring.
Qed.

(* -------------------------------------------------------------------
   A specialized 2x2 base case of [det_int_laplace_correct], stated
   directly on the concrete shape [[a;b];[c;d]].  The general
   [det_int_laplace_correct] for n = 2 then reduces to this one by
   list-shape case analysis (the badly-shaped cases are impossible
   for well-formed square matrices; this reduction is captured in
   [det_int_laplace_correct_two], Admitted for now).
   -------------------------------------------------------------------- *)
Lemma det_int_laplace_correct_two_shape (a b c d : Z) :
  ((Z_to_int (det_int_laplace [[a; b]; [c; d]]))%:~R : rat)
  = (\det (mat_int_to_rat [[a; b]; [c; d]] 1 2))%R.
Proof.
  (* LHS: closed-form the Laplace integer determinant. *)
  rewrite det_int_laplace_two.
  rewrite Z_to_int_sub_loc !Z_to_int_mul_loc.
  (* Now pull the int-to-rat injection through the arithmetic. *)
  rewrite intrB !intrM.
  (* RHS: expand the abstract determinant along row 0. *)
  rewrite (expand_det_row _ ord0).
  (* The sum has 2 terms. *)
  rewrite big_ord_recl big_ord_recl big_ord0 addr0.
  (* Each cofactor involves a 1x1 minor, whose \det is the single
     entry via det_mx11. *)
  rewrite /cofactor !det_mx11 /mat_int_to_rat !mxE.
  (* Simplify denominator: Z_to_int 1 = 1, then _/1 = _. *)
  change (Z_to_int 1) with (1%R : int).
  rewrite !divr1.
  (* Reduce the sign exponents [ord0 + ord0 = 0] and
     [ord0 + lift ord0 ord0 = 1] at the nat level.  These are
     definitionally true but refuse to beta-reduce under [^+]
     without a manual [rewrite]. *)
  have E0 : ((@ord0 1 : nat) + (@ord0 1 : nat))%N = 0%nat by [].
  have E1 : ((@ord0 1 : nat) + (lift (@ord0 1) (@ord0 0) : nat))%N = 1%nat by [].
  rewrite E0 E1.
  rewrite expr0 expr1 mul1r mulN1r.
  (* Evaluate the concrete mat_get calls on the list [[a;b];[c;d]]. *)
  rewrite /mat_get /nth_Z /=.
  by rewrite mulrN.
Qed.

(* -------------------------------------------------------------------
   3x3 bridge on the concrete shape [[a;b;c];[d;e;f];[g;h;i]].
   Same technique as the 2x2 case: unfold Laplace via the closed
   form, expand the abstract determinant along row 0 with
   [expand_det_row] three times (the outer 3x3 and each 2x2
   minor), reduce the 1x1 sub-sub-minors via [det_mx11], and
   match arithmetic.
   -------------------------------------------------------------------- *)
Lemma det_int_laplace_correct_three_shape
  (a b c d e f g h i : Z) :
  ((Z_to_int (det_int_laplace [[a; b; c]; [d; e; f]; [g; h; i]]))%:~R : rat)
  = (\det (mat_int_to_rat [[a; b; c]; [d; e; f]; [g; h; i]] 1 3))%R.
Proof.
  (* LHS: closed-form the 3x3 Laplace integer determinant. *)
  rewrite det_int_laplace_three.
  rewrite Z_to_int_add_loc !Z_to_int_sub_loc !Z_to_int_mul_loc
          !Z_to_int_sub_loc !Z_to_int_mul_loc.
  rewrite intrD !intrB !intrM.
  (* RHS: expand the abstract determinant along row 0 (3 terms),
     then each 2x2 cofactor along its row 0 (2 inner terms each),
     then reduce the 1x1 sub-minors via [det_mx11]. *)
  rewrite (expand_det_row _ ord0).
  rewrite big_ord_recl big_ord_recl big_ord_recl big_ord0 addr0.
  rewrite /cofactor.
  rewrite !(expand_det_row _ ord0).
  rewrite !big_ord_recl !big_ord0 !addr0.
  rewrite /cofactor !det_mx11 /mat_int_to_rat !mxE.
  change (Z_to_int 1) with (1%R : int).
  rewrite !divr1.
  (* Evaluate concrete list-level [mat_get] calls, then reduce the
     sign exponents ord0 + (lift^k ord0) at the nat level. *)
  rewrite /mat_get /nth_Z /=.
  rewrite !add0n /bump /=.
  rewrite !expr0 !expr1 (exprS _ 1%N) expr1 mulrNN.
  rewrite !mul1r !mulN1r.
  rewrite !rmorphB !rmorphM /=.
  (* With the arithmetic exposed on both sides, set the nine
     atoms and finish with associativity/distributivity. *)
  set A := ((Z_to_int a)%:~R : rat).
  set B := ((Z_to_int b)%:~R : rat).
  set C := ((Z_to_int c)%:~R : rat).
  set D := ((Z_to_int d)%:~R : rat).
  set E := ((Z_to_int e)%:~R : rat).
  set F := ((Z_to_int f)%:~R : rat).
  set G := ((Z_to_int g)%:~R : rat).
  set H := ((Z_to_int h)%:~R : rat).
  set I := ((Z_to_int i)%:~R : rat).
  rewrite !mulrN !mulrDr.
  by rewrite -!addrA.
Qed.

(* -------------------------------------------------------------------
   Target A: the minor-commutes-with-lift lemma.

   This says that taking a list-level minor (drop row 0, drop column j)
   and then lifting to a rat matrix is the same as lifting first and
   then taking the MathComp-level minor (row' ord0 + col' j_ord).
   It is the key ingredient in the inductive step of
   [det_int_laplace_correct]: once minors on both sides are identified,
   the induction hypothesis applies summand-wise in [expand_det_row].
   -------------------------------------------------------------------- *)

Lemma nth_nil_Z_loc (n : nat) (d : Z) : ListDef.nth n [::] d = d.
Proof. by case: n. Qed.

(** `drop_nth` commutes with `nth_Z` via the `bump` index shift. *)
Lemma nth_Z_drop_nth (row : list Z) (j j' : nat) :
  nth_Z (drop_nth j row) j' = nth_Z row (bump j j').
Proof.
  rewrite /nth_Z /bump.
  elim: row j j' => [|x xs IH] j j'.
  { rewrite (_ : drop_nth j [::] = [::]); last by case: j.
    by rewrite !nth_nil_Z_loc. }
  case: j => [|j] /=. { by rewrite add0n. }
  case: j' => [|j'] /=. by [].
  rewrite IH /=. by rewrite addnS.
Qed.

(** `map (drop_nth j)` commutes with `nth` at default `[::]`. *)
Lemma map_drop_nth_nth (rest : list (list Z)) (j i' : nat) :
  ListDef.nth i' (List.map (drop_nth j) rest) [::]
  = drop_nth j (ListDef.nth i' rest [::]).
Proof.
  elim: rest i' => [|r rs IH] i'.
  - simpl. case: i' => [|i''] /=. case: j => //. case: j => //.
  - case: i' => [|i''] /=; first by []. by rewrite IH.
Qed.

(** List-level `mat_get` of a minor reduces to a `mat_get` of the
    original matrix with indices shifted by 1 (row) and by `bump j`
    (column). *)
Lemma mat_get_minor (M : mat) (j i' j' : nat) :
  M <> [::] ->
  mat_get (minor_mat j M) i' j' = mat_get M i'.+1 (bump j j').
Proof.
  move=> Hne. rewrite /mat_get /minor_mat.
  destruct M as [|row rest]; first by exfalso; apply Hne.
  simpl (ListDef.nth i'.+1 (row :: rest) [::]).
  rewrite map_drop_nth_nth. by rewrite nth_Z_drop_nth.
Qed.

(** **Target A** — the main minor-commutes-with-lift lemma.  Lifting a
    list-level minor to a rat matrix is the same as taking the
    MathComp-level minor (row' ord0 composed with col' at `Ordinal Hj`)
    of the lifted matrix. *)
Lemma mat_int_to_rat_minor (M : mat) (k : nat) (j : nat)
  (Hne : M <> [::]) (Hj : (j < k.+1)%nat) :
  mat_int_to_rat (minor_mat j M) 1 k
  = row' ord0 (col' (Ordinal Hj) (mat_int_to_rat M 1 k.+1)).
Proof.
  apply/matrixP => i j'. rewrite !mxE /=.
  by rewrite mat_get_minor.
Qed.

(** Dimension of a list-level minor: drop one row, drop one column. *)
Lemma mat_dim_minor_mat (M : mat) (j : nat) :
  mat_dim (minor_mat j M) = (mat_dim M).-1.
Proof. rewrite /minor_mat /mat_dim. case: M => //= r rs. by rewrite length_map. Qed.

(** Pointwise read of `mat_int_to_rat` at integer ordinals. *)
Lemma mat_int_to_rat_get (M : mat) (k : nat) (i j : 'I_k) :
  (mat_int_to_rat M 1 k) i j = ((Z_to_int (mat_get M i j))%:~R : rat).
Proof.
  rewrite mxE /=.
  change (Z_to_int 1) with (1%R : int).
  by rewrite divr1.
Qed.

(* -------------------------------------------------------------------
   Helpers for the first-row Laplace expansion lemma.
   -------------------------------------------------------------------- *)

(** `Nat.even` agrees with negated MathComp `odd`. *)
Local Lemma Nat_even_odd (n : nat) : Nat.even n = ~~ (odd n).
Proof.
  have H : forall m, Nat.even m = ~~ odd m
    by fix IH 1; case => [|[|n0]] //=; rewrite !negbK; apply IH.
  exact: H.
Qed.

(** The Z-level sign `(if even j then 1 else -1)`, after lifting to
    rat, equals the MathComp exponent `(-1)^+j`. *)
Local Lemma sign_even_rat (j0 : nat) :
  ((Z_to_int (if Nat.even j0 then BinInt.Z.one
              else BinInt.Z.opp BinInt.Z.one))%:~R : rat)
  = ((-1) ^+ j0)%R.
Proof.
  rewrite Nat_even_odd. case Hodd: (odd j0).
  - simpl negb. rewrite Z_to_int_neg_pos_loc /=.
    rewrite rmorphN /=. rewrite -(signr_odd rat j0) Hodd. by [].
  - simpl negb. rewrite -(signr_odd rat j0) Hodd. by [].
Qed.

(** `drop_nth` reduces the list length by 1 when the index is in
    range. *)
Local Lemma length_drop_nth {A : Type} (j : nat) (xs : list A) :
  (j < length xs)%nat -> length (drop_nth j xs) = (length xs).-1.
Proof.
  elim: xs j => [|x xs' IH] j Hj //.
  case: j Hj => [|j'] Hj //=.
  have Hj' : (j' < length xs')%nat.
  { simpl in Hj. rewrite ltnS in Hj. exact: (leq_trans (ltnSn _) Hj). }
  rewrite IH //. by case: (length xs') Hj'.
Qed.

(** Row-length predicate is preserved by [minor_mat]. *)
Local Lemma Forall_minor_mat (M : mat) (k j : nat) :
  Forall (fun row => length row = k.+1) M ->
  (j < k.+1)%nat ->
  Forall (fun row => length row = k) (minor_mat j M).
Proof.
  move=> HF Hj. rewrite /minor_mat.
  destruct M as [|r rs] => /=; first by constructor.
  inversion HF as [|? ? Hr Hrs]; subst.
  clear r Hr HF.
  induction rs as [|r' rs' IH].
  - simpl. constructor.
  - inversion Hrs as [|? ? Hr' Hrs']; subst.
    simpl. constructor.
    + rewrite length_drop_nth; [rewrite Hr'; by [] | rewrite Hr'; exact Hj].
    + exact (IH Hrs').
Qed.

(** A standalone version of the inner `expand` fixpoint inside
    [det_int_laplace_fuel].  We need this as a named function so that
    [laplace_row_sum_bigop] can be stated and used by [rewrite]. *)
Fixpoint laplace_row_sum (j0 : nat) (r : list BinInt.Z)
    (fuel : nat) (rest : list (list BinInt.Z)) : BinInt.Z :=
  match r with
  | nil => BinInt.Z0
  | x :: r' =>
      let sign := if Nat.even j0 then BinInt.Z.one
                   else BinInt.Z.opp BinInt.Z.one in
      BinInt.Z.add
        (BinInt.Z.mul (BinInt.Z.mul sign x)
           (det_int_laplace_fuel fuel
              (List.map (drop_nth j0) rest)))
        (laplace_row_sum (S j0) r' fuel rest)
  end.

(** The key induction lemma: [laplace_row_sum] equals a MathComp
    big-op over the ordinals `'I_(length r)`. *)
Local Lemma laplace_row_sum_bigop (j0 : nat) (r : list BinInt.Z)
    (fuel : nat) (rest : mat) :
  ((Z_to_int (laplace_row_sum j0 r fuel rest))%:~R : rat) =
  (\sum_(i < length r)
     ((-1) ^+ (j0 + i)
        * ((Z_to_int (ListDef.nth i r BinInt.Z0))%:~R : rat)
        * (Z_to_int (det_int_laplace_fuel fuel
             (List.map (drop_nth (j0 + i)) rest)))%:~R))%R.
Proof.
  elim: r j0 => [|x r' IH] j0.
  - simpl. by rewrite big_ord0.
  - simpl laplace_row_sum. simpl length.
    rewrite Z_to_int_add_loc intrD.
    rewrite big_ord_recl /=.
    rewrite addn0.
    congr (_ + _)%R.
    + rewrite Z_to_int_mul_loc Z_to_int_mul_loc intrM intrM.
      by rewrite sign_even_rat.
    + rewrite IH.
      apply: eq_bigr => i _.
      rewrite /bump /= !add0n.
      by rewrite addnS.
Qed.

(** The anonymous inner `expand` fixpoint inside [det_int_laplace_fuel]
    is propositionally equal to [laplace_row_sum].  The proof uses
    [change] to expose the anonymous fix as a syntactically matchable
    term, then closes by induction on the row list. *)
Local Lemma det_int_laplace_fuel_eq (row : list BinInt.Z)
    (k : nat) (rest : list (list BinInt.Z)) :
  row <> nil ->
  det_int_laplace_fuel k.+1 (row :: rest) =
  laplace_row_sum 0%nat row k rest.
Proof.
  move=> Hne.
  destruct row as [|x0 row']; first by (exfalso; apply Hne).
  have H : forall j (r : list BinInt.Z),
    (fix expand (j0 : nat) (r0 : seq BinInt.Z) {struct r0} : BinInt.Z :=
       match r0 with
       | [::] => BinInt.Z0
       | x :: r' =>
           BinInt.Z.add
             (BinInt.Z.mul
                (BinInt.Z.mul
                   (if Nat.even j0 then BinInt.Z.one
                    else BinInt.Z.opp BinInt.Z.one) x)
                (det_int_laplace_fuel k
                   (ListDef.map (drop_nth j0) rest)))
             (expand j0.+1 r')
       end) j r
    = laplace_row_sum j r k rest.
  { move=> j r. revert j. induction r as [|x r' IH] => j.
    - reflexivity.
    - simpl laplace_row_sum. simpl.
      congr (BinInt.Z.add _ _). exact (IH j.+1). }
  change (det_int_laplace_fuel k.+1 ((x0 :: row') :: rest))
    with ((fix expand (j0 : nat) (r0 : seq BinInt.Z) {struct r0}
             : BinInt.Z :=
             match r0 with
             | [::] => BinInt.Z0
             | x :: r' =>
                 BinInt.Z.add
                   (BinInt.Z.mul
                      (BinInt.Z.mul
                         (if Nat.even j0 then BinInt.Z.one
                          else BinInt.Z.opp BinInt.Z.one) x)
                      (det_int_laplace_fuel k
                         (ListDef.map (drop_nth j0) rest)))
                   (expand j0.+1 r')
             end) 0%nat (x0 :: row')).
  exact (H 0%nat (x0 :: row')).
Qed.

(* -------------------------------------------------------------------
   Target B step lemma — first row Laplace expansion of
   `det_int_laplace`, in MathComp `\sum` form.

   The proof uses [det_int_laplace_fuel_eq] to replace the anonymous
   inner `expand` fixpoint with the named [laplace_row_sum], then
   applies [laplace_row_sum_bigop] to turn it into a MathComp big-op,
   and closes the remaining index bookkeeping.
   -------------------------------------------------------------------- *)
Lemma det_int_laplace_expand (M : mat) (k : nat) :
  mat_dim M = k.+1 ->
  Forall (fun row => length row = k.+1) M ->
  ((Z_to_int (det_int_laplace M))%:~R : rat)
  = (\sum_(j < k.+1)
       ((-1)^+j * (Z_to_int (mat_get M 0 j))%:~R
                * (Z_to_int (det_int_laplace (minor_mat j M)))%:~R) : rat)%R.
Proof.
  move=> Hdim HF.
  destruct M as [|row rest] eqn:HM; first by (simpl in Hdim; discriminate).
  inversion HF as [|? ? Hrowlen HFrest]; subst.
  have Hrest : mat_dim rest = k by injection Hdim.
  destruct row as [|x0 row']; first by (simpl in Hrowlen; discriminate).
  have Hrowlen' : length row' = k by simpl in Hrowlen; injection Hrowlen.
  have Hne : (x0 :: row') <> [::] by discriminate.
  (* Rewrite det_int_laplace to det_int_laplace_fuel *)
  have -> : det_int_laplace ((x0 :: row') :: rest)
          = det_int_laplace_fuel k.+1 ((x0 :: row') :: rest).
  { rewrite /det_int_laplace.
    change (mat_dim ((x0 :: row') :: rest)) with (mat_dim rest).+1.
    by rewrite Hrest. }
  (* Replace det_int_laplace_fuel with laplace_row_sum *)
  rewrite (det_int_laplace_fuel_eq (x0 :: row') k rest Hne).
  (* Apply the bigop lemma *)
  rewrite laplace_row_sum_bigop.
  (* Both sides are now big-ops; reconcile the index ranges and
     simplify bookkeeping. *)
  simpl length. rewrite Hrowlen'.
  apply: eq_bigr => i _.
  rewrite /= add0n.
  congr (_ * _ * _)%R.
  (* Minor-determinant fuel: length (map ...) = length rest = k *)
  rewrite /det_int_laplace /mat_dim.
  by rewrite length_map -/(mat_dim rest) Hrest.
Qed.

(** **Target B step** — the inductive step of [det_int_laplace_correct]:
    given the IH at dimension `n`, lift it to dimension `n.+1`.

    This uses [det_int_laplace_expand] to bring the LHS into a sum
    matching MathComp's [expand_det_row], [mat_int_to_rat_minor] (Target
    A) to identify the minors on both sides, and the IH applied to each
    minor to close the induction. *)
Lemma det_int_laplace_correct_step (n : nat)
  (IH : forall M : mat,
        mat_dim M = n ->
        Forall (fun row => length row = n) M ->
        ((Z_to_int (det_int_laplace M))%:~R : rat) = (\det (mat_int_to_rat M 1 n))%R) :
  forall M : mat,
    mat_dim M = n.+1 ->
    Forall (fun row => length row = n.+1) M ->
    ((Z_to_int (det_int_laplace M))%:~R : rat) = (\det (mat_int_to_rat M 1 n.+1))%R.
Proof.
  move=> M Hdim HF.
  have Hne : M <> [::]. { by case: M Hdim HF. }
  rewrite (det_int_laplace_expand M n Hdim HF).
  rewrite (expand_det_row _ (@ord0 n)).
  apply: eq_bigr => j _.
  rewrite /cofactor.
  rewrite mat_int_to_rat_get.
  have Hj : (nat_of_ord j < n.+1)%nat by apply: ltn_ord.
  have -> : row' (@ord0 n) (col' j (mat_int_to_rat M 1 n.+1))
          = mat_int_to_rat (minor_mat j M) 1 n.
  { by rewrite (mat_int_to_rat_minor M n j Hne Hj); congr row'. }
  rewrite -IH; last first.
  { exact: (Forall_minor_mat M n j HF Hj). }
  { by rewrite mat_dim_minor_mat Hdim. }
  rewrite add0n.
  by rewrite mulrCA mulrA.
Qed.

(* -------------------------------------------------------------------
   The general Step B lemma, proved by induction on n.
   -------------------------------------------------------------------- *)
Lemma det_int_laplace_correct (M : mat) (n : nat) :
  mat_dim M = n ->
  Forall (fun row => length row = n) M ->
  ((Z_to_int (det_int_laplace M))%:~R : rat)
  = (\det (mat_int_to_rat M 1 n))%R.
Proof.
  elim: n M => [|n IH] M Hdim HF.
  - have hM : M = [::] by case: M Hdim HF => //=.
    rewrite hM /= det_mx00. reflexivity.
  - exact: (det_int_laplace_correct_step n IH M Hdim HF).
Qed.

(* ===================================================================
   Main bridge lemma — derived from Steps A and B.
   =================================================================== *)

(** The headline bridge: our computational `det_int` agrees, after
    lifting to rationals, with MathComp's abstract determinant on the
    lifted matrix.  Requires the no-swap condition. *)
Lemma det_int_correct (M : mat) (n : nat) :
  mat_dim M = n ->
  Forall (fun row => length row = n) M ->
  bareiss_no_swap (mat_dim M) BinInt.Z.one M ->
  ((Z_to_int (det_int M))%:~R : rat)
  = (\det (mat_int_to_rat M 1 n))%R.
Proof.
  move=> sq HF Hns.
  rewrite -(det_int_laplace_eq_det_int M n sq HF Hns).
  exact: det_int_laplace_correct.
Qed.

(* ===================================================================
   Downstream corollary: nonzero integer determinant ensures the
   lifted matrix is a unit (invertible).  This is what Cert.v needs
   to discharge the `A_rat_unitmx` admit.
   =================================================================== *)

(** When the computed integer determinant is nonzero, the lifted
    MathComp matrix lies in [unitmx].  The proof reuses
    [det_int_correct] to transport the nonzero-ness from Z to rat.
    Requires the Bareiss no-swap condition. *)
Lemma mat_int_to_rat_unitmx
  (M : mat) (n : nat) (sq : mat_dim M = n)
  (HF : Forall (fun row => length row = n) M)
  (Hns : bareiss_no_swap (mat_dim M) BinInt.Z.one M) :
  det_int M <> BinInt.Z0 ->
  mat_int_to_rat M 1 n \in unitmx.
Proof.
  move=> hnz.
  rewrite unitmxE unitfE.
  rewrite -(det_int_correct M n sq HF Hns).
  apply/eqP => H.
  apply hnz.
  have H2 : (Z_to_int (det_int M))%R = 0%R.
  { apply/eqP. move: H => /eqP. by rewrite intr_eq0. }
  destruct (det_int M) as [|p|p] eqn:Hd; [reflexivity| |].
  - rewrite Z_to_int_pos_pos_loc in H2.
    have Hp := Pos2Nat.is_pos p.
    have H3 : (Pos.to_nat p : int) = 0%R by exact H2.
    move: H3 => /eqP; rewrite -[(0%R : int)]/(Posz 0) eqz_nat => /eqP ?; lia.
  - rewrite Z_to_int_neg_pos_loc in H2.
    have Hp := Pos2Nat.is_pos p.
    have H3 : (Pos.to_nat p : int) = 0%R.
    { apply/eqP; move: H2 => /eqP; by rewrite eqr_oppLR oppr0. }
    move: H3 => /eqP; rewrite -[(0%R : int)]/(Posz 0) eqz_nat => /eqP ?; lia.
Qed.

(* ===================================================================
   Print-Assumptions hygiene note.

   This file is a LEAF in the dependency DAG: it imports IntMat and
   CharPoly but is not imported by Cert.v. Therefore the assumption
   set of `Cert.maynard_eigenvalue_S1` is unaffected by anything
   Admitted here.  When a later sprint closes the Admitted lemmas
   above, Cert.v can then import IntMatProof and use
   [mat_int_to_rat_unitmx] directly to discharge [A_rat_unitmx].
   =================================================================== *)
