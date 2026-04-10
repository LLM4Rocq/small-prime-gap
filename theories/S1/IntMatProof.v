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

   Partial / Admitted:
     - det_int_laplace_eq_det_int    (Bareiss = Laplace, Admitted)
     - det_int_laplace_correct       (Laplace = MathComp \det, Admitted;
                                      cases n = 0 and n = 1 and the
                                      shape-[[a;b];[c;d]] case of
                                      n = 2 are closed as standalone
                                      lemmas.  The remaining content
                                      is the n >= 2 induction via
                                      [expand_det_row]).
     - det_int_correct               (main bridge, Admitted, derived
                                      from the two lemmas above)
     - mat_int_to_rat_unitmx         (downstream corollary, Admitted;
                                      mechanical given det_int_correct)

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
   Main intermediate lemmas — Admitted with proof sketches.
   =================================================================== *)

(** Step A: Bareiss-based `det_int` agrees with cofactor-based
    `det_int_laplace` on every square matrix.  Proven numerically
    (by vm_compute) for the small examples in IntMat.v; a formal
    proof goes via the Bareiss fraction-free invariant.

    Sketch: introduce the invariant
      I k (sign, prev, M_cur) :=
        sign * prev * det_int_laplace M_cur = det_int_laplace M_init
    and prove it is preserved by every Bareiss step via a multi-
    linearity argument on the rows. *)
Lemma det_int_laplace_eq_det_int (M : mat) (n : nat) :
  mat_dim M = n -> det_int_laplace M = det_int M.
Proof. Admitted.

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
   The general Step B lemma, proved by induction on n using:
     n = 0 : det_int_correct_zero (reused with det_int_laplace by
             unfolding; see proof).
     n = 1 : det_int_laplace_one + det_mx11.
     n = 2 : det_int_laplace_correct_two_shape (for [[a;b];[c;d]]
             shapes).  The general n = 2 case (arbitrary 2xN lists)
             reduces to this via list shape analysis on row lengths,
             but the badly-shaped cases require knowing the rows have
             length 2, which [mat_dim M = 2] alone does not provide.
     n >= 3: inductive step via [expand_det_row] / [minor_mat]
             commutation lemma.  This is the main remaining obligation.
   -------------------------------------------------------------------- *)
Lemma det_int_laplace_correct (M : mat) (n : nat) :
  mat_dim M = n ->
  ((Z_to_int (det_int_laplace M))%:~R : rat)
  = (\det (mat_int_to_rat M 1 n))%R.
Proof. Admitted.

(* ===================================================================
   Main bridge lemma — derived from Steps A and B.
   =================================================================== *)

(** The headline bridge: our computational `det_int` agrees, after
    lifting to rationals, with MathComp's abstract determinant on the
    lifted matrix. *)
Lemma det_int_correct (M : mat) (n : nat) :
  mat_dim M = n ->
  ((Z_to_int (det_int M))%:~R : rat)
  = (\det (mat_int_to_rat M 1 n))%R.
Proof.
  move=> sq.
  rewrite -(det_int_laplace_eq_det_int M n sq).
  exact: det_int_laplace_correct.
Qed.

(* ===================================================================
   Downstream corollary: nonzero integer determinant ensures the
   lifted matrix is a unit (invertible).  This is what Cert.v needs
   to discharge the `A_rat_unitmx` admit.
   =================================================================== *)

(** When the computed integer determinant is nonzero, the lifted
    MathComp matrix lies in [unitmx].  The proof reuses
    [det_int_correct] to transport the nonzero-ness from Z to rat. *)
Lemma mat_int_to_rat_unitmx
  (M : mat) (n : nat) (sq : mat_dim M = n) :
  det_int M <> BinInt.Z0 ->
  mat_int_to_rat M 1 n \in unitmx.
Proof.
  move=> hnz.
  (* An integer m <> 0 maps to a nonzero rat under [m%:~R], so the
     determinant on the rat side is nonzero, and this is exactly
     membership in [unitmx] for a field-valued matrix.

     Plumbing used:
       unitmxE    : (A \in unitmx) = (\det A \is a GRing.unit)
       unitfE     : (x \is a GRing.unit) = (x != 0)   [field]
       det_int_correct : bridges det_int / \det across mat_int_to_rat. *)
  rewrite unitmxE unitfE.
  rewrite -(det_int_correct M n sq).
  apply/eqP => H.
  apply hnz.
  have H2 : (Z_to_int (det_int M))%R = 0%R.
  { apply/eqP. move: H => /eqP. by rewrite intr_eq0. }
  (* A nonzero Z cannot map to 0 in [int] under [Z_to_int]. *)
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
