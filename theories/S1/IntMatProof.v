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
     - det_int_correct_zero          (0 x 0 bridge, Qed)
     - det_mat_int_to_rat_nil        (empty-list trivia, Qed)

   Partial / Admitted:
     - det_int_one_dim               (1 x 1 base case, Admitted stub)
     - det_int_laplace_eq_det_int    (Bareiss = Laplace, Admitted)
     - det_int_laplace_correct       (Laplace = MathComp \det, Admitted)
     - det_int_correct               (main bridge, Admitted, derived
                                      from the two lemmas above)

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
      - Step n = k.+1 with k >= 1: rewrite the LHS by Laplace on the
        first row of the list representation; rewrite the RHS by
        [expand_det_row _ ord0]; pair up summands via a minor-lifting
        lemma
           mat_int_to_rat (minor_mat j M) 1 k
              = row' ord0 (col' j_ord (mat_int_to_rat M 1 n))
        and then apply the induction hypothesis under the bigop. *)
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
  (* The plan:
       (\det (mat_int_to_rat M 1 n) = (Z_to_int (det_int M))%:~R)
     is [det_int_correct] above, symmetrised.  An integer m <> 0 maps
     to a nonzero rational under [m%:~R], so the determinant on the
     rat side is nonzero, and this is exactly membership in [unitmx]
     for a matrix over a field.

     The plumbing step requires:
       - Z_to_int_nz   : z <> 0 -> Z_to_int z <> 0
       - intr_eq0      : (m%:~R == 0) = (m == 0)  (from MathComp)
       - unitmxE       : (A \in unitmx) = (\det A != 0)  (field case)

     Deferred. *)
Admitted.

(* ===================================================================
   Print-Assumptions hygiene note.

   This file is a LEAF in the dependency DAG: it imports IntMat and
   CharPoly but is not imported by Cert.v. Therefore the assumption
   set of `Cert.maynard_eigenvalue_S1` is unaffected by anything
   Admitted here.  When a later sprint closes the Admitted lemmas
   above, Cert.v can then import IntMatProof and use
   [mat_int_to_rat_unitmx] directly to discharge [A_rat_unitmx].
   =================================================================== *)
