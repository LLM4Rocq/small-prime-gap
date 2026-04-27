(* ==================================================================
   MaynardBridge.v — partial formalization of audit finding M-2.

   Context.  The headline theorem `maynard_eigenvalue_S1` (in
   theories/S1/Cert.v) currently proves only:

     exists lambda : realalg,
       eigenvalue (map_mx ratr A_rat) lambda /\
       (4 < 105 * lambda).

   where A_rat = M1^{-1} . M2 in 'M[rat]_42, lifted to realalg.
   This is *strictly weaker* than Maynard's claim M_{105} > 4
   (arXiv:1311.4600).  Two unformalized math steps lie between:

   (a) Lemma 8.3 (Rayleigh-Ritz):
         sup_F (J_k(F) / I_k(F)) = lambda_max(M1^{-1} . M2),
       valid because M1, M2 are symmetric and M1 is positive
       definite.

   (b) Spectrum reality: M1^{-1} . M2 is similar to the symmetric
       matrix M1^{-1/2} . M2 . M1^{-1/2}, so all its eigenvalues
       are real, and lambda_max >= any real eigenvalue.

   What this file proves.  Algebraic prerequisites: symmetry of
   the Gram matrices on the rat side and on the Z side.  These
   are the easy half of (a)+(b); they are an absolute requirement
   for any future closure of (a), (b), and the final "M_{105} > 4"
   bridge.

     * M1_entry, M2_entry are symmetric in (bi, ci) <-> (bj, cj)
       on the rat side (Maynard's formulas are visibly symmetric).
     * M1_int, M2_int (Z-level list-of-list matrices shipped in
       Witness.v) are symmetric, by a single vm_compute on a 42x42
       boolean grid.
     * The rat-level matrices `mat_int_to_rat M1_int D_M1 42` and
       `mat_int_to_rat M2_int D_M2 42` are symmetric, deduced from
       the Z-level fact via mat_int_to_rat's defining equation.

   What this file does NOT prove (gaps documented for future work).

     * Positive-definiteness of M1 over Q.  The mathematical
       justification is a^T M1 a = integral_0^1 F(t)^2 dt >= 0
       for the basis polynomial F associated with vector a.  This
       is analytic and out of scope for an algebraic-only
       formalization.  An alternative algebraic route — proving
       det(M1) > 0 in Q — is also non-trivial; M1_charpoly_hd_nz
       (in CertL2.v) only gives nonzero, not positive.

     * Real spectrum of M1^{-1} . M2.  The standard argument uses
       a positive-definite square root of M1 and the spectral
       theorem.  Both are missing from MathComp's current matrix
       library; building them is a multi-week project.

     * Lemma 8.3 (M_k = k * lambda_max).  Requires a bridge to
       an integral library to evaluate Maynard's J_k / I_k
       functionals.  Not tractable here.

     * Bridge from "exists real eigenvalue lambda > 4/105" to
       "M_{105} > 4".  Combines the three items above; it is the
       full M-2 audit gap.

   These gaps remain on the paper side of the verification.
   Together they account for the difference between
   `maynard_eigenvalue_S1` (formalized in Cert.v) and Maynard's
   theorem M_{105} > 4 (the paper claim).

   Trust contract.  No `Admitted`, no `Axiom`, no `admit`.  Each
   Qed in this file is a closed proof in the standard MathComp +
   Stdlib + PrimInt63/Uint63 axiom set — the same trust contract
   as the rest of the project.
   ================================================================== *)

From Stdlib Require Import ZArith List.
From mathcomp Require Import all_ssreflect all_algebra.
From PrimeGapS1 Require Import IntMat CharPoly Witness
                                MaynardFactQ MaynardBasis MaynardSpec.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

(* ------------------------------------------------------------------
   Section 1 — rat-level symmetry of M1_entry.

   M1_entry only depends on (bi + bj) and (ci + cj), so symmetry
   follows from commutativity of nat addition.
   ------------------------------------------------------------------ *)

Local Open Scope ring_scope.

Lemma M1_entry_sym (bi ci bj cj : nat) :
  M1_entry bi ci bj cj = M1_entry bj cj bi ci.
Proof.
  rewrite /M1_entry.
  by rewrite (addnC bi bj) (addnC ci cj).
Qed.

(* ------------------------------------------------------------------
   Section 2 — rat-level symmetry of M2_entry.

   M2_entry is a double sum.  Swapping (bi,ci) <-> (bj,cj) renames
   cp1 <-> cp2, after which bp1 <-> bp2, and bsum, csum are
   invariant under that swap.  We just exchange the order of the
   two iterated sums.
   ------------------------------------------------------------------ *)

Lemma M2_entry_sym (bi ci bj cj : nat) :
  M2_entry bi ci bj cj = M2_entry bj cj bi ci.
Proof.
  rewrite /M2_entry.
  rewrite exchange_big /=.
  apply: eq_bigr => cp2 _.
  apply: eq_bigr => cp1 _.
  rewrite (addnC (bi + 2 * ci - 2 * cp1 + 1)%N
                 (bj + 2 * cj - 2 * cp2 + 1)%N).
  rewrite (addnC cp1 cp2).
  rewrite [alpha bi ci cp1 * alpha bj cj cp2]GRing.mulrC.
  by [].
Qed.

(* ------------------------------------------------------------------
   Section 3 — index-level symmetry of M{1,2}_spec_ij.

   Direct consequence of M{1,2}_entry_sym.
   ------------------------------------------------------------------ *)

Lemma M1_spec_ij_sym (i j : nat) :
  M1_spec_ij i j = M1_spec_ij j i.
Proof. by rewrite /M1_spec_ij M1_entry_sym. Qed.

Lemma M2_spec_ij_sym (i j : nat) :
  M2_spec_ij i j = M2_spec_ij j i.
Proof. by rewrite /M2_spec_ij M2_entry_sym. Qed.

Local Close Scope ring_scope.

(* ------------------------------------------------------------------
   Section 4 — Z-level symmetry of M1_int and M2_int (the shipped
   integer matrices in Witness.v).

   We decide the 42x42 boolean grid by vm_compute.  This complements
   `MaynardVerify.all_match_M{1,2}Z_true`: we now know not only that
   the shipped integers match Maynard's closed form, but also that
   they are symmetric as integer matrices.
   ------------------------------------------------------------------ *)

Definition M1_int_sym_check : bool :=
  List.forallb
    (fun i =>
       List.forallb
         (fun j => Z.eqb (mat_get M1_int i j) (mat_get M1_int j i))
         (List.seq 0 42))
    (List.seq 0 42).

Definition M2_int_sym_check : bool :=
  List.forallb
    (fun i =>
       List.forallb
         (fun j => Z.eqb (mat_get M2_int i j) (mat_get M2_int j i))
         (List.seq 0 42))
    (List.seq 0 42).

Lemma M1_int_sym_check_true : M1_int_sym_check = true.
Proof. vm_compute. reflexivity. Qed.

Lemma M2_int_sym_check_true : M2_int_sym_check = true.
Proof. vm_compute. reflexivity. Qed.

(* Pointwise consequence: for all i, j < 42, M1_int[i][j] = M1_int[j][i]. *)
Lemma M1_int_sym_pointwise (i j : nat) :
  (i < 42)%nat -> (j < 42)%nat ->
  mat_get M1_int i j = mat_get M1_int j i.
Proof.
  move=> Hi Hj.
  have Hgrid := M1_int_sym_check_true.
  rewrite /M1_int_sym_check in Hgrid.
  move/forallb_forall in Hgrid.
  have Hi_in : List.In i (List.seq 0 42).
  { apply List.in_seq. split; [apply Nat.le_0_l|].
    by apply/ssrnat.ltP. }
  have Hrow := Hgrid _ Hi_in.
  move/forallb_forall in Hrow.
  have Hj_in : List.In j (List.seq 0 42).
  { apply List.in_seq. split; [apply Nat.le_0_l|].
    by apply/ssrnat.ltP. }
  have Hcell := Hrow _ Hj_in.
  by apply Z.eqb_eq.
Qed.

Lemma M2_int_sym_pointwise (i j : nat) :
  (i < 42)%nat -> (j < 42)%nat ->
  mat_get M2_int i j = mat_get M2_int j i.
Proof.
  move=> Hi Hj.
  have Hgrid := M2_int_sym_check_true.
  rewrite /M2_int_sym_check in Hgrid.
  move/forallb_forall in Hgrid.
  have Hi_in : List.In i (List.seq 0 42).
  { apply List.in_seq. split; [apply Nat.le_0_l|].
    by apply/ssrnat.ltP. }
  have Hrow := Hgrid _ Hi_in.
  move/forallb_forall in Hrow.
  have Hj_in : List.In j (List.seq 0 42).
  { apply List.in_seq. split; [apply Nat.le_0_l|].
    by apply/ssrnat.ltP. }
  have Hcell := Hrow _ Hj_in.
  by apply Z.eqb_eq.
Qed.

(* ------------------------------------------------------------------
   Section 5 — rat-level symmetry of the Gram matrices.

   `mat_int_to_rat M D 42` is a MathComp `'M[rat]_42` whose (i, j)
   entry is `(M_int[i][j]) / D`.  Since the underlying integer
   matrix is symmetric and the denominator is shared, the rat
   matrix is symmetric: `M (i,j) = M (j,i)` for all ordinals
   i, j : 'I_42.
   ------------------------------------------------------------------ *)

Local Open Scope ring_scope.

Lemma mat_int_to_rat_sym
      (M : mat) (D : Z) (n : nat)
      (Hsym : forall i j : nat, (i < n)%nat -> (j < n)%nat ->
                                mat_get M i j = mat_get M j i)
      (i j : 'I_n) :
  (mat_int_to_rat M D n) i j = (mat_int_to_rat M D n) j i.
Proof.
  rewrite /mat_int_to_rat !mxE.
  have Hi : (nat_of_ord i < n)%nat by case: i.
  have Hj : (nat_of_ord j < n)%nat by case: j.
  by rewrite (Hsym (nat_of_ord i) (nat_of_ord j) Hi Hj).
Qed.

Lemma M1_rat_sym (i j : 'I_42) :
  (mat_int_to_rat M1_int D_M1 42) i j
  = (mat_int_to_rat M1_int D_M1 42) j i.
Proof.
  apply: mat_int_to_rat_sym.
  exact: M1_int_sym_pointwise.
Qed.

Lemma M2_rat_sym (i j : 'I_42) :
  (mat_int_to_rat M2_int D_M2 42) i j
  = (mat_int_to_rat M2_int D_M2 42) j i.
Proof.
  apply: mat_int_to_rat_sym.
  exact: M2_int_sym_pointwise.
Qed.

(* Restated in the standard MathComp idiom: trmx M = M. *)
Lemma M1_rat_symmetric :
  trmx (mat_int_to_rat M1_int D_M1 42) = mat_int_to_rat M1_int D_M1 42.
Proof.
  apply/matrixP => i j.
  rewrite mxE.
  by rewrite M1_rat_sym.
Qed.

Lemma M2_rat_symmetric :
  trmx (mat_int_to_rat M2_int D_M2 42) = mat_int_to_rat M2_int D_M2 42.
Proof.
  apply/matrixP => i j.
  rewrite mxE.
  by rewrite M2_rat_sym.
Qed.

Local Close Scope ring_scope.

(* ==================================================================
   Summary of remaining gaps (from this file's header, repeated for
   future readers grepping the codebase).

   To get from `maynard_eigenvalue_S1` (eigenvalue of M1^{-1} . M2
   in realalg, > 4/105) to `M_{105} > 4`:

     1. M1 positive-definite over Q.    [analytic; needs integrals]
     2. Spectral theorem for symmetric  [needs PD square root and
        matrices over R, applied to      MathComp spectral lemmas
        M1^{-1/2} . M2 . M1^{-1/2}]      not yet in mathlib]
     3. Lemma 8.3 (Maynard 8.3):        [needs integral library]
        M_k = k * lambda_max(M1^{-1} M2)
     4. Final numerical bridge:         [follows from 1-3]
        4 < 105 * lambda  =>  M_{105} > 4

   Items 1-3 are out of scope for an algebraic-only formalization.
   The symmetry facts proved here are the algebraic prerequisite
   for items 2 and 3.
   ================================================================== *)
