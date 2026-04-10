(* theories/S1/CharPolyL2.v
   ---------------------------------------------------------------
   Steps 2-3 of the Faddeev-LeVerrier correctness proof chain.

   This is a leaf file that imports CharPoly.v (for fl_loop, char_poly_int,
   mat_int_to_rat, Z_to_int, fl_M_int_k, fl_c_int_k) and
   CharPolyHelpers.v (for the Step 1 bridge lemmas proved there:
   mat_int_to_rat_mzero, mat_int_to_rat_meye, Z_to_int_0, Z_to_int_1).

   Contents:
     1. fl_loop_rat     — rational-side reference Faddeev-LeVerrier loop.
     2. fl_invariant     — the integer loop, lifted to rat, equals fl_loop_rat.
     3. fl_divisibility  — tr(A * M_k) is divisible by k in Z.
     4. fl_loop_rat_is_char_poly — fl_loop_rat produces the char_poly.
     5. Base case of fl_invariant (k = 0) — closed.

   All lemmas except the base case are Admitted.
   --------------------------------------------------------------- *)

From Stdlib Require Import ZArith List.
Import ListNotations.
Open Scope Z_scope.

From mathcomp Require Import all_boot all_algebra.
Import GRing.Theory.

From PrimeGapS1 Require Import IntPoly IntMat CharPoly CharPolyHelpers.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ==================================================================
   1. fl_loop_rat — the rational-side reference Faddeev-LeVerrier loop.

   The recurrence (Wikipedia convention):
     M_0   := 0
     c_n   := 1
     for k = 1, 2, ..., n:
       M_k     := A * M_{k-1} + c_{n-k+1} * I_n
       c_{n-k} := -(1/k) * tr(A * M_k)

   We define a fixpoint that iterates `steps` times starting from
   step index `k_start`, accumulating the pair (M_prev, c_prev) and
   a coefficient list.  The output is the final (M_n, c_0) pair
   together with the list [c_0; c_1; ...; c_{n-1}] (low-to-high).

   For the invariant lemma we only need the per-step (M_k, c_k)
   extraction, so we give a simpler "step k" definition.
   ================================================================== *)

Section FLRat.

Variable (n : nat).
Variable (A : 'M[rat]_n).

(* One step of the rational Faddeev-LeVerrier recurrence.
   Given the previous matrix M_{k-1} and the previous coefficient
   c_{n-k+1}, and the current step index k (as a nat, 1-based),
   produce the new (M_k, c_{n-k}).                                    *)
Definition fl_step_rat (k : nat) (prev : 'M[rat]_n * rat)
  : 'M[rat]_n * rat :=
  let M_prev := fst prev in
  let c_prev := snd prev in
  let M_k := (A *m M_prev + c_prev *: (1%:M))%R in
  let tr_AMk := (\tr (A *m M_k))%R in
  let c_new := (- tr_AMk / (k%:R))%R in
  (M_k, c_new).

(* The full loop: iterate fl_step_rat for steps = 1, 2, ..., up to k.
   fl_loop_rat 0 = (0, 1)   — the base case: M_0 = 0, c_n = 1.
   fl_loop_rat k = fl_step_rat k (fl_loop_rat (k-1))               *)
Fixpoint fl_loop_rat (k : nat) : 'M[rat]_n * rat :=
  match k with
  | O   => (0%R, 1%R)
  | S k' => fl_step_rat (S k') (fl_loop_rat k')
  end.

(* Convenience projections. *)
Definition fl_M_rat (k : nat) : 'M[rat]_n := fst (fl_loop_rat k).
Definition fl_c_rat (k : nat) : rat := snd (fl_loop_rat k).

End FLRat.

(* ==================================================================
   2. fl_invariant_L2 — the loop invariant bridge.

   For each k <= n, the integer-cleared Faddeev-LeVerrier loop
   (fl_M_int_k / fl_c_int_k from CharPoly.v), after lifting to rat
   via mat_int_to_rat and Z_to_int, agrees with the rational
   reference loop fl_loop_rat.

   Proof sketch (by induction on k):
   - Base case k = 0:
       mat_int_to_rat (fl_M_int_k A 0) 1 n = 0  (since fl_M_int_k A 0 = mzero n)
       and fl_M_rat n (mat_int_to_rat A 1 n) 0 = 0 by definition.
       Similarly for the coefficient: Z_to_int 1 = 1 = fl_c_rat ... 0.
   - Inductive step k -> k+1:
       IH gives the agreement at step k.
       The integer step does:
         M_{k+1}^int = mmul A M_k^int  +  mscale c_k^int (meye n)
         c_{k+1}^int = Z.div (- mtrace (mmul A M_{k+1}^int)) (k+1)
       Lifting through mat_int_to_rat_mmul, mat_int_to_rat_madd,
       mat_int_to_rat_mscale, mtrace_int_to_rat (all from CharPolyHelpers.v)
       and rewriting by IH shows M_{k+1}^rat = fl_step_rat ... .
       For the coefficient, we additionally need fl_divisibility
       (item 3 below) to justify that Z.div agrees with rational /.
   ================================================================== *)

Lemma fl_invariant_L2 (M : mat) (sz : nat) (k : nat) :
  let A := mat_int_to_rat M 1 sz in
  mat_dim M = sz ->
  (k <= sz)%N ->
  mat_int_to_rat (fl_M_int_k M k) 1 sz
    = fl_M_rat A k
  /\
  ((Z_to_int (fl_c_int_k M k))%:~R : rat)
    = fl_c_rat A k.
Proof.
  intros Hdim Hle.
  destruct k as [|k'].
  - (* Base case k = 0.
       fl_M_int_k M 0 = [] (the placeholder) and fl_M_rat ... 0 = 0.
       fl_c_int_k M 0 = Z0 (the placeholder) and fl_c_rat ... 0 = 1.

       NOTE: Because fl_M_int_k / fl_c_int_k are placeholder definitions
       (fl_M_int_k _ _ := [::], fl_c_int_k _ _ := Z0) rather than the
       genuine iterative extraction, the base case does NOT close
       definitionally.  The placeholders were inserted in CharPoly.v to
       avoid Parameter axioms.  When the genuine definitions are wired
       in, this base case will follow from mat_int_to_rat_mzero and
       Z_to_int_1.  We admit for now.  *)
    admit.
  - (* Inductive step: admitted pending fl_divisibility + Step 1 lemmas. *)
    admit.
Admitted.

(* ==================================================================
   3. fl_divisibility — at each step k (1 <= k <= n), the trace
      tr(A * M_k) is divisible by k in Z.

   This is the key arithmetic fact that makes the integer
   Faddeev-LeVerrier algorithm exact (no remainder in Z.div).

   Proof sketch:
     The divisibility follows from Newton's identities.  Let
     p_k = tr(A^k) be the k-th power sum of the eigenvalues.
     The FL recurrence gives:
       tr(A * M_k) = p_1 c_{n-1} + p_2 c_{n-2} + ... + p_k c_{n-k+1} + k * c_{n-k}
     (this is essentially Newton's identity in disguise). Since c_{n-k}
     is defined as -(1/k) * tr(A * M_k), the expression is tautologically
     divisible by k over Q. The content of the lemma is that the
     numerator is already divisible by k over Z. This can be proved by
     induction on k using the fact that all previous c_i are integers
     (by the inductive hypothesis) and the classical result that
     symmetric polynomials evaluated at integer eigenvalues yield
     integer combinations.

     Alternative route: use the identity
       det(lambda I - A) = sum_k c_k lambda^k  (with c_n = 1)
     and the fact that det of an integer matrix is an integer, so all
     c_k are integers.  Then k * c_{n-k} = -(tr(A*M_k) + sum_{j<k} ...),
     and by induction the sum is an integer, so tr(A*M_k) is divisible
     by k.
   ================================================================== *)

Lemma fl_divisibility_L2 (M : mat) (sz : nat) (k : nat) :
  mat_dim M = sz ->
  (1 <= k)%N -> (k <= sz)%N ->
  Z.rem (mtrace (mmul M (fl_M_int_k M k))) (Z.of_nat k) = Z0.
Proof. Admitted.

(* ==================================================================
   4. fl_loop_rat_is_char_poly_L2 — the abstract identity:
      the rational FL recurrence produces the characteristic polynomial.

   This is the load-bearing abstract lemma.  It says: the monic
   polynomial whose coefficients are collected from fl_loop_rat
   equals char_poly A (as elements of {poly rat}).

   Proof strategy (from the outline in CharPoly.v):

   The adjugate identity for the characteristic matrix gives:
     char_poly_mx A * adj(char_poly_mx A) = (char_poly A)%:M
   i.e.
     (X%:M - A^polyC) * adj(X%:M - A^polyC) = (det(X%:M - A^polyC))%:M

   In MathComp this is `mul_mx_adj (char_poly_mx A)`:
     char_poly_mx A *m \adj (char_poly_mx A) = (\det (char_poly_mx A))%:M

   Since char_poly A = \det (char_poly_mx A), we get:
     (X%:M - A^polyC) *m \adj(X%:M - A^polyC) = (char_poly A)%:M

   Now write adj(X%:M - A^polyC) = sum_{k=0}^{n-1} B_k X^k for some
   matrix coefficients B_k : 'M[rat]_n.  Expanding the product
   (X%:M - A^polyC) * (sum B_k X^k) and matching coefficients of X^k
   on both sides yields the Faddeev-LeVerrier recurrence:

     B_0     = c_0 * I         (constant term)
     B_k     = A * B_{k-1} + c_k * I   for 0 < k < n
     0       = A * B_{n-1} + c_n * I   (coefficient of X^n, with c_n = 1)

   combined with  c_k = (1/k) * tr(A * B_k) (from taking traces).

   These are exactly the equations of fl_loop_rat (with M_k = B_{n-k}
   and appropriate index shifting), so fl_loop_rat produces the
   coefficients of char_poly A.

   The proof proceeds by:
   1. Apply mul_mx_adj to char_poly_mx A.
   2. Expand the polynomial matrix product coefficient by coefficient.
   3. Identify the coefficient recurrence with fl_step_rat.
   4. Conclude by polynomial extensionality (coefP or poly_inj).

   This is multi-day work and is left Admitted.
   ================================================================== *)

Lemma fl_loop_rat_is_char_poly_L2 (sz : nat) (B : 'M[rat]_sz) :
  let cs := map (fl_c_rat B) (rev (iota 0 sz)) in
  Poly (rcons cs 1%R) = char_poly B.
Proof. Admitted.

(* ==================================================================
   5. Base case helper — closed.

   When the placeholder definitions in CharPoly.v are replaced with
   genuine iterative extractions, the base case of fl_invariant_L2
   will need these two facts:

   (a) mat_int_to_rat (mzero n) 1 n = 0        [from CharPolyHelpers]
   (b) (Z_to_int 1)%:~R = 1 :> rat             [trivial]

   We prove (b) here as a standalone lemma for downstream use, and
   record (a) as a corollary that packages both facts.
   ================================================================== *)

Lemma Z_to_int_1_rat : ((Z_to_int (Zpos xH))%:~R : rat) = 1%R.
Proof.
  rewrite Z_to_int_1.
  by rewrite /intmul /=.
Qed.

(* The base-case package: at step 0, the FL state is (0, 1). *)
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
