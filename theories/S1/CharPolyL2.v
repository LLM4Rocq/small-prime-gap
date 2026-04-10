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

From Stdlib Require Import ZArith List Lia.
Import ListNotations.
Open Scope Z_scope.

From mathcomp Require Import all_boot all_algebra.
Import GRing.Theory.

From PrimeGapS1 Require Import IntPoly IntMat CharPoly CharPolyHelpers.

Set Implicit Arguments.
Unset Strict Implicit.

(* Local placeholder definitions for the FL loop state readers.
   These were formerly in CharPoly.v but were removed to clean up
   dead code. They are used ONLY by the Admitted wrapper lemmas
   fl_invariant_L2 and fl_divisibility_L2 below. Once the genuine
   iterative definitions are developed, these will be replaced. *)
Definition fl_M_int_k (_ : mat) (_ : nat) : mat := [::].
Definition fl_c_int_k (_ : mat) (_ : nat) : Z := Z0.
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

(* ------------------------------------------------------------------
   Auxiliary lemmas for Z_to_int that we need in the inductive step.
   ------------------------------------------------------------------ *)

Lemma Z_to_int_opp (a : Z) :
  Z_to_int (BinInt.Z.opp a) = (- Z_to_int a)%R.
Proof.
  destruct a as [|pa|pa]; simpl BinInt.Z.opp.
  - by rewrite oppr0.
  - by rewrite Z_to_int_neg_pos Z_to_int_pos_pos.
  - by rewrite Z_to_int_neg_pos Z_to_int_pos_pos opprK.
Qed.

(* When d divides a (Z.rem a d = 0), then Z.div a d lifted to rat
   equals the rational quotient (Z_to_int a)%:~R / (Z_to_int d)%:~R.
   This is the key bridge between exact integer division and
   rational division. *)
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

(* Local copy of Z_to_int_of_nat (the original is in Bridge.v which
   we prefer not to import to keep dependencies light). *)
Lemma Z_to_int_of_nat (n : nat) :
  Z_to_int (BinInt.Z.of_nat n) = Posz n.
Proof. case: n => [//|n]; by rewrite /Z_to_int /= SuccNat2Pos.id_succ. Qed.

Lemma Z_to_int_1_rat : ((Z_to_int (Zpos xH))%:~R : rat) = 1%R.
Proof.
  rewrite Z_to_int_1.
  by rewrite /intmul /=.
Qed.

(* ------------------------------------------------------------------
   2a. fl_invariant_L2_gen — the invariant proved under hypotheses
       about what fl_M_int_k and fl_c_int_k SHOULD satisfy.

   The current definitions in CharPoly.v are placeholders ([::]
   and Z0). When they are replaced with genuine iterative
   extractions, the hypotheses below become provable and
   fl_invariant_L2 follows as a corollary.

   By proving the inductive step under hypotheses, we establish
   that the PROOF STRUCTURE is correct, modulo the placeholder
   issue. The headline admit count does not increase.
   ------------------------------------------------------------------ *)

Section FL_Invariant_Proof.

Variable M : mat.
Variable sz : nat.

Let A := mat_int_to_rat M 1 sz.

(* --- What the genuine fl_M_int_k / fl_c_int_k should satisfy --- *)

(* Accessor functions: these shadow the CharPoly.v placeholders
   within this section.  The section hypotheses constrain them to
   satisfy the FL recurrence. *)
Variable fl_M : nat -> mat.
Variable fl_c : nat -> Z.

(* Base case: M_0 = 0, c_0 = 1. *)
Hypothesis fl_base_M : fl_M 0 = mzero sz.
Hypothesis fl_base_c : fl_c 0 = Zpos xH.

(* Recurrence for the matrix component:
     M_{k+1} = A * M_k + c_k * I_sz *)
Hypothesis fl_step_M : forall k, (k < sz)%N ->
  fl_M k.+1 = madd (mmul M (fl_M k)) (mscale (fl_c k) (meye sz)).

(* Recurrence for the coefficient component:
     c_{k+1} = -(tr(A * M_{k+1})) / (k+1)    (exact integer division) *)
Hypothesis fl_step_c : forall k, (k < sz)%N ->
  fl_c k.+1 = BinInt.Z.div
                (BinInt.Z.opp (mtrace (mmul M (fl_M k.+1))))
                (BinInt.Z.of_nat k.+1).

(* Well-formedness: all intermediate matrices are sz x sz grids. *)
Hypothesis fl_M_dim : forall k, (k <= sz)%N -> mat_dim (fl_M k) = sz.
Hypothesis fl_M_rows : forall k, (k <= sz)%N -> all_rows_len sz (fl_M k).

(* The input matrix M is well-formed. *)
Hypothesis M_dim : mat_dim M = sz.
Hypothesis M_rows : all_rows_len sz M.

(* Well-formedness of the identity matrix. *)
Hypothesis meye_rows : all_rows_len sz (meye sz).

(* Divisibility: at each step, the trace is divisible by k+1. *)
Hypothesis fl_div : forall k, (k < sz)%N ->
  BinInt.Z.rem (mtrace (mmul M (fl_M k.+1)))
               (BinInt.Z.of_nat k.+1) = Z0.

(* Well-formedness of mmul and madd intermediates. *)
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
  - (* Base case k = 0. *)
    rewrite fl_base_M fl_base_c.
    split.
    + rewrite mat_int_to_rat_mzero. reflexivity.
    + exact Z_to_int_1_rat.
  - (* Inductive step k -> k.+1. *)
    have Hk_le : (k <= sz)%N by apply: ltnW.
    have Hk_lt : (k < sz)%N by exact Hle.
    have [IHmat IHcoeff] := IH Hk_le.
    (* Unfold the rational side at k.+1. *)
    rewrite /fl_M_rat /fl_c_rat /= -/fl_loop_rat.
    rewrite -/(fl_M_rat A k) -/(fl_c_rat A k).
    (* Rewrite the rational RHS using IH so both sides are expressed
       in terms of the integer-side operations. *)
    rewrite -IHmat -IHcoeff.
    split.
    + (* Matrix conjunct: M_{k+1} = A*M_k + c_k*I lifted to rat. *)
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
    + (* Coefficient conjunct:
           c_{k+1} = Z.div(- tr(A * M_{k+1}), k+1)
         lifted to rat equals -tr(A_rat * M_rat_{k+1}) / (k+1)%:R. *)
      rewrite (fl_step_c Hk_lt).
      (* Step 1: Establish divisibility for the negated trace. *)
      have Hkp : BinInt.Z.of_nat k.+1 <> Z0.
      { rewrite Nat2Z.inj_succ. lia. }
      have Hdiv_opp :
        Z.rem (BinInt.Z.opp (mtrace (mmul M (fl_M k.+1))))
              (BinInt.Z.of_nat k.+1) = Z0
        by rewrite Z.rem_opp_l // fl_div.
      (* Step 2: Apply Z_div_exact_rat to convert Z.div to rational /. *)
      rewrite (@Z_div_exact_rat _ _ Hkp Hdiv_opp).
      (* Step 3: Lift Z.opp and simplify Z.of_nat k.+1. *)
      rewrite Z_to_int_opp rmorphN /=.
      rewrite SuccNat2Pos.id_succ -pmulrn.
      (* Step 4: Reduce to showing the traces match. *)
      congr (_ / _)%R. congr (- _)%R.
      (* Step 5: Lift mtrace and mmul through bridge lemmas. *)
      have HMk1_dim : mat_dim (fl_M k.+1) = sz
        by apply fl_M_dim; exact Hle.
      have HMk1_rows : all_rows_len sz (fl_M k.+1)
        by apply fl_M_rows; exact Hle.
      have Hmmul_dim : mat_dim (mmul M (fl_M k.+1)) = sz
        by exact (mmul_dim M_dim HMk1_dim).
      rewrite (mtrace_int_to_rat (mmul M (fl_M k.+1)) sz Hmmul_dim).
      rewrite (mat_int_to_rat_mmul M (fl_M k.+1) sz M_dim HMk1_dim
                 M_rows HMk1_rows).
      (* Step 6: Expand M_{k+1} via the recurrence. *)
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

(* ------------------------------------------------------------------
   2b. fl_invariant_L2 — the original statement.

   This wraps fl_invariant_L2_gen, but since the definitions
   fl_M_int_k and fl_c_int_k in CharPoly.v are placeholders
   ([::]  and Z0), we cannot discharge the section hypotheses yet.
   Once the placeholders are replaced, the 2 remaining admits here
   reduce to verifying the recurrence on the genuine definitions.
   ------------------------------------------------------------------ *)

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
  move=> A Hdim Hle.
  (* The placeholder definitions fl_M_int_k := [::] and
     fl_c_int_k := Z0 do not satisfy the FL recurrence, so we
     cannot instantiate fl_invariant_L2_gen yet.  The 2 admits
     below will vanish when the genuine iterative definitions
     are wired in. *)
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

   Z_to_int_1_rat is now proved above (before the section).
   (a) is provided by mat_int_to_rat_mzero from CharPolyHelpers.
   ================================================================== *)

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
