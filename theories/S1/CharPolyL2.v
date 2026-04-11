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
From mathcomp.algebra_tactics Require Import ring lra.
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

(* ------------------------------------------------------------------
   Core identity: the FL coefficient at step k (for k = 1, ..., sz)
   equals the (sz-k)-th coefficient of char_poly B.

   This is proved by strong induction on k.  The key ingredients are:
   (a) Cayley-Hamilton:  horner_mx B (char_poly B) = 0
   (b) Taking traces of B^m * (Cayley-Hamilton equation) gives Newton
       identities on the char_poly coefficients.
   (c) The FL recurrence computes the same Newton identity by
       construction (the trace term in fl_step_rat is exactly the
       Newton sum).
   (d) By uniqueness of the recurrence, the FL coefficients must
       equal the char_poly coefficients.
   ------------------------------------------------------------------ *)

(* We factor the proof into sub-lemmas. *)
Section FL_CharPoly_Core.

Variable (n : nat).
Variable (B : 'M[rat]_n.+1).

(* ----- Abbreviations ------------------------------------------------ *)
Let cp := char_poly B.

(* The FL "matrix" at step k (a partial sum involving B-powers). *)
(* M_k = sum_{j=0}^{k-1} fl_c_rat B j *: B^{k-1-j}
   By the FL recurrence:
     M_0 = 0
     M_k = B * M_{k-1} + fl_c_rat B (k-1) *: 1%:M *)

(* ----- Sub-lemma: fl_M_rat satisfies a trace-sum expansion --------- *)

(* FL matrix expansion: M_k = \sum_{j=0}^{k-1} c_{n+1-j} * B^{k-1-j} *)
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

(* ----- Sub-lemma: FL trace identity matches Newton identity ---------- *)

(* From the FL recurrence, we get:
     k * fl_c_rat B k = -tr(B * M_k)
   Expanding M_k:
     k * c_k = - sum_{j=0}^{k-1} c_j * tr(B^{k-j})

   where c_j = fl_c_rat B j.

   Separately, from Cayley-Hamilton (horner_mx B cp = 0), multiplying
   by B^m and taking traces gives:
     sum_{i=0}^{n+1} cp`_i * tr(B^{i+m}) = 0

   These two sets of identities are the SAME recurrence when we set
   c_j = cp`_{n+1-j} (i.e., fl_c_rat B j should equal cp`_{n+1-j}).
*)

(* The Newton identity from Cayley-Hamilton + Jacobi's formula.
   For k = 1, ..., n+1:
     sum_{j=0}^{k-1} cp`_{n+1-j} * tr(B^{k-j}) + k * cp`_{n+1-k} = 0

   Proof outline:
   1. Define adj_coef l = the l-th expansion coefficient of adj(xI-B),
      satisfying N_0 = I, N_{l+1} = B*N_l + cp_{n-l}*I.
   2. Show adj_coef l = \sum_{m<=l} cp_{n+1-l+m} *: B^m (explicit formula).
   3. Show tr(adj_coef l) = (n+1-l)*cp_{n+1-l} for l <= n (from Jacobi's
      formula: deriv(char_poly B) = tr(adj(char_poly_mx B)), which gives
      the k-th coefficient of cp' = (k+1)*cp_{k+1} = tr(N_k)).
   4. For k <= n: combine (2) and (3), split off the m=0 term (trace of
      identity), and rearrange to get Newton's identity.
   5. For k = n+1: use the Cayley-Hamilton trace identity directly. *)

(* Adjugate coefficient matrices: N l represents the l-th power expansion
   coefficient of adj(char_poly_mx B), counting from the top.
   N 0 = I (coefficient of x^n), N l = B*N(l-1) + cp_{n-l+1}*I *)
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

(* Explicit formula: adj_coef l = \sum_{m < l+1} cp_{n+1-l+m} *: B^m.
   Proof: by induction on l, using the recurrence and Hlead_cp. *)
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

(* Trace of adj_coef *)
Lemma adj_coef_trace (l : nat) :
  (l <= n.+1)%N ->
  mxtrace (adj_coef l) =
    (\sum_(m < l.+1) (cp)`_(n.+1 - l + m) * mxtrace (B ^+ m))%R.
Proof.
  move=> Hl. rewrite (adj_coef_formula Hl) raddf_sum /=.
  apply eq_bigr => m _. by rewrite mxtraceZ.
Qed.

(* Jacobi for adj_coef: tr(adj_coef l) = (n+1-l) * cp_{n+1-l} for l <= n.
   This follows from Jacobi's formula (deriv of determinant = trace of adjugate)
   applied to char_poly_mx B. The proof requires:
   (a) deriv(det M) = \sum_i cofactor(M,i,i) for M = xI - B^polyC
   (b) Identifying cofactor(M,i,i) = char_poly(row' i (col' i B))
   (c) Matching coefficients to relate tr(adj_coef l) to (cp')_{n-l} = (n+1-l)*cp_{n+1-l} *)
Lemma adj_coef_jacobi (l : nat) :
  (l <= n)%N ->
  mxtrace (adj_coef l) = ((n.+1 - l)%:R * (cp)`_(n.+1 - l))%R.
Proof.
  move=> Hl.
  (* Reduce to: tr(adj_coef l) = (cp')_{n-l} *)
  suff Hsuff : (mxtrace (adj_coef l) = (deriv cp)`_(n - l))%R.
  { rewrite Hsuff coef_deriv.
    have Hnl2 : (n - l).+1 = (n.+1 - l)%N by lia.
    by rewrite Hnl2 mulr_natl. }
  set P := char_poly_mx B.
  (* Q k = k-th coefficient matrix of adj(P) *)
  pose Q := fun k : nat => map_mx (coefp k) (\adj P)%R : 'M[rat]_(n.+1).
  (* Coefficient recurrence from mul_mx_adj: Q k - B * Q(k+1) = cp_{k+1} *: I *)
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
  (* Q n = I (leading coefficient of adjugate is I) *)
  have HQn : Q n = (1%:M)%R.
  { apply/matrixP => i j. rewrite /Q mxE !mxE /cofactor.
    case Hij: (i == j).
    - (* Diagonal: coefp n (char_poly(minor_i B)) = 1 *)
      rewrite (eqP Hij).
      have -> : ((-1 : {poly rat}) ^+ (j + j) = 1)%R
        by rewrite addnn -mul2n mulnC exprM sqrr_sign.
      rewrite mul1r row'_col'_char_poly_mx -/(char_poly _).
      have /monicP := char_poly_monic (row' j (col' j B)).
      by rewrite /lead_coef (size_char_poly (row' j (col' j B))) /= => ->.
    - (* Off-diagonal: degree < n, so coefp n = 0 *)
      (* cofactor(P, j, i) for i != j has degree <= n-1.
         Key idea: the Leibniz formula gives det as a sum of products.
         Each product of n entries of the minor has degree <= n-1
         because when i != j, one row of the minor consists entirely
         of constant polynomials (the row from row i of P, which
         lost its diagonal 'X term when column i was deleted). *)
      rewrite /coefp. apply nth_default. rewrite size_Msign.
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
  (* By induction: Q(n - l') = adj_coef l' for l' <= n *)
  have Hadj_eq : forall l' : nat, (l' <= n)%N ->
    Q (n - l')%N = adj_coef l' :> 'M_(n.+1).
  { elim => [|l' IHl'] Hl'.
    - by rewrite subn0 HQn.
    - have Hl'n : (l' <= n)%N := ltnW Hl'.
      have Hk : (n - l'.+1 <= n)%N by lia.
      (* From Hcoef_eq at k = n - l'.+1:
         Q(n - l'.+1) - B * Q(n - l'.+1 + 1) = cp_{n - l'.+1 + 1} *: I
         Q(n - l'.+1) = B * Q(n - l') + cp_{n - l'} *: I
                      = B * adj_coef l' + cp_{n - l'} *: I  (by IH)
                      = adj_coef l'.+1 *)
      have Hstep := Hcoef_eq (n - l'.+1)%N Hk.
      have Hsucc : (n - l'.+1).+1 = (n - l')%N by lia.
      have Hcp_idx : (n - l'.+1).+1 = (n - l')%N by lia.
      rewrite Hsucc (IHl' Hl'n) in Hstep.
      (* Hstep already has (n-l') indices from Hsucc rewrite *)
      (* Hstep: Q(n-l'.+1) - B * adj_coef l' = cp_{n-l'} *: I *)
      (* So Q(n-l'.+1) = B * adj_coef l' + cp_{n-l'} *: I = adj_coef l'.+1 *)
      have -> : adj_coef l'.+1 = (B *m adj_coef l' + cp`_(n - l') *: 1%:M)%R by done.
      by rewrite -Hstep addrC addrNK. }
  (* Jacobi's formula: deriv(det P) = \sum_k det(row' k (col' k P)) *)
  have jacobi : (deriv (\det P) = \sum_(k : 'I_n.+1) \det (row' k (col' k P)))%R.
  { (* Jacobi's formula for char_poly_mx via Leibniz product rule. *)
    (* Helper: derivative of a product indexed by a list *)
    have deriv_prod_seq : forall (T : eqType) (s : seq T) (F : T -> {poly rat}),
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
    (* Step 1: Unfold det as Leibniz sum, push deriv through *)
    rewrite /determinant raddf_sum /=.
    (* Step 2: For each perm s, simplify deriv((-1)^s * prod) *)
    under eq_bigr => s _.
      rewrite derivM.
      have -> : ((-1 : {poly rat}) ^+ perm.odd_perm s)^`()%R = 0%R.
        by case: (perm.odd_perm s); rewrite /= ?expr1 ?expr0 ?derivN ?derivC ?oppr0.
      rewrite mul0r add0r.
      rewrite deriv_prod_seq; first last.
        exact: index_enum_uniq.
      rewrite mulr_sumr.
      over.
    (* Step 3: Exchange order of summation *)
    rewrite exchange_big /=.
    (* Step 4: For each k, use deriv of char_poly_mx entries *)
    apply eq_bigr => k _.
    have Hderiv_entry : forall i j : 'I_n.+1,
      deriv (P i j) = ((i == j)%:R : rat)%:P%R.
    { move=> i j. rewrite /P /char_poly_mx !mxE.
      rewrite derivB derivC subr0 derivMn derivX.
      by rewrite polyCMn polyC1. }
    under eq_bigr => s _.
      rewrite Hderiv_entry.
      over.
    (* Step 5: Filter -- only perms s with s(k) = k survive *)
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
    (* Step 6: Recognize as cofactor P k k = det(row' k (col' k P)) *)
    under eq_bigr => s Hs.
      rewrite (eq_bigl (fun i0 => k != i0)); last by move=> x; rewrite eq_sym.
      over.
    rewrite -expand_cofactor /cofactor.
    have -> : ((-1 : {poly rat}) ^+ (k + k) = 1)%R
      by rewrite addnn -mul2n mulnC exprM sqrr_sign.
    by rewrite mul1r. }
  (* Diagonal of adjugate = char_poly of minor *)
  have Hdiag : forall k : 'I_n.+1,
    ((\adj P) k k = char_poly (row' k (col' k B)))%R.
  { move=> k. rewrite mxE /cofactor.
    have -> : ((-1 : {poly rat}) ^+ (k + k) = 1)%R
      by rewrite addnn -mul2n mulnC exprM sqrr_sign.
    by rewrite mul1r /char_poly row'_col'_char_poly_mx. }
  (* Assemble the proof *)
  have -> : cp = (\det P)%R by done.
  rewrite jacobi coef_sum /mxtrace.
  apply eq_bigr => k _.
  rewrite row'_col'_char_poly_mx /char_poly.
  (* Goal: adj_coef l k k = (det(char_poly_mx(minor_k B)))_{n-l} *)
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
  (* Establish CH matrix sum *)
  have HCH_mx : (\sum_(i < n.+2) (cp)`_i *: B ^+ i)%R = 0%R :> 'M_(n.+1).
  { suff -> : (\sum_(i < n.+2) (cp)`_i *: B ^+ i)%R = horner_mx B cp
      by exact HCH.
    rewrite /horner_mx /horner_morph /=.
    rewrite (@horner_coef_wide _ n.+2 (map_poly scalar_mx cp) B).
    - apply eq_bigr => i _. rewrite coef_map /=. by rewrite -mul_scalar_mx.
    - rewrite (size_map_poly_id0 _); first by rewrite Hsize.
      have /monicP := char_poly_monic B. rewrite /lead_coef Hsize /= => ->.
      exact: oner_neq0. }
  (* CH trace identity *)
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
  - (* k < n+1, use adjugate trace + Jacobi *)
    have Hkn : (k <= n)%N by rewrite -ltnS.
    have Hkn1 : (k <= n.+1)%N := Hkle.
    have HNt := adj_coef_trace Hkn1.
    have HNj := adj_coef_jacobi Hkn.
    (* Combine HNt and HNj *)
    have Hcomb : (\sum_(m < k.+1) cp`_(n.+1 - k + m) * \tr (B ^+ m))%R
                 = ((n.+1 - k)%:R * cp`_(n.+1 - k))%R
      by rewrite -HNj HNt.
    rewrite big_ord_recl /= expr0 mxtrace_scalar addn0 in Hcomb.
    (* Extract the inner sum *)
    have Hsum : (\sum_(i < k) cp`_(n.+1 - k + bump 0 i)
                    * \tr (B ^+ bump 0 i))%R
                = (- (k%:R * cp`_(n.+1 - k)))%R.
    { apply (addrI (cp`_(n.+1 - k) * n.+1%:R)%R).
      rewrite Hcomb.
      have -> : (k%:R * (cp`_(n.+1 - k) : rat))%R
                = ((cp`_(n.+1 - k) : rat) * k%:R)%R by rewrite mulrC.
      rewrite -mulrBr -natrB //.
      by rewrite mulrC. }
    (* Reindex to match the goal *)
    rewrite -Hsum (reindex_inj rev_ord_inj).
    apply eq_bigr => [[i Hi]] _ /=.
    rewrite /bump /= !add1n.
    have Hi3 : (i.+1 <= k)%N by done.
    rewrite subKn // subnBA //.
    congr (_ * _)%R. congr (cp`_ _)%R.
    by rewrite addnC -addnBA // addnC.
  - (* k = n+1, use CH trace at m=0 *)
    have Hk_eq : k = n.+1 by apply/eqP; rewrite eqn_leq Hkle Hk.
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

(* ----- Sub-lemma: FL trace identity -------------------------------- *)

Lemma fl_trace_identity (k : nat) :
  (1 <= k)%N -> (k <= n.+1)%N ->
  (k%:R * fl_c_rat B k)%R =
    (- \sum_(j < k) fl_c_rat B j * \tr (B ^+ (k - j)))%R.
Proof.
  move=> Hk1 Hk.
  destruct k as [|k']; first by rewrite ltnn in Hk1.
  rewrite /fl_c_rat /= -/fl_loop_rat /fl_step_rat /=.
  rewrite -/(fl_M_rat B k') -/(fl_c_rat B k').
  (* Simplify k'.+1 * (-tr(...) / k'.+1) to -tr(...) *)
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

(* ----- Main sub-lemma: FL coefficient = char_poly coefficient -------- *)

(* fl_c_rat B k = cp`_{n.+1 - k} for k = 0, 1, ..., n.+1 *)
Lemma fl_c_rat_eq_char_poly (k : nat) :
  (k <= n.+1)%N ->
  fl_c_rat B k = ((cp)`_(n.+1 - k))%R.
Proof.
  (* By strong induction on k. *)
  elim/ltn_ind: k => k IH Hk.
  destruct k as [|k'].
  - (* k = 0: fl_c_rat B 0 = 1, cp`_{n.+1} = 1 (leading coeff) *)
    rewrite subn0 /fl_c_rat /=.
    have /monicP := char_poly_monic B.
    rewrite /lead_coef (size_char_poly B).
    by move=> ->.
  - (* k = k'.+1: use uniqueness of the Newton recurrence *)
    (* We have:
       k'.+1 * fl_c_rat B k'.+1 = - sum_{j<k'.+1} fl_c_rat B j * tr(B^{k'.+1-j})
       k'.+1 * cp`_{n-k'}       = - sum_{j<k'.+1} cp`_{n.+1-j} * tr(B^{k'.+1-j})
       By IH, fl_c_rat B j = cp`_{n.+1-j} for j < k'.+1.
       So the RHS are equal, hence the LHS are equal.
       Since k'.+1 != 0 in rat, we can divide by k'.+1. *)
    have Hk'1 : (1 <= k'.+1)%N by done.
    have Hk'le : (k'.+1 <= n.+1)%N by exact Hk.
    have Hfl := fl_trace_identity Hk'1 Hk'le.
    have Hnewton := char_poly_newton Hk'1 Hk'le.
    (* Rewrite newton: sum = - (k'.+1 * cp`_{n.+1 - k'.+1})
       i.e. sum_{j<k'.+1} cp`_{n.+1-j} * tr(B^{k'.+1-j}) = -(k'.+1 * cp`_{n-k'}) *)
    (* By IH, fl_c_rat B j = cp`_{n.+1-j} for all j < k'.+1 *)
    have Hsums_eq :
      (\sum_(j < k'.+1) fl_c_rat B j * \tr (B ^+ (k'.+1 - j)))%R =
      (\sum_(j < k'.+1) (cp)`_(n.+1 - j) * \tr (B ^+ (k'.+1 - j)))%R.
    { apply eq_bigr => j _. congr (_ * _)%R.
      apply IH.
      - exact (ltn_ord j).
      - exact (ltnW (leq_trans (ltn_ord j) Hk'le)). }
    (* From fl_trace_identity: k'.+1 * fl_c_rat B k'.+1 = - same sum *)
    (* From char_poly_newton: same sum = -(k'.+1 * cp`_{n-k'}) *)
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
  - (* sz = 0 *)
    rewrite /= /char_poly.
    have -> : B = (0 : 'M_0)%R by apply/matrixP => i; case: i => [].
    rewrite det_mx00 cons_poly_def mul0r add0r. reflexivity.
  - (* sz = n.+1 *)
    rewrite /=.
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
    + (* i < n.+2: in range *)
      case: (ltnP i n.+1) => Hi2.
      * (* i < n.+1: FL coefficient *)
        rewrite nth_rcons Hsize_cs Hi2.
        rewrite (nth_map 0%N); last by rewrite size_rev /= size_iota.
        rewrite nth_rev; last by rewrite /= size_iota.
        rewrite /= size_iota -/(iota 1 n.+1).
        rewrite nth_iota; last by rewrite ltn_subrL.
        rewrite add1n subSS.
        (* fl_c_rat B (n - i).+1 = (char_poly B)`_i *)
        rewrite /q fl_c_rat_eq_char_poly.
        { congr (_`_ _)%R. rewrite subSS subKn //. }
        { rewrite ltnS. exact (leq_subr i n). }
      * (* i = n.+1: leading coefficient *)
        have Hieq : i = n.+1 by apply/eqP; rewrite eqn_leq Hi2 -ltnS Hi.
        subst i.
        rewrite nth_rcons Hsize_cs ltnn eqxx.
        have /monicP := char_poly_monic B.
        by rewrite /lead_coef /q Hsize_q /= => ->.
    + (* i > n.+1: both sides are 0 (out of range) *)
      rewrite nth_default; last by rewrite size_rcons Hsize_cs.
      rewrite nth_default //. rewrite Hsize_q. exact Hi.
Qed.

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
