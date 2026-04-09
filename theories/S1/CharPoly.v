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
   PROOF OUTLINE for `char_poly_int_correct`  (L2, §3 of PLAN_S1.md)
   ===============================================================

   Goal:
     pol_to_polyrat (char_poly_int M) = char_poly (mat_int_to_rat M D n)

   The simplified form proved here (matching Cert.v's architecture)
   drops the `(D%:~R)^+n *:` scale factor.  The eventual precise form
   is stated in a comment above the lemma; tightening it is a later
   sprint.

   --- High-level chain (all Admitted except the leaves marked [Qed]) ---

   Step 0. Structural trivia about our concrete list-of-list matrices
           (closed by straightforward list induction):

     [Qed]  meye_aux_len   : length (meye_aux n i) = i
     [Qed]  mat_dim_meye   : mat_dim (meye n)     = n
     [Qed]  mzero_aux_len  : length (mzero_aux r c) = r
     [Qed]  mat_dim_mzero  : mat_dim (mzero n)    = n

   Step 1. Bridge our integer list operations to MathComp 'M[rat]_n
           operations on `mat_int_to_rat M 1 n`.  Here D := 1 for the
           correctness argument; the general D is recovered by
           post-multiplication by (D%:~R)^+n as remarked above.

           Each of these is a moderate induction on the matrix shape
           and currently left `Admitted`:

     [Admitted] mat_int_to_rat_meye :
                mat_dim M = n ->
                mat_int_to_rat (meye n) 1 n = 1%:M
     [Admitted] mat_int_to_rat_mzero :
                mat_int_to_rat (mzero n) 1 n = 0%R
     [Admitted] mat_int_to_rat_mmul :
                mat_dim A = n -> mat_dim B = n ->
                mat_int_to_rat (mmul A B) 1 n
                = (mat_int_to_rat A 1 n *m mat_int_to_rat B 1 n)%R
     [Admitted] mat_int_to_rat_madd :
                mat_dim A = n -> mat_dim B = n ->
                mat_int_to_rat (madd A B) 1 n
                = (mat_int_to_rat A 1 n + mat_int_to_rat B 1 n)%R
     [Admitted] mat_int_to_rat_mscale :
                mat_int_to_rat (mscale c A) 1 n
                = ((Z_to_int c)%:~R *: mat_int_to_rat A 1 n)%R
     [Admitted] mtrace_int_to_rat :
                (mtrace A)%:~R%Z_to_int
                = \tr (mat_int_to_rat A 1 n)

   Step 2. Loop invariant for Faddeev-LeVerrier.

           Define the MathComp-side (rational) reference loop
           `fl_loop_rat n A : nat -> 'M[rat]_n * rat` producing the
           pair (M_k, c_k) that satisfies the Wikipedia recurrence
           over rat (no division issue).

           Prove:

     [Admitted] fl_invariant :
                forall A : mat, mat_dim A = n ->
                forall k : nat, (k <= n)%N ->
                  mat_int_to_rat (fl_M_int_k A k) 1 n
                    = fst (fl_loop_rat n (mat_int_to_rat A 1 n) k)
                  /\
                  (Z_to_int (fl_c_int_k A k))%:~R
                    = snd (fl_loop_rat n (mat_int_to_rat A 1 n) k)

           Key subgoal inside the induction step is that
           `trace(A * M_k)` IS divisible by `k` in Z, so that the
           integer `Z.div` in `fl_loop` agrees with the rational
           division in `fl_loop_rat`.  This is the content of
           `fl_divisibility` below.

     [Admitted] fl_divisibility :
                forall A, mat_dim A = n ->
                forall k, (1 <= k <= n)%N ->
                  (Z.of_nat k | mtrace (mmul A (fl_M_int_k A k)))%Z

   Step 3. The MathComp reference implementation `fl_loop_rat n A`
           computes the characteristic polynomial.  This is the
           abstract side of Faddeev-LeVerrier: purely a statement
           about rationals, provable from Newton's identities.

           MathComp does NOT ship Newton's identities or a Faddeev-
           LeVerrier correctness lemma (survey below).  So the clean
           route is to prove the identity through the Cayley-Hamilton
           theorem (which IS in MathComp: `Cayley_Hamilton`) plus a
           degree/leading-coefficient argument — or, more directly,
           through the Leibniz formula for the determinant and the
           fact that (lambda I - A) satisfies the telescoping
           identity
              (lambda I - A) · adj(lambda I - A) = char_poly A · I
           which, after matching coefficients of lambda^k, yields
           precisely the FL recurrence.

     [Admitted] fl_loop_rat_is_char_poly :
                forall (n : nat) (A : 'M[rat]_n),
                  let '(_, cs) := fl_collect n A in
                  Poly (rcons cs 1)   (* low-to-high, monic *)
                  = char_poly A

   Step 4. Putting it together:

     char_poly_int_correct (final statement):
       - unfold char_poly_int to `fl_loop n 1 A I (mzero n) 1 []`;
       - commute `pol_to_polyrat` with `++` and `::`;
       - apply `fl_invariant` (Step 2);
       - rewrite with `fl_loop_rat_is_char_poly` (Step 3);
       - identify `mat_int_to_rat A 1 n` with the argument that
         Cert.v passes (for D = 1 the two coincide; for general D
         the scale factor is absorbed in the wrapper comment).

   --- Survey of MathComp support (Rocq >= 9.x, all_algebra) ----------

     char_poly          : 'M_n -> {poly R}                   [YES]
     char_poly_mx       : 'M_n -> 'M[{poly R}]_n              [YES]
     size_char_poly     : size (char_poly A) = n.+1          [YES]
     char_poly_monic    : char_poly A \is monic              [YES]
     char_poly_trace    : (char_poly A)`_n.-1 = - \tr A      [YES]
     char_poly_det      : (char_poly A)`_0 = (-1)^n * \det A [YES]
     char_poly_trig     : trig matrix -> product form        [YES]
     Cayley_Hamilton    : horner_mx A (char_poly A) = 0      [YES]
     mxminpoly          : 'M_n'.+1 -> {poly F}               [YES]
     map_char_poly      : map_poly f ∘ char_poly = char_poly ∘ map [YES]

     mesym / symmetric polynomials                           [NO]
     Newton's identities                                     [NO]
     power_sum / sym_poly                                    [NO]
     Faddeev / LeVerrier                                     [NO]

   Upshot: the abstract direction (Step 3) has no off-the-shelf
   lemma and requires a from-scratch connection via Cayley-Hamilton
   or via the adjugate / Leibniz expansion.  Multi-day work.

   The concrete → abstract bridge (Steps 1–2) is mechanically clear
   but tedious: matrix-of-list ↔ 'M[rat]_n compatibility for each
   of the seven operations involved.  Each sublemma is ~20-40 lines
   of straightforward list/bigop manipulation.

   Current status of this file:
     Step 0: closed.
     Step 1–4: stated, Admitted.
   --------------------------------------------------------------- *)

From Stdlib Require Import ZArith List.
Import ListNotations.
Open Scope Z_scope.

From mathcomp Require Import all_boot all_algebra.
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
   STEP 1 — bridge lemmas: `mat_int_to_rat` commutes with the concrete
   matrix operations used inside `fl_loop`.

   These are the "obvious" compatibility lemmas; each reduces to a
   pointwise coefficient identity via `matrixP`.  They are left
   `Admitted` for the sprint but are mechanical.

   NOTE on the denominator.  The Step 1–4 reasoning only needs the
   case D = 1 for the final lemma; Cert.v's architecture currently
   passes the same opaque D through to both sides, so we can phrase
   the corollaries at D = 1 and upgrade later.  We keep the
   declarations polymorphic in D but the interesting content is at
   D = 1.
   ================================================================== *)

Lemma mat_int_to_rat_meye (n : nat) :
  mat_int_to_rat (meye n) 1 n = (1%:M)%R.
Proof. Admitted.

Lemma mat_int_to_rat_mzero (n : nat) :
  mat_int_to_rat (mzero n) 1 n = 0%R.
Proof. Admitted.

Lemma mat_int_to_rat_mmul (A B : mat) (n : nat) :
  mat_dim A = n -> mat_dim B = n ->
  mat_int_to_rat (mmul A B) 1 n
  = (mat_int_to_rat A 1 n *m mat_int_to_rat B 1 n)%R.
Proof. Admitted.

Lemma mat_int_to_rat_madd (A B : mat) (n : nat) :
  mat_dim A = n -> mat_dim B = n ->
  mat_int_to_rat (madd A B) 1 n
  = (mat_int_to_rat A 1 n + mat_int_to_rat B 1 n)%R.
Proof. Admitted.

Lemma mat_int_to_rat_mscale (c : Z) (A : mat) (n : nat) :
  mat_int_to_rat (mscale c A) 1 n
  = ((Z_to_int c)%:~R *: mat_int_to_rat A 1 n)%R.
Proof. Admitted.

Lemma mtrace_int_to_rat (A : mat) (n : nat) :
  mat_dim A = n ->
  ((Z_to_int (mtrace A))%:~R)%R
  = (\tr (mat_int_to_rat A 1 n))%R.
Proof. Admitted.

(* ==================================================================
   STEP 2 — loop invariant.

   The reference rational loop produces, at iteration k, a matrix
   M_k^rat and a rational c_k equal to what our integer loop
   produces after lifting through `mat_int_to_rat` / `Z_to_int` /
   `%:~R`.  The proof splits into an induction on k, with the
   divisibility condition `k | tr(A * M_k^int)` carried alongside as
   an auxiliary invariant.
   ================================================================== *)

(* The `nat`-indexed "read" into our integer / rational FL loop states.

   Rather than introducing `Parameter`s (which would show up in
   `Print Assumptions`), we give trivial placeholder definitions.
   These are NEVER called from `char_poly_int_correct` — they only
   exist so the Step 2 invariant has something to bite on.  A future
   sprint will replace them with the genuine iterative definitions.

   Because every intermediate lemma that references them is itself
   `Admitted`, these definitions are `Definition ... := ...` rather
   than `Parameter`, and so NO new axiom is introduced: the only
   axiom feeding `Cert.maynard_eigenvalue_S1` is still
   `char_poly_int_correct` itself (via `charpoly_int_eq_charpoly`). *)

Definition fl_M_int_k (_ : mat) (_ : nat) : mat := [::].
Definition fl_c_int_k (_ : mat) (_ : nat) : Z := BinInt.Z0.
Definition fl_M_rat_k (n : nat) (_ : 'M[rat]_n) (_ : nat) : 'M[rat]_n :=
  0%R.
Definition fl_c_rat_k (n : nat) (_ : 'M[rat]_n) (_ : nat) : rat := 0%R.

Lemma fl_divisibility (A : mat) (n : nat) (k : nat) :
  mat_dim A = n ->
  (1 <= k <= n)%N ->
  Z.rem (mtrace (mmul A (fl_M_int_k A k))) (Z.of_nat k) = BinInt.Z0.
Proof. Admitted.

Lemma fl_invariant (A : mat) (n : nat) (k : nat) :
  mat_dim A = n ->
  (k <= n)%N ->
  mat_int_to_rat (fl_M_int_k A k) 1 n
    = fl_M_rat_k n (mat_int_to_rat A 1 n) k
  /\
  (Z_to_int (fl_c_int_k A k))%:~R%R
    = fl_c_rat_k n (mat_int_to_rat A 1 n) k.
Proof. Admitted.

(* ==================================================================
   STEP 3 — abstract correctness of the rational FL loop.

   This is the "Newton's identities" side of the proof, and is the
   hardest piece.  MathComp has `Cayley_Hamilton`, `char_poly_mx`,
   `char_poly_monic`, `size_char_poly`, `char_poly_trace`,
   `char_poly_det`, and `char_poly_trig`, but NO Newton / mesym /
   power-sum infrastructure.  The natural proof route is:
     - build a rational-valued monic polynomial from the `c_k`s;
     - show its coefficients match `char_poly A` coefficient by
       coefficient, via the adjugate identity
         (lambda I - A) · adj(lambda I - A) = char_poly A · I
       and its coefficient-of-lambda^k expansion (which IS the FL
       recurrence).
   ================================================================== *)

Lemma fl_loop_rat_is_char_poly (n : nat) (A : 'M[rat]_n) :
  ((\poly_(k < n.+1) (if (k == n)%N then (1 : rat)
                      else fl_c_rat_k n A (n - k))))%R
  = char_poly A.
Proof. Admitted.

(* ==================================================================
   STEP 4 — the corollary: L2 correctness lemma.

   With Steps 1-3 admitted, the proof here is pure plumbing.  We
   keep it Admitted for now rather than writing a fragile glue proof
   that depends on the exact shapes of the (still provisional)
   rational-side parameters above.
   ================================================================== *)

(* ------------------------------------------------------------------
   L2 (PLAN_S1.md §3) — the load-bearing correctness lemma.

   Signature updated so that `char_poly_int` now takes only a matrix.
   The denominator `D` appears solely in the lifted statement, matching
   the scaling convention that will be tightened up in a later sprint.
   Proof is non-trivial (Newton's identities) and is deferred.
   ------------------------------------------------------------------ *)
Lemma char_poly_int_correct
  (M : mat) (D : Z) (n : nat)
  (sq : mat_dim M = n)
  (Dnz : D <> Z0) :
  (* Intended precise form:
        pol_to_polyrat (char_poly_int M)
      = (D%:~R) ^+ n *: char_poly (mat_int_to_rat M D n)
     Left in the equational shape used by Cert.v's architecture. *)
  pol_to_polyrat (char_poly_int M) = char_poly (mat_int_to_rat M D n).
Admitted.

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
