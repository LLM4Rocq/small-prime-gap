# Maynard `M_{105} > 4` — A Rocq-audited Rayleigh-quotient proof

This document explains the structure of the Rocq formalisation that
closes the numerical step in James Maynard's *Small gaps between
primes* (arXiv:1311.4600; Annals of Mathematics **181** (2015),
383–413). The headline theorem

```rocq
Theorem maynard_M105_certified_rayleigh :
  (forall i j, (i < 42)%nat -> (j < 42)%nat ->
     M1_spec_ij i j = Z2rat (mat_get M1_int i j) / Z2rat D_M1) /\
  (forall i j, (i < 42)%nat -> (j < 42)%nat ->
     M2_spec_ij i j = Z2rat (mat_get M2_int i j) / Z2rat D_M2) /\
  4%:Q * quad_spec M1_spec_ij < 105%:Q * quad_spec M2_spec_ij.
```

is `Qed` in `theories/S1/CertRayleigh.v`. A single
`Print Assumptions maynard_M105_certified_rayleigh` reports *Closed
under the global context* and covers (a) the closed-form match
between the FLINT-shipped `M1_int / M2_int` and the readable
paper-form spec `MaynardSpec.M{1,2}_spec_ij` (which transcribes
Maynard's Lemma 8.2 character-for-character), and (b) the strict
Rayleigh-quotient bound at the shipped 42-entry rational witness.
The companion document `AUDITOR_CHECKLIST.md` enumerates the
load-bearing lemmas in audit order.

The whole proof chain is axiom-free: there are no `Admitted`, no
`Axiom`, and no `Parameter` declarations anywhere in
`theories/S1/`. Because every reduction happens in `Z` arithmetic
(`vm_compute` on `list`-of-`list`-of-`Z` matrices and `list (Z*Z)`
vectors), the headline does not even pull in the native 63-bit
primitive-integer interface: no `PrimInt63`, no `Uint63Axioms`, no
`CarryType` appear in `Print Assumptions` output.

The document is written for a reader who is reasonably comfortable
with Rocq/Coq and with undergraduate linear algebra (Rayleigh
quotient, Gram matrix). It aims to explain *how* each layer closes
inside the kernel.

## 1. The problem

### 1.1 The shape of Maynard's argument

Maynard's 2013 proof of bounded gaps between primes proceeds by
constructing a positive weight *f* on *k*-tuples of shifts and
comparing two sums, *J_k(f)* and *I_k(f)*, where *I_k(f)* is an
*L²*-integral over the simplex *R_k* and *J_k(f)* is a partial
integral along one coordinate. Setting

```
M_k := sup_F (k · J_k(F) / I_k(F))
```

over a specified class of symmetric polynomial test functions, Maynard
shows (Proposition 4.3) that *M_k > 4* implies bounded gaps at
parameter *k*. The main theorem (Theorem 1.1) follows by proving

**M_{105} > 4**  (formula 8.15)

This is an inequality between two *I_k*- and *J_k*-integrals
evaluated on a finite-dimensional basis of polynomials *F(x, y)* with
*deg_x F + 2 · deg_y F ≤ 11*. That basis has exactly 42 monomials.
Both *I_k(F)* and *J_k(F)* are quadratic forms in the coefficient
vector, given by 42×42 Gram-style matrices *M_1, M_2 ∈ ℚ^{42×42}* with
entries given by closed-form Beta-function integrals (Maynard's
Lemmas 8.1 / 8.2). Maynard's Lemma 8.3 gives the generalised
Rayleigh-quotient identity

```
M_k = k · sup_F  J_k(F) / I_k(F),
```

so any rigorous lower bound of `4/k` on `sup_F J_k(F)/I_k(F)` yields
`M_k > 4`. Since the supremum is at least the value at any single
*F*, it suffices to exhibit a *single* test function (equivalently,
a single coefficient vector *v ∈ ℚ^{42}*) whose Rayleigh quotient
*vᵀM₂v / vᵀM₁v* exceeds `4/k`.

### 1.2 Why it is "numerical"

The matrices *M_1, M_2* are fully explicit: every entry is a rational
number with denominator bounded by a specific ratio of factorials.
There is no analytic estimate involved — only a finite ℚ-linear-algebra
computation. But:

- *M_1, M_2* are 42×42. Their numerators in common-denominator form
  have up to ~220 decimal digits (`D_M1`, `D_M2` in
  `theories/S1/Witness.v`).
- A rational witness vector *v ∈ ℚ^{42}* requires denominators
  reaching ~14 decimal digits (the eigenvector spans ~14 orders of
  magnitude, which lower-bounds the smallest-denominator rational
  approximation that preserves the Rayleigh inequality).

In Maynard's original proof these computations are done inside a
Mathematica notebook (`Computations.nb`), shipped with the arXiv
submission as supplementary material. Mathematica's kernel is
closed-source, so a successful evaluation is not a formal proof.
For a proof that a Maynard-style argument produces a bounded gap at
the claimed level, the Mathematica computation is the last
remaining informal step in the trust chain. This project replaces
it.

### 1.3 What this project provides

Two stages:

1. A **Python + FLINT layer** (`python/build_certificate.py`,
   `python/flint_probe.py`, `python/build_quad_witness.py`) that
   rebuilds *M_1, M_2* from the closed-form integrals, computes the
   top eigenvector of *M_1^{-1} M_2* at 1024-bit precision, snaps
   each entry to a small-denominator rational via continued-fraction
   convergents, and emits Rocq source files (`Witness.v`,
   `Witness_Rayleigh.v`).

2. A **Rocq 9.1 layer** (`theories/S1/*.v`) that consumes the
   certificate as compile-time data, re-does *every* arithmetic step
   inside the Rocq kernel, and proves the headline theorem.

The Rocq layer does not trust the Python layer. It only takes from
it lists of integers (matrix entries `M{1,2}_int`, the common
denominators `D_M{1,2}`, and the 42 `(num, den) : Z × Z` pairs of
the witness vector). Every algebraic claim about those integers is
then verified by the kernel: the matrix entries are cross-checked
against Maynard's closed forms by `vm_compute` over 1764 + 1764
Z-level cross-multiplications, and the witness vector's Rayleigh
inequality is closed by a single `vm_compute` reflexivity on
`Z`-arithmetic.

The FLINT layer's role is twofold:

- A **second independent implementation** of the same matrices. A
  mismatch between FLINT and the Rocq kernel would catch
  transcription errors or a bug in either toolchain.
- The **candidate data** (the integer matrices and the rational
  witness vector) that the Rocq layer only has to check, not
  re-derive. Finding the witness vector from scratch inside the
  kernel would be infeasible.

This project does not change Maynard's computation; the contribution
is the assurance level.

### 1.4 Why a witness, not an eigenvalue

Maynard's notebook proves the supremum exceeds `4/k` via the
**Rayleigh-quotient route**: Mathematica numerically computes the
top eigenvector *v* of `M_1^{-1} M_2` at high precision, snaps each
entry to a small-denominator rational `RatVec` ≈ *v*, and then
evaluates the *Rayleigh quotient*

```
k · RatVecᵀ M_2 RatVec  /  RatVecᵀ M_1 RatVec
```

in **exact rational arithmetic**. The supremum of `J_k(F)/I_k(F)`
over admissible test functions is at least the quotient at any
individual coefficient vector, so a clear margin at *any* `v` of
choice is a rigorous lower bound. Mathematica's eigenvector routine
is treated as a black box: it only has to be close enough to the
true eigenvector for the rational Rayleigh quotient to clear `4/k`.
The notebook prints `≈ 4.0021`.

This project mechanises exactly that strategy. The Python layer
emits `Witness_Rayleigh.v` containing a 42-entry rational vector
*v_witness*, and the Rocq layer closes the strict inequality
`4 · vᵀM_1 v < 105 · vᵀM_2 v` at *v_witness* in pure `Z`-arithmetic
by a single `vm_compute`. The eigenvector itself is *not* in the
trust base: the Rocq layer only checks the resulting integer
Rayleigh inequality. If the Python layer shipped a vector that
failed the inequality, the kernel `vm_compute` would fail to reduce
to `true` and the build would stop.

The verified slack — `(105 · vᵀM_2 v − 4 · vᵀM_1 v) / vᵀM_1 v` —
is `≈ +2.07 · 10⁻³`, comfortably positive.

## 2. Architecture: candidate generation + kernel verification

The project is two stages. The FLINT layer (§2.1) is the
**candidate generator**: it computes matrix entries and a
Rayleigh-quotient witness, ships them as Rocq source. The Rocq
layer (§2.2) is the **verification**: it consumes that certificate
as untrusted input data and kernel-checks every matrix entry
against an independent Rocq-side closed form (`MaynardVerify`
against `MaynardSpec`) and the Rayleigh inequality at the shipped
witness against pure-Z arithmetic (`CertRayleigh`). Only the Rocq
layer's Qeds are in the trust base; the FLINT layer is auxiliary.

### 2.1 The FLINT layer (candidate generator)

Run with `python python/build_certificate.py` (for the matrix data)
and `python python/build_quad_witness.py` (for the witness vector).
The pipeline performs:

1. Build *M_1, M_2 ∈ ℚ^{42×42}* from the Mathematica formulas, cached
   in `python/m1m2.pkl`. Full audit: all 3 528 entries agree with
   closed-form Beta integrals.
2. Clear denominators: produce `M1_int, M2_int : list[list[int]]`
   and scalars `D_M1, D_M2` such that
   `(M_l)[i][j] = M_l_int[i][j] / D_M_l`.
3. Compute the top eigenvector of `M_1^{-1} M_2` at 1024-bit
   precision via `acb_mat.eig` (Arb interval arithmetic),
   phase-aligned (largest entry positive real).
4. Snap each entry to a small-denominator rational via
   Mathematica-style absolute-tolerance `Rationalize` with
   `tol = 10⁻¹⁴` (continued-fraction convergents).
5. Verify in exact rationals: `vᵀM_1 v > 0` and
   `(105 · vᵀM_2 v − 4 · vᵀM_1 v) / vᵀM_1 v ≈ +2.07 · 10⁻³`.
6. Emit `theories/S1/Witness.v` (matrix entries and basis) and
   `theories/S1/Witness_Rayleigh.v` (42-entry rational witness).

Both `.v` files are autogenerated and checked into the repository so
that the Rocq build does not need Python.

### 2.2 The Rocq layer (verification)

The Rocq layer consumes:

- `M1_int`, `M2_int` and the denominators `D_M1`, `D_M2` (in
  `Witness.v`).
- The 42-entry rational witness `v_witness : list (Z × Z)` (in
  `Witness_Rayleigh.v`).

It verifies, in this order:

1. The 42-pair basis enumeration matches Maynard's
   `{(b, c) ∈ ℕ² : b + 2c ≤ 11}` (`MaynardBasis`).
2. The shipped 42×42 integer matrices match Maynard's closed-form
   spec entry-by-entry, modulo the common denominators
   (`MaynardVerify` + `MaynardSpecBridge`, composed by `Cert`).
3. The integer Rayleigh inequality
   `4 · D_M2 · v_numᵀ M1_int v_num < 105 · D_M1 · v_numᵀ M2_int v_num`
   holds at the integer-rescaled witness `v_num` (`CertRayleigh`).
4. The integer inequality lifts to the rat-level Rayleigh bound at
   the paper-form spec matrices, i.e. the headline
   `CertRayleigh.maynard_M105_certified_rayleigh`.

## 3. The Rocq tree, file by file

The dependency order is exactly the order of `_CoqProject`. There
are **20 `.v` files** under `theories/S1/` (including the seven
files in the `MaynardVerify/` parallel-chunk subdirectory), totaling
**9 590 lines** under `theories/S1/`, of which `Witness.v` alone
accounts for ~5 700 lines of autogenerated matrix-entry data.

### 3.1 Scaffolding and certificate data

**`Recompose.v`**. Defines `lift_bigZ : list BigZ.t_ -> list Z`.
Legacy helper retained for `Witness.v` parsing speed.

**`Witness.v`** (autogenerated). The matrix certificate: the
42-element `basis`, the integer matrices `M1_int, M2_int`, their
denominators `D_M1, D_M2`. The additional fields shipped by the
FLINT pipeline (the integer matrix `A_int`, the scalars `D_A` and
`D_q`, and the cleared char-poly coefficient lists) are unused by
the headline: no downstream file imports them. Large integers are
written as `bigZ` to keep parser time manageable.

**`Witness_Rayleigh.v`** (autogenerated). The Rayleigh-quotient
certificate: a single definition
`v_witness : list (Z * Z)` listing the 42 `(num, den)` pairs of the
rational witness vector, in the same row/column order as the
`MaynardBasis.maynard_basis` enumeration. The file header documents
the provenance (1024-bit Arb eigenvector,
absolute-tolerance Rationalize), the verification statistics
(max denominator `67 213 321 643 309 ≈ 1.4 · 10¹³`, ~14 decimal
digits / 46 bits; verified slack `≈ +2.07 · 10⁻³`), and the
ill-conditioning warning that motivated the precision choice.

### 3.2 Core libraries

**`IntPoly.v`**. Defines `pol := list Z` and a few polynomial
operations. Retained as a dependency of `CharPoly.v` (below); the
polynomial-side operations are not consumed by the
Rayleigh-quotient route.

**`IntMat.v`**. Defines `mat := list (list Z)`, row-major, no
well-formedness invariant. Operations: `mzero`, `meye`, `madd`,
`mscale`, `mmul`, `mtrans`, `mtrace`, `mat_get`, plus length
lemmas. All theorems go through list induction; nothing is imported
from MathComp. The reason is that `'M[R]_42` does not reduce under
`vm_compute` at the sizes we need, but nested `list (list Z)` does
(a 42×42 matrix multiplication takes ~0.14 s by `vm_compute`).

**`CharPoly.v`**. This file contributes only the Z to rat /
Z to int bridging definitions consumed downstream:
`Z_to_int : Z -> int`, the `Z2rat` embedding wrapper, the basic
arithmetic morphism lemmas (`Z_to_int_add`, `Z_to_int_mul`, etc.),
and `mat_int_to_rat`. The historical Faddeev–LeVerrier recurrence
and its correctness proof remain in the file for completeness but
are not transitively reached from `CertRayleigh.v`'s `Require Import`s.

### 3.3 Maynard input verification (M1, M2)

The five files `MaynardFactQ.v`, `MaynardBasis.v`, `MaynardSpec.v`,
`MaynardVerify.v`, `MaynardSpecBridge.v` close the trust loop on the
42x42 input matrices. They sit downstream of `Witness.v`. `Cert.v`
imports `MaynardVerify` and `MaynardSpecBridge`; both feed the
composed rat-level identity inside `M{1,2}_spec_eq_int`: the Z-level
cross-multiplication bool facts `all_match_M{1,2}Z_true` plus the
rat-to-Z bridges `M{1,2}_spec_rat_eq` are lifted to a single rat
equality `M{1,2}_spec_ij = Z2rat (mat_get M{1,2}_int i j) /
Z2rat D_M{1,2}` by a `qfrac_eq_div` helper local to `Cert.v`.
The Z-level checks and the Z-to-rat bridges remain available as
standalone Qeds for auditors who want to trace the chain
step-by-step.

A companion document `SPEC_TO_PAPER.md` at the repo root maps every
definition in `MaynardSpec.v` (`compositions`, `cff`, `G_2`,
`alpha`, `M1_entry`, `M2_entry`) to specific lines of
arXiv:1311.4600 v3 §8.

**`MaynardFactQ.v`** (~25 lines). Tiny rat-level wrappers
`factQ n := n!%:R : rat`, `binQ n k := 'C(n, k)%:R : rat`, and a
couple of helper lemmas (`factQ_neq0`, `factQ_succ`).

**`MaynardBasis.v`** (~85 lines). Rebuilds the 42-element basis
`{(b, c) in nat * nat : b + 2c <= 11}` in the Mathematica
enumeration order used in `Witness.v`, and pins it to the canonical
predicate via three Qed lemmas:

```rocq
Lemma maynard_basis_size : length maynard_basis = 42.
Lemma maynard_basis_uniq : uniq maynard_basis.
Lemma maynard_basis_spec : forall p,
  (p \in maynard_basis) = (p.1 + 2 * p.2 <= 11)%N.
Lemma maynard_basis_eq_witness :
  maynard_basis = Witness.basis.
```

`maynard_basis_spec` + `maynard_basis_uniq` + `maynard_basis_size`
together certify that `maynard_basis` is *exactly* the multiset
`{(b, c) in nat^2 : b + 2c <= 11}` — a reviewer never has to read
the 42-pair literal. The proof goes via a canonical
`[seq p <- allpairs ... | p.1 + 2*p.2 <= 11]` and a `vm_compute`-Qed
`perm_eq` lemma; the residual `2c <= 11 ==> c < 6` step is closed by
`lia` (mczify).

**`MaynardSpec.v`** (~255 lines). Transcribes Maynard's closed forms:

- `G_2 n k : rat`: the polynomial
  `G_{n,2}(k) = n! * Sum_{r=1}^{n} C(k, r) * Sum_{a in compositions(r, n)} cff(a)`
  from Lemma 8.1 (= v1 Lemma 7.1), where `compositions r n`
  enumerates the length-r compositions of n with parts >= 1, and
  `cff a := Prod (2 b_i)!/b_i!` is the per-composition inner factor.
- `M1_entry bi ci bj cj : rat = b!/(105+b+2c)! * G_2 c 105` where
  `b = bi+bj`, `c = ci+cj`.
- `alpha b c cp : rat`, the eq. 8.8 expansion coefficient.
- `M2_entry bi ci bj cj : rat`: a double sum over
  `(cp1, cp2) in [0, ci] x [0, cj]` of
  `alpha(bi, ci, cp1) * alpha(bj, cj, cp2) * bsum!/(104+bsum+2*csum)! * G_2 csum 104`.

The file also provides Z-level twins `m1_num_den_at`,
`m2_num_den_at : nat -> nat -> Z * Z` that compute the same rationals
as a (numerator, denominator) pair of integers.

**`MaynardVerify/Def.v`** (~130 lines). Definitions plus the fast
M1 cross-check:

```rocq
Definition M1_entry_matchZ (i j : nat) : bool :=
  Z.eqb (m1_num i j * D_M1) (mat_get M1_int i j * m1_den i j).

Definition all_match_M1Z : bool :=
  forallb (fun i => forallb (fun j => M1_entry_matchZ i j) (seq 0 42))
          (seq 0 42).

Lemma all_match_M1Z_true : all_match_M1Z = true.
Proof. vm_compute. reflexivity. Qed.
```

Same shape for M2's `M2_entry_matchZ` / `all_match_M2Z`, but the
M2 check is split into six row-range chunks
(`MaynardVerify/M2_0.v` ... `M2_5.v`, 7 rows each) so `make -j` runs
them concurrently. **`MaynardVerify.v`** (~105 lines) is the
assembly: it imports `Def` plus the six chunks and proves
`all_match_M2Z_true` via `seq_split_42` + `forallb_app` from the
six chunk Qeds — no new `vm_compute`.

The cross-check is at the Z level (`num * D = M_int * den`) rather
than the rat level: closing the rat-level matrix equality at
concrete dim 42 triggers MathComp HB canonical-structure
elaboration stalls, while adding no numerical content beyond the
bool facts.

**Timing**: M1 is a single ~90 s `vm_compute` Qed. M2 is split into
six 7-row chunks (`MaynardVerify/M2_<k>.v`) so `make -j` runs them
concurrently; on a 16 GB / 6-thread machine each chunk finishes in
~6–18 minutes of CPU but the chunks overlap, putting the headline
cold-build wall time at ~25–30 minutes with `make -j6`.

**`MaynardSpecBridge.v`** (~615 lines). Kernel-Qed bridge between
Part A (rat-level, paper-shaped) and Part B (Z-level,
`vm_compute`-shaped) of `MaynardSpec.v`:

```rocq
Theorem M1_spec_rat_eq (i j : nat) :
  M1_spec_ij i j = qfrac (m1_num_den_at i j).

Theorem M2_spec_rat_eq (i j : nat) :
  M2_spec_ij i j = qfrac (m2_num_den_at i j).
```

where `qfrac (n, d) := (Z_to_int n)%:~R / (Z_to_int d)%:~R : rat`
reads a (numerator, denominator) ℤ-pair as a rational. Both
theorems are `Qed` and `Print Assumptions` reports *Closed under
the global context* — no axioms, no `Uint63` primitives. The
bridge is layered through `factZ_to_rat`, `dblratZ_to_rat`,
`binZ_to_rat`, `compositionsZ_eq_compositions`, `G2Z_to_rat`,
`qfrac_qmul`, `qfrac_qplus`, and `alphaZ_to_rat`.

### 3.4 The slim auditor bridge

**`Cert.v`** (65 lines). Combines the Z-level bool match from
`MaynardVerify` with the rat-to-Z bridge from `MaynardSpecBridge`
into the per-entry composed identity that the headline surfaces:

```rocq
Lemma M1_spec_eq_int {i j} :
  (i < 42)%nat -> (j < 42)%nat ->
  M1_spec_ij i j = Z2rat (mat_get M1_int i j) / Z2rat D_M1.

Lemma M2_spec_eq_int {i j} :
  (i < 42)%nat -> (j < 42)%nat ->
  M2_spec_ij i j = Z2rat (mat_get M2_int i j) / Z2rat D_M2.
```

Both proofs use a thin `qfrac_eq_div` lifting helper:
`a * d = c * b` in ℤ with `b, d > 0` implies
`qfrac (a, b) = Z2rat c / Z2rat d` in ℚ. The Z-level cross-product
is extracted per-entry from `M{1,2}_entry_match_in_grid` (a
forallb-membership lemma), and denominator positivity from
`m{1,2}_num_den_at_den_pos` and `D_M{1,2}_pos` (both `vm_compute`).

### 3.5 The Rayleigh-quotient witness route

**`CertRayleigh.v`** (438 lines). The headline file. Structure in
sections:

- *Section 1 — integer reduction of v_witness.* Defines
  `v_den := fold_left lcm` over the witness denominators, and
  `v_num := map (fun (n, d) => n * (v_den / d)) v_witness`. After
  scaling, `v_witness[i] = v_num[i] / v_den` for every `i`.
- *Section 2 — integer quadratic forms.* Defines `row_dot`,
  `mat_vec_mul`, and `quad M v := vᵀ M v` on `list Z`. The integer
  Rayleigh numerators are `num_M1 := quad M1_int v_num` and
  `num_M2 := quad M2_int v_num`.
- *Section 3 — the integer inequalities (vm_compute Qeds).* The key
  reduction-by-reflexivity lemmas:

  ```rocq
  Lemma rayleigh_witness_M1_positive : 0 < num_M1.
  Proof. vm_compute. reflexivity. Qed.

  Lemma rayleigh_witness_holds :
    4 * D_M2 * num_M1 < 105 * D_M1 * num_M2.
  Proof. vm_compute. reflexivity. Qed.
  ```

  Both reduce in pure `Z`-arithmetic. *Closed under the global
  context*: no `Uint63` primitives. The integer inequality is
  equivalent (after clearing the common denominator `D_M_l *
  v_den^2` on both sides) to the strict Rayleigh-quotient bound
  `4 * vᵀM_1 v < 105 * vᵀM_2 v` on the FLINT integer matrices.

- *Section 4 — rat-level Rayleigh-quotient bound.* Defines the
  rat-level numerators against the paper-form spec via a bigop:

  ```rocq
  Definition v_rat (i : nat) : rat :=
    Z2rat (List.nth i v_num BinInt.Z0) / Z2rat v_den.

  Definition quad_spec (M_spec : nat -> nat -> rat) : rat :=
    \sum_(i < 42) \sum_(j < 42)
      v_rat i * M_spec i j * v_rat j.
  ```

- *Section 5 — Z to rat bridge for the Rayleigh-quotient sum.* The
  load-bearing structural lemmas. `Z2rat_quad_eq_sum` recasts
  `Z2rat (quad M v_num)` as the rat-level bigop on `nth` of `M`
  and `v_num`, via structural induction on the `row_dot` /
  `mat_vec_mul` chain. All `Qed`, *Closed under the global
  context*.

- *Section 6 — well-formedness.* `M{1,2}_int_rows`,
  `M{1,2}_int_cols`, `v_num_length`, plus positivity wrappers for
  the denominators. All by `vm_compute`.

- *Section 7 — Rayleigh-quotient identity for M_spec.* The
  Qed-sealed per-cell algebraic identity (heavy `field` call kept
  out of the inner per-cell goal):

  ```rocq
  Lemma quad_cell_identity (dm vd vi mij vj : rat) :
    vd != 0 -> dm != 0 ->
    dm * vd^+2 * (vi / vd * (mij / dm) * (vj / vd)) = vi * mij * vj.
  ```

  Then the rat-level bigop bridge:

  ```rocq
  Lemma quad_spec_eq_Z (M_spec : nat -> nat -> rat) (M_int : list (list Z))
                       (D_M : Z) ... :
    Z2rat D_M * Z2rat v_den ^+ 2 * quad_spec M_spec =
    Z2rat (quad M_int v_num).
  ```

  Structurally a `Z2rat_quad_eq_sum` invocation followed by two
  nested `eq_bigr` applications of `quad_cell_identity` to clear
  denominators. Qed-sealing the per-cell identity keeps the
  bigop walk referring to it by name instead of inlining the
  `field` proof term under each of the 42·42 = 1764 binders, so
  the closure is small enough for the kernel. `Qed`, *Closed
  under the global context*.

  The two specialisations `quad_M{1,2}_spec_eq_Z` apply
  `quad_spec_eq_Z` with the matrix-side hypotheses discharged by
  `M{1,2}_int_rows`, `M{1,2}_int_cols`, `D_M{1,2}_pos`, and
  `@M{1,2}_spec_eq_int`.

- *Section 8 — strict Rayleigh-quotient bound at v_witness.*
  `Z2rat_pos` and `Z2rat_lt` lift the integer inequality to ℚ
  (`rayleigh_witness_holds_rat`). The abstract lift
  `rayleigh_lift_generic` then takes two scaled-quad identities
  `Z2rat d_k · v² · q_k = Z2rat a_k` (k = 1, 2) plus the integer
  comparison `4·d2·a1 < 105·d1·a2` and concludes `4·q1 < 105·q2`.
  Abstracting `q1`, `q2`, `v`, and the integer scalars keeps the
  two interior `ring` calls operating on tiny abstract scalars
  rather than the concrete `quad_spec M{1,2}_spec_ij` bigops, so
  the proof term stays small for kernel checking. The headline
  shim is then a one-liner:

  ```rocq
  Lemma rayleigh_lt_main : 4%:Q * quad_spec M1_spec_ij <
                           105%:Q * quad_spec M2_spec_ij.
  Proof.
    exact: (rayleigh_lift_generic D_M1_pos D_M2_pos
                                  (Z2rat_pos v_den_pos)
                                  quad_M1_spec_eq_Z quad_M2_spec_eq_Z
                                  rayleigh_witness_holds_rat).
  Qed.
  ```

  Both `rayleigh_lift_generic` and `rayleigh_lt_main` are `Qed`
  and *Closed under the global context*.

- *Section 9 — headline.* Three-way `split` over `M{1,2}_spec_eq_int`
  and `rayleigh_lt_main`.

## 4. Trust base

`Print Assumptions maynard_M105_certified_rayleigh` after `coqc` of
`CertRayleigh.v` reports a single line: *Closed under the global
context*. The whole proof chain is axiom-free.

This is stronger than the typical "vm_compute Qed" footprint: the
matrices and the witness vector are encoded as `list (list Z)` and
`list (Z × Z)` rather than as native 63-bit packed arrays, so
`vm_compute` reduces them through Rocq's `Z` arithmetic instead of
through the `PrimInt63` / `Uint63Axioms` / `CarryType` kernel
primitives. None of those primitives appear in the headline's
assumptions.

**A reviewer who trusts:**

1. The Rocq 9.1 kernel's type-checking algorithm.
2. `coqc`'s handling of `vm_compute`. (The project does not use
   `native_compute` anywhere.)

obtains, as output, a certified strict Rayleigh-quotient bound on
the paper-form spec matrices at the shipped 42-entry rational
witness, together with the closed-form match of those matrices to
Maynard's specification.

**The FLINT layer is outside the trust base.** The Rocq proof never
invokes Python and never loads the JSON certificate directly; the
autogenerated `Witness.v` and `Witness_Rayleigh.v` are ordinary Rocq
files. If the FLINT layer shipped incorrect data, one of the
following `vm_compute`-based checks would fail to reduce to `true`
and the build would stop:

- `MaynardVerify.Def.all_match_M1Z_true`,
  `MaynardVerify.all_match_M2Z_true` — the 42x42 input matrices
  match Maynard's closed form (Lemma 8.2 / eq. 8.4).
- `CertRayleigh.rayleigh_witness_M1_positive` — the integer
  positivity `v_numᵀ M1_int v_num > 0`.
- `CertRayleigh.rayleigh_witness_holds` — the integer Rayleigh
  inequality at the shipped witness.

Each of these is `Qed` and reduces in pure kernel arithmetic. The
file `MaynardBasis.maynard_basis_eq_witness` further verifies that
the basis enumeration in `Witness.basis` matches the canonical
spec (`vm_compute` Qed).

## 5. Numerical highlights

- **Matrix dimension.** 42x42. Maynard's *M_{105}* construction
  uses 42 basis polynomials `{x^b * y^c : b + 2c <= 11}`.
- **Denominators.** `D_M1` has ~221 decimal digits, `D_M2` ~227.
  Both are strictly positive (`vm_compute`).
- **Witness denominators.** The 42 rational entries of `v_witness`
  have denominators up to `67 213 321 643 309 ≈ 1.4 * 10^13` (~14
  decimal digits, 46 bits). The smallest non-zero `|v_i|` is
  `≈ 10^-14` and the largest is `≈ 1`, so the eigenvector spans
  ~14 decimal orders of magnitude — this lower-bounds the
  denominator size, since truncating small components destroys the
  inequality.
- **Verified slack.**
  `(105 * vᵀM_2 v - 4 * vᵀM_1 v) / vᵀM_1 v  ≈  +2.07 * 10^-3`.
- **Build time.** A clean rebuild on a 16 GB / 6-thread machine
  takes **~25–30 min wall with `make -j6`**. The dominant cost is
  the six `MaynardVerify/M2_0..5.v` chunks (`vm_compute` over 1764
  entries each summing up to 36 rational terms); under `make -j6`
  they run concurrently. The new `CertRayleigh.rayleigh_witness_holds`
  Qed adds ~5 s.
- **Total Rocq proof size.** 20 `.v` files (13 top-level +
  7 files in the `MaynardVerify/` parallel-chunk subdirectory),
  9 590 lines under `theories/S1/`; `Witness.v` alone is ~5 700
  lines of autogenerated certificate data.

## 6. Map of key lemmas and files

```
Item 1 (basis is exactly {(b,c) : b + 2c <= 11})
  MaynardBasis.v   maynard_basis_size, _uniq, _spec, _eq_witness

Items 2-4 (input matrices match Maynard's closed form)
  MaynardVerify.v   all_match_M2Z_true (chunks M2_0..5)
  MaynardVerify/Def.v   all_match_M1Z_true
  MaynardSpec.v   G_2, M1_entry, M2_entry (closed forms)
  MaynardSpecBridge.v   M{1,2}_spec_rat_eq (rat = qfrac of a Z-pair)
  Cert.v   M{1,2}_spec_eq_int (composed rat-level identity)
  Witness.v   provides M1_int, M2_int, D_M1, D_M2, basis

Item 5 (strict Rayleigh-quotient bound at v_witness)
  Witness_Rayleigh.v   v_witness (42 (num, den) pairs, slack ≈ +2.07e-3)
  CertRayleigh.v   rayleigh_witness_M1_positive, rayleigh_witness_holds
              (both vm_compute Qed, Closed under global context)
  CertRayleigh.v   quad_cell_identity, quad_spec_eq_Z,
              rayleigh_lift_generic, rayleigh_lt_main
              (rat-level lift, all Qed, Closed under global context)

Headline (composes items 4 + 5):
  CertRayleigh.v   maynard_M105_certified_rayleigh
    = (forall i j, M1_spec_ij i j = Z2rat M1_int[i,j] / Z2rat D_M1)
      /\ (forall i j, M2_spec_ij i j = Z2rat M2_int[i,j] / Z2rat D_M2)
      /\ 4%:Q * quad_spec M1_spec_ij < 105%:Q * quad_spec M2_spec_ij
```

The dependency graph is linear: `Witness` + `Witness_Rayleigh` to
`MaynardFactQ` / `MaynardBasis` / `MaynardSpec` to `MaynardVerify` /
`MaynardSpecBridge` to `Cert` to `CertRayleigh`. There is no separate
char-poly backbone.

Everything lives behind a single Rocq `Require` — `Require Import
PrimeGapS1.CertRayleigh.` loads the full proof.
