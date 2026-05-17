# Maynard `M_{105} > 4` — A Rocq-audited proof

This document explains the structure of the Rocq formalisation that closes
the numerical step in James Maynard's *Small gaps between primes*
(arXiv:1311.4600; Annals of Mathematics **181** (2015), 383–413). The headline
theorem

```rocq
Theorem maynard_eigenvalue_S1 :
  exists lambda : realalg,
    eigenvalue (map_mx (ratr : rat -> realalg) A_rat) lambda
    /\ (ratr (4%:Q / 105%:Q) : realalg) < lambda.
```

is `Qed` in `theories/S1/Cert.v`. A sibling theorem
`maynard_M105_certified` in the same file conjoins this eigenvalue claim
with two readable rat-level identities stating that the paper-form spec
`MaynardSpec.M{1,2}_spec_ij` equals the FLINT integer entry over the
common denominator `D_M{1,2}`, so a single
`Print Assumptions maynard_M105_certified` (which reports 51 standard
`PrimInt63.*` / `Uint63Axioms.*` kernel primitives — no project-specific
axioms) covers the full chain: the FLINT-shipped integer matrices match
the rat-level paper-form spec entry-by-entry over a common denominator,
and the eigenvalue bound holds. The Z-level cross-multiplication checks
and the rat↔Z bridge are now proof-internal implementation details;
they remain available as standalone Qeds
(`MaynardVerify.all_match_M{1,2}Z_true` and
`MaynardSpecBridge.M{1,2}_spec_rat_eq`) for auditors who want to trace
the closed-form match step-by-step.
Either theorem exposes only the standard `PrimInt63` / `Uint63Axioms`
kernel primitives shipped with Rocq 9.0/9.1 (native 63-bit integers, used
by `vm_compute` on the CRT and char-poly computations).

The repository contains zero `Axiom` declarations and zero `Admitted`
lemmas anywhere — including the 42x42 input matrices `M1_int`, `M2_int`,
which are themselves kernel-checked against Maynard's closed-form
specification (Lemma 8.2 / eq. 7.8). The FLINT generator's transcription
is therefore not part of the trust base; the Rocq kernel re-derives every
algebraic claim from the integer data alone. The companion document
`AUDITOR_CHECKLIST.md` at the repo root enumerates the load-bearing
lemmas in audit order.

The document is written for a reader who is reasonably comfortable with
Rocq/Coq and with undergraduate algebra (characteristic polynomial,
intermediate value theorem on a real-closed field, CRT,
Faddeev–LeVerrier). It aims to explain *how* each layer closes and, in
particular, the four techniques that were essential to getting the
proof past the kernel within a reasonable time budget.

## 1. The problem

### 1.1 The shape of Maynard's argument

Maynard's 2013 proof of bounded gaps between primes proceeds by constructing
a positive weight *f* on *k*-tuples of shifts and comparing two sums,
*J_k(f)* and *I_k(f)*, where *I_k(f)* is an *L²*-integral over the simplex
*R_k* and *J_k(f)* is a partial integral along one coordinate. Setting

```
M_k := sup_f (k * J_k(f) / I_k(f))
```

over a specified class of symmetric polynomial test functions, Maynard shows
(Proposition 4.3) that *M_k > 4* implies bounded gaps at parameter *k*. The
main theorem (Theorem 1.1) follows by proving

**M_{105} > 4** (formula 8.15)

This is an inequality between two *I_k*- and *J_k*-integrals evaluated on a
finite-dimensional basis of polynomials *F(x,y)* with *deg_x F + 2·deg_y F ≤
11*. That basis has exactly 42 monomials. Both *I_k(F)* and *J_k(F)* are
linear in the coefficient vector and (symmetric) positive-definite in the
appropriate sense, so

```
sup_F (J_k(F) / I_k(F)) = lambda_max(M1^(-1) * M2)
```

where *M1, M2 ∈ ℚ^{42×42}* are Gram-style matrices whose entries are given
by closed-form Beta-function integrals (see `notebook_reconstructed.md`
§2–§3). The claim *M_{105} > 4* becomes

```
lambda_max(M1^(-1) * M2) > 4/105.
```

### 1.2 Why it is "numerical"

The matrices *M1, M2* are fully explicit: every entry is a rational number
with denominator bounded by a specific ratio of factorials. There is no
analytic estimate involved — only a finite ℚ-linear-algebra computation.
But the computation is non-trivial:

- *M1, M2* are 42×42. Their numerators in common-denominator form have up
  to ~220 decimal digits (`D_M1`, `D_M2` in `theories/S1/Witness.v`).
- The characteristic polynomial of *A = M1^(-1)·M2* in cleared form has
  coefficients up to ~20 000 bits.
- Running Faddeev–LeVerrier directly on the integer matrix `A_int`
  inside the Rocq kernel would touch intermediate values with similar
  magnitudes; the project instead does a 710-prime CRT cross-check
  against a FLINT-shipped candidate polynomial (§3.6).

In Maynard's original proof these computations are done inside a
Mathematica notebook (`Computations.nb`), shipped with the arXiv
submission as supplementary material. The notebook source is fully
readable, but its evaluation depends on Mathematica's closed-source
kernel — which is not a formal proof system, so a successful evaluation
is not a kernel-level proof. For a proof that a Maynard-style argument
produces a bounded gap at the claimed level, the Mathematica computation
is the last remaining informal step in the trust chain. This project
replaces it.

### 1.3 What this project provides

Two *independent* verification layers:

1. A **Python + FLINT layer** (`python/build_certificate.py`,
   `python/flint_probe.py`) that rebuilds *M1, M2* from the closed-form
   integrals, computes *A* and its characteristic polynomial over exact
   rationals (via `python-flint`, i.e. GMP/MPFR), and emits a JSON
   certificate.

2. A **Rocq 9.0/9.1 layer** (`theories/S1/*.v`) that consumes the
   certificate as compile-time data, re-does *every* arithmetic step
   inside the Rocq kernel, and proves the headline theorem at the level
   of MathComp's abstract `eigenvalue` predicate.

The Rocq layer does not trust the Python layer. It only takes from it a
list of integers (matrix entries and the shipped char-poly
coefficients). Every algebraic claim about those integers is then
verified by the kernel, either by `vm_compute` (on modular and BigZ
data) or by ordinary `Qed` proofs (on MathComp algebra).

The FLINT layer's role is threefold:

- A **second independent implementation** of the same computation. A
  mismatch between FLINT and the Rocq kernel would catch transcription
  errors or a bug in either toolchain.
- The **candidate data** (the shipped char-poly coefficients) that the
  Rocq layer only has to check, not re-derive. Finding these objects
  from scratch inside the kernel would be infeasible.
- A cross-check via Arb (256-bit interval arithmetic): top eigenvalue
  ≈ 0.038114950113695686, so 105·λ ≈ 4.002069761938047. This matches
  Mathematica's value to >12 decimal digits.

This project does not change Maynard's computation; the contribution is
the assurance level.

### 1.4 Two distinct certificates for the same fact

Maynard's notebook and our Rocq layer prove the same inequality
`λ_max(M₁⁻¹M₂) > 4/k` (which gives `M_k > 4` via Lemmas 8.2 + 8.3 in
the paper) by **different routes**, neither of which requires the
other.

- **Maynard's notebook** uses the eigenvector route: Mathematica
  numerically computes the top eigenvector *v* of `M₁⁻¹M₂` at
  150-decimal precision, snaps each entry to a small-denominator
  rational `RatVec` ≈ *v*, and then evaluates the *Rayleigh quotient*
  ```
  k · RatVecᵀ M₂ RatVec  /  RatVecᵀ M₁ RatVec
  ```
  in **exact rational arithmetic**. For *any* nonzero *a*,
  `aᵀM₂a / aᵀM₁a ≤ λ_max(M₁⁻¹M₂)`, so this is a true rigorous lower
  bound on `λ_max`. Mathematica's eigenvector routine is treated as
  a black box: it only has to be close enough to the true eigenvector
  for the rational Rayleigh quotient to clear `4/k`. The notebook
  prints `≈ 4.0021`.

- **Our Rocq proof** uses the characteristic-polynomial route: the
  intermediate value theorem on `char_poly(M₁⁻¹M₂)` certifies the
  *existence* of a real root (= eigenvalue) strictly above `4/105`,
  from the sign of the polynomial at `4/105` (negative, by direct
  `vm_compute`) and at MathComp's `cauchy_bound` (positive, from the
  leading coefficient). No eigenvector is ever constructed. The
  argument bypasses the Rayleigh quotient entirely and works purely
  on the polynomial side.

Both strategies fit Maynard's §8 framework. Lemma 8.2 (the closed
form for the matrix entries) is verified inside Rocq
(`MaynardVerify`); Lemma 8.3 (the generalised Rayleigh-quotient
identity that gives `M_k = k · λ_max`, plus its hypotheses
`M_1 ≻ 0` and `M_2 = M_2ᵀ`) is *not* formalised here —
its Maynard-style use in the notebook (eigenvector → Rayleigh
quotient) and our IVT-on-char-poly alternative both invoke its
*conclusion* "max ratio = largest eigenvalue", which is needed in
either strategy to bridge `λ > 4/k` to `M_k > 4`. The analytic content
of Lemma 8.3 remains paper-side, by design of this project's scope
(replace the Mathematica computation, not Maynard's paper). The
notebook's Rayleigh-quotient lower bound *also* relies on `M_1 ≻ 0`
implicitly, so the Rocq layer's trust contract on this point is
exactly the same as the notebook's.

## 2. Architecture: candidate generation + kernel verification

The project is two stages, not two co-equal verification layers.
The FLINT layer (§2.1) is the **candidate generator**: it computes a
JSON certificate (matrices, char poly) and ships it as Rocq source.
The Rocq layer (§2.2) is the **verification**: it consumes that
certificate as untrusted input data and kernel-checks every entry
against an independent Rocq-side derivation (entry-by-entry matrix
match against Maynard's closed forms, 710-prime CRT against an
in-Rocq Faddeev–LeVerrier on `A_int`, etc.). Only the Rocq layer's
Qeds are in the trust base; the FLINT layer is auxiliary.

### 2.1 The FLINT layer (candidate generator)

Run with `python python/build_certificate.py`. The script performs:

1. Build *M1, M2 ∈ ℚ^{42×42}* from the Mathematica formulas, cached in
   `python/m1m2.pkl`. Sanity-check a dozen entries against closed-form Beta
   integrals. Full audit: all 3 528 entries agree with closed-form values.
2. Clear denominators: produce `M1_int, M2_int : list[list[int]]` and
   scalars `D_M1, D_M2` such that `(M_l)[i][j] = M_l_int[i][j] / D_M_l`.
3. Form `A_flint = M1^(-1) * M2` in `fmpq_mat`; clear denominators to get
   `A_int, D_A` with `A = A_int / D_A`.
4. Compute `charpoly_of_A_int` = clear-denominator form of
   `chi_A(x) = det(xI - A)`, with a separate scalar `D_q`: each
   coefficient of `D_q * chi_A` is an integer.
5. Cross-check *lambda_max* against an `arb_mat` computation at 256-bit
   precision.
6. Write `python/certificate.json` (~510 KB metadata).

The translator `python/json_to_v.py` converts the JSON into Rocq sources:
`Witness.v` (matrix entries, char poly as `list Z` and `list BigZ`).
The file is autogenerated and checked into the repository so that the
Rocq build does not need Python.

### 2.2 The Rocq layer (verification)

The Rocq layer consumes:

- `M1_int`, `M2_int`, `A_int` and the denominators `D_M1`, `D_M2`,
  `D_A`, `D_q` (in `Witness.v`).
- `charpoly_int` (the cleared char-poly of *A* at the `D_q` level) and
  `charpoly_of_A_int` (char-poly of the integer matrix `A_int` directly
  — these are related by a known scaling factor).

It verifies, in this order:

1. There is a real algebraic root of `charpoly_int` above `4/105`,
   established by `poly_ivtoo` from `P(4/105) < 0` (direct
   `vm_compute` on `sign_at_rat charpoly_int 4 105`) and
   `P(cauchy_bound) > 0` (from leading-coefficient positivity).
2. `char_poly_int A_int = charpoly_of_A_int` as lists of `Z` (proved
   via CRT over 710 Uint63 primes).
3. `pol_to_polyrat charpoly_int = D_q *: char_poly A_rat` in
   `{poly rat}`, where `A_rat : 'M[rat]_42` is the MathComp-level
   rational matrix.
4. Therefore any root of `charpoly_int` is a root of
   `char_poly A_rat` after clearing the nonzero scalar `D_q`; by
   `eigenvalue_root_char` + `map_char_poly` that root is an
   eigenvalue of `A_rat` over `realalg`.

### 2.3 An alternative route: the `quad` branch (pencil determinant)

The `quad` branch ships an independent proof of
`maynard_M105_certified_pencil` (in `theories/S1/CertPencil.v`) that
substitutes the 43-coefficient CRT comparison of step 2 with a
**single-coefficient** comparison on the constant term of two integer
matrices, then derives the sign of `(char_poly A_rat).[4/105]` via
Agent A's pencil identity

```
\det (l *: M1 - M2) = \det M1 * (char_poly (M1^-1 *m M2)).[l].
```

Specialising `M1 := M1_rat`, `M2 := M2_rat`, `l := 4/105` and clearing
denominators reduces the eigenvalue bound to the sign of two integer
determinants:

* `det(M1_int)` — 2044 bits, positive — closed via the 710-prime CRT
  product (`crt_product_710` in `CRTLift.v`).
* `det(pencil_int_clean)` — 2613 bits, negative — closed via the
  **same** 710-prime CRT product.  Here
  `pencil_int_clean := D_pencil_clean · (4·M1_rat − 105·M2_rat)` is
  the *clean* integer pencil: `D_pencil_clean` is the LCM of the
  denominators of `4·M1_rat − 105·M2_rat` (689 bits, roughly half of
  `D_M1·D_M2` = 1368 bits), so the resulting determinant is 2613 bits
  rather than the 31131 bits of the naively scaled
  `4·D_M2·M1 − 105·D_M1·M2`.  The per-entry cross-check
  `D_M1·D_M2·pencil_int_clean[i,j] =
  D_pencil_clean·(4·D_M2·M1_int[i,j] − 105·D_M1·M2_int[i,j])` is
  closed by a single 1764-cell `vm_compute` Qed in
  `PencilCleanGrid.v`.

Both determinant comparisons run a 1-coefficient `vm_compute` per
prime (vs. the main route's 43-coefficient comparison) and a
Hadamard-style bound on `|det|` (`CRTPencilHadamardGeneric.v` + the
per-matrix specialisations). The remaining steps (IVT / realalg /
eigenvalue) are identical to the main route.

Trade-offs: about 3× the LOC at comparable compile time relative to
the main route, after the clean-pencil refactor.  The earlier
`4·D_M2·M1 − 105·D_M1·M2` formulation required a 1210-prime CRT
product (710 mainline + 500 extras) and roughly doubled the compile
time.  The `quad` branch is kept as a worked alternative that
demonstrates the pencil approach is mechanizable; it is not the
canonical proof.

## 3. The Rocq tree, file by file

The dependency order is exactly the order of `_CoqProject`. There are
**23 `.v` files** (plus 14 in two parallel-chunk subdirectories — a
`Def.v` and six chunk files under each of `CharPolyAgree/` and
`MaynardVerify/`), totaling ~13 000 lines under `theories/S1/`, of
which Witness.v alone accounts for ~5 700 lines of autogenerated
certificate data.

### 3.1 Scaffolding and certificate data

**`Recompose.v`**. Defines `lift_bigZ : list BigZ.t_ -> list Z`. Rocq's
stdlib `Z` literal parser is superlinear; a 20 kbit literal takes ~0.4 s
to elaborate as `bigZ` but several seconds as `Z`. The shipped
`charpoly_of_A_int` reaches ~20 kbit per coefficient, so we ship it as
`bigZ` and convert to `Z` lazily via `BigZ.to_Z` only where a downstream
proof really needs `Z`.

**`Witness.v`** (autogenerated). The ground certificate: the 42-element
`basis`, the integer matrices `M1_int, M2_int, A_int`, their
denominators `D_M1, D_M2, D_A`, the cleared-char-poly `charpoly_int`
(43 coefficients), `charpoly_of_A_int` (43 coefficients, ~20 000 bits
max, shipped as `bigZ` and converted via `lift_bigZ`), and the scaling
scalar `D_q`. Large integers are written as `bigZ` to keep parser time
manageable.

### 3.2 Core computational libraries

**`IntPoly.v`**. Defines `pol := list Z`, low-to-high. Operations:
`padd`, `psub`, `pneg`, `pscale`, `pmul`, `pderiv`, `prem`
(pseudo-remainder), `plead`, `pdeg`, `pnorm` (strip trailing zeros),
Horner evaluation `peval`, and a specialised `peval_at_rat p num den`
(= *den^|p| · p(num/den)*). Everything reduces under `vm_compute`.

**`IntMat.v`**. Defines `mat := list (list Z)`, row-major, no
well-formedness invariant. Operations: `mzero`, `meye`, `madd`,
`mscale`, `mmul`, `mtrans`, `mtrace`, `mat_get`, plus length lemmas. All
theorems go through list induction; nothing is imported from MathComp.
The reason is that `'M[R]_42` does not reduce under `vm_compute` at the
sizes we need, but nested `list (list Z)` does (a 42×42 matrix
multiplication takes ~0.14 s by `vm_compute`).


**`SignChain.v`**. The sign primitives consumed by L1: `sgn_Z`,
`sign_at_rat` (= `sgn_Z (peval_at_rat p num den)`), and
`sign_at_pinf` (= `sgn_Z (plead p)`). Pure-`list Z` arithmetic;
`vm`-computable.

### 3.3 Characteristic polynomial and its bridges

**`CharPoly.v`** (~2 000 lines). One of the two "big" files. It gives:

- A hand-rolled Faddeev–LeVerrier (FL) recurrence on `list (list Z)`:

  ```rocq
  Fixpoint fl_loop (steps : nat) (k : Z) (A I_n M_prev : mat) (c_prev : Z)
    (acc : list Z) : list Z := ...
  Definition char_poly_int (A : mat) : pol :=
    let n := mat_dim A in
    let coeffs := fl_loop n Z.one A (meye n) (mzero n) Z.one [] in
    coeffs ++ [Z.one].
  ```

- Bridging definitions `Z_to_int : Z -> int` (to MathComp integers),
  `mat_int_to_rat : mat -> Z -> nat -> 'M[rat]_n`, and
  `pol_to_polyrat : pol -> {poly rat}`.
- The key correctness lemma:

  ```rocq
  Lemma char_poly_int_correct (M : mat) (n : nat)
    (sq : mat_dim M = n)
    (wf : forall i, (i < length M)%coq_nat -> length (nth i M nil) = n) :
    pol_to_polyrat (char_poly_int M) = char_poly (mat_int_to_rat M 1 n).
  ```

  Proved by a long induction showing `fl_loop` is a faithful encoding of
  FL on rationals (`fl_loop_rat_is_char_poly_L2`) plus `fl_invariant_L2`
  / `fl_divisibility_L2` (the classical Newton-identity fact that
  `trace(A · M_k)` is divisible by `k` at every step). All `Qed`, no
  admits.

**`CharPolyScale.v`**. The one-lemma file that proves

```
(char_poly (c *: M))`_k = c^(n-k) * (char_poly M)`_k    (c != 0, k <= n)
```

The proof factors *c* out of *xI - cM*, uses `detZ`, recognises the
resulting polynomial matrix as *chi_M* composed with *c^(-1)·x*, and
applies `det_map_mx` plus a direct coefficient computation
(`coef_comp_scaleX`). Fully `Qed`. This lemma is what lets us relate
`char_poly A_rat` to `char_poly (D_A *: A_rat)`, which is in turn equal
to `char_poly (mat_int_to_rat A_int 1 42)` by `char_poly_int_correct`.

### 3.4 The IVT → root bridge (L1)

**`Bridge.v`** (~500 lines). The bridge between the concrete
`list Z`-level sign machinery (IntPoly/SignChain) and the abstract
MathComp `real_closed` machinery. Defines
`pol_to_polyralg : pol -> {poly realalg}` as the composition of
`pol_to_polyrat` with `map_poly ratr`. Provides `sgn_matches`-style
lemmas that connect the integer sign functions to MathComp's
`sgp_pinfty` / polynomial-value signs, plus the wiring around
`cauchy_bound` for an explicit upper bound on all real roots.

**`CertL1.v`**. The **L1 layer**: produces an explicit `realalg` root of
`charpoly_int` above 4/105.

The strategy uses MathComp's `poly_ivtoo` (intermediate value theorem on
real-closed fields). We establish:

- `P(4/105) < 0` from `sign_at_rat charpoly_int 4 105 = -1`, a direct
  `vm_compute` Qed on the integer-list polynomial.
- `P(cb) > 0` where `cb` is MathComp's `cauchy_bound` of *P*, because
  (i) *P ≠ 0*, (ii) `cb` is a strict upper bound for all roots of *P*,
  so `sgr(P(cb)) = sgr(lc(P)) = 1` (and the leading coefficient sign
  comes from `sign_at_pinf charpoly_int = 1`, also a `vm_compute` Qed).

Then `poly_ivtoo` gives *x ∈ [4/105, cb]* with *P(x) = 0*.

```rocq
Lemma maynard_L1_concrete :
  exists lambda : realalg,
    root (pol_to_polyralg charpoly_int) lambda
    /\ (threshold_ralg 4 105 < lambda)%R.
Proof.
  ...
  case: (poly_ivtoo Hab Hprod) => x Hx Hroot.
  exists x; split; first exact: Hroot.
  by move: Hx; rewrite inE /= => /andP [].
Qed.
```

This is the **entire L1 layer**, fully `Qed`, zero project axioms.

### 3.5 Modular plumbing shared by CRT proofs

**`ModularArith.v`**. The single source of truth for Uint63 modular
arithmetic on matrices. Defines `addmod63`, `mulmod63`, `negmod63`,
`powmod_fast` (square-and-multiply with fuel), `inv_mod63` (via Fermat's
little theorem: *a^(-1) = a^(p-2)*), `divmod63`. Then a matrix layer:
`mmat := list (list int)`, `Z_to_mod63 p z`, `reduce_mat_Z p M`,
`mmat_vadd`, `mmat_add`, `mmat_vscale`, `mmat_scale`, `dot_mod`,
`mmat_heads`, `mmat_tails`, `mmat_trans_fuel`, `mmat_trans`, `mmat_mul`,
`mmat_trace`, `mmat_eye`, `mmat_zero`, `fl_mod_loop`, `char_poly_mod p
M`.

The existence of this file is *the* thing that unblocks CRTLift.v — see
Technique (c) in §4.

### 3.6 CRT cross-validation of the shipped polynomial

The computational core of the CRT check is split across the
`CharPolyAgree/` directory:

- **`CharPolyAgree/Def.v`** (~870 lines). Beyond structural lemmas
  (dimensions, length, monic, etc.):
    - `crt_primes_local : list int` (10 primes ≥ 2^30) and
      `crt_primes_extra` (700 more),
      `crt_primes_all := local ++ extra` (710 Uint63 primes, all ≥ 2^30).
    - `check_charpoly_one_prime_710 p := list_eqb63 (char_poly_mod p A_int)
      (List.map (bigZ_to_mod63 p) charpoly_of_A_int_bigZ)`.
    - `check_mat_identity_one_prime p`: verifies
      `D_M2 · (M1 · A) ≡ D_M1 · D_A · M2  (mod p)`.
    - `crt_chunk_0..5` and `crt_primes_all_split` decompose
      `crt_primes_all` into six contiguous 119-prime sublists (the last
      has 115).

- **`CharPolyAgree/Chunk_0.v` … `Chunk_5.v`** (~12 lines each).
  Each runs the per-prime char-poly and matrix-identity checks on its
  119-prime chunk via `vm_compute`. Six files compile in parallel
  under `make -j`.

- **`CharPolyAgree.v`** (~170 lines). The assembly: imports `Def` and
  the six chunks, and proves
    - `char_poly_int_agrees_710 : check_charpoly_710 = true`
    - `matrix_identity_710 : check_mat_identity_710 = true`
  via `crt_primes_all_split` plus `forallb_app`. No new `vm_compute`.
- `scaling_Z_from_check (k : nat)`: if *k < 43* then
  *c_k · D_A^(42-k) = D_q · c'_k* where *c_k* is the *k*-th coefficient
  of `charpoly_int` and *c'_k* of `charpoly_of_A_int`. Derived from a
  BigZ-level check that each pair of coefficients satisfies the scaling
  identity exactly; it is the link between our cleared polynomial and
  the "raw" char poly of `A_int`.

The 710 primes come from three requirements:

1. Each prime *p* must satisfy *p < 2^31* so that *a·b < 2^62 < 2^63* —
   no 63-bit multiplication overflow inside `vm_compute`.
2. The product *∏ p_i* must exceed *2B* where *B* is a verified bound on
   the maximum coefficient magnitude (see `fl_crt_bound` and
   `matrix_crt_bound_sufficient` in CRTLift.v). 710 primes at ~2^30 give
   a product >2^{21300}.
3. Each *p > n+1 = 43* so the FL recurrence's divisions by *k = 1..42*
   are all well-defined in *𝔽_p*.

### 3.7 CRT-lifted Z identities

**`CRTCheck.v`**. A *generic* CRT toolkit. Provides `small_multiple_zero`
(if `P | c`, `0 < P`, and `2*|c| < P`, then `c = 0`), coprimality lemmas,
and the capstone `all_primes_divide_product` (if `NoDup ps` and every
`p ∈ ps` is prime and divides `c`, then `∏ ps | c`).

**`Fermat.v`**. Fermat's little theorem. The workhorse is `fermat_mod :
prime p'.+2 -> (0 < k < p'.+2)%N -> k * k^(p'.+2 - 2) = 1 %[mod p'.+2]`,
proved through MathComp's `expf_card`. `fermat_Z` and
`Zprime_to_ssrprime` bridge to `Znumtheory.prime` and stdlib ℤ, which is
the interface consumed by the 710-prime lift.

**`PrimeCheck.v`**. A pure-`Z` trial-division primality checker:
`check_prime_Z p` returns `true` iff *p* has no prime factor *≤ ⌊√p⌋*.
Proved sound for `Znumtheory.prime` and bridged to MathComp's
`ssrnat.prime`. On our ~2^30 primes, a single check is ~0.6 s by
`vm_compute`; for all 710 primes ~7 min. That cost is paid once in
`check_all_primes_710` / `crt_primes_710_all_prime` inside CRTLift.v.

**`CRTBridge.v`** (~1 400 lines). The **soundness of FL mod p**:
whatever `char_poly_mod p M` computes in Uint63, it agrees, after
lifting, with `List.map (Z_to_mod63 p) (char_poly_int M)`. Concretely:

```rocq
Theorem char_poly_mod_sound (p : int) (M : list (list Z)) :
  valid_prime p ->
  square_mat (length M) M ->
  (Z.of_nat (length M) + 1 < to_Z p)%Z ->
  fl_all_divisible (length M) Z.one M (meye (length M)) (mzero (length M)) Z.one ->
  (forall j, 0 < j < to_Z p -> (j * j^(to_Z p - 2)) mod to_Z p = 1 mod to_Z p) ->
  List.map (Z_to_mod63 p) (char_poly_int M) = char_poly_mod p M.
```

Proved by threading soundness lemmas for each modular operation through
the FL recurrence. `Z_to_mod63_spec` proves
`to_Z (Z_to_mod63 p z) = z mod to_Z p` under `valid_prime p` (which
requires *p < 2^31* so the result fits in the Uint63 no-overflow zone).

**`CRTLift.v`** (~1 200 lines). **The CRT lift itself.** Two headline
theorems:

```rocq
Lemma fl_eq_flint : char_poly_int A_int = charpoly_of_A_int.
Lemma matrix_identity_Z :
  mscale D_M2 (mmul M1_int A_int) = mscale (Z.mul D_M1 D_A) M2_int.
```

(Wrapped in opaque definitions `charpoly_Z_A`, `mat_lhs_opaque`,
`mat_rhs_opaque` — the equations are as stated but sandboxed against
kernel unfolding; see §4b.)

The proof pattern is the same for both:

1. Unfold the goal to an entry-by-entry / coefficient-by-coefficient
   equality: *a_i = b_i* in ℤ with a verified bound *|a_i|, |b_i| ≤ B*.
2. Reduce to *(a_i - b_i) = 0* via `small_multiple_zero` with *P = ∏
   p_i* over the 710-prime list.
3. For each prime *p* in the list, prove *p | (a_i - b_i)* by lifting
   the Uint63-level equality `char_poly_mod p A_int = List.map
   (Z_to_mod63 p) charpoly_of_A_int` (resp. the matrix analogue) to ℤ
   via `Z_to_mod63_spec`.
4. Use `all_primes_divide_product` to conclude *P | (a_i - b_i)*.
5. `vm_compute` verifies *2B < P*.

### 3.8 Maynard input verification (M1, M2)

The five files `MaynardFactQ.v`, `MaynardBasis.v`, `MaynardSpec.v`,
`MaynardVerify.v`, `MaynardSpecBridge.v` close the trust loop on the
42x42 input matrices. They sit downstream of `Witness.v` and
`CharPoly.v`. `Cert.v` imports `MaynardVerify` and `MaynardSpecBridge`
(both feed the composed rat-level identity inside
`maynard_M105_certified`: the Z-level cross-multiplication bool facts
`all_match_M{1,2}Z_true` plus the rat↔Z bridges `M{1,2}_spec_rat_eq`
are lifted to a single rat equality `M{1,2}_spec_ij = Z2rat (mat_get
M{1,2}_int i j) / Z2rat D_M{1,2}` by a `qfrac_eq_div` helper local to
`Cert.v`). The Z-level checks and the Z↔rat bridges remain available
as standalone Qeds for auditors who want to trace the chain step-by-step.

A companion document `SPEC_TO_PAPER.md` at the repo root maps every
definition in `MaynardSpec.v` (`compositions`, `cff`, `G_2`, `alpha`,
`M1_entry`, `M2_entry`) to specific lines of arXiv:1311.4600 v3 §8,
giving the line-level reference from the Rocq spec back to the paper.

**`MaynardFactQ.v`** (~30 lines). Tiny rat-level wrappers `factQ n
:= n`!%:R : rat`, `binQ n k := 'C(n, k)%:R : rat`, and a couple of
helper lemmas (`factQ_neq0`, `factQ_succ`).

**`MaynardBasis.v`** (~75 lines). Rebuilds the 42-element basis
`{(b, c) ∈ ℕ × ℕ : b + 2c ≤ 11}` in the Mathematica enumeration order
used in `Witness.v`, and pins it to the canonical predicate via three
Qed lemmas:

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
`{(b, c) ∈ ℕ² : b + 2c ≤ 11}` — a reviewer never has to read the 42-pair
literal. The proof goes via a canonical `[seq p <- allpairs ... | p.1 +
2*p.2 ≤ 11]` and a `vm_compute`-Qed `perm_eq` lemma; the residual
`2c ≤ 11 ⇒ c < 6` step is closed by `lia` (mczify).

**`MaynardSpec.v`** (~250 lines). Transcribes Maynard's closed forms:

- `G_2 n k : rat`: the polynomial
  `G_{n,2}(k) = n! · Σ_{r=1}^{n} C(k, r) · Σ_{a ∈ compositions(r, n)} cff(a)`
  from Lemma 8.1 (= v1 Lemma 7.1), where `compositions r n` enumerates
  the length-r compositions of n with parts ≥ 1, and `cff a := Π (2 b_i)!/b_i!`
  is the per-composition inner factor. Both the n! prefactor and the
  inner product appear at the same positions as in Maynard's paper.
- `M1_entry bi ci bj cj : rat = b!/(105+b+2c)! · G_2 c 105` where
  `b = bi+bj`, `c = ci+cj`. Single term per matrix entry.
- `alpha b c cp : rat`, the eq. 7.8 expansion coefficient.
- `M2_entry bi ci bj cj : rat`: a double sum over `(cp1, cp2) ∈
  [0, ci] × [0, cj]` of `α(bi, ci, cp1)·α(bj, cj, cp2)·bsum!/(104+
  bsum+2·csum)!·G_2 csum 104` (up to 36 terms per entry).

The file also provides Z-level twins `m1_num_den_at`, `m2_num_den_at
: nat → nat → Z * Z` that compute the same rationals as a
(numerator, denominator) pair of integers, avoiding `rat`'s canonical
`gcd`-normalisation cost during `vm_compute`.

**`MaynardVerify/Def.v`** (~75 lines). Definitions plus the fast M1
cross-check:

```rocq
Definition M1_entry_matchZ (i j : nat) : bool :=
  Z.eqb (m1_num i j * D_M1) (mat_get M1_int i j * m1_den i j).

Definition all_match_M1Z : bool :=
  forallb (fun i => forallb (fun j => M1_entry_matchZ i j) (seq 0 42))
          (seq 0 42).

Lemma all_match_M1Z_true : all_match_M1Z = true.
Proof. vm_compute. reflexivity. Qed.
```

Same shape for M2's `M2_entry_matchZ` / `all_match_M2Z`, but the M2
check is split into six row-range chunks
(`MaynardVerify/M2_0.v` … `M2_5.v`, 7 rows each) so `make -j`
runs them concurrently. **`MaynardVerify.v`** (~95 lines) is the
assembly: it imports `Def` plus the six chunks and proves
`all_match_M2Z_true` via `seq_split_42` + `forallb_app` from the
six chunk Qeds — no new `vm_compute`.

The cross-check is at the Z level (`num · D = M_int · den`) rather
than the rat level (`M_int / D = num / den` in `'M[rat]_42`)
deliberately: closing the rat-level matrix equality at concrete dim
42 triggers the MathComp HB canonical-structure stall described in
§4d, while adding no numerical content beyond the bool facts. The
Z cross-check is the load-bearing fact; rational cross-multiplication
is one well-known identity away from the rat-level statement.

**Timing**: M1 is a single ~90 s `vm_compute` Qed. M2 is split into
six 7-row chunks (`MaynardVerify/M2_<k>.v`) so `make -j` runs them
concurrently; on this machine each chunk finishes in ~6–18 minutes
of CPU but the chunks overlap with the six 710-prime CRT chunks in
`CharPolyAgree/`, putting the headline cold-build wall time at
~28 minutes with `make -j6` (and ~62 minutes with `make -j2`) on a
16 GB / 6-thread box.

**`MaynardSpecBridge.v`** (~520 lines). Kernel-Qed bridge between Part
A (rat-level, paper-shaped) and Part B (Z-level, `vm_compute`-shaped)
of `MaynardSpec.v`:

```rocq
Theorem M1_spec_rat_eq (i j : nat) :
  M1_spec_ij i j = qfrac (m1_num_den_at i j).

Theorem M2_spec_rat_eq (i j : nat) :
  M2_spec_ij i j = qfrac (m2_num_den_at i j).
```

where `qfrac (n, d) := (Z_to_int n)%:~R / (Z_to_int d)%:~R : rat` reads
a (numerator, denominator) ℤ-pair as a rational. Both theorems are `Qed`
and `Print Assumptions` reports *Closed under the global context* — no
axioms, no `Uint63` primitives, just structural induction over the
parallel definitions. The bridge is layered through `factZ_to_rat`,
`dblratZ_to_rat`, `binZ_to_rat`, `compositionsZ_eq_compositions`,
`G2Z_to_rat`, `qfrac_qmul`, `qfrac_qplus`, and `alphaZ_to_rat`.

The bridge is a leaf in the dependency DAG: `Cert.v` does not import it,
and it is independent of `MaynardVerify.v`'s load-bearing Z-level
cross-check. Its purpose is to certify in the kernel that the rat-level
paper-form spec — the readable definition a reviewer reads against
arXiv:1311.4600 §8 — and the Z-level computational spec — the form
`vm_compute` consumes inside `MaynardVerify` — encode the same closed
forms. Together with `MaynardVerify.all_match_M{1,2}Z_true`, this gives
a two-step kernel chain: `M1_int` agrees with `m1_num_den` (Z), and
`m1_num_den` agrees with `M1_entry` (rat-level, paper-shaped).

### 3.9 The L2 / L3 / L4 assembly

**`CertL2.v`**. Defines

```rocq
Definition A_rat : 'M[rat]_42 :=
  ((invmx (mat_int_to_rat M1_int D_M1 42)) *m
   mat_int_to_rat M2_int D_M2 42)%R.
```

and proves:

- `M1_1_unit : mat_int_to_rat M1_int 1 42 \in unitmx`, via a modular
  determinant check at one prime plus `char_poly_mod_sound` (the head
  coefficient of the modular char poly is nonzero, so the Z-level
  determinant is nonzero, so the rational matrix is invertible).
- `mat_A_scale_eq_Arat : mat_int_to_rat A_int 1 42 = (Z_to_int D_A)%:~R
  *: A_rat`. The proof is *the* place where MathComp's HB
  canonical-structure elaborator caused pain (§4d). It is closed by
  isolating the algebraic manipulation in a generic-dimension section
  `abstract_mat_scale` and specialising only at the final call site.
- `charpoly_int_Dq_scaled : pol_to_polyrat charpoly_int = (Z_to_int
  D_q)%:~R *: char_poly A_rat`. The headline L2 fact. Chains:
  `scaling_Z` (per-coefficient ℤ identity from CharPolyAgree) →
  `char_poly_int_correct` (FL correctness at rat) → `fl_eq_flint` (CRT
  lift) → `mat_A_scale_eq_Arat` (structural equality above) →
  `CharPolyScale.char_poly_scale` (the *c^(n-k)* formula).

All of CertL2.v is `Qed`; the two previously-slow steps
(`mat_A_eq_Arat` and `charpoly_int_Dq_scaled`) were closed using the
generic-n-helper technique described in §4d.

**`Cert.v`**. **The headline assembly.** Four small lemmas glue L1–L4
together; the full proof of `maynard_eigenvalue_S1` is a few tactic
lines.

## 4. The four critical techniques

### 4a. CRT lift via 710 Uint63 primes

The central computational obstacle is showing `char_poly_int A_int =
charpoly_of_A_int` in ℤ. Both sides are lists of 43 integers; their
coefficients reach ~20 000 bits. `vm_compute` on `char_poly_int A_int`
directly requires running Faddeev–LeVerrier on a 42×42 matrix over ℤ
with arithmetic on 1 000-digit numbers. Empirically this is measurable
in hours and produces proof terms that are then impractical to
type-check.

**Solution (CRTLift.v).** Fix 710 primes *p_i* with *2^30 ≤ p_i < 2^31*.
For each *p_i*:

- `char_poly_mod p_i A_int` uses only Uint63 operations: 42 FL
  iterations, each doing a 42×42 modular multiplication (~74 000 Uint63
  ops) plus a trace and a modular division. Total ~10^7 Uint63 ops per
  prime; `vm_compute` handles this in ~0.5 s.
- `List.map (Z_to_mod63 p_i) charpoly_of_A_int` reduces 43 large
  integers mod *p_i*, ~microseconds.
- Equality of the two lists (`list_eqb63`): another `vm_compute`.

So `check_charpoly_710` is a `forallb` over 710 primes of a single-prime
check, all inside Uint63 arithmetic.
`Lemma char_poly_int_agrees_710 : check_charpoly_710 = true` closes by
`vm_compute. reflexivity.`.

Lifting modular equality to ℤ uses `CRTCheck.v`'s `small_multiple_zero`
+ `all_primes_divide_product`. Key ingredients (all in CRTLift.v):

- `crt_primes_710_NoDup`: 710 distinct primes (decidable `nodup_Z` +
  `vm_compute`).
- `crt_primes_710_all_prime`: each prime really is prime, by
  `check_prime_Z_sound` and a 710-step `forallb` check. This dominates
  compile time — ~7 min.
- `crt_primes_valid`: each *p* satisfies *1 < p < 2^31*, needed by
  `Z_to_mod63_spec`.
- `crt_bound_sufficient`: *2B + 2|c'| < ∏ p_i*, where *B =*
  `fl_coeff_bound 42 (max_abs_entry A_int)` is a purely arithmetic upper
  bound for any coefficient produced by the FL recurrence, tracked
  through the computable recurrence `fl_bound_aux`. The bound itself
  is ~10^2000 and the product is ~2^{21300}; `vm_compute` discharges
  the comparison (the project's only invocation of this `vm_compute`,
  in `CRTLift.fl_crt_bound`, takes ~18 minutes — by far the dominant
  step in the whole build). An earlier, lighter version of the bound
  ran in ~2 minutes; that is what the in-source comment estimating
  "~2 min" is a remnant of.

Putting it all together:

```rocq
Lemma fl_eq_flint : charpoly_Z_A = charpoly_of_A_int.
Proof.
  apply List.nth_ext with 0%Z 0%Z.
  { rewrite length_charpoly_Z_A. rewrite length_charpoly_of_A. reflexivity. }
  intros n Hn. ...
  apply (small_multiple_zero _ crt_product_710).
  { (* product | (a - b) *)
    unfold crt_product_710. apply all_primes_divide_product.
    { exact crt_primes_710_NoDup. }
    { exact crt_primes_710_all_prime. }
    intros pz Hpz. ...
    pose proof (per_prime_agreement p Hin) as Hagree.
    ... exists ((a / to_Z p - b / to_Z p)%Z). ... lia. }
  { exact crt_product_710_pos. }
  { (* 2*|a - b| < product *)
    apply Z.le_lt_trans with (2 * Z.abs a + 2 * Z.abs b)%Z.
    { pose proof (Z.abs_triangle a (-b)). rewrite Z.abs_opp in H. lia. }
    apply Z.le_lt_trans with (2 * fl_coeff_bound 42 (max_abs_entry A_int) +
                                2 * max_abs_coeff charpoly_of_A_int)%Z.
    { apply Z.add_le_mono.
      { apply Z.mul_le_mono_nonneg_l; [lia|].
        exact (charpoly_coeff_bound n Hn). }
      { apply Z.mul_le_mono_nonneg_l; [lia|]. apply max_abs_coeff_bound. ... } }
    exact crt_bound_sufficient. }
Qed.
```

`matrix_identity_Z` is structurally identical, with a simpler
coefficient bound because the matrix entries are not the output of a
long recurrence.

`charpoly_coeff_bound` itself needs a ℤ-level bound on the *k*-th
coefficient of `char_poly_int A_int` for every *k ≤ 42*. We derive it by
*tracking the FL recurrence itself*. The function `fl_bound_aux` is an
arithmetic recurrence that strictly upper-bounds `max_abs_entry (fl
M_k)` and `|c_k|` after *k* FL steps. The helper `fl_loop_coeff_bound`
proves, by induction on the remaining steps, that every coefficient
produced by `fl_loop` is bounded by `fl_bound_aux`. Then the lemma
specialises to `A_int` and compares against the CRT product by
`vm_compute`.

### 4b. `Strategy opaque` on the conversion side

Once `check_charpoly_710 = true` is established, to extract *per-prime*
agreement you want the step:

```rocq
Lemma per_prime_shipped_eq p (Hin : In p crt_primes_all) :
  char_poly_mod p A_int = List.map (bigZ_to_mod63 p) charpoly_of_A_int_bigZ.
```

The natural proof is `apply list_eqb63_sound; exact (shipped_per_prime p
Hin)` where `shipped_per_prime` extracts the prime *p*'s entry from
`check_charpoly_710 = true`. On paper this typechecks instantaneously.

The problem is that when the kernel compares `shipped_per_prime p Hin :
check_charpoly_one_prime_710 p = true` against `list_eqb63 X Y = true`,
it wants to check that `check_charpoly_one_prime_710 p` is convertible
with `list_eqb63 X Y`. Because `check_charpoly_one_prime_710` is
`let`-free this is *shallow* — `check_charpoly_one_prime_710 p`
beta-reduces to `list_eqb63 (char_poly_mod p A_int) _` — but the
kernel's WHNF reducer keeps going: it tries to iota-reduce `list_eqb63`
into its match-on-arguments, which forces WHNF on the first argument
`char_poly_mod p A_int`. That triggers the full FL recurrence on the
concrete 42×42 matrix, in kernel reduction (not `vm_compute`, because at
`Qed` time the conversion check is done by the ordinary reducer).
Empirical result: the Qed hangs for > 25 minutes.

**Solution.** Mark the offending constants opaque *for the duration of
this specific Qed*:

```rocq
Strategy opaque [list_eqb63 char_poly_mod A_int charpoly_of_A_int_bigZ
                 bigZ_to_mod63 reduce_mat_Z mmat_eye mmat_zero fl_mod_loop].
Lemma per_prime_shipped_eq p (Hin : In p crt_primes_all) :
  char_poly_mod p A_int = List.map (bigZ_to_mod63 p) charpoly_of_A_int_bigZ.
Proof.
  apply list_eqb63_sound. exact (shipped_per_prime p Hin).
Qed.
Strategy transparent [list_eqb63 char_poly_mod A_int charpoly_of_A_int_bigZ
                      bigZ_to_mod63 reduce_mat_Z mmat_eye mmat_zero fl_mod_loop].
```

With `list_eqb63` opaque, the kernel checks the proof structurally:
`shipped_per_prime p Hin` has type `check_charpoly_one_prime_710 p =
true`, which unfolds (delta) to `list_eqb63 X Y = true`; the kernel sees
`list_eqb63` matches head-to-head on both sides and accepts. No descent
into `X` or `Y` happens. The Qed takes milliseconds.

The exact same technique is used for `per_prime_matrix_agreement`, where
`mmat_eqb` would otherwise trigger WHNF descent into `mmat_scale p c
(mmat_mul p A B)` on concrete 42×42 Uint63 matrices.

### 4c. ModularArith extraction

Before this project gained `ModularArith.v`, the two files `CRTBridge.v`
and `CharPolyAgree.v` each defined their own copies of `addmod63`,
`mulmod63`, `mmat_add`, `mmat_mul`, `mmat_trans`, `reduce_mat_Z`,
`fl_mod_loop`, and crucially `char_poly_mod`. The bodies were identical
text but the *constants* were different (two `Definition char_poly_mod`s,
one per file, with the same source but distinct kernel identifiers).

When CRTLift.v tried to rewrite `char_poly_mod p A_int` (from CRTBridge)
by a fact mentioning `char_poly_mod p A_int` (from CharPolyAgree), the
kernel saw two syntactically distinct head constants. It could only
unify them by *delta-unfolding both*, which is precisely the 42-iteration
FL recurrence on concrete 42×42, which is precisely what we do not want
the kernel to do.

**Solution.** Factor every shared definition into a single
`ModularArith.v`. Both CRTBridge and CharPolyAgree (and CRTLift) now
import from one canonical source. The `char_poly_mod` constant is now a
*single* kernel name, so unification of `char_poly_mod p A_int` against
`char_poly_mod p A_int` is by head reflexivity — zero reduction, zero
time.

This is not mathematics; it is a Rocq-engineering fix that deserves a
name because it is easy to miss. The header of `ModularArith.v`
explicitly documents the reason:

> Both CRTBridge.v and CharPolyAgree.v previously duplicated all of
> these definitions, which caused the kernel's conversion checker to
> explode when comparing terms involving char_poly_mod from different
> files (two different constants, identical bodies). Extracting them
> here ensures a single canonical definition.

### 4d. Generic-n helpers for MathComp's HB elaborator

The two closures `mat_A_scale_eq_Arat` and `charpoly_int_Dq_scaled` in
CertL2.v work entirely inside MathComp: `A_rat : 'M[rat]_42`, and the
goals involve `invmx`, `\det`, `char_poly`, `char_poly_mx`, `map_mx`,
`scalerA`, `mulVr`, `mulKVmx`, `invmxZ`. Every call to a tactic like
`rewrite scalerA` or `apply char_poly_scale` forces MathComp's HB
canonical-structure resolver to locate the `scalarType` / `ringType` /
`comRingType` / `fieldType` / ... instances for `'M[rat]_42`, `rat`,
`{poly rat}`, and combinations thereof.

On a fully concrete `'M[rat]_42`, instance resolution traverses an
instance graph whose size is quadratic in the goal term. This is not
kernel reduction — `Strategy opaque` does not help. This is the
*tactic-level* elaborator walking the instance graph before the tactic
even starts. Empirically it takes ~40–90 min per rewrite.

**Solution.** Two sub-techniques, both visible in CertL2.v.

**(i) Sections with abstract field and dimension.** Write the slow
algebraic manipulation once, inside a section that abstracts over `F :
fieldType` and `n : nat`. Inside the section the instance graph is small
(`F` and `n` are opaque), so elaboration is instantaneous. At the call
site, the section lemma is applied with explicit arguments:

```rocq
Section AbstractMatScale.
Variable (F : fieldType) (n : nat).
Variables (M1_1 A_1_int M2_1 : 'M[F]_n) (c1 c2 cA : F).
Hypothesis Hc1 : c1 != 0.  Hypothesis Hc2 : c2 != 0.
Hypothesis Hu : M1_1 \in unitmx.
Hypothesis Hid : c2 *: (M1_1 *m A_1_int) = (c1 * cA) *: M2_1.

Lemma abstract_mat_scale :
  A_1_int = cA *: (invmx (c1^-1 *: M1_1) *m (c2^-1 *: M2_1)).
Proof.
  have Hc1' : c1^-1 != 0 by rewrite invr_neq0.
  have Hu' : c1^-1 *: M1_1 \in unitmx by rewrite unitmxZ ?unitfE.
  rewrite invmxZ // invrK.
  rewrite -scalemxAl -scalemxAr !scalerA.
  apply: (can_inj (mulKmx Hu)).
  rewrite !scalemxAr mulmxA mulmxV // mul1mx.
  apply: (can_inj (scalerK Hc2)).
  rewrite scalerA Hid.
  congr (_ *: _).
  by rewrite mulrCA mulrAC divff // mulr1 mulrC.
Qed.
End AbstractMatScale.
```

Now `mat_A_scale_eq_Arat` is proved by a single call to
`abstract_mat_scale` with explicit `rat`, `42%N` arguments. The slow
rewrites all happen in the proof of `abstract_mat_scale`, but **at
abstract `F` and `n`**, so elaboration is fast.

**(ii) Term-mode plugging + pre-specialised helpers.** For
`charpoly_int_Dq_scaled`, the cleanest proof would use `rewrite Hcpi`,
where `Hcpi : pol_to_polyrat (char_poly_int A_int) = char_poly
(mat_int_to_rat A_int 1 42)`. But `rewrite` triggers unification of the
goal with `Hcpi`'s LHS at the concrete `'M[rat]_42`, which is slow.
Instead we build the rewritten hypothesis `Hcda` by a purely term-level
chain of `eq_trans` / `f_equal`:

```rocq
have Hcda : pol_to_polyrat charpoly_of_A_int
          = char_poly ((Z_to_int D_A)%:~R *: A_rat)
  := eq_trans (f_equal pol_to_polyrat (esym Hfl'))
       (eq_trans Hcpi (f_equal (@char_poly _ 42) HA1)).
```

This bypasses `rewrite` entirely. Similarly, `apply: char_poly_scale`
would elaborate `char_poly_scale` at the concrete dimension 42; instead
we pre-specialise it to `(rat, 42)`:

```rocq
Lemma char_poly_scale_rat42 (c : rat) (M : 'M[rat]_42) (k : nat) :
  c != 0 -> (k <= 42)%N ->
  (char_poly (c *: M))`_k = c ^+ (42 - k) * (char_poly M)`_k.
Proof. exact: char_poly_scale. Qed.

Lemma expf_neq0_rat (c : rat) (n : nat) : c != 0 -> c ^+ n != 0.
Proof. exact: expf_neq0. Qed.

Lemma size_char_poly_42 (M : 'M[rat]_42) : size (char_poly M) = 43.
Proof. exact: size_char_poly. Qed.
```

and invoke them in term mode, `Hscale := char_poly_scale_rat42 _ _ _
HDA_ne Hk`. Each pre-specialisation lemma is a one-liner; its `Qed`
elaborates *once*, paying the instance-resolution cost once.

Finally, to eliminate the last `(char_poly A_rat)`_k` reference from the
goal before applying a pure-rat algebraic cancellation, `pose` and
`change` hide the matrix-level term behind a rat-level variable:

```rocq
pose c : rat := (char_poly A_rat)`_k.
rewrite -/c in HcpA_of_A.
change (char_poly A_rat)`_k with c.
apply: mat_cancel_helper; [exact HcpA_of_A | exact HZrat | exact HdApow].
```

where `mat_cancel_helper : a * d = e * b -> b = d * c -> d != 0 -> a = e
* c` is a trivial rat-level identity. At this point the residual goal is
pure-rat algebra with all matrix / polynomial instance resolution
already done. The whole `charpoly_int_Dq_scaled` Qed takes seconds
instead of hours.

**Summary of (4b) vs (4d).** The distinction is important:

- (4b) is about **kernel WHNF reduction** at conversion time, defeated
  by `Strategy opaque`.
- (4d) is about **tactic-level elaboration** of MathComp's HB canonical
  structures, defeated by keeping the concrete `'M[rat]_42` out of the
  tactic goal (sections at generic *n*, term-mode plugging,
  pre-specialised helpers).

Both are invisible in textbook mathematics and both have to be dealt
with to get a proof of this size past the kernel.

## 5. The headline, layer by layer

Restating the goal:

```rocq
Theorem maynard_eigenvalue_S1 :
  exists lambda : realalg,
    eigenvalue (map_mx (ratr : rat -> realalg) A_rat) lambda
    /\ (ratr (4%:Q / 105%:Q) : realalg) < lambda.
```

A combined sibling theorem in the same file, `maynard_M105_certified`,
conjoins this with two readable rat-level identities stating that the
paper-form spec equals the FLINT integer entry over the common
denominator:

```rocq
Theorem maynard_M105_certified :
  (forall i j : nat, (i < 42)%nat -> (j < 42)%nat ->
     M1_spec_ij i j = Z2rat (mat_get M1_int i j) / Z2rat D_M1) /\
  (forall i j : nat, (i < 42)%nat -> (j < 42)%nat ->
     M2_spec_ij i j = Z2rat (mat_get M2_int i j) / Z2rat D_M2) /\
  exists lambda : realalg,
    eigenvalue (map_mx (ratr : rat -> realalg) A_rat) lambda
    /\ (ratr (4%:Q / 105%:Q) : realalg) < lambda.
```

where `Z2rat (z : Z) : rat := (Z_to_int z)%:~R` embeds Z into rat. One
`Print Assumptions` covers (a) the closed-form match between the
FLINT-shipped `M1_int / M2_int` and the readable paper-form spec
`MaynardSpec.M{1,2}_spec_ij` (which transcribes Maynard's Lemma 8.2
character-for-character), and (b) the eigenvalue bound. The audit
chain still factors through "FLINT integer matrices = Z-level closed
form = rat-level paper-form spec", but only the *composed* identity
is surfaced in the headline.

The Z-level cross-multiplication checks `all_match_M{1,2}Z = true`
and the rat↔Z bridges `MaynardSpecBridge.M{1,2}_spec_rat_eq` are now
proof-internal implementation steps of `maynard_M105_certified`. The
assembly composes:

- `M{1,2}_spec_rat_eq` (rat = `qfrac` of a Z-pair, from
  `MaynardSpecBridge`),
- per-entry extraction of the Z-level cross-multiplication from
  `all_match_M{1,2}Z_true` over the 42×42 grid,
- a `qfrac_eq_div` helper that lifts the Z cross-multiplication to a
  rat-level equality,
- per-entry denominator positivity (`m{1,2}_num_den_at_den_pos`,
  `D_M{1,2}_pos`) needed to invoke `eqr_div`.

Both `all_match_M{1,2}Z_true` and `M{1,2}_spec_rat_eq` remain
standalone Qeds in `MaynardVerify` and `MaynardSpecBridge` for any
auditor who wants to inspect the chain step-by-step.

The assembly of `maynard_eigenvalue_S1` in `Cert.v` is a few lines of
tactic:

```rocq
Proof.
  destruct sturm_count_correct as [lambda [Hroot Hgt]].
  exists lambda; split; [| exact Hgt].
  apply eigenvalue_of_root_realalg.
  exact (charpoly_root_transfer lambda Hroot).
Qed.
```

### L0 — Inputs match Maynard's specification

Stated and `Qed` in `MaynardVerify.v`. For every (i, j) ∈ [0, 42)²,

```
m1_num(i, j) · D_M1  =  M1_int[i][j] · m1_den(i, j)    (in ℤ)
m2_num(i, j) · D_M2  =  M2_int[i][j] · m2_den(i, j)    (in ℤ)
```

where `m{1,2}_num`, `m{1,2}_den` are the closed-form numerator and
denominator from Maynard's Lemma 8.2 / eq. 7.8 (transcribed in
`MaynardSpec.v` as `m{1,2}_num_den_at`). Verified by single
`vm_compute`s. `Print Assumptions` reports `Closed under the global
context` — the verification does not even depend on Uint63
primitives, since the bool scans live entirely in stdlib `Z`
arithmetic. This eliminates the FLINT generator from the trust base.

A companion **L0'** step in `MaynardSpecBridge.v` closes the loop
on the readable side: `M{1,2}_spec_rat_eq` are kernel-Qed proofs that
the Z-level `m{1,2}_num_den_at` equals the rat-level paper-form
specification `MaynardSpec.M{1,2}_spec_ij` — the form that
transcribes Maynard's Lemma 8.2 character-for-character. Both are
`Qed` with `Print Assumptions` reporting `Closed under the global
context` (no axioms, not even Uint63), since they are purely
rat-level algebraic identities. `maynard_M105_certified` composes L0
and L0' into a single rat-level identity (per (i,j) ∈ [0,42)²,
`M{1,2}_spec_ij i j = Z2rat (mat_get M{1,2}_int i j) / Z2rat D_M{1,2}`)
that is surfaced directly in the headline; the Z-level booleans and
rat↔Z bridges move into the proof body.

### L1 — IVT root existence

`Cert.sturm_count_correct : exists lambda, root charpoly_as_poly_realalg
lambda /\ ratr (4/105) < lambda` is a thin wrapper around
`maynard_L1_concrete`. (The lemma name predates the cleanup to the
IVT-only L1 layer; mathematically the proof now uses IVT, not a
Sturm-variation count.) The proof uses:

- Sign at the lower endpoint: `sign_at_rat charpoly_int 4 105 = -1`,
  a direct `vm_compute` Qed on the integer-list polynomial.
- Sign at +∞: `sign_at_pinf charpoly_int = 1`, also `vm_compute`-Qed
  (reads the sign of the leading coefficient via `plead`).
- These yield *P(4/105) < 0* and *P(cb) > 0* at the realalg level (via
  `sgn_matches` bridges in Bridge.v).
- MathComp's `poly_ivtoo` extracts a root *x ∈ [4/105, cb]*. Since
  *P(4/105) < 0* and *P(x) = 0*, *x ≠ 4/105*, hence *4/105 < x*.

Fully `Qed`, zero project axioms. Note this is **IVT, not a Sturm-count
proof**: we do not need any count, only the existence of some root
above the threshold; the two endpoint signs are all the chain-free
proof requires.

### L2 — Root transfer to `char_poly A_rat`

`charpoly_root_transfer` converts

```
root (map_poly ratr (pol_to_polyrat charpoly_int)) lambda
  ==>
root (map_poly ratr (char_poly A_rat)) lambda
```

The proof is one `rewrite charpoly_int_Dq_scaled`, which changes the LHS
into `map_poly ratr (D_q *: char_poly A_rat)`, then `map_polyZ` pulls
the scalar out and `rootZ` says a nonzero scalar does not kill roots.
The nonzero-ness of `D_q` is discharged by a direct computation (it is a
positive integer shipped in Witness.v, so its `Z_to_int` image is the
positive `Posz` constructor and equals 0 would contradict
`Pos2Nat.is_pos`).

All the work is in `charpoly_int_Dq_scaled`, which combines the CRT lift
(`fl_eq_flint`), `char_poly_int_correct`, the structural scaling
`mat_A_scale_eq_Arat`, and `CharPolyScale.char_poly_scale` as explained
in §4d.

### L3 — Root → eigenvalue

`eigenvalue_of_root_realalg` is literally:

```rocq
rewrite (map_char_poly (ratr : {rmorphism rat -> realalg})).
by rewrite eigenvalue_root_char.
```

`map_char_poly` says `char_poly (map_mx f M) = map_poly f (char_poly M)`
for a ring morphism *f*; `eigenvalue_root_char` says an eigenvalue is
exactly a root of the char poly.

## 6. Trust base

The recommended canonical Print-Assumptions target is
`maynard_M105_certified`: a single lemma whose assumptions cover
(a) the rat-level identity stating that the paper-form spec
`MaynardSpec.M{1,2}_spec_ij` equals the FLINT integer entry over the
common denominator (composed internally from the Z-level matrix
cross-check `all_match_M{1,2}Z = true` and the rat↔Z bridges
`MaynardSpecBridge.M{1,2}_spec_rat_eq`), and (b) the eigenvalue
bound. `maynard_eigenvalue_S1` is unchanged and still present, but
it is strictly weaker for end-to-end audit because it does not
surface the closed-form match. Auditors who want to inspect the
internal Z-level cross-check or the rat↔Z bridge separately can
still target `MaynardVerify.all_match_M{1,2}Z_true` and
`MaynardSpecBridge.M{1,2}_spec_rat_eq` directly — they remain
standalone Qeds.

`Print Assumptions maynard_M105_certified` (or
`maynard_eigenvalue_S1`) after `coqc` of Cert.v prints exactly **51
standard kernel primitives** — `PrimInt63.*` (and their `Z` /
`Uint63` specifications) shipped with Rocq 9.0/9.1 and the
`Bignums` library: things like `Uint63.add`, `Uint63.mul`,
`Uint63.to_Z`, `BigN.succ_spec`. No project-specific axioms appear.
(`MaynardSpecBridge.M{1,2}_spec_rat_eq` themselves report `Closed
under the global context` — they introduce no Uint63 primitives,
since they are pure rat-level structural inductions.)

These are not project-specific axioms; they are Rocq's declaration that
the native-integer kernel primitives implement the claimed specifications.
Equivalent statements appear in any proof that uses `vm_compute` on
`Uint63`.

**Concretely, a reviewer who trusts:**

1. The Rocq 9.0/9.1 kernel's type-checking algorithm.
2. The `Uint63` and `BigN` primitive axioms (i.e., that the OCaml
   implementation of 63-bit integer arithmetic is faithful to the
   spec).
3. `coqc`'s handling of `vm_compute`. (The project does not use
   `native_compute` anywhere; a `grep -n native_compute theories/S1`
   returns zero hits in real proof code.)

gets, as output, a certified existence of a `realalg` eigenvalue of a
specific 42×42 rational matrix `A_rat` strictly above 4/105, *together*
with the closed-form match of that matrix to Maynard's specification.

**The FLINT layer is outside the trust base.** The Rocq proof never
invokes Python and never loads the JSON certificate directly; the
autogenerated `Witness.v` is an ordinary Rocq file. If the FLINT
layer shipped incorrect data, one of the following `vm_compute`-based
checks would fail to reduce to `true` and the build would stop:

- `MaynardVerify.all_match_M1Z = true`, `all_match_M2Z = true` —
  the 42x42 input matrices match Maynard's closed form (Lemma 8.1 /
  eq. 8.4). This closes the trust gap on the matrix entries
  themselves, not just downstream derivations. The companion doc
  `SPEC_TO_PAPER.md` at the repo root maps every `MaynardSpec`
  definition to the corresponding line of arXiv:1311.4600 v3 §8.
- `CharPolyAgree.char_poly_int_agrees_710 = true` — the shipped
  `charpoly_of_A_int` is the char poly of `A_int`, mod 710 primes.
- `CharPolyAgree.matrix_identity_710 = true` — the shipped
  `M1·A = (D_M1·D_A/D_M2)·M2` identity holds, mod 710 primes.
- `CertL1.sign_at_rat_charpoly`, `sign_at_pinf_charpoly` —
  `vm_compute` reflexivity on `sign_at_rat charpoly_int 4 105 = -1`
  and `sign_at_pinf charpoly_int = 1`. These two reductions
  (together with the `sgn_matches`-style bridges in `Bridge.v`)
  feed the endpoint signs into `poly_ivtoo`.

Each of these is `Qed` and reduces in pure kernel arithmetic. The
repository has zero `Axiom` declarations and zero `Admitted` lemmas
anywhere.

## 7. Numerical highlights

- **Matrix dimension.** 42×42. Maynard's *M_{105}* construction uses 42
  basis polynomials {*x^b · y^c : b + 2c ≤ 11*}. The 42-element
  `Witness.basis` enumerates them; the dimension 42 is hard-wired into
  CRTLift.v and CharPolyAgree.v via `A_int_dim = 42`.
- **Charpoly degree.** 42 (43 coefficients), coefficients up to
  ~20 000 bits.
- **CRT primes.** 710 Uint63 primes, all in [2^30, 2^31), listed in
  `CharPolyAgree.v`: `crt_primes_local` has 10, `crt_primes_extra` has
  700. The product exceeds 2^{21 300}, well above the verified bound
  *2B < 2^{6 500}* needed for the CRT lift.
- **Denominators.** `D_M1` has ~221 decimal digits, `D_M2` ~227, `D_A`
  ~139, `D_q` ~333. All four are strictly positive.
- **Cauchy bound.** The IVT step uses MathComp's `cauchy_bound` — an
  explicit rational upper bound on all real roots of the polynomial,
  derived from the coefficients. No custom bound is needed.
- **Build time.** A clean rebuild on a 16 GB / 6-thread machine takes
  **~28 min wall with `make -j6`** and **~62 min wall with `make -j2`**.
  The two heaviest phases (CharPolyAgree's 710-prime CRT check and
  MaynardVerify's M2 row scan) each split into six parallel chunks
  under `CharPolyAgree/Chunk_0..5.v` and `MaynardVerify/M2_0..5.v`,
  which is what gives `make -j` headroom.
  The dominant costs are:
  - `MaynardVerify.all_match_M2Z_true`: ~35 min CPU total (six
    `M2_0..5.v` chunks at ~6–18 min CPU each, `vm_compute` over
    1764 entries each summing up to 36 rational terms with
    ~10^7000-digit accumulator denominators). Under `make -j6`
    the six chunks run concurrently, so this contributes ~18 min
    to the wall clock rather than 35.
  - `crt_primes_710_all_prime`: ~7 min (710 Z-level primality checks
    by trial division).
  - `check_charpoly_710`, `matrix_identity_710`: ~5–10 min each
    (710 × 42-step FL in Uint63, plus matrix multiplication), split
    across `CharPolyAgree/Chunk_0..5.v`.
  - `fl_crt_bound`, `matrix_crt_bound_sufficient`: ~18 min for
    `fl_crt_bound` (`vm_compute` on a ~10 000-digit arithmetic
    comparison), a few minutes for `matrix_crt_bound_sufficient`.
    The project has no `native_compute` invocations: the single
    earlier use here was replaced with `vm_compute` to keep the
    trust-base enumeration in §6 minimal. `fl_crt_bound` is now the
    single dominant sequential step in the build wall clock; the
    in-source comment estimating "~2 min" predates a strengthening
    of the bound and is stale.
  - `MaynardVerify.all_match_M1Z_true`: ~90 s.
  - CertL2.v: ~10 s post-refactor (MathComp canonical structures
    tamed by §4d techniques).
  - `Witness.v` parsing: ~30 s (`bigZ` literal parser on the shipped
    `charpoly_of_A_int_bigZ` integers).
  Note: under `make -j6`, the six M2 chunks run concurrently with
  the six CRT chunks and with the primality / FL-bound phases, so
  M2 does not strictly add 35 minutes to the wall clock — but it
  dominates the tail of the build once those finish.
- **Total Rocq proof size.** 23 `.v` files plus 14 in two
  parallel-chunk subdirectories (a `Def.v` and six chunks each under
  `CharPolyAgree/` and `MaynardVerify/`), ~13 000 lines under
  `theories/S1/`; Witness.v alone is ~5 700 lines of autogenerated
  certificate data.

## 8. Map of key lemmas and files

```
L0 (input matrices match Maynard's closed form)
  MaynardVerify.v   all_match_M1Z_true, all_match_M2Z_true (vm_compute)
    + MaynardSpec.v  G_2, M1_entry, M2_entry (closed forms)
    + MaynardBasis.v  maynard_basis_eq_witness
    + Witness.v provides M1_int, M2_int, D_M1, D_M2

L0' (rat-level paper-form spec matches Z-level computational spec)
  MaynardSpecBridge.v   M1_spec_rat_eq, M2_spec_rat_eq (Qed, no axioms)
    + MaynardSpec.v  PART A (rat) and PART B (Z) definitions

L1 (IVT root existence)
  CertL1.v   maynard_L1_concrete
    + Bridge.v bridges int-level sign data to realalg
    + CertL1.v: sign_at_rat_charpoly, sign_at_pinf_charpoly (vm_compute)
    + Witness.v provides charpoly_int

L2 (root → char_poly A_rat)
  CertL2.v   charpoly_int_Dq_scaled
    + CharPoly.v  char_poly_int_correct
    + CharPolyScale.v  char_poly_scale
    + CertL2.v  mat_A_scale_eq_Arat (uses abstract_mat_scale)
    + CRTLift.v  fl_eq_flint
    + CRTLift.v  matrix_identity_Z
    + CharPolyAgree.v  scaling_Z_from_check

L3 (char_poly root → eigenvalue)
  Cert.v   eigenvalue_of_root_realalg
    + MathComp: map_char_poly, eigenvalue_root_char

Headline (canonical, end-to-end):
  Cert.v   maynard_M105_certified
    = (forall i j, M1_spec_ij i j = Z2rat M1_int[i,j] / Z2rat D_M1)
      /\ (forall i j, M2_spec_ij i j = Z2rat M2_int[i,j] / Z2rat D_M2)
      /\ maynard_eigenvalue_S1
    (the two rat-level identities are composed internally from
     all_match_M{1,2}Z_true and M{1,2}_spec_rat_eq)

Headline (eigenvalue-only sibling, kept for backward compatibility):
  Cert.v   maynard_eigenvalue_S1
```

The dependency graph has roughly two independent backbones that merge at
Cert.v:

- **IVT backbone**: Witness → IntPoly / SignChain → Bridge → CertL1.
- **CharPoly backbone**: Witness → IntMat / IntPoly → CharPoly →
  ModularArith → CharPolyAgree + CRTBridge → CRTLift → CharPolyScale →
  CertL2.

Everything lives behind a single Rocq `Require` — `Require Import
PrimeGapS1.Cert.` loads the full proof.
