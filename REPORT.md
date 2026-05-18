# Maynard `M_{105} > 4` — A Rocq-audited proof via the pencil-determinant identity

This document explains the structure of the Rocq formalisation that closes
the numerical step in James Maynard's *Small gaps between primes*
(arXiv:1311.4600; Annals of Mathematics **181** (2015), 383–413). The headline
theorem

```rocq
Theorem maynard_eigenvalue_S1_pencil :
  exists lambda : realalg,
    eigenvalue (map_mx (ratr : rat -> realalg) A_rat) lambda
    /\ (ratr (4%:Q / 105%:Q) : realalg) < lambda.
```

is `Qed` in `theories/S1/CertPencil.v`. A sibling theorem
`maynard_M105_certified_pencil` in the same file conjoins this
eigenvalue claim with two readable rat-level identities stating that
the paper-form spec `MaynardSpec.M{1,2}_spec_ij` equals the FLINT
integer entry over the common denominator `D_M{1,2}`, so a single
`Print Assumptions maynard_M105_certified_pencil` (which reports
standard `PrimInt63.*` / `Uint63Axioms.*` kernel primitives — no
project-specific axioms) covers the full chain: the FLINT-shipped
integer matrices match the rat-level paper-form spec entry-by-entry
over a common denominator, and the eigenvalue bound holds. The
Z-level cross-multiplication checks and the rat↔Z bridge are
proof-internal implementation details; they remain available as
standalone Qeds (`MaynardVerify.all_match_M{1,2}Z_true` and
`MaynardSpecBridge.M{1,2}_spec_rat_eq`) for auditors who want to
trace the closed-form match step-by-step.

> **A short history note.**  The git history shows two earlier
> incarnations of this development (a Sturm/IVT route on `main`, and a
> first 1210-prime pencil-determinant draft on this branch (then named `quad`)).  Both were
> retired during the Phase A/B cleanup that produced the current tree:
> the proof on disk is the standalone pencil-determinant proof
> described below.  No "alternative route" remains in the repository.

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
- The two integer determinants required by the pencil-determinant
  route — `det(M1_int)` and `det(pencil_int_clean)` — reach 2044 and
  2613 bits respectively.
- Running Faddeev–LeVerrier (FL) directly on either integer matrix
  inside the Rocq kernel would touch intermediate values with similar
  magnitudes; the project instead does a 710-prime CRT cross-check
  against shipped integer constant terms (§3.6).

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

The Rocq layer does not trust the Python layer.  It only takes from
it a list of integers (matrix entries, the clean integer pencil
`pencil_int_clean`, the shipped determinants `det_M1_int_value` and
`D_pencil_int_value`, and the Hadamard-style coefficient bounds
`fl_coeff_bound_{M1,pencil}_value`).  Every algebraic claim about
those integers is then verified by the kernel, either by
`vm_compute` (on modular and BigZ data) or by ordinary `Qed` proofs
(on MathComp algebra).

The FLINT layer's role is threefold:

- A **second independent implementation** of the same computation. A
  mismatch between FLINT and the Rocq kernel would catch transcription
  errors or a bug in either toolchain.
- The **candidate data** (matrix entries, clean pencil, determinant
  literals, Hadamard bound literals) that the Rocq layer only has
  to check, not re-derive.  Finding these objects from scratch
  inside the kernel would be infeasible.
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

- **The Rocq proof** uses the **pencil-determinant route**: a
  generic identity of commutative-ring algebra,
  `det(λ·M₁ − M₂) = det(M₁) · char_poly(M₁⁻¹M₂)(λ)`
  (`DetPencil.det_pencil`, one-line mathcomp proof), specialised at
  `λ = 4/105` and rescaled to integers, reduces the eigenvalue
  bound to the sign of two integer determinants (`det(M1_int)`
  positive, `det(pencil_int_clean)` negative).  Both signs are
  extracted by a single shared 710-prime CRT lift on the
  *constant terms* of the characteristic polynomials.  The
  intermediate value theorem on `char_poly A_rat` (using MathComp's
  `poly_ivtoo` together with `cauchy_bound`) then certifies the
  *existence* of a real eigenvalue strictly above `4/105`.  No
  eigenvector is ever constructed.  See §3.8 and §5.

Both strategies fit Maynard's §8 framework. Lemma 8.2 (the closed
form for the matrix entries) is verified inside Rocq
(`MaynardVerify`); Lemma 8.3 (the generalised Rayleigh-quotient
identity that gives `M_k = k · λ_max`, plus its hypotheses
`M_1 ≻ 0` and `M_2 = M_2ᵀ`) is *not* formalised here —
its Maynard-style use in the notebook (eigenvector → Rayleigh
quotient) and our pencil-determinant + IVT route both invoke its
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
JSON certificate (matrices, clean pencil, determinant literals,
Hadamard-bound literals) and ships it as Rocq source.  The Rocq
layer (§2.2) is the **verification**: it consumes that certificate
as untrusted input data and kernel-checks every entry against an
independent Rocq-side derivation (entry-by-entry matrix match
against Maynard's closed forms; entry-by-entry clean-pencil match
against the rescaled FLINT matrices; 710-prime CRT lift on the two
integer determinants; Hadamard-style coefficient bound vs. the
710-prime product).  Only the Rocq layer's Qeds are in the trust
base; the FLINT layer is auxiliary.

### 2.1 The FLINT layer (candidate generator)

Run with `python python/build_certificate.py`. The script performs:

1. Build *M1, M2 ∈ ℚ^{42×42}* from the Mathematica formulas, cached in
   `python/m1m2.pkl`. Sanity-check a dozen entries against closed-form Beta
   integrals. Full audit: all 3 528 entries agree with closed-form values.
2. Clear denominators: produce `M1_int, M2_int : list[list[int]]` and
   scalars `D_M1, D_M2` such that `(M_l)[i][j] = M_l_int[i][j] / D_M_l`.
3. Build the **clean integer pencil**: let
   `D_pencil_clean := lcm of denominators of (4·M1_rat − 105·M2_rat)`
   (689 bits, roughly half of `D_M1·D_M2 = 1368` bits) and set
   `pencil_int_clean[i,j] := D_pencil_clean·(4·M1_rat[i,j] − 105·M2_rat[i,j])`.
   The two integer determinants `det_M1_int_value := det(M1_int)`
   (2044 bits, positive) and `D_pencil_int_value :=
   det(pencil_int_clean)` (2613 bits, negative) are shipped as literal
   `Z` constants.
4. Hadamard-style coefficient bound: precompute
   `fl_coeff_bound_M1_value` and `fl_coeff_bound_pencil_value`, the
   closed-form bounds `fl_coeff_bound 42 (max_abs_entry _)` evaluated
   on each matrix, and ship them as literals.
5. Cross-check *lambda_max* against an `arb_mat` computation at 256-bit
   precision.
6. Write `python/certificate.json` (~510 KB metadata).

The translator `python/json_to_v.py` converts the JSON into Rocq
sources: `Witness.v` (matrix entries), `Witness_PencilDet.v`
(`det_M1_int_value`), `Witness_PencilClean.v` (`D_pencil_clean`,
`pencil_int_clean`, `D_pencil_int_value`), and the bound literals
`Witness_M1Bound.v`, `Witness_PencilBound.v`.  All five files are
autogenerated and checked into the repository so that the Rocq
build does not need Python.

### 2.2 The Rocq layer (verification)

The Rocq layer consumes:

- `M1_int`, `M2_int` and the denominators `D_M1`, `D_M2` (in
  `Witness.v`).
- `pencil_int_clean`, `D_pencil_clean`, the shipped pencil
  determinant `D_pencil_int_value` and the shipped M1 determinant
  `det_M1_int_value` (in `Witness_PencilClean.v` and
  `Witness_PencilDet.v`).
- The Hadamard bound literals `fl_coeff_bound_{M1,pencil}_value` (in
  `Witness_M1Bound.v` and `Witness_PencilBound.v`).

It verifies, in this order:

1. The shipped clean-pencil matrix matches the FLINT-shipped M1 / M2
   per-entry: for every `(i, j) ∈ [0, 42)²`,
   `D_M1·D_M2·pencil_int_clean[i,j]
      = D_pencil_clean·(4·D_M2·M1_int[i,j] − 105·D_M1·M2_int[i,j])`,
   by a single 1764-cell `vm_compute` Qed
   (`PencilCleanGrid.all_pencil_clean_match_true`).
2. The shipped integer determinants are the actual constant terms of
   the characteristic polynomials of `M1_int` and
   `pencil_int_clean`: `det_M1_int = det_M1_int_value` and
   `D_pencil_int = D_pencil_int_value`, each closed via the same
   710-prime CRT product
   (`CRTPencilCheck.{det_M1_int_eq, D_pencil_int_eq}`) plus a
   closed-form Hadamard coefficient bound versus `crt_product_710`
   (`CRTPencilM1Bound.crt_bound_M1_sufficient_literal`,
   `CRTPencilPencilBound.crt_bound_pencil_sufficient_literal`).
3. The pencil-determinant identity at `λ = 4/105`:
   `det(λ·M1_rat − M2_rat) = det(M1_rat) · char_poly(A_rat)(4/105)`
   (`DetPencil.det_pencil`, generic mathcomp fact), where
   `A_rat := invmx(M1_rat) *m M2_rat`.  Combined with the integer
   determinant signs of (2), this gives
   `(char_poly A_rat).[4/105] < 0`.
4. The leading coefficient of `char_poly A_rat` is `1 > 0`, so above
   MathComp's `cauchy_bound` the evaluation is positive.  MathComp's
   `poly_ivtoo` then yields a `realalg` root *λ* in the open interval
   `(4/105, cauchy_bound)`.
5. `eigenvalue_root_char` + `map_char_poly` convert that root to
   `eigenvalue (map_mx ratr A_rat) λ`.

## 3. The Rocq tree, file by file

The dependency order is exactly the order of `_CoqProject`. There are
**41 `.v` files** under `theories/S1/` (33 top-level files plus 8
chunk files — `MaynardVerify/Def.v` + `MaynardVerify/M2_0..5.v` and
`CharPolyAgree/Def.v`), totaling ~15 964 lines, of which `Witness.v`
alone accounts for ~5 700 lines and `Witness_PencilClean.v` for
another ~1 890 lines of autogenerated certificate data.

### 3.1 Scaffolding and certificate data

**`Recompose.v`**. Defines `lift_bigZ : list BigZ.t_ -> list Z`.
Rocq's stdlib `Z` literal parser is superlinear; a 20 kbit literal
takes ~0.4 s to elaborate as `bigZ` but several seconds as `Z`.
Used by witness files for large constants.

**`Witness.v`** (autogenerated, ~5 700 lines).  The base
certificate: the 42-element `basis`, the integer matrices
`M1_int, M2_int`, and their denominators `D_M1, D_M2`.  Large
integers are written as `bigZ` where helpful to keep parser time
manageable.

**`Witness_PencilClean.v`** (autogenerated, ~1 890 lines).  Ships
the clean-pencil scalar `D_pencil_clean`, the 42×42 integer matrix
`pencil_int_clean`, and the shipped pencil determinant literal
`D_pencil_int_value`.

**`Witness_PencilDet.v`**, **`Witness_M1Bound.v`**,
**`Witness_PencilBound.v`** (autogenerated, small).  Ship the M1
determinant literal `det_M1_int_value` and the two Hadamard-style
coefficient-bound literals `fl_coeff_bound_{M1,pencil}_value`.

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


**`AllRowsLenHelper.v`**.  A tiny reflection helper bridging the
`forallb`-style `forall row, length row = n` check against the
proof-style `all_rows_len n M` predicate consumed by `CharPoly.v`.

### 3.3 Characteristic polynomial

**`CharPoly.v`** (~1 786 lines). One of the two "big" files. It gives:

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

### 3.4 Modular plumbing shared by CRT proofs

**`ModularArith.v`**. The single source of truth for Uint63 modular
arithmetic on matrices. Defines `addmod63`, `mulmod63`, `negmod63`,
`powmod_fast` (square-and-multiply with fuel), `inv_mod63` (via Fermat's
little theorem: *a^(-1) = a^(p-2)*), `divmod63`. Then a matrix layer:
`mmat := list (list int)`, `Z_to_mod63 p z`, `reduce_mat_Z p M`,
`mmat_vadd`, `mmat_add`, `mmat_vscale`, `mmat_scale`, `dot_mod`,
`mmat_heads`, `mmat_tails`, `mmat_trans_fuel`, `mmat_trans`, `mmat_mul`,
`mmat_trace`, `mmat_eye`, `mmat_zero`, `fl_mod_loop`, `char_poly_mod p
M`.

The existence of this file is *the* thing that unblocks the CRT
proofs in `CRTPencilCheck.v` — see Technique (c) in §4.

### 3.5 The 710 primes (CharPolyAgree/Def.v, CRTLift.v)

`CharPolyAgree/Def.v` (~878 lines) hosts the 710-prime list and
related structural definitions:

- `crt_primes_local : list int` (10 primes ≥ 2^30) and
  `crt_primes_extra` (700 more),
  `crt_primes_all := local ++ extra` (710 Uint63 primes, all ≥ 2^30).

`CRTLift.v` (slimmed to ~616 lines) hosts the supporting
`Z`-level primality / NoDup / coefficient-bound infrastructure
(`crt_primes_710_all_prime`, `crt_primes_710_NoDup`,
`crt_primes_valid`, `crt_product_710`, `crt_product_710_pos`,
`fl_coeff_bound`, `fl_bound_aux`, `max_abs_entry`).

The 710 primes come from three requirements:

1. Each prime *p* must satisfy *p < 2^31* so that *a·b < 2^62 < 2^63* —
   no 63-bit multiplication overflow inside `vm_compute`.
2. The product *∏ p_i* must exceed *2B* where *B* is a verified bound
   on the coefficient magnitude.  For the M1 determinant the bound is
   ~2044 bits; for the clean pencil determinant ~5830 bits; the
   710-prime product is >2^{21300}, well above either.
3. Each *p > n+1 = 43* so the FL recurrence's divisions by *k = 1..42*
   are all well-defined in *𝔽_p*.

### 3.6 CRT toolkit

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

**`CRTLift.v`** (slimmed to ~616 lines).  Generic CRT-lift toolkit:
`crt_primes_710_NoDup`, `crt_primes_710_all_prime`,
`crt_primes_valid`, `crt_product_710`, `crt_product_710_pos`,
`fl_coeff_bound`, `fl_bound_aux`, `max_abs_entry`.  Consumed by the
pencil determinant lifts in `CRTPencilCheck.v` (see §3.8).

### 3.7 Maynard input verification (M1, M2)

The five files `MaynardFactQ.v`, `MaynardBasis.v`, `MaynardSpec.v`,
`MaynardVerify.v`, `MaynardSpecBridge.v` close the trust loop on the
42x42 input matrices. They sit downstream of `Witness.v` and
`CharPoly.v`. `Cert.v` imports `MaynardVerify` and `MaynardSpecBridge`
(both feed the composed rat-level identity inside
`maynard_M105_certified_pencil`: the Z-level cross-multiplication
bool facts `all_match_M{1,2}Z_true` plus the rat↔Z bridges
`M{1,2}_spec_rat_eq` are lifted to a single rat equality
`M{1,2}_spec_ij = Z2rat (mat_get M{1,2}_int i j) / Z2rat D_M{1,2}`
by a `qfrac_eq_div` helper local to `Cert.v`).  The Z-level checks
and the Z↔rat bridges remain available as standalone Qeds for
auditors who want to trace the chain step-by-step.

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

### 3.8 The pencil-determinant backbone

This is the substantive content of the proof.  Eight files live
exclusively in this layer; they consume the Maynard / CharPoly /
CRT scaffolding from §3.2–§3.7.

**`Cert.v`** (~63 lines).  The composed paper-spec identity
`M{1,2}_spec_eq_int : M{1,2}_spec_ij i j = Z2rat(mat_get
M{1,2}_int i j) / Z2rat D_M{1,2}`, surfaced directly as the first
two conjuncts of the headline.  Internally composes
`MaynardSpecBridge.M{1,2}_spec_rat_eq` (rat = `qfrac` of a Z-pair),
the per-entry extraction `M{1,2}_entry_match_in_grid` from the
1764-cell `all_match_M{1,2}Z_true` grid, and the
`MaynardSpecBridge.qfrac_eq_div` helper.

**`CertL2.v`** (~134 lines).  Structural lemmas surfaced by the
pencil-determinant route: dimension / well-formedness on `M1_int`
(`M1_int_dim'`, `M1_int_rows_42`, `M1_int_wf'`); the rational
matrix `A_rat := invmx(mat_int_to_rat M1_int D_M1 42) *m
mat_int_to_rat M2_int D_M2 42`; the inverse witness `M1_1_unit`
(via `M1_charpoly_hd_neq0` — one-prime modular check that the
constant term of the modular char poly is nonzero, lifted to ℚ
through `char_poly_mod_sound`); and a small `pol_to_polyrat_coef0`
helper.

**`DetPencil.v`** (~30 lines).  Agent A's identity: for any
`comUnitRingType R`, dimension `n`, matrices `M1, M2 : 'M[R]_n` with
`M1 \in unitmx`, and scalar `λ`,
```
\det (λ *: M1 - M2)
  = \det M1 * (char_poly (invmx M1 *m M2)).[λ].
```
One-line proof on top of `char_poly_horner_eval`.

**`CertPencilDef.v`** (~172 lines).  Sealed wrappers for the
in-kernel determinants, using `sigT/proj1_sig` indirection to
prevent the kernel from unfolding the 42-step FL recurrence on a
42×42 matrix during conversion (the §4b problem at concrete
dimension).  Also exports the well-formedness lemmas on
`pencil_mat_int = pencil_int_clean` that downstream Hadamard chains
require.

**`AbstractPencilHelper.v`** (~116 lines).  Two generic-dimension
helpers: `pencil_cell_eq` and `pencil_matrix_bridge`, both written
at generic `F : fieldType` and generic `n : nat` to dodge the
MathComp HB-elaboration stall at concrete dim 42 (§4d).

**`PencilCleanGrid.v`** (~98 lines).  The 1764-cell per-entry
cross-check `D_M1·D_M2·pencil_int_clean[i,j] =
D_pencil_clean·(4·D_M2·M1_int[i,j] − 105·D_M1·M2_int[i,j])`, one
`vm_compute` Qed (`all_pencil_clean_match_true`), plus reflection
lemmas (`pencil_clean_match_in_grid`, `pencil_clean_match_Z`).

**`CRTPencilCheck.v`** (~374 lines).  The two integer determinants
themselves: `det_M1_int_eq : det_M1_int = det_M1_int_value` and
`D_pencil_int_eq : D_pencil_int = D_pencil_int_value`.  Both lift
per-prime modular agreement (from `CRTPencilChecksProof.v`) over
the 710-prime CRT product via `all_primes_divide_product`, then
close with `small_multiple_zero` under the Hadamard bound proved
in `CRTPencilM1Bound.v` / `CRTPencilPencilBound.v`.

**`CRTPencilChecksProof.v`** (~54 lines).  The two 710-prime
`vm_compute` Qeds `check_M1_det_710_true` and
`check_pencil_det_710_true`.  Each compares
`List.nth 0 (char_poly_mod p _) 0` against
`Z_to_mod63 p _value` for each `p` in `crt_primes_all`.  The
clean-pencil refactor was what made the single 710-prime list
suffice for both determinants.

**`CRTPencilHadamardGeneric.v`** (~74 lines).  A generic Hadamard
chain `|det M| ≤ fl_coeff_bound n (max_abs_entry M)` for square
matrices that pass `square_mat`.  Factored so that the M1 and pencil
specialisations are one-liners.

**`CRTPencilM1Bound.v`** (~46 lines) and
**`CRTPencilPencilBound.v`** (~59 lines).  Per-matrix
specialisations of the Hadamard chain plus the `vm_compute`
discharges `crt_bound_{M1,pencil}_sufficient_literal`.

**`CertPencil.v`** (~465 lines).  The headline assembly.  Lifts the
integer determinant signs (`D_pencil_int_neg`, `det_M1_int_pos`) to
rat-level (`pencil_rat_eq_int_scaled`, `det_M1_rat_eq_int_scaled`),
then applies `DetPencil.det_pencil` at `λ = 4/105` to obtain
`(char_poly A_rat).[4/105] < 0`.  Combined with `charpoly_lc_pos_rat`
(the leading coefficient of `char_poly A_rat` is `1 > 0`) and the
Cauchy-bound positive endpoint
(`charpoly_A_realalg_pos_at_cb`), MathComp's `poly_ivtoo` extracts
a `realalg` root strictly above `4/105`, which
`eigenvalue_root_char + map_char_poly` convert to the eigenvalue
statement.  Final theorems: `maynard_eigenvalue_S1_pencil` and
`maynard_M105_certified_pencil`.

## 4. The four critical techniques

### 4a. CRT lift via 710 Uint63 primes

The central computational obstacle is showing
`det_M1_int = det_M1_int_value` and
`D_pencil_int = D_pencil_int_value` in ℤ, where the LHS is the
constant term of `char_poly_int` of a 42×42 integer matrix.
`vm_compute` on these directly requires running Faddeev–LeVerrier
on integer matrices with arithmetic on hundreds-to-thousands-bit
numbers; the M1 determinant alone is 2044 bits, the clean pencil
2613 bits.  Empirically full FL on these matrices in `vm_compute`
inside the kernel is measurable in hours and produces proof terms
that are then impractical to type-check.

**Solution (`CRTPencilCheck.v` + `CRTPencilChecksProof.v`).**  Fix
710 primes *p_i* with *2^30 ≤ p_i < 2^31*.  For each *p_i*:

- `char_poly_mod p_i M` uses only Uint63 operations: 42 FL
  iterations, each doing a 42×42 modular multiplication
  (~74 000 Uint63 ops) plus a trace and a modular division.  Total
  ~10^7 Uint63 ops per prime; `vm_compute` handles this in ~0.5 s.
- `Z_to_mod63 p_i det_M1_int_value` (and `…_value` for the pencil):
  two ℤ-mod reductions, microseconds.
- Equality of the two constant terms (`Uint63.eqb`): another
  `vm_compute`.

So `check_M1_det_710` and `check_pencil_det_710` are `forallb`s
over 710 primes of single-prime checks, all inside Uint63
arithmetic.  `check_M1_det_710_true` and
`check_pencil_det_710_true` close by `vm_compute. reflexivity.`.

Lifting modular equality to ℤ uses `CRTCheck.v`'s
`small_multiple_zero` + `all_primes_divide_product`.  Key
ingredients (split across `CRTLift.v` and the `CRTPencil*` files):

- `crt_primes_710_NoDup`: 710 distinct primes (decidable `nodup_Z` +
  `vm_compute`).
- `crt_primes_710_all_prime`: each prime really is prime, by
  `check_prime_Z_sound` and a 710-step `forallb` check.  This
  dominates compile time — ~7 min.
- `crt_primes_valid`: each *p* satisfies *1 < p < 2^31*, needed by
  `Z_to_mod63_spec`.
- `crt_bound_{M1,pencil}_sufficient_literal`:
  `2·fl_coeff_bound_*_value + 2·|*_value| < crt_product_710`,
  closed by `vm_compute`.  The Hadamard bounds are 2044 / 5830 bits
  respectively, well within the ~21300-bit product.

Putting it all together (for the M1 determinant; the pencil follows
the same pattern):

```rocq
Theorem det_M1_int_eq : det_M1_int = det_M1_int_value.
Proof.
  apply (small_multiple_zero _ crt_product_710).
  - apply all_primes_divide_product.
    + exact crt_primes_710_NoDup.
    + exact crt_primes_710_all_prime.
    + intros p Hin. exact (per_prime_div_M1 p Hin).
  - exact crt_product_710_pos.
  - eapply Z.le_lt_trans;
      [exact (abs_diff_le det_M1_int_witness) | ].
    by rewrite fl_coeff_bound_M1_eq; exact crt_bound_M1_sufficient_literal.
Qed.
```

The Hadamard `fl_coeff_bound` is precomputed by the FLINT layer
(`fl_coeff_bound_{M1,pencil}_value`) and tied to the closed-form
recurrence by a `vm_compute`-Qed equality.

### 4b. `Strategy opaque` + sealing on the conversion side

Once `check_M1_det_710 = true` is established, to extract *per-prime*
agreement you want:

```rocq
Lemma per_prime_mod_eq_M1 (p : Uint63.int) (Hin : In p crt_primes_all) :
  List.nth 0 (char_poly_mod p M1_int) 0%uint63
    = Z_to_mod63 p det_M1_int_value.
```

The natural proof would `apply Uint63.eqb_eq` on the per-prime
extraction.  But the kernel must compare
`Uint63.eqb (List.nth 0 (char_poly_mod p M1_int) 0%uint63)
            (Z_to_mod63 p det_M1_int_value)`
against `true`, and its WHNF reducer wants to evaluate
`char_poly_mod p M1_int` — the full FL recurrence on a concrete
42×42 matrix.  Empirically that hangs at Qed time.

**Solution (used throughout `CRTPencilCheck.v` and
`CertPencilDef.v`).**  Combine two tricks:

- **`Strategy opaque`**: mark the offending constants
  (`char_poly_mod`, `Z_to_mod63`, `M1_int`, `pencil_mat_int`)
  opaque while extracting the bool fact.  Forces head-to-head
  comparison instead of WHNF descent.
- **`sigT/proj1_sig` sealing of the determinants** (in
  `CertPencilDef.v`): the kernel constants `det_M1_int` and
  `D_pencil_int` are *defined* as `proj1_sig` of an existential
  witness whose equation form `_eq_nth` is the only way to unfold
  them.  Downstream proofs (`CRTPencilCheck.det_M1_int_eq`, the
  sign lemmas in `CertPencil.v`) chain `_eq_nth` with the bool
  fact; the kernel never descends into the FL recurrence on the
  concrete matrix.

### 4c. ModularArith extraction

Before this project gained `ModularArith.v`, the two files
`CRTBridge.v` and the per-prime check files each defined their own
copies of `addmod63`, `mulmod63`, `mmat_add`, `mmat_mul`,
`mmat_trans`, `reduce_mat_Z`, `fl_mod_loop`, and crucially
`char_poly_mod`.  The bodies were identical text but the *constants*
were different (two `Definition char_poly_mod`s, one per file, with
the same source but distinct kernel identifiers).

When `CRTPencilCheck.v` tried to rewrite `char_poly_mod p M1_int`
(from CRTBridge) by a fact mentioning `char_poly_mod p M1_int`
(from a per-prime check file), the kernel saw two syntactically
distinct head constants. It could only unify them by
*delta-unfolding both*, which is precisely the 42-iteration FL
recurrence on concrete 42×42, which is precisely what we do not want
the kernel to do.

**Solution.** Factor every shared definition into a single
`ModularArith.v`. Both `CRTBridge.v` and the `CRTPencil*` files now
import from one canonical source. The `char_poly_mod` constant is
now a *single* kernel name, so unification of `char_poly_mod p
M1_int` against `char_poly_mod p M1_int` is by head reflexivity —
zero reduction, zero time.

This is not mathematics; it is a Rocq-engineering fix that deserves
a name because it is easy to miss. The header of `ModularArith.v`
explicitly documents the reason:

> Both CRTBridge.v and CharPolyAgree.v previously duplicated all of
> these definitions, which caused the kernel's conversion checker to
> explode when comparing terms involving char_poly_mod from different
> files (two different constants, identical bodies). Extracting them
> here ensures a single canonical definition.

### 4d. Generic-n helpers for MathComp's HB elaborator

`AbstractPencilHelper.pencil_cell_eq` and the rational-side lemmas
in `CertPencil.v` (`pencil_rat_scaled_eq`,
`pencil_rat_eq_int_scaled`, `det_M1_rat_eq_int_scaled`) work
entirely inside MathComp at `'M[rat]_42`.  Every call to a tactic
like `rewrite scalerA` or `apply char_poly_scale` forces MathComp's
HB canonical-structure resolver to locate the `scalarType` /
`ringType` / `comRingType` / `fieldType` / ... instances for
`'M[rat]_42`, `rat`, `{poly rat}`, and combinations thereof.

On a fully concrete `'M[rat]_42`, instance resolution traverses an
instance graph whose size is quadratic in the goal term.  This is
not kernel reduction — `Strategy opaque` does not help.  This is
the *tactic-level* elaborator walking the instance graph before the
tactic even starts.  Empirically it takes ~40–90 min per rewrite.

**Solution.**  Sections with abstract field and dimension.  Write
the slow algebraic manipulation once, inside a section that
abstracts over `F : fieldType` and `n : nat`.  Inside the section
the instance graph is small (`F` and `n` are opaque), so
elaboration is instantaneous.  At the call site, the section lemma
is applied with explicit arguments.  See
`AbstractPencilHelper.pencil_cell_eq` (generic-`F`, generic-`n`)
and `CertPencil.det_mat_int_to_rat_via_charpoly` (generic-`n`) for
the load-bearing instances.

**Summary of (4b) vs (4d).** The distinction is important:

- (4b) is about **kernel WHNF reduction** at conversion time,
  defeated by `Strategy opaque` plus `sigT/proj1_sig` sealing.
- (4d) is about **tactic-level elaboration** of MathComp's HB
  canonical structures, defeated by keeping the concrete
  `'M[rat]_42` out of the tactic goal (sections at generic *n*).

Both are invisible in textbook mathematics and both have to be
dealt with to get a proof of this size past the kernel.

## 5. The headline, layer by layer

Restating the goal:

```rocq
Theorem maynard_eigenvalue_S1_pencil :
  exists lambda : realalg,
    eigenvalue (map_mx (ratr : rat -> realalg) A_rat) lambda
    /\ (ratr (4%:Q / 105%:Q) : realalg) < lambda.
```

A combined sibling theorem in the same file,
`maynard_M105_certified_pencil`, conjoins this with two readable
rat-level identities stating that the paper-form spec equals the
FLINT integer entry over the common denominator:

```rocq
Theorem maynard_M105_certified_pencil :
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
and the rat↔Z bridges `MaynardSpecBridge.M{1,2}_spec_rat_eq` are
proof-internal implementation steps of the matrix conjuncts.  The
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
rat-level algebraic identities.  `Cert.M{1,2}_spec_eq_int` composes
L0 and L0' into a single rat-level identity (per (i,j) ∈ [0,42)²,
`M{1,2}_spec_ij i j = Z2rat (mat_get M{1,2}_int i j) / Z2rat D_M{1,2}`)
that is surfaced directly in the headline; the Z-level booleans and
rat↔Z bridges move into the proof body.

### L1 — Clean-pencil grid identity

Stated in `PencilCleanGrid.v`: for every `(i, j) ∈ [0, 42)²`,
```
D_M1 · D_M2 · pencil_int_clean[i,j]
  = D_pencil_clean · (4·D_M2·M1_int[i,j] − 105·D_M1·M2_int[i,j]).
```
One 1764-cell `vm_compute` Qed (`all_pencil_clean_match_true`).
Combined with `pencil_matrix_bridge` (from `AbstractPencilHelper.v`)
this lifts to a rat-level matrix identity
`D_M1 · D_M2 · (4 *: M1_rat − 105 *: M2_rat) = D_pencil_clean · pencil_int_clean`
required by L3.

### L2 — Integer determinants match the shipped literals

`CRTPencilCheck.det_M1_int_eq` (resp. `D_pencil_int_eq`) close
`det_M1_int = det_M1_int_value` (resp. `D_pencil_int =
D_pencil_int_value`) by the 710-prime CRT lift of §4a.  Both
together give `det_M1_int_pos` and `D_pencil_int_neg` in
`CertPencil.v` (via `det_M1_int_value_pos` /
`D_pencil_int_value_neg`, both single-`vm_compute` Qeds on the
shipped literals).

### L3 — Rat-level pencil identity at λ = 4/105

`CertPencil.pencil_rat_eq_int_scaled` lifts L1 to a rat-level
matrix equality, then `pencil_at_lambda` rewrites
`(4 *: M1_rat − 105 *: M2_rat) = 105 *: (lambda_q *: M1_rat − M2_rat)`
(where `lambda_q := 4/105`), so the sign of the rat-level pencil
determinant at `λ = 4/105` equals the sign of the shipped clean
pencil determinant.

### L4 — Pencil identity → char_poly evaluation

`DetPencil.det_pencil` applied at `M1 := M1_rat`, `M2 := M2_rat`,
`l := 4/105` gives
```
\det (lambda_q *: M1_rat − M2_rat)
  = \det M1_rat * (char_poly A_rat).[lambda_q]
```
where `A_rat := invmx M1_rat *m M2_rat`.  Combined with the
positive sign of `det M1_rat` (from `det_M1_int_pos` lifted via
`det_mat_int_to_rat_via_charpoly`) and the negative sign of `\det
(lambda_q *: M1_rat − M2_rat)` (from L3), this gives
`(char_poly A_rat).[4/105] < 0`
(`CertPencil.abstract_charpoly_neg` then
`charpoly_neg_at_threshold_rat`).

### L5 — IVT root existence in realalg

`CertPencil.maynard_root_above_threshold` runs `poly_ivtoo` (from
mathcomp-real-closed) on `charpoly_A_realalg := map_poly ratr
(char_poly A_rat)`:
- lower endpoint `lambda_ralg := ratr (4/105)`:
  `charpoly_A_realalg_neg_at_threshold` from L4 lifted via
  `map_polyZ` and `horner_map`.
- upper endpoint `cauchy_bound (charpoly_A_realalg)`:
  `charpoly_A_realalg_pos_at_cb` from `charpoly_lc_pos_rat`
  (leading coef is `1 > 0`) and the standard `cauchy_bound` fact.
- nonzero: `charpoly_A_realalg_neq0`.

`poly_ivtoo` returns `x ∈ [lambda_ralg, cb]` with
`charpoly_A_realalg.[x] = 0`; since the endpoint sign at
`lambda_ralg` is strict, `lambda_ralg < x`.

### L6 — Root → eigenvalue

`maynard_eigenvalue_S1_pencil` is two lines:

```rocq
rewrite eigenvalue_root_char
  -(map_char_poly (ratr : {rmorphism rat -> realalg})).
exact: Hroot.
```

`map_char_poly` says `char_poly (map_mx f M) = map_poly f (char_poly M)`
for a ring morphism *f*; `eigenvalue_root_char` says an eigenvalue is
exactly a root of the char poly.

## 6. Trust base

The recommended canonical Print-Assumptions target is
`maynard_M105_certified_pencil`: a single lemma whose assumptions
cover (a) the rat-level identity stating that the paper-form spec
`MaynardSpec.M{1,2}_spec_ij` equals the FLINT integer entry over
the common denominator (composed internally from the Z-level
matrix cross-check `all_match_M{1,2}Z = true` and the rat↔Z
bridges `MaynardSpecBridge.M{1,2}_spec_rat_eq`), and (b) the
eigenvalue bound.  The spectral-only sibling
`maynard_eigenvalue_S1_pencil` is also present; it is strictly
weaker for end-to-end audit because it does not surface the
closed-form match.  Auditors who want to inspect the internal
Z-level cross-check or the rat↔Z bridge separately can still
target `MaynardVerify.all_match_M{1,2}Z_true` and
`MaynardSpecBridge.M{1,2}_spec_rat_eq` directly — they remain
standalone Qeds.

`Print Assumptions maynard_M105_certified_pencil` after `coqc` of
`CertPencil.v` prints only standard `PrimInt63.*` / `Uint63Axioms.*`
kernel primitives shipped with Rocq 9.0/9.1 and the `Bignums`
library: things like `Uint63.add`, `Uint63.mul`, `Uint63.to_Z`,
`BigN.succ_spec`. No project-specific axioms appear.
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
autogenerated witness files are ordinary Rocq files.  If the FLINT
layer shipped incorrect data, one of the following
`vm_compute`-based checks would fail to reduce to `true` and the
build would stop:

- `MaynardVerify.all_match_M1Z = true`, `all_match_M2Z = true` —
  the 42x42 input matrices match Maynard's closed form (Lemma 8.1 /
  eq. 8.4). This closes the trust gap on the matrix entries
  themselves, not just downstream derivations. The companion doc
  `SPEC_TO_PAPER.md` at the repo root maps every `MaynardSpec`
  definition to the corresponding line of arXiv:1311.4600 v3 §8.
- `PencilCleanGrid.all_pencil_clean_match_true` — the shipped
  `pencil_int_clean` literal equals `4·D_M2·M1_int − 105·D_M1·M2_int`
  per-cell after the appropriate scaling.
- `CRTPencilChecksProof.check_M1_det_710_true` and
  `check_pencil_det_710_true` — the shipped constant-term literals
  for the two integer determinants are correct modulo each of 710
  Uint63 primes.
- `CRTPencilM1Bound.crt_bound_M1_sufficient_literal` and
  `CRTPencilPencilBound.crt_bound_pencil_sufficient_literal` —
  `2·bound + 2·|literal| < crt_product_710` for each determinant.

Each of these is `Qed` and reduces in pure kernel arithmetic. The
repository has zero `Axiom` declarations and zero `Admitted` lemmas
anywhere.

## 7. Numerical highlights

- **Matrix dimension.** 42×42. Maynard's *M_{105}* construction uses 42
  basis polynomials {*x^b · y^c : b + 2c ≤ 11*}. The 42-element
  `Witness.basis` enumerates them.
- **Determinants.** `det(M1_int)` is 2044 bits, positive;
  `det(pencil_int_clean)` is 2613 bits, negative.
- **CRT primes.** 710 Uint63 primes, all in [2^30, 2^31), listed in
  `CharPolyAgree/Def.v`: `crt_primes_local` has 10, `crt_primes_extra`
  has 700. The product exceeds 2^{21 300}, well above the
  Hadamard-style coefficient bounds (~2^2044 for `M1_int`, ~2^5830 for
  the clean pencil).
- **Denominators.** `D_M1` has ~221 decimal digits, `D_M2` ~227,
  `D_pencil_clean` ~210 decimal digits. All three are strictly
  positive.
- **Cauchy bound.** The IVT step uses MathComp's `cauchy_bound` — an
  explicit rational upper bound on all real roots of the polynomial,
  derived from the coefficients. No custom bound is needed.
- **Build time.** A clean rebuild on a 16 GB / 6-thread machine takes
  **~30–50 min wall with `make -j6`**.  The dominant costs are:
  - `MaynardVerify.all_match_M2Z_true`: ~35 min CPU total (six
    `M2_0..5.v` chunks at ~6–18 min CPU each, `vm_compute` over
    1764 entries each summing up to 36 rational terms with
    ~10^7000-digit accumulator denominators). Under `make -j6`
    the six chunks run concurrently.
  - `crt_primes_710_all_prime`: ~7 min (710 Z-level primality checks
    by trial division).
  - `check_M1_det_710_true`, `check_pencil_det_710_true`: ~5–10 min
    each (710 × 42-step FL in Uint63, plus the constant-term
    extraction).
  - `crt_bound_{M1,pencil}_sufficient_literal`: a few minutes each
    (`vm_compute` on a few-thousand-digit arithmetic comparison).
  - `MaynardVerify.all_match_M1Z_true`: ~90 s.
  - `Witness.v` / `Witness_PencilClean.v` parsing: ~30–60 s.
- **Total Rocq proof size.** 41 `.v` files (33 top-level files plus
  8 chunk files: `MaynardVerify/Def.v`, `MaynardVerify/M2_0..5.v`,
  `CharPolyAgree/Def.v`), ~15 964 lines under `theories/S1/`;
  `Witness.v` alone is ~5 700 lines and `Witness_PencilClean.v`
  ~1 890 lines of autogenerated certificate data.

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

L0+L0' composed (rat-level paper-form = FLINT entry)
  Cert.v   M1_spec_eq_int, M2_spec_eq_int

L1 (clean pencil grid identity)
  PencilCleanGrid.v   all_pencil_clean_match_true (1764-cell vm_compute)
    + Witness_PencilClean.v provides D_pencil_clean, pencil_int_clean

L2 (integer determinants match shipped literals)
  CRTPencilCheck.v   det_M1_int_eq, D_pencil_int_eq
    + CRTPencilChecksProof.v  check_{M1,pencil}_det_710_true (710 primes)
    + CRTPencilM1Bound.v / CRTPencilPencilBound.v  Hadamard bound vs. crt_product_710
    + CRTLift.v  crt_primes_710_NoDup, _all_prime, crt_product_710, fl_coeff_bound
    + CRTBridge.v  char_poly_mod_sound
    + Witness_{PencilDet,M1Bound,PencilBound}.v shipped literals

L3 (rat-level pencil identity)
  CertPencil.v   pencil_rat_eq_int_scaled
    + AbstractPencilHelper.v  pencil_cell_eq, pencil_matrix_bridge
    + PencilCleanGrid.v  pencil_clean_match_Z

L4 (pencil identity → char_poly evaluation)
  DetPencil.v   det_pencil      (generic mathcomp fact)
  CertPencil.v  pencil_at_lambda, abstract_charpoly_neg,
                charpoly_neg_at_threshold_rat
    + CertL2.v  A_rat, M1_1_unit

L5 (IVT root above 4/105 in realalg)
  CertPencil.v  maynard_root_above_threshold
    + mathcomp-real-closed  poly_ivtoo, cauchy_bound

L6 (char_poly root → eigenvalue)
  CertPencil.v  maynard_eigenvalue_S1_pencil
    + MathComp: map_char_poly, eigenvalue_root_char

Headline (canonical, end-to-end):
  CertPencil.v  maynard_M105_certified_pencil
    = (forall i j, M1_spec_ij i j = Z2rat M1_int[i,j] / Z2rat D_M1)
      /\ (forall i j, M2_spec_ij i j = Z2rat M2_int[i,j] / Z2rat D_M2)
      /\ maynard_eigenvalue_S1_pencil
    (the two rat-level identities are composed internally from
     all_match_M{1,2}Z_true and M{1,2}_spec_rat_eq via Cert.v)

Headline (eigenvalue-only sibling):
  CertPencil.v  maynard_eigenvalue_S1_pencil
```

The dependency graph has two independent backbones that merge at
`CertPencil.v`:

- **Pencil backbone**: Witness / Witness_PencilClean →
  IntMat / IntPoly → CharPoly → ModularArith → CharPolyAgree/Def +
  CRTLift + CRTBridge → CRTPencilCheck + CRTPencilChecksProof +
  CRTPencilHadamardGeneric + CRTPencilM1Bound + CRTPencilPencilBound
  + PencilCleanGrid + AbstractPencilHelper + CertPencilDef +
  DetPencil + CertL2 → CertPencil.
- **Maynard-spec backbone**: Witness → MaynardFactQ →
  MaynardBasis + MaynardSpec → MaynardVerify (+ M2 chunks) +
  MaynardSpecBridge → Cert → CertPencil.

Everything lives behind a single Rocq `Require` — `Require Import
PrimeGapS1.CertPencil.` loads the full proof.
