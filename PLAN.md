# Plan: formalise Maynard's M1 / M2 specification inside Rocq

## Objective

Close the loop on `M1_int`, `M2_int` in `theories/S1/Witness.v`: prove, inside
the Rocq kernel, that these integer matrices (divided by `D_M1`, `D_M2`) agree
with a structural Rocq definition that transcribes Maynard's closed-form
specification for the 42x42 Gram matrices *M1*, *M2* used in
*M_{105} > 4* (arXiv:1311.4600 §7-8).

After this work the FLINT layer's role is strictly independent
cross-check / data generation — the Rocq proof no longer trusts *any*
transcription of Maynard's formula by the Python layer.

## Non-goals

- Re-prove the analytic Dirichlet integral `∫_Δ ∏ t_i^{a_i} dt = ∏ a_i! / (k + Σ a_i)!`
  from measure theory. We take the closed form as the rational **definition**,
  in a dedicated file with a comment pointing at the analytic meaning. This
  avoids pulling `coq-mathcomp-analysis` into the project.
- Redo any of the current CertL1/CertL2/Cert assembly. This work is additive.

## Ecosystem inputs (reusable from already-installed 2.5 switch)

- `mathcomp.boot.binomial`: `factorial` (`n`!), `bin`, `fact_prod`, `bin_fact`.
- `mathcomp.multinomials.mpoly`: `'X_{1..n < b}`, `{mpoly R[n]}`, `mcoeffM`.
  (We do not actually need `{mpoly _ _}` for the matrix values themselves —
  only for the basis enumeration if we want a structural one.)
- `mathcomp.algebra.rat`: `rat`, `_%:Q`, ring/field tactics.
- `mathcomp-analysis 1.15` has `beta_fun_fact` in
  `probability_theory/beta_distribution.v`. **Not a runtime dependency of
  this plan**, but noted so that a future, stronger proof reducing the
  closed form to a real integral can plug it in.

## Mathematical input (from research agent §1-§4)

Fix `k := 105`, degree cap `11`, basis size `42`.

- Basis: all `(b, c) ∈ nat × nat` with `b + 2c ≤ 11`. The ordering used in
  `theories/S1/Witness.v:21-65` is the Mathematica `xExponents[5]`,
  `yExponents[5]` enumeration; it is not lexicographic.

- **Auxiliary polynomial** `G_{n,2}(k) : rat` (from Maynard Lemma 7.1):
  ```
  G_{0,2}(k) = 1
  G_{n,2}(k) = k · (2n)!
             + Σ_{i = 1}^{n - 1} C(k, i + 1) · Σ_{a ∈ Bnd(i, n)} Cff(a, n)
  Cff(a, n)  = n! · ∏_{j} (2 a_j)! / a_j!  ·  (2(n - Σa))! / (n - Σa)!
  Bnd(i, n)  = { a ∈ nat^i : each a_j ≥ 1 and Σ a_j ≤ n - 1 }
  ```
  For fixed `k = 105` and `n ≤ 11`, this is a list of 12 concrete rationals.
  For `k = 104` and `n ≤ 22`, a list of 23 concrete rationals.

- **M1 entry** (single term):
  ```
  M1(b_i, c_i, b_j, c_j) = (b_i + b_j)! / (k + b + 2c)! · G_{c, 2}(k)
    where b = b_i + b_j, c = c_i + c_j
  ```

- **M2 entry** (double sum over `cp1 ∈ [0, c_i]`, `cp2 ∈ [0, c_j]`):
  ```
  α(b, c, cp) = C(c, cp) · b! · (2c - 2cp)! / (b + 2c - 2cp + 1)!

  M2(b_i, c_i, b_j, c_j) =
    Σ_{cp1 = 0}^{c_i} Σ_{cp2 = 0}^{c_j}
      α(b_i, c_i, cp1) · α(b_j, c_j, cp2)
      · bsum! / ((k-1) + bsum + 2 · csum)!
      · G_{csum, 2}(k - 1)
    where bsum = (b_i + 2c_i - 2cp1 + 1) + (b_j + 2c_j - 2cp2 + 1),
          csum = cp1 + cp2
  ```

All factorials have arguments `≤ 127`; all sums have at most 36 terms per
entry; 42 × 42 = 1764 entries per matrix.

## Architecture

Four new files, added to `_CoqProject` in this order, BEFORE `Cert.v` / after
`Witness.v`:

```
theories/S1/MaynardFactQ.v      # factorial / binomial as rat, small helpers
theories/S1/MaynardBasis.v      # the 42-pair basis with an ordering lemma
theories/S1/MaynardSpec.v       # G_{n,2}, M1_spec, M2_spec : rat closed forms
theories/S1/MaynardVerify.v     # vm_compute-proved agreement with Witness.v
```

No existing file is modified. `Cert.v` is not touched. The project still
compiles if any of these four fail to compile, because they are leaves in the
dependency DAG.

## File-by-file design

### MaynardFactQ.v  (~80 lines)

Tiny helper file. Uses only `mathcomp.ssreflect` + `mathcomp.algebra`.

```coq
From mathcomp Require Import all_ssreflect all_algebra.
Import GRing.Theory.
Open Scope ring_scope.

Definition factQ (n : nat) : rat := (n`!)%:R.
Definition binQ (n k : nat) : rat := ('C(n, k))%:R.

Lemma factQ_nz (n : nat) : factQ n != 0.
Lemma factQ_succ (n : nat) : factQ n.+1 = (n.+1)%:R * factQ n.

(* Pair of (numerator, denominator) with positive denominator,
   for entry representation before the final rat construction.
   Useful for vm_compute so we stay in Z/Z arithmetic. *)
```

### MaynardBasis.v  (~150 lines)

Defines the 42-element basis matching `Witness.v` exactly.

```coq
(* Maynard's Mathematica enumeration: for stratum i = 0..5, emit monomials
   built from tmp = 2·[1..i+1] and tmp' = [i, i-1, ..., 1, 0]. *)

Definition maynard_basis : seq (nat * nat) := <explicit 42-element literal>.

Lemma maynard_basis_size : size maynard_basis = 42.
Proof. by []. Qed.

Lemma maynard_basis_degree (bc : nat * nat) :
  bc \in maynard_basis -> bc.1 + 2 * bc.2 <= 11.
Proof. by case: bc => ? ?; rewrite /maynard_basis !inE; do 42 (case/orP;
  [move/eqP->|]); [..]; reflexivity. Qed.  (* vm_computable *)

Lemma maynard_basis_eq_witness :
  maynard_basis = List.map <project Witness.basis> (iota 0 42).
Proof. vm_compute. reflexivity. Qed.
```

The `maynard_basis = Witness.basis` bridge is just a `vm_compute`-closeable
list-equality between two concrete `seq (nat * nat)`.

### MaynardSpec.v  (~300 lines)

The closed-form definitions.

```coq
From PrimeGapS1 Require Import MaynardFactQ MaynardBasis.

(* Integer compositions of length i with entries >= 1 summing to <= n-1. *)
Definition bnd (i n : nat) : seq (seq nat) := <list-of-seq enumeration>.

Definition cff (a : seq nat) (n : nat) : rat :=
  factQ n * \prod_(x <- a) (factQ (2 * x) / factQ x)
           * (factQ (2 * (n - sumn a)) / factQ (n - sumn a)).

Definition G_2 (n k : nat) : rat :=
  if n == 0 then 1 else
    k%:R * factQ (2 * n) +
    \sum_(i <- iota 1 n.-1) binQ k i.+1 * \sum_(a <- bnd i n) cff a n.

Definition M1_entry (bi ci bj cj : nat) : rat :=
  let b := bi + bj in
  let c := ci + cj in
  factQ b / factQ (105 + b + 2 * c) * G_2 c 105.

Definition alpha (b c cp : nat) : rat :=
  binQ c cp * factQ b * factQ (2 * c - 2 * cp) / factQ (b + 2 * c - 2 * cp + 1).

Definition M2_entry (bi ci bj cj : nat) : rat :=
  \sum_(cp1 <- iota 0 ci.+1)
    \sum_(cp2 <- iota 0 cj.+1)
      let bsum := (bi + 2 * ci - 2 * cp1 + 1) + (bj + 2 * cj - 2 * cp2 + 1) in
      let csum := cp1 + cp2 in
      alpha bi ci cp1 * alpha bj cj cp2
      * factQ bsum / factQ (104 + bsum + 2 * csum)
      * G_2 csum 104.

Definition M1_spec_ij (ij : nat * nat) : rat :=
  let bci := nth (0, 0) maynard_basis ij.1 in
  let bcj := nth (0, 0) maynard_basis ij.2 in
  M1_entry bci.1 bci.2 bcj.1 bcj.2.

Definition M2_spec_ij (ij : nat * nat) : rat :=
  let bci := nth (0, 0) maynard_basis ij.1 in
  let bcj := nth (0, 0) maynard_basis ij.2 in
  M2_entry bci.1 bci.2 bcj.1 bcj.2.
```

Everything is pure rational arithmetic on small factorials. `vm_compute`
evaluates every entry to its canonical `rat` representative.

### MaynardVerify.v  (~150 lines)

Agreement with the shipped integer data.

```coq
From PrimeGapS1 Require Import IntMat CharPoly Witness MaynardSpec.

(* mat_int_to_rat is already defined in CharPoly.v for dim 42. *)
Definition M1_rat : 'M[rat]_42 := mat_int_to_rat M1_int D_M1 42.
Definition M2_rat : 'M[rat]_42 := mat_int_to_rat M2_int D_M2 42.

Definition M1_spec : 'M[rat]_42 := \matrix_(i, j) M1_spec_ij (i, j).
Definition M2_spec : 'M[rat]_42 := \matrix_(i, j) M2_spec_ij (i, j).

Lemma M1_correct : M1_rat = M1_spec.
Proof. apply/matrixP => i j. rewrite !mxE. vm_compute. reflexivity. Qed.

Lemma M2_correct : M2_rat = M2_spec.
Proof. apply/matrixP => i j. rewrite !mxE. vm_compute. reflexivity. Qed.
```

Each `vm_compute` reduces a single rational on both sides and compares them.
1764 per matrix = 3528 total reductions, each O(factorial(≤127) + small sum).
Expected total time: **seconds, worst case a minute**.

### Fallback if `apply/matrixP => i j` Qed is slow

The elaboration of `'M[rat]_42` is known slow in this project (see REPORT.md
§4d). Mitigations, in order:

1. Replace the `matrixP` approach with an entry-wise check in `Prop`:
   ```coq
   Lemma M1_correct_entry (i j : 'I_42) :
     mat_int_to_rat M1_int D_M1 42 i j = M1_spec_ij (nat_of_ord i, nat_of_ord j).
   ```
   Avoids `\matrix_(..)` materialisation.

2. Aggregate via `forallb` over `iota 0 42` × `iota 0 42`, each entry a
   list-to-list `rat` comparison, closed by one `vm_compute`:
   ```coq
   Lemma M1_correct_bool :
     all (fun i => all (fun j =>
       rat_eqb (mat_get_rat M1_int D_M1 i j) (M1_spec_nat i j)) (iota 0 42))
         (iota 0 42).
   Proof. vm_compute. reflexivity. Qed.
   ```
   Then lift to `M1_rat = M1_spec` with a light matrixP bridge done
   off-the-critical-path.

3. If `rat` vm_compute is slow (canonical-form normalisation), fall back to
   comparing *numerators with common denominator*: represent each side as
   `(num : int, den : positive)` and compare `num1 * den2 = num2 * den1`
   with `Z`. This stays in `Z` arithmetic only and should be fastest.

## Risk register

| Risk | Likelihood | Mitigation |
|---|---|---|
| `maynard_basis` does not match `Witness.basis` | medium | bridge lemma by `vm_compute. reflexivity` catches it immediately |
| `G_2` expression off by one (0-based vs 1-based `iota`) | medium | unit-test on `G_2 1 105`, `G_2 2 105` against expected Python values |
| Eq. 7.8 `y^{cp}` vs `(1-x')^{2cp}` ambiguity | low | project already commits to MMA-literal form; stay consistent |
| `'M[rat]_42` apply/matrixP Qed slow | medium | fall back to `forallb` + `vm_compute` bool form (see §Fallback) |
| `rat` vm_compute slow on large numerators | low | fall back to `num * den'` integer equality |
| New files perturb the existing build | very low | they are leaves in the DAG and not imported by `Cert.v` |

## Unit tests to run first (before touching Rocq)

In Python, to validate the formulas we will transcribe:

```python
# Verify G_2 produces the same values as the existing flint_probe.py
from flint_probe import Poly_at_k  # or equivalent
from fractions import Fraction
k = 105
for n in range(12):
    print(n, Poly_at_k(n, 2, k))
```

Compare with a Rocq-side `vm_compute` test once `MaynardSpec.v` exists.

## Implementation order

1. `MaynardFactQ.v`  — ~5 min, trivial.
2. `MaynardBasis.v`  — ~30 min, mostly transcribing the 42-element literal.
   Validate with `vm_compute` bridge to `Witness.basis`.
3. `MaynardSpec.v`   — ~90 min, careful transcription of the formulas.
   Spot-check ~5 entries against Python values before committing.
4. `MaynardVerify.v` — ~30 min + compile time.
5. If a `vm_compute` equality stalls, apply the Fallback §.

Total estimated effort: **one afternoon + ~5 min of compile time per iteration**.

## Success criteria

- `M1_correct` and `M2_correct` are `Qed` (not `Admitted`, not axiomatised).
- `Print Assumptions M1_correct` and `Print Assumptions M2_correct`
  report only `PrimInt63.*` / `Uint63Axioms.*` — no new project axioms.
- `make -j` still succeeds end-to-end (Cert.v still compiles, no
  regressions).
- A brief paragraph added to `REPORT.md` §7 noting that M1, M2 are now
  kernel-verified against Maynard's closed form.
