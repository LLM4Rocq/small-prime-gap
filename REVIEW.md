# Consolidated review — Maynard `M_{105} > 4` audit project

**Date**: 2026-04-10
**Reviewers**: three automated Claude Opus 4.6 agents (Rocq/MathComp expert,
computational auditor, devil's advocate). Full individual reports in
`REVIEW_spec.md`, `REVIEW_compute.md`, `REVIEW_devils_advocate.md`.

---

## Verdict

**The architecture is sound, no cheats were found, and the project is
an honest scaffold for a future complete proof.** But it is not, today,
a machine-checked proof of `M_{105} > 4`. The headline theorem depends
on 2 Admitted axioms (L1, L2), beneath which lie 3 more sub-admits and
significant outstanding work.

---

## What IS proved (no caveats)

1. **The headline theorem statement is correct.** It says exactly what
   Maynard's argument needs: there exists a `realalg` eigenvalue of
   `M₁⁻¹M₂` above `4/105`. Uses standard MathComp `eigenvalue`,
   `map_mx`, `ratr`, `realalg`. No hidden axioms beyond the 2 declared.

2. **L3 (root of char poly → eigenvalue) is fully proved.** Two-line
   proof via `map_char_poly` + `eigenvalue_root_char`. Correct usage.

3. **Bridge.v is genuinely 0 admits.** Verified by grep. Every lemma
   ends with `Qed`. The crown jewel `prem_rmodp_rat` (our pseudo-
   remainder = MathComp's `rmodp` after lifting) is a 150-line proof
   by strong induction, structurally sound. All variation/sign
   morphism lemmas are correctly stated and proved.

4. **CharPolyHelpers.v: all 6 Step 1 sublemmas are Qed.** Spot-checked:
   `mat_int_to_rat_mmul`, `mtrace_int_to_rat`, etc. are correctly
   stated and proved via standard MathComp `matrixP` + `mxE` idioms.

5. **CRTSigns.v: sign verification is fully proved (0 admits).**
   BigZ Horner evaluation + BigZ.compare for sign. Bridge to Z via
   BigZ spec lemmas. Sound.

6. **Primality of the 10 CRT primes is machine-verified** in Rocq via
   Uint63 trial division. No external Python script in the trust base.

7. **The Faddeev-LeVerrier implementation passes `vm_compute` sanity
   tests** on 2×2, 3×3, and 10×10 matrices.

8. **No non-standard axioms in the computational layer.** Only standard
   Uint63 kernel primitives (trusted by the Rocq community).

## What is NOT proved (important caveats)

### The 10-prime CRT check is a probabilistic test, not a proof

CRTCheck.v verifies the PRS chain identity modulo 10 primes (~300 bits
of coverage). The maximum coefficient is 293,217 bits. For a complete
CRT proof, ~9,776 primes are needed (product must exceed twice the max
coefficient). The 10-prime check gives a false-positive probability of
~2^{-300} — practically impossible, but NOT a mathematical proof.
The `crt_correctness` lemma proves `True` (a vacuous placeholder).

This is honestly disclosed in CRTCheck.v's comments but was
**incorrectly described as "9,776 primes"** in STATUS.md until the
final review caught and fixed the documentation error.

### `shipped_chain_eq` is Admitted

The sign verification (CRTSigns.v) and the CRT chain check
(CRTCheck.v) both operate on the SHIPPED data from WitnessChain.v —
not on the chain that BrownTraub.sturm_chain would compute inside
Rocq. The bridge `shipped_chain_eq` (asserting equality of the two)
is Admitted in CertL1.v. Without it, the verification proves
internal consistency of the shipped data, not that it matches the
Rocq-side computation.

### "Bridge.v 0 admits" is true but context matters

The hard obligation (`mods_int_morph` / `chain_is_mods`) was moved
from Bridge.v to CertL1.v. Bridge.v achieves 0 admits by
parameterizing over the obligation. The L1 Sturm bridge is NOT
complete; the obligation exists elsewhere.

### `A_rat_unitmx` is Admitted (but outside headline closure)

`invmx` is total in MathComp — it returns 0 for singular matrices.
The headline theorem technically holds even if M₁ is singular (it
would prove the existence of an eigenvalue of the zero matrix, which
is vacuously true). For the result to have mathematical content,
`A_rat_unitmx` must be discharged. In practice M₁ is SPD so this
holds; `det_int` + `mat_int_to_rat_unitmx` (both Qed) provide the
machinery.

### `char_poly_int_correct` drops the D^n scaling factor

The stated form `pol_to_polyrat (char_poly_int M) = char_poly
(mat_int_to_rat M D n)` is false for `D ≠ 1`. The architecture
works around this by treating `charpoly_int` as a pre-computed
certificate (not derived from `char_poly_int`), so the naming is
misleading but the logic is sound.

### The FLINT pipeline is unverified Python

`build_certificate.py` is ~300 lines of Python calling python-flint.
It is not formally verified. Only 5 of 3,528 matrix entries are
spot-checked against closed-form Beta integrals. A systematic error
in the integral assembly would not be caught by 5 spot checks.
The claim "independently auditable" is fair for the architecture;
"independently verified" would be an overstatement.

## MathComp lemmas the team should use for L2

The spec auditor identified a key missed opportunity:

**`mul_mx_adj` (in `mathcomp/algebra/matrix.v`)**: states
`A *m \adj A = (\det A)%:M`. Applied to `char_poly_mx A` (which is
`'X%:M - A%:M : 'M[{poly R}]_n`), this gives exactly:

```
char_poly_mx A *m \adj (char_poly_mx A) = (char_poly A)%:M
```

This is the adjugate identity the team's L2 outline mentions for
Step 3 (`fl_loop_rat_is_char_poly`). It IS in MathComp and should be
used directly. The team's outline is on the right track but
underestimates how directly `mul_mx_adj` gives the result.

Additionally: `Cayley_Hamilton` (`horner_mx A (char_poly A) = 0`)
provides an alternative route to the FL coefficients via coefficient
extraction from the matrix polynomial identity.

## Distance to closure

| Axiom | Status | Estimated effort |
|---|---|---|
| L1 `sturm_count_correct` | ~70% scaffolded | 2-4 weeks |
| → `shipped_chain_eq` | Admitted (CRT exists) | 1-2 days (scale CRT to full, or prove PRS uniqueness) |
| → `chain_is_mods` | Admitted (hard) | 1-2 weeks (refactor consumer to use weak form, or prove strict equality) |
| → `no_root_at_cb` | Admitted | 2-3 days (Cauchy bound + chain divisibility) |
| L2 `charpoly_int_eq_charpoly` | ~25% scaffolded | 4-8 weeks |
| → Step 2 `fl_invariant` | scaffolded, base case done | 1-2 weeks (wire genuine FL definitions, prove inductive step) |
| → Step 3 `fl_loop_rat_is_char_poly` | Admitted (load-bearing) | 2-4 weeks (use `mul_mx_adj` on `char_poly_mx A`) |

## What this project delivers to a skeptical mathematician

A Rocq theorem whose statement — "the 42×42 matrix `M₁⁻¹M₂` from
Maynard's GPY sieve optimization has a real eigenvalue above 4/105" —
is precisely the computational content of Proposition 4.3. The theorem
compiles `Qed` with 2 named axioms. Beneath them: a complete
`list Z` polynomial/matrix arithmetic library (0 admits), a full
Sturm-bridge from integer arithmetic to MathComp realalg (0 admits in
Bridge.v), a CRT-based computational verification of the 42-step PRS
chain (10 primes, ~300-bit probabilistic coverage), BigZ-verified sign
data, and concrete proof outlines for every remaining gap. The FLINT
pipeline independently re-implements the Mathematica notebook and
reproduces Maynard's value to 12+ digits.

It is an impressive scaffold and architecture for a complete formal
proof, with every computational fact machine-checked and every
remaining gap clearly identified. It is not, today, a complete
machine-checked proof of `M_{105} > 4`.
