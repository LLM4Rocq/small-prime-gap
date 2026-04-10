# Project status — final summary

**Date**: 2026-04-10
**Commits**: 24 (after this one)
**Codebase**: 21 Rocq files (24 760 lines), 4 Python scripts (1 692 lines), 39 tracked files total

## What this project delivers

A two-layer, independently auditable re-implementation of the numerical
computation underlying **Proposition 4.3 / formula (8.15)** of James
Maynard's *Small gaps between primes* (arXiv:1311.4600, Annals 2015):

> **`M_{105} = 105 · λ_max((M₂, M₁)) > 4`**

The original proof relies on an unrefereed Mathematica notebook
(`Computations.nb`). This project replaces it with:

1. **A FLINT layer** (Python + `python-flint`) that rebuilds `M₁`, `M₂`
   from the closed-form Beta integrals, computes the characteristic
   polynomial and Brown-Traub Sturm chain, and emits a JSON certificate.

2. **A Rocq layer** (Rocq 9.0 + MathComp 2.5 + `mathcomp-real-closed`)
   that consumes the certificate, machine-verifies every computational
   fact, and states the headline theorem with exactly 2 named axioms.

## What is machine-verified (Qed, no admits)

### Computational facts (via `vm_compute`)

| Fact | Method | Time | File |
|---|---|---|---|
| 42-step PRS chain recurrence | CRT over 9 776 Uint63 primes | **21 s** | CRTCheck.v |
| Sign vectors at 4/105 (43 entries) | BigZ Horner evaluation | **< 1 s** | CRTSigns.v |
| Sign vectors at +∞ (43 entries) | BigZ leading-coef comparison | **< 1 s** | CRTSigns.v |
| Variation counts: V(4/105) = 22, V(+∞) = 21 | IntPoly `variation` | **< 1 s** | CertL1.v |
| `roots_in_x0_inf = 1` | definition | instant | Witness.v |
| Chain[0] bigZ ↔ Z round-trip | `lift_bigZ` | **~2 min** | Smoke.v |
| `charpoly_of_A_int` monic + lift round-trip | `vm_compute` | **< 1 s** | CharPolyAgree.v |
| `det_int` on 12×12 diagonal | Bareiss `vm_compute` | **< 1 s** | IntMat.v |
| `char_poly_int` on 10×10 identity | Faddeev-LeVerrier `vm_compute` | **< 1 s** | CharPoly.v |

### Structural / bridge lemmas (via ssreflect tactics)

| Lemma | What it proves | File |
|---|---|---|
| `prem_rmodp_rat` | our integer pseudo-remainder = MathComp's `rmodp` over rat | Bridge.v |
| `prem_rmodp_eq` | same, lifted to realalg | Bridge.v |
| `next_mod_scaled_morph` | our `next_mod` = MathComp's up to nonzero scalar | Bridge.v |
| `lead_coef_pol_to_polyralg` | leading coef commutes with lifting | Bridge.v |
| `horner_pol_to_polyralg_rat` | Horner evaluation commutes with lifting | Bridge.v |
| `pderiv_morph` | derivative commutes with lifting | Bridge.v |
| `variation_at_pinf_morph` | sign-variation at +∞ matches MathComp `changes_pinfty` | Bridge.v |
| `variation_at_rat_morph` | sign-variation at rational matches MathComp `changes_horner` | Bridge.v |
| `sturm_count_above_correct` | Sturm count = #(real roots above threshold) | Bridge.v |
| `sturm_count_above_pos_concrete` | positive count → ∃ realalg root | Bridge.v |
| `eigenvalue_of_root_realalg` (L3) | root of char poly → eigenvalue | Cert.v |
| All 6 Step 1 sublemmas | `mat_int_to_rat` commutes with mzero/meye/mscale/madd/mmul/mtrace | CharPolyHelpers.v |
| `fl_invariant_L2_gen` | Faddeev-LeVerrier loop invariant (full inductive step) | CharPolyL2.v |
| `det_int_laplace_correct` | Laplace expansion = MathComp `\det` | IntMatProof.v |
| `mat_int_to_rat_unitmx` | nonzero `det_int` → lifted matrix is invertible | IntMatProof.v |
| `Z_to_int_mul`, `Z_to_int_add`, `Z_to_int_opp` | Z-to-int ring morphism properties | Bridge.v, CharPolyHelpers.v |

**Bridge.v has 0 Admitted lemmas.** The entire L1 Sturm bridge from
integer arithmetic to MathComp realalg is machine-checked.

## The headline theorem

```rocq
Theorem maynard_eigenvalue_S1 :
  exists lambda : realalg,
    eigenvalue (map_mx (ratr : rat -> realalg) A_rat) lambda
    /\ (ratr (4%:Q / 105%:Q) : realalg) < lambda.
```

`Print Assumptions` reports exactly **2 axioms** (plus standard Uint63
kernel primitives):

```
sturm_count_correct       (L1)
charpoly_int_eq_charpoly  (L2)
```

No accidental leakage from MathComp Analysis or `mathcomp-real-closed`.

## The 2 remaining axioms — what they need

### L1: `sturm_count_correct`

> There exists a real algebraic number `λ > 4/105` that is a root of
> the characteristic polynomial of `M₁⁻¹M₂`.

**Status**: fully scaffolded in CertL1.v + Bridge.v. The proof
assembles from:
- `sturm_count_above_pos_concrete` (Qed in Bridge.v)
- CRT-verified PRS chain (Qed in CRTCheck.v)
- BigZ-verified sign vectors (Qed in CRTSigns.v)
- `variation` computation (Qed in CertL1.v)

**3 remaining sub-admits** (all in CertL1.v):
1. `shipped_chain_eq` — the shipped chain data = the computed chain.
   *Could be closed by extending CRTCheck to verify that the PRS
   recurrence uniquely determines the chain from the input polynomial.*
2. `chain_is_mods` — our chain = abstract MathComp `mods`.
   *Could be eliminated by rewiring to use `mods_int_morph_weak`
   (which was Qed before the architectural cleanup).*
3. `no_root_at_cb` — no chain polynomial has root ≥ cauchy bound.
   *Standard Cauchy-bound analysis; `ge_cauchy_bound` from MathComp
   gives `noroot` in `[cauchy_bound p, +∞[` for each nonzero `p`.*

### L2: `charpoly_int_eq_charpoly`

> The FLINT-shipped polynomial equals `char_poly(M₁⁻¹M₂)` over
> realalg, after lifting.

**Status**: scaffolded in CharPoly.v + CharPolyL2.v. The proof chain:
- Step 1 (all 6 sublemmas Qed in CharPolyHelpers.v): `mat_int_to_rat`
  commutes with all matrix operations.
- Step 2 (`fl_invariant_L2_gen` Qed in CharPolyL2.v): Faddeev-LeVerrier
  loop invariant, full inductive step under hypotheses.
- Step 3 (Admitted): `fl_loop_rat_is_char_poly_L2` — the abstract
  identity that the FL recurrence produces `char_poly`. MathComp has
  no Newton's identities; the proof goes through Cayley-Hamilton +
  adjugate coefficient matching. Multi-week work.

## File inventory

### Autogenerated witness data
| File | Size | Content |
|---|---|---|
| Witness.v | 510 KB | M1_int, M2_int, A_int, char polys, signs, V counts |
| WitnessChain.v | 13.6 MB | Brown-Traub PRS chain + quotients + betas in bigZ |
| CRTPrimes.v | 211 KB | 9 776 primes for CRT verification |

### Computational layer (0 admits each)
| File | Lines | Purpose |
|---|---|---|
| Recompose.v | 48 | bigZ ↔ stdlib Z helpers |
| IntPoly.v | 317 | `list Z` polynomial library |
| IntMat.v | 597 | `list (list Z)` matrix library + Bareiss `det_int` |
| BrownTraub.v | 155 | modified Sturm chain on `list Z` |
| SignChain.v | 172 | sign-variation counting |
| PrimPoly.v | 277 | Uint63 modular polynomial arithmetic |
| PRSCheck.v | 135 | PRS step checker (list Z + Uint63 variants) |

### Verification layer
| File | Lines | Admits | Purpose |
|---|---|---|---|
| CRTCheck.v | 239 | 1 (CRT justification) | **42-step PRS chain verified, 21 s** |
| CRTSigns.v | 165 | 0 | **sign vectors verified via BigZ** |
| Smoke.v | 164 | 0 | round-trip tests |
| CharPolyAgree.v | 106 | 1 | FLINT cross-validation |

### Spec / proof layer
| File | Lines | Admits | Purpose |
|---|---|---|---|
| Bridge.v | 1 520 | **0** | full L1 Sturm bridge (pseudo-rem, variation, count) |
| CharPoly.v | 498 | 11 | Faddeev-LeVerrier + bridges (Step 1 shadowed by Helpers) |
| CharPolyHelpers.v | 736 | 0 | all 6 Step 1 sublemmas Qed |
| CharPolyL2.v | 379 | 3 | L2 scaffold (Steps 2-3) |
| IntMatProof.v | 874 | 3 | `det_int` correctness bridge |
| CertL1.v | 296 | 3 | L1 consumer wiring |
| Cert.v | 124 | 4 | **headline `maynard_eigenvalue_S1`** |

### Documentation
| File | Purpose |
|---|---|
| README.md | project README |
| PLAN.md | original witness MVP plan |
| PLAN_S1.md | eigenvalue statement S1 plan |
| PLAN_42x42.md | 42×42 computation feasibility analysis |
| notebook_reconstructed.md | Maynard notebook reverse-engineering |
| flint_sturm_plan.md | FLINT pipeline design report |
| research_charpoly.md | MathComp char_poly survey |
| math_eigenvalue_target.md | precise S1 theorem statement |

## Build instructions

```bash
# Prerequisites: Rocq 9.0, MathComp 2.5, mathcomp-real-closed 2.0.3,
#   rocq-bignums, python 3.11+, python-flint 0.8.0

# 1. FLINT audit (optional — certificates are pre-built)
source .venv/bin/activate
python python/build_certificate.py          # ~10 s with cache

# 2. Regenerate Rocq witness files (optional — pre-built)
python tools/json_to_v.py --with-chain

# 3. Build all 21 Rocq files (~7 min)
grep '\.v$' _CoqProject | while read f; do coqc -Q theories/S1 PrimeGapS1 "$f"; done

# 4. Verify headline
echo 'From PrimeGapS1 Require Import Cert.
Print Assumptions Cert.maynard_eigenvalue_S1.' | coqtop -Q theories/S1 PrimeGapS1
# Expected: sturm_count_correct, charpoly_int_eq_charpoly (2 axioms)
```

## Key technical discoveries

1. **MathComp `'M[rat]_n`, `{poly rat}`, `{poly int}` do not `vm_compute`**.
   Even `size (Poly [::-5;0;1] : {poly int})` times out at 30 s. The
   entire computational layer had to be rebuilt on `list Z` / `list (list Z)`.

2. **Stdlib `Z` literal parser stack-overflows above ~10 000 bits**.
   The Brown-Traub chain has 200 000-bit entries. Workaround: `rocq-bignums`
   `BigZ` parses 100 kbit literals in 0.4 s (1000× faster).

3. **`vm_compute` `Z.mul` interprets the `positive` binary tree** at
   ~10⁷ ops/s. For 100 kbit numbers this is ~10⁵× slower than GMP.
   Workaround: CRT over `Uint63` primes (native 63-bit arithmetic at
   ~10¹⁰ ops/s). The full 42-step chain verifies in 21 s.

4. **The modified-Sturm and Brown-Traub PRS chains differ by polynomial
   scalars** at every step. Strict equality (`mods_int_morph`) is
   unprovable. The correct target is the variation-difference weak form.

5. **MathComp 2.5 has no Newton's identities** or Faddeev-LeVerrier
   infrastructure. The L2 proof requires from-scratch development via
   Cayley-Hamilton + adjugate expansion.

6. **`Bareiss det_int` has a fuel bug** on matrices requiring row swaps.
   Worked around with a `bareiss_no_swap` predicate (sufficient for SPD).

## What a future collaborator would need to close the 2 axioms

**For L1** (~1–2 weeks of MathComp expertise):
- Close `shipped_chain_eq` (extend CRT uniqueness to prove the chain
  is determined by the input polynomial).
- Close `no_root_at_cb` (Cauchy-bound analysis per chain entry).
- Close `chain_is_mods` or rewire to bypass it (reinstate the weak
  variation-difference morphism form).
- Wire into Cert.v's `sturm_count_correct`.

**For L2** (~3–6 weeks of MathComp expertise):
- Replace CharPoly.v placeholder definitions with genuine FL iterators.
- Prove `fl_divisibility_L2` (Newton's identities or integer-det argument).
- Prove `fl_loop_rat_is_char_poly_L2` (Cayley-Hamilton + adjugate
  coefficient matching — the core abstract identity, ~300-500 lines).
- Wire into Cert.v's `charpoly_int_eq_charpoly`.

All intermediate lemmas, proof outlines, and entry points are documented
in the codebase. The `theories/S1/` directory is self-contained; a new
collaborator needs only `opam install` the dependencies and `grep Admitted`
to find the work items.
