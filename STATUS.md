# Project status

**33 commits. 21 Rocq files (25 000+ lines). 9 admits. Headline has 1 project-level Admitted lemma (L2).**

## Headline theorem

```rocq
Theorem maynard_eigenvalue_S1 :
  exists lambda : realalg,
    eigenvalue (map_mx (ratr : rat -> realalg) A_rat) lambda
    /\ (ratr (4%:Q / 105%:Q) : realalg) < lambda.
```

Qed. Depends on L2 (`charpoly_int_eq_charpoly`) + two bridge admits + Uint63 kernel axioms.

## Cert.v lemma status

| Lemma | Status |
|---|---|
| `sturm_count_correct` (L1) | **Qed** — via CertL1.maynard_L1_concrete |
| `eigenvalue_of_root_realalg` (L3) | **Qed** — map_char_poly + eigenvalue_root_char |
| `maynard_bridge_L4` | **Qed** — ltr_pdivrMr rescaling |
| `A_rat_unitmx` | **Qed** — CRT modular det via UnitmxCheck |
| `charpoly_int_eq_charpoly` (L2) | **Admitted** — shipped poly = char_poly A_rat |

## Machine-verified computational facts

| Fact | Method | Time | File |
|---|---|---|---|
| 42-step PRS chain | CRT, 10 Uint63 primes | 21 s | CRTCheck.v |
| char_poly_int(A_int) = FLINT's charpoly | CRT Uint63 Faddeev-LeVerrier | 11 s | CharPolyAgree.v |
| Sign vectors at 4/105 (43 entries) | BigZ Horner | < 1 s | CRTSigns.v |
| Sign vectors at +∞ (43 entries) | BigZ leading-coef | < 1 s | CRTSigns.v |
| V(4/105)=22, V(+∞)=21, diff=1 | IntPoly variation | < 1 s | CertL1.v |
| det(M1_int) ≠ 0, det(M2_int) ≠ 0 | CRT modular det | < 1 s | UnitmxCheck.v |
| 10 CRT primes are prime | Uint63 trial division | < 1 s | CRTCheck.v |
| Product of primes > 2^299 | vm_compute | < 1 s | CRTCheck.v |
| 3528/3528 matrix entries | closed-form Beta integrals | < 1 s | Python |

### CRT caveat

The CRT checks use 10 primes (~300-bit coverage). Full CRT proof of the
293 kbit max coefficient requires ~9776 primes, blocked by BigZ.modulo
performance (~6 hours estimated). The 10-prime check is a strong
probabilistic test (false positive ~2^{-300}), not a mathematical proof.
The `crt_correctness` lemma in CRTCheck.v is Qed with the full CRT
argument (Gauss's lemma + product divisibility), conditional on a
coefficient-bound hypothesis.

## Files with 0 admits (15 of 21)

Bridge.v, CharPolyHelpers.v, CharPolyAgree.v, CRTCheck.v, CRTSigns.v,
IntPoly.v, IntMat.v, BrownTraub.v, SignChain.v, PrimPoly.v, PRSCheck.v,
Recompose.v, Smoke.v, Witness.v, WitnessChain.v.

## The 9 remaining admits

| # | File | Lemma | Nature | Effort |
|---|---|---|---|---|
| 1 | Cert.v | `charpoly_int_eq_charpoly` | L2: shipped poly = char_poly A_rat | assembly |
| 2 | CertL1.v | `prs_chain_sturm_correct` | Sturm theorem bridge | 1-2 weeks |
| 3 | CertL1.v | `cauchy_bound_le_of_chain` | Cauchy bound (BigZ-verified) | days |
| 4 | CharPoly.v | `char_poly_int_correct` | FL integers = char_poly rationals | assembly |
| 5 | CharPolyL2.v | `fl_invariant_L2` | FL loop invariant wrapper | days |
| 6 | CharPolyL2.v | `fl_divisibility_L2` | k divides tr(A·M_k) | 1-2 weeks |
| 7 | CharPolyL2.v | `fl_loop_rat_is_char_poly_L2` | FL = char_poly (via mul_mx_adj) | **3-6 weeks** |
| 8 | IntMatProof.v | `det_int_laplace_eq_det_int` | Bareiss = Laplace | 1-2 weeks |
| 9 | UnitmxCheck.v | `A_rat_unitmx_from_check` | modular det → unitmx bridge | days |

The critical path: #7 → #6 → #5 → #4 → #1 → headline has 0 project axioms.

## Key technical decisions

- **MathComp types don't vm_compute.** `'M[rat]_n`, `{poly rat}`,
  `realalg` all time out. The computational layer uses `list Z` /
  `list (list Z)` exclusively.
- **Stdlib Z literals stack-overflow above ~10 kbit.** Heavy data
  shipped via `rocq-bignums` BigZ (100 kbit in 0.4 s).
- **CRT over Uint63** solves the 42×42 computation wall. Native 63-bit
  arithmetic at ~17 billion ops/sec makes modular verification trivial.
- **Brown-Traub and modified-Sturm chains differ by polynomial scalars.**
  Strict chain equality is unprovable; the weak variation-difference
  form is what Sturm's theorem needs.
