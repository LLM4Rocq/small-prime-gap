# Project status

**18 Rocq files. 1 Admitted lemma (headline). 17 files with 0 admits.**

## Headline theorem

```rocq
Theorem maynard_eigenvalue_S1 :
  exists lambda : realalg,
    eigenvalue (map_mx (ratr : rat -> realalg) A_rat) lambda
    /\ (ratr (4%:Q / 105%:Q) : realalg) < lambda.
```

Qed. 1 project axiom: `charpoly_int_Dq_scaled` + Uint63 kernel axioms.

## Cert.v lemma status

| Lemma | Status |
|---|---|
| `sturm_count_correct` (L1) | **Qed** — via CertL1.maynard_L1_concrete (IVT) |
| `charpoly_root_transfer` (L2) | **Qed** — via rootZ + map_polyZ |
| `eigenvalue_of_root_realalg` (L3) | **Qed** — map_char_poly + eigenvalue_root_char |
| `maynard_bridge_L4` | **Qed** — ltr_pdivrMr rescaling |
| `A_rat_unitmx` | **Qed** — CRT modular det via UnitmxCheck |
| `charpoly_int_Dq_scaled` | **Admitted** — pol_to_polyrat charpoly_int = D_q *: char_poly A_rat |

## Machine-verified computational facts

| Fact | Method | Time | File |
|---|---|---|---|
| FL(A_int) = FLINT's charpoly | CRT, 710 Uint63 primes | ~12 min | CharPolyAgree.v |
| M1\*A\*D_M2 = M2\*(D_M1\*D_A) | CRT, 710 Uint63 primes | ~12 min | CharPolyAgree.v |
| charpoly_int[k]\*D_A^{42-k} = D_q\*cp_A[k] | BigZ exact arithmetic | < 1 s | CharPolyAgree.v |
| char_poly(c \*: M)\_k = c^{n-k} \* (char_poly M)\_k | MathComp algebra | < 1 s | CharPolyScale.v |
| 42-step PRS chain | CRT, 10 Uint63 primes | 21 s | CRTCheck.v |
| Sign vectors at 4/105, +inf | BigZ Horner / leading-coef | < 1 s | CRTSigns.v |
| V(4/105)−V(+inf) = 1 | IntPoly variation | < 1 s | CertL1.v |
| det(M1\_int) ≠ 0, det(M2\_int) ≠ 0 | CRT modular det | < 1 s | UnitmxCheck.v |
| 3528/3528 matrix entries | closed-form Beta integrals | < 1 s | Python |

## L1: IVT proof (fully Qed, zero project axioms)

`maynard_L1_concrete` proves root existence via the intermediate value
theorem (`poly_ivtoo`): P(4/105) < 0 (BigZ Horner) and P(cauchy_bound) > 0
(leading coefficient sign via `sgp_pinftyP`), so IVT gives a root in between.

## L2: Faddeev-LeVerrier = char_poly (fully Qed)

- **adj_coef_jacobi** (Jacobi's formula): Qed via mul_mx_adj + Leibniz.
- **fl_loop_rat_is_char_poly_L2**: Qed via adj_coef_jacobi.
- **fl_divisibility_L2**: Qed via Newton's identity + Cayley-Hamilton.
- **fl_invariant_L2**: Qed (inductive bridge from Z to rat).
- **char_poly_int_correct**: Qed — `pol_to_polyrat(FL(M)) = char_poly(M/1)`.
- **char_poly_scale**: Qed — `(char_poly(c *: M))_k = c^{n-k} * (char_poly M)_k`.

## The 1 remaining admit

| File | Lemma | Nature |
|---|---|---|
| Cert.v | `charpoly_int_Dq_scaled` | shipped poly = D_q \* char_poly A_rat |

No other admits exist in the codebase.

### Critical path for closing the headline

```
charpoly_int_Dq_scaled               ← ONLY headline admit
  All sub-components are Qed:
    (a) char_poly_int A_int = charpoly_of_A_int   [710-prime CRT, Qed]
    (b) charpoly_int[k] * D_A^{42-k} = D_q * cp_A[k]  [BigZ exact, Qed]
    (c) M1*A*D_M2 = M2*(D_M1*D_A)                [710-prime CRT, Qed]
    (d) char_poly(c *: M) scaling formula         [CharPolyScale.v, Qed]
  Assembly is in CertL2.v (separate file, no realalg import).
  CertL2.v uses native_compute for the heavy Z-level facts and
  needs >= 8 GB RAM. On the current machine, Cert.v keeps the
  admit; on a better machine, compile CertL2.v first then
  import it in Cert.v to close the admit.
```

## Files with 0 admits (17 of 18)

All files except Cert.v (1 admit): Bridge.v, BrownTraub.v, CertL1.v,
CharPoly.v, CharPolyAgree.v, CharPolyScale.v, CRTCheck.v, CRTSigns.v,
IntMat.v, IntPoly.v, PrimPoly.v, PRSCheck.v, Recompose.v, SignChain.v,
Smoke.v, Witness.v, WitnessChain.v.

## Key technical decisions

- **MathComp types don't vm_compute.** `'M[rat]_n`, `{poly rat}`,
  `realalg` all time out. The computational layer uses `list Z` /
  `list (list Z)` exclusively.
- **Stdlib Z literals stack-overflow above ~10 kbit.** Heavy data
  shipped via `rocq-bignums` BigZ (100 kbit in 0.4 s).
- **CRT over Uint63** solves the 42x42 computation wall. Native 63-bit
  arithmetic at ~17 billion ops/sec makes modular verification trivial.
- **710 Uint63 primes** (~21000-bit coverage) verify both the FL
  polynomial agreement and the matrix identity.
