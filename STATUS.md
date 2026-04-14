# Project status

**23 Rocq files. 3 axioms + 4 admits in CertL2.v; all other files 0 admits.**

## Headline theorem

```rocq
Theorem maynard_eigenvalue_S1 :
  exists lambda : realalg,
    eigenvalue (map_mx (ratr : rat -> realalg) A_rat) lambda
    /\ (ratr (4%:Q / 105%:Q) : realalg) < lambda.
```

Qed in Cert.v. 1 project axiom: `charpoly_int_Dq_scaled` (closed by CertL2.v).

## Cert.v lemma status

| Lemma | Status |
|---|---|
| `sturm_count_correct` (L1) | **Qed** — via CertL1.maynard_L1_concrete (IVT) |
| `charpoly_root_transfer` (L2) | **Qed** — via rootZ + map_polyZ |
| `eigenvalue_of_root_realalg` (L3) | **Qed** — map_char_poly + eigenvalue_root_char |
| `maynard_bridge_L4` | **Qed** — ltr_pdivrMr rescaling |
| `A_rat_unitmx` | **Qed** — CRT modular det via UnitmxCheck |
| `charpoly_int_Dq_scaled` | **Admitted** locally — closed by CertL2.v |

## CertL2.v status

| Item | Type | Status | Closure path |
|---|---|---|---|
| `charpoly_coeff_bound` | Axiom | Provable (~200 lines) | MathComp det_expand + triangle inequality |
| `per_prime_agreement` | Axiom | Provable (~50 lines + 8 min) | char_poly_mod_sound + fermat_Z wiring |
| `length_char_poly_int_A` | Axiom | Provable (~5 lines) | Induction on fl_loop |
| `fl_eq_flint` | Admitted | ~30 lines | CRT lift: per_prime_agreement + small_multiple_zero |
| `matrix_identity_Z` | Admitted | ~40 lines | Same CRT pattern for matrix entries |
| `mat_A_eq_Arat` | Admitted | 0 new lines | Correct proof in git history, needs >10 min on 'M[rat]_42 |
| `charpoly_int_Dq_scaled` | Admitted | 0 new lines | Correct proof in git history, needs >10 min + 8 GB |
| `M1_charpoly_hd_nz` | **Qed** | ✓ | char_poly_mod_sound + M1_det_nz_mod |
| `M1_1_unit` | **Qed** | ✓ | M1_charpoly_hd_nz + char_poly_int_correct |
| `mat_identity_rat` | **Qed** | ✓ | matrix_identity_Z + mat_int_to_rat_mscale |
| `crt_bound_sufficient` | **Qed** | ✓ | vm_compute: 2^20958 < 2^21300 |

## Fully Qed files (0 admits, 0 axioms)

| File | Qed count | Description |
|---|---|---|
| CRTBridge.v | 56 | FL modular soundness, powmod_fast, divmod63, char_poly_mod_sound |
| Fermat.v | 5 | fermat_mod, fermat_Z, fermat_dvdn, expn_pow, fermat_nat_eq |
| PrimeCheck.v | 4 | check_prime_Z_sound, Zprime_to_ssrprime, check_prime_Z_mc |
| CharPoly.v | ~50 | FL loop, char_poly_int_correct, fl_divisibility_L2 |
| CharPolyAgree.v | ~20 | 710-prime CRT checks, scaling_Z_from_check |
| CRTCheck.v | ~20 | CRT infrastructure: small_multiple_zero, all_primes_divide_product |
| All other S1 files | — | Bridge, BrownTraub, CertL1, CharPolyScale, CRTSigns, IntMat, IntPoly, PrimPoly, PRSCheck, Recompose, SignChain, Smoke, Witness, WitnessChain |

## Machine-verified computational facts

| Fact | Method | File |
|---|---|---|
| FL(A_int) ≡ FLINT charpoly mod 710 primes | Uint63 CRT | CharPolyAgree.v |
| M1·A·D_M2 ≡ M2·(D_M1·D_A) mod 710 primes | Uint63 CRT | CharPolyAgree.v |
| charpoly_int[k]·D_A^{42-k} = D_q·cp_A[k] | BigZ exact | CharPolyAgree.v |
| 2·(2·42·B)^42 + 2·max_coeff < product_710 | vm_compute | CertL2.v |
| det(M1_int) ≠ 0 mod p | Uint63 | CharPolyAgree.v |
| 42-step PRS chain | Uint63 CRT, 10 primes | CRTCheck.v |
| Sign vectors at 4/105, +∞ | BigZ Horner | CRTSigns.v |
| V(4/105)−V(+∞) = 1 | IntPoly variation | CertL1.v |
| All 710 CRT primes are prime | Z trial division | PrimeCheck.v + vm_compute |

## Key technical decisions

- **MathComp types don't vm_compute.** `'M[rat]_n`, `{poly rat}`,
  `realalg` all time out. The computational layer uses `list Z` /
  `list (list Z)` exclusively.
- **Stdlib Z literals stack-overflow above ~10 kbit.** Heavy data
  shipped via `rocq-bignums` BigZ (100 kbit in 0.4 s).
- **CRT over Uint63** solves the 42×42 computation wall. Native 63-bit
  arithmetic at ~17 billion ops/sec makes modular verification trivial.
- **710 Uint63 primes** (~21000-bit coverage) verify both the FL
  polynomial agreement and the matrix identity.
- **Opaque Z_to_int** prevents stack overflow when MathComp tries to
  reduce ~150-digit Z values to `Posz (S (S ...))`.
- **No Hadamard inequality needed.** Crude cofactor bound `(2nB)^n`
  suffices: 2^20958 < 2^21300 (product of 710 primes).
- **PrimeCheck.v** provides Z-level trial division primality checker
  (~0.65s per 10^9 prime via vm_compute), bridged to MathComp `prime`.

## Closure plan

See `TODO.md` for detailed closure instructions for each axiom and admit.
**Critical path:** ~370 lines of new proof + 8 min vm_compute + a machine
with ≥ 8 GB RAM for the slow `'M[rat]_42` rewrites.
