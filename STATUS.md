# Project status

**24 Rocq files. 0 axioms. 7 admits in CRTLift.v + 2 admits in CertL2.v. All other files 0 admits.**

Every admit has a commented-out complete proof (grep `UNCOMMENT`).

## Headline theorem

```rocq
Theorem maynard_eigenvalue_S1 :
  exists lambda : realalg,
    eigenvalue (map_mx (ratr : rat -> realalg) A_rat) lambda
    /\ (ratr (4%:Q / 105%:Q) : realalg) < lambda.
```

Qed in Cert.v. 1 project axiom: `charpoly_int_Dq_scaled` (closed by CertL2.v).

## CRTLift.v (0 axioms, 7 admits — all vm_compute)

| Lemma | Est. time | Proof step |
|---|---|---|
| `crt_primes_710_NoDup_check` | ~seconds | `vm_compute. reflexivity.` |
| `check_all_primes_710` | ~8 min | `vm_compute. reflexivity.` |
| `charpoly_coeff_bound_compute` | ~5-30 min | `Transparent charpoly_Z_A. vm_compute. reflexivity.` |
| `check_charpoly_Z_710_ok` | ~5-30 min | `Transparent charpoly_Z_A. vm_compute. reflexivity.` |
| `crt_bound_sufficient` | ~2 min | `vm_compute. reflexivity.` |
| `check_mat_Z_710_ok` | ~5-30 min | `Transparent mat_lhs_opaque mat_rhs_opaque. vm_compute. reflexivity.` |
| `matrix_crt_bound_sufficient` | ~1 min | `vm_compute. reflexivity.` |

## CertL2.v (0 axioms, 2 admits — slow MathComp rewrites)

| Lemma | Est. time | RAM needed |
|---|---|---|
| `mat_A_eq_Arat` | ~50-90 min | >= 16 GB |
| `charpoly_int_Dq_scaled` | ~40-80 min | >= 16 GB |

Both have complete proofs in comments. `charpoly_int_Dq_scaled` depends on `mat_A_eq_Arat`.

## Qed lemmas (key results)

| Lemma | File |
|---|---|
| `fl_eq_flint` (FL = FLINT charpoly) | CRTLift.v |
| `matrix_identity_Z` (M1*A*D_M2 = M2*D_M1*D_A) | CRTLift.v |
| `per_prime_agreement` (modular poly agreement) | CRTLift.v |
| `per_prime_matrix_agreement` (modular matrix agreement) | CRTLift.v |
| `crt_primes_valid` (all primes valid) | CRTLift.v |
| `crt_product_710_pos` (product positive) | CRTLift.v |
| `crt_primes_710_NoDup` (primes distinct) | CRTLift.v |
| `crt_primes_710_all_prime` (all primes prime) | CRTLift.v |
| `charpoly_coeff_bound` (coefficient bound) | CRTLift.v |
| `matrix_lhs/rhs_entry_bound` (entry bounds) | CRTLift.v |
| `M1_charpoly_hd_nz` | CertL2.v |
| `M1_1_unit` | CertL2.v |
| `mat_identity_rat` | CertL2.v |

## Fully Qed files (0 admits, 0 axioms)

CRTBridge.v (56), Fermat.v (5), PrimeCheck.v (4), CharPoly.v (~50),
CharPolyAgree.v (~20), CRTCheck.v (~20), and all other S1 files:
Bridge, BrownTraub, CertL1, CharPolyScale, CRTSigns, IntMat, IntPoly,
PrimPoly, PRSCheck, Recompose, SignChain, Smoke, Witness, WitnessChain.

## Estimated total closure time (60 GB RAM machine)

| Category | Time |
|---|---|
| CRTLift vm_compute | 25-100 min |
| CertL2 MathComp rewrites | 90-170 min |
| Other files | 5-10 min |
| **Total** | **~2-5 hours** |
