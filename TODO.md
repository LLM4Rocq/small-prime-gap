# TODO: Closing remaining axioms and admits

## CRTLift.v: 5 axioms + 2 admits

### Axioms (provable, ~450 lines + 8 min vm_compute total)

#### 1. `per_prime_agreement` (~50 lines + 8 min vm_compute)

For each of 710 CRT primes p:
`map (Z_to_mod63 p) (char_poly_int A_int) = map (Z_to_mod63 p) charpoly_of_A_int`.

**How to prove:** Wire together:
- `char_poly_mod_sound` (Qed in CRTBridge.v)
- `char_poly_int_agrees_710` (Qed in CharPolyAgree.v)
- `fermat_Z` (Qed in Fermat.v)

The 8 minutes is for 710 primality checks via vm_compute (~0.65s each).

#### 2. `charpoly_coeff_bound` (~200 lines)

Cofactor expansion bound: `|c_k| <= (2*n*B)^n`.

**How to prove:** Use MathComp `det_expand` + triangle inequality.
Standard linear algebra -- no Hadamard bound needed.

#### 3. `crt_primes_710_NoDup` (~30 lines)

`NoDup (map Uint63.to_Z crt_primes_all)`.

**How to prove:** Define boolean NoDup checker (e.g., strictly-increasing
check or O(n^2) pairwise-distinct check), prove soundness, vm_compute.

#### 4. `crt_primes_710_all_prime` (~20 lines + 8 min vm_compute)

All 710 primes satisfy `Znumtheory.prime`.

**How to prove:** Use `check_prime_Z_sound` from PrimeCheck.v on each prime.
`forallb check_prime_Z (map Uint63.to_Z crt_primes_all) = true` by vm_compute.

#### 5. `per_prime_matrix_agreement` (~100 lines)

Per-entry modular agreement from `matrix_identity_710`.

**How to prove:** Soundness chain for `check_mat_identity_one_prime`:
`mmat_eqb` + `mmat_scale` + `mmat_mul` + `reduce_mat_Z` soundness.

### Admits (vm_compute, needs better machine)

- `crt_bound_sufficient` — `2*(2*42*B)^42 + 2*max_coeff < product_710` (~2 min)
- `matrix_crt_bound_sufficient` — `2*LHS_bound + 2*RHS_bound < product_710` (fast)

---

## CertL2.v: 2 admits (slow MathComp, need better machine)

### 1. `mat_A_eq_Arat` (0 new lines)

`mat_int_to_rat A_int D_A 42 = A_rat`.

Proof exists in git history. 5 algebraic rewrites on `'M[rat]_42`,
each >10 min. Needs >= 8 GB RAM, 30-60 min patience.

### 2. `charpoly_int_Dq_scaled` (0 new lines)

`pol_to_polyrat charpoly_int = (Z_to_int D_q)%:~R *: char_poly A_rat`.

Proof exists in git history. 4 slow steps on `'M[rat]_42` / `{poly rat}`.
Needs >= 8 GB RAM; may need >16 GB to avoid OOM.

---

## Summary

| Category | Count | Lines needed | Compute needed |
|---|---|---|---|
| Axioms (CRTLift.v) | 5 | ~450 | 8 min (primality) |
| Admits (CRTLift.v) | 2 | 0 | ~2 min vm_compute |
| Admits (CertL2.v) | 2 | 0 | 30-60 min + 8 GB RAM |
| **Total** | **9** | **~450** | **~40-70 min + 8 GB** |

All other files: **0 axioms, 0 admits**.
