# TODO: Closing remaining axioms and admits

All remaining gaps are in `theories/S1/CertL2.v`.
Every other file in the project is fully Qed with zero project axioms.

## 3 Axioms (all provable, ~300 lines total)

### 1. `charpoly_coeff_bound` (~200-300 lines)

Cofactor expansion bound: for an n x n integer matrix M with max
absolute entry B, `|c_k| <= (2*n*B)^n`.

**How to prove:** Use MathComp `det_expand` + triangle inequality.
Each coefficient c_k of char_poly_int(M) is a sum of C(n,k) k x k
minors, each bounded by k! * B^k <= (n*B)^n.  Summing:
`|c_k| <= C(n,k) * (n*B)^n <= (2*n*B)^n`.

Standard linear algebra -- no Hadamard bound needed.

The concrete bound is already verified computationally by
`crt_bound_sufficient` (vm_compute Qed).

### 2. `per_prime_agreement` (~50 lines + 8 min vm_compute)

For each of 710 CRT primes p:
`map (Z_to_mod63 p) (char_poly_int A_int) = map (Z_to_mod63 p) charpoly_of_A_int`.

**How to prove:** Wire together:
- `char_poly_mod_sound` (Qed in CharPoly.v)
- `char_poly_int_agrees_710` (Qed in CharPolyAgree.v)
- `fermat_Z` (Qed in Fermat.v)

The 8 minutes is for `all_primes_710_verified` -- 710 primality checks
via vm_compute (~0.65s each).

### 3. `length_char_poly_int_A` (~5 lines)

`length (char_poly_int A_int) = 43`.

**How to prove:** Induction on `fl_loop` steps showing the loop produces
exactly n+1 = 43 elements.  Alternatively, unfold through `fl_loop` and
use the dimension invariants.

---

## 4 Admits (all closeable, ~70 new lines total)

### 4. `fl_eq_flint` (~30 lines)

`char_poly_int A_int = charpoly_of_A_int`.

**How to close:** CRT lift wiring:
1. `per_prime_agreement` -- agreement mod each prime
2. `all_primes_divide_product` (Qed in CRTCheck.v) -- product divides difference
3. `small_multiple_zero` (Qed in CRTCheck.v) -- if product > 2*|diff|, diff = 0
4. `charpoly_coeff_bound` -- coefficient bound
5. `crt_bound_sufficient` (Qed) -- concrete bound check

Apply per-coefficient: for each k, the difference of the k-th
coefficients is divisible by the CRT product and bounded by it,
hence zero.

### 5. `matrix_identity_Z` (~40 lines)

`mscale D_M2 (mmul M1_int A_int) = mscale (D_M1 * D_A) M2_int`.

**How to close:** Same CRT pattern as `fl_eq_flint`, applied per-entry
instead of per-coefficient.  Needs an entry-level bound axiom
(analogous to `charpoly_coeff_bound` but for matrix products).

### 6. `mat_A_eq_Arat` (0 new lines)

`mat_int_to_rat A_int D_A 42 = A_rat`.

**How to close:** The proof is already complete in git history
(commit ad3b1ca).  It performs 5 algebraic rewrites (scalerA, mulVr,
mulKVmx, invmxZ, invrM) on `'M[rat]_42` that each take >10 min due
to MathComp canonical structure resolution at dimension 42.

Compile on a machine with >= 8 GB RAM and 30-60 min patience.

### 7. `charpoly_int_Dq_scaled` (0 new lines)

`pol_to_polyrat charpoly_int = (Z_to_int D_q)%:~R *: char_poly A_rat`.

**How to close:** The proof is already complete in git history
(commit 2fa86a8).  It has 4 slow steps doing rewrites on
`'M[rat]_42` / `{poly rat}` that each take >10 min.  Once
`mat_A_eq_Arat` is Qed, the HA1 step becomes a one-liner using
`mat_int_to_rat_scale_inv'`.

Compile on a machine with >= 8 GB RAM; may need >16 GB to avoid OOM.

---

## Fully Qed files (0 admits, 0 project axioms)

| File               | Lemmas |
|--------------------|--------|
| CRTBridge.v        | 56 Qed |
| Fermat.v           | 5 Qed  |
| PrimeCheck.v       | 4 Qed  |
| CharPoly.v         | 0 admits |
| CharPolyAgree.v    | 0 admits |
| CharPolyScale.v    | 0 admits |
| CRTCheck.v         | 0 admits |
| IntPoly.v          | 0 admits |
| IntMat.v           | 0 admits |
| BrownTraub.v       | 0 admits |
| SignChain.v        | 0 admits |
| Bridge.v           | 0 admits |
| CRTSigns.v         | 0 admits |
| CertL1.v           | 0 admits |
| PRSCheck.v         | 0 admits |
| PrimPoly.v         | 0 admits |
| Recompose.v        | 0 admits |
| Witness.v          | 0 admits (data) |
| WitnessChain.v     | 0 admits (data) |
| Smoke.v            | 0 admits |
| Cert.v             | 1 local admit (closed by CertL2.v) |

## Summary

- **Total new lines needed:** ~370 (mostly `charpoly_coeff_bound`)
- **Total compute time needed:** ~8 min (710 primality checks) + 30-60 min (slow rewrites)
- **RAM needed:** >= 8 GB (ideally 16 GB for `charpoly_int_Dq_scaled`)
- **Critical path:** `charpoly_coeff_bound` -> `per_prime_agreement` -> `fl_eq_flint` -> `charpoly_int_Dq_scaled`
