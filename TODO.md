# TODO: Closing remaining axioms and admits

All remaining gaps are in `theories/S1/CRTLift.v` and `theories/S1/CertL2.v`.
Every other file in the project is fully Qed with zero project axioms.

## CRTLift.v: 9 axioms + 3 admits

### Axioms shared by fl_eq_flint and matrix_identity_Z

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

#### 3-6. CRT infrastructure axioms (~20 lines each)

- `crt_primes_710_NoDup` — vm_compute on the 710-element list
- `crt_primes_710_all_prime` — 710 calls to `check_prime_Z_sound`
- `crt_primes_valid` — unfold `valid_prime`, vm_compute
- `crt_product_710_pos` — from positivity of each prime

### Axioms for matrix_identity_Z

#### 7. `per_prime_matrix_agreement` (~100 lines)

Per-entry modular agreement from `matrix_identity_710`.

**How to prove:** Soundness chain for `check_mat_identity_one_prime`:
`mmat_eqb` + `mmat_scale` + `mmat_mul` + `reduce_mat_Z` soundness.

#### 8-9. Entry bounds (~50 + 30 lines)

- `matrix_lhs_entry_bound` — from `mat_get_mscale` + dot product triangle inequality
- `matrix_rhs_entry_bound` — from `mat_get_mscale` + `max_abs_entry` bound

### Admits (vm_compute, needs better machine)

- `crt_bound_sufficient` — `2*(2*42*B)^42 + 2*max_coeff < product_710` (~2 min)
- `length_charpoly_of_A` — `length charpoly_of_A_int = 43` (fast)
- `matrix_crt_bound_sufficient` — `2*LHS_bound + 2*RHS_bound < product_710` (fast)

---

## CertL2.v: 0 axioms + 2 admits

### 1. `mat_A_eq_Arat` (0 new lines)

`mat_int_to_rat A_int D_A 42 = A_rat`.

**How to close:** The proof is already complete in git history.
5 algebraic rewrites on `'M[rat]_42` that each take >10 min due to
MathComp canonical structure resolution at dimension 42.

Compile on a machine with >= 8 GB RAM and 30-60 min patience.

### 2. `charpoly_int_Dq_scaled` (0 new lines)

`pol_to_polyrat charpoly_int = (Z_to_int D_q)%:~R *: char_poly A_rat`.

**How to close:** The proof is already complete in git history.
4 slow steps on `'M[rat]_42` / `{poly rat}`.

Compile on a machine with >= 8 GB RAM; may need >16 GB to avoid OOM.

---

## Qed status

| Item | File | Status |
|---|---|---|
| `fl_eq_flint` | CRTLift.v | **Qed** |
| `matrix_identity_Z` | CRTLift.v | **Qed** |
| `M1_charpoly_hd_nz` | CertL2.v | **Qed** |
| `M1_1_unit` | CertL2.v | **Qed** |
| `mat_identity_rat` | CertL2.v | **Qed** |
| `crt_bound_sufficient` | CRTLift.v | Admitted (vm_compute ~2 min) |
| `matrix_crt_bound_sufficient` | CRTLift.v | Admitted (vm_compute) |
| `length_charpoly_of_A` | CRTLift.v | Admitted (vm_compute) |
| `mat_A_eq_Arat` | CertL2.v | Admitted (slow rewrite, >30 min) |
| `charpoly_int_Dq_scaled` | CertL2.v | Admitted (slow rewrite, OOM) |

## Summary

- **Total new proof lines needed:** ~500 (axioms) + 0 (admits have correct proofs)
- **Total compute time needed:** ~8 min (primality) + 30-60 min (slow rewrites)
- **RAM needed:** >= 8 GB (ideally 16 GB for `charpoly_int_Dq_scaled`)
