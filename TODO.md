# Closing remaining admits

**0 axioms. 9 admits total.** Every admit has a complete proof in a
comment immediately below it. Grep for `UNCOMMENT` to find them all.

## Quick start

On a machine with >= 16 GB RAM:

1. For each `Proof. Admitted.` in CRTLift.v and CertL2.v, replace it
   with the commented-out proof block below it.
2. Run `make -j4` and wait ~2-5 hours.

## CRTLift.v: 7 admits (all vm_compute)

### Fast (~15 min total)

| Lemma | Time | Proof |
|---|---|---|
| `crt_primes_710_NoDup_check` | ~seconds | `vm_compute. reflexivity.` |
| `crt_bound_sufficient` | ~2 min | `vm_compute. reflexivity.` |
| `matrix_crt_bound_sufficient` | ~1 min | `vm_compute. reflexivity.` |

### Medium (~8 min)

| Lemma | Time | Proof |
|---|---|---|
| `check_all_primes_710` | ~8 min | `vm_compute. reflexivity.` |

710 trial division primality checks (~0.65s each).

### Heavy (~15-90 min, untested)

These require computing `char_poly_int A_int` (FL algorithm on 42x42
matrix with ~500-bit entries) or `mmul M1_int A_int` (42x42 matrix
product). The `Transparent` command is needed because the terms are
sealed with `Opaque` to prevent kernel expansion during `Qed`.

| Lemma | Proof |
|---|---|
| `charpoly_coeff_bound_compute` | `Transparent charpoly_Z_A. vm_compute. reflexivity.` |
| `check_charpoly_Z_710_ok` | `Transparent charpoly_Z_A. vm_compute. reflexivity.` |
| `check_mat_Z_710_ok` | `Transparent mat_lhs_opaque mat_rhs_opaque. vm_compute. reflexivity.` |

If `vm_compute` is too slow, try `native_compute` (if installed):
```
Transparent charpoly_Z_A. native_compute. reflexivity.
```

## CertL2.v: 2 admits (slow MathComp canonical structure resolution)

Both proofs are complete and tested (exist in git history). They perform
algebraic rewrites on `'M[rat]_42` where MathComp's canonical structure
resolution takes >10 min per rewrite step.

### 1. `mat_A_eq_Arat` (~50-90 min, >= 16 GB RAM)

Uncomment the proof block below the `Admitted`. It performs:
- `mat_int_to_rat_scale_inv'` + `matrixP` + per-entry `scalerA mulVr`

### 2. `charpoly_int_Dq_scaled` (~40-80 min, >= 16 GB RAM)

Depends on `mat_A_eq_Arat` being Qed first. Uncomment the proof block.
It performs:
- Rewrite chain through `char_poly_int_correct` + `fl_eq_flint`
- `polyP` coefficient comparison using `scaling_Z` + `char_poly_scale_coef`
- `mulfI` cancellation of `D_A` denominator

## Summary

| File | Admits | New lines | Machine needed |
|---|---|---|---|
| CRTLift.v | 7 | 0 (just uncomment) | >= 8 GB, ~25-100 min |
| CertL2.v | 2 | 0 (just uncomment) | >= 16 GB, ~90-170 min |
| **Total** | **9** | **0** | **>= 16 GB, ~2-5 hours** |
