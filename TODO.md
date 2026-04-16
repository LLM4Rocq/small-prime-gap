# Closing remaining gaps

**1 axiom, 8 admits.** Estimated total: ~2-3 hours on a 60 GB machine.

## CRTLift.v

### Axiom: `charpoly_coeff_bound` (~200 lines)

Cofactor expansion bound: `|c_k| <= (2nB)^n`. Provable from
MathComp `det_expand` + triangle inequality. The concrete bound
is already verified by `crt_bound_sufficient`.

### Admits (fast, ~11 min total)

All use Uint63 modular arithmetic (the CRTBridge design) or
simple Z arithmetic. No heavy FL or matrix computation at Z level.

```
crt_primes_710_NoDup_check   — vm_compute. reflexivity.  (~seconds)
check_all_primes_710         — vm_compute. reflexivity.  (~8 min)
per_prime_agreement          — vm_compute. reflexivity.  (~seconds)
per_prime_matrix_agreement   — vm_compute. reflexivity.  (~seconds)
crt_bound_sufficient         — vm_compute. reflexivity.  (~2 min)
matrix_crt_bound_sufficient  — vm_compute. reflexivity.  (~1 min)
```

For `per_prime_agreement` and `per_prime_matrix_agreement`: the
deductive proof via `char_poly_mod_sound` + `char_poly_int_agrees_710`
is logically complete but the Rocq kernel's Qed check is slow (expands
forallb over 710 primes). On a machine with `native_compute`, try:
```
Proof. native_compute. reflexivity. Qed.
```

## CertL2.v

### `mat_A_eq_Arat` (~50-90 min, >= 16 GB RAM)

5 algebraic rewrites on `'M[rat]_42`. Complete proof in comment.

### `charpoly_int_Dq_scaled` (~40-80 min, >= 16 GB RAM)

Depends on `mat_A_eq_Arat`. Complete proof in comment.

## Summary

| Category | Count | Time |
|---|---|---|
| Axiom (theoretical) | 1 | ~200 lines to prove |
| Fast admits (CRTLift) | 6 | ~11 min |
| Slow admits (CertL2) | 2 | ~90-170 min |
| **Total** | **9** | **~2-3 hours** |
