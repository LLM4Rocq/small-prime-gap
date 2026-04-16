# Closing remaining gaps

**1 axiom + 4 admits.** Estimated: ~2-3 hours on a 60 GB machine.

## CRTLift.v: 1 axiom + 2 admits

### Axiom: `charpoly_coeff_bound` (~200 lines)

Cofactor expansion bound `|c_k| <= (2nB)^n`. Provable from MathComp
`det_expand` + triangle inequality. The concrete bound is already
verified by the Qed lemma `crt_bound_sufficient`.

### Admits: `per_prime_shipped_eq` + `per_prime_matrix_agreement`

Both have complete deductive proofs. The bottleneck is Rocq's kernel
Qed check which takes >10 min expanding `forallb` over 710 primes.

**To close on target machine**, try replacing `Proof. Admitted.` with:
```
Proof. native_compute. reflexivity. Qed.
```

If `native_compute` is not available, the deductive proof (in comments
above each Admitted) works but needs a patient kernel (~15 min each).

## CertL2.v: 2 admits

### `mat_A_eq_Arat` (~50-90 min, >= 16 GB RAM)

Uncomment the proof block below the `Admitted` (grep `UNCOMMENT`).

### `charpoly_int_Dq_scaled` (~40-80 min, >= 16 GB RAM)

Depends on `mat_A_eq_Arat`. Uncomment the proof block.

## Summary

| Item | File | Type | Time |
|---|---|---|---|
| `charpoly_coeff_bound` | CRTLift.v | Axiom | ~200 lines to write |
| `per_prime_shipped_eq` | CRTLift.v | Admitted | ~15 min Qed (or native_compute) |
| `per_prime_matrix_agreement` | CRTLift.v | Admitted | ~15 min Qed (or native_compute) |
| `mat_A_eq_Arat` | CertL2.v | Admitted | ~50-90 min |
| `charpoly_int_Dq_scaled` | CertL2.v | Admitted | ~40-80 min |
