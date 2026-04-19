# Closing remaining gaps

**0 axioms in critical path. 6 admits total.** Estimated: ~2-3 hours on a 60 GB machine.

## CRTLift.v: 3 admits (all kernel Qed limits)

### `charpoly_coeff_bound` (kernel limit)

FL coefficient bound assembly. Complete proof exists in the file
(lines 569-605) but Qed hangs >10 min. The proof was verified
interactively via rocq-mcp. The bottleneck is `change charpoly_Z_A
with (char_poly_int A_int)` which forces the kernel to evaluate the
FL loop on the concrete 42x42 matrix during Qed.

**To close**: try `native_compute` on a machine with it enabled, or
accept the slow Qed (~hours).

### `per_prime_shipped_eq` + `per_prime_matrix_agreement` (kernel limits)

Both have complete deductive proofs. The bottleneck is Rocq's kernel
Qed check which takes >10 min expanding `forallb` over 710 primes.

**To close on target machine**, try replacing `Proof. Admitted.` with:
```
Proof. native_compute. reflexivity. Qed.
```

## CertL2.v: 2 admits (MathComp slow rewrites)

### `mat_A_eq_Arat` (~50-90 min, >= 16 GB RAM)

Uncomment the proof block below the `Admitted` (grep `UNCOMMENT`).
**Bug**: the commented proof passes wrong number of arguments to
`mat_int_to_rat_scale_inv'`. Remove the `[| ... | ... | ...]` clause.

### `charpoly_int_Dq_scaled` (~40-80 min, >= 16 GB RAM)

Depends on `mat_A_eq_Arat`. Uncomment the proof block.
**Bug**: references `CharPolyScale.char_poly_scale_coef` which doesn't
exist. Correct name: `CharPolyScale.char_poly_scale`.

## Cert.v: 1 local admit

- `charpoly_int_Dq_scaled` -- closed automatically when CertL2.v compiles.

## Summary

| Item | File | Type | Closure |
|---|---|---|---|
| `charpoly_coeff_bound` | CRTLift.v | Kernel limit | native_compute or patience |
| `per_prime_shipped_eq` | CRTLift.v | Kernel limit | native_compute |
| `per_prime_matrix_agreement` | CRTLift.v | Kernel limit | native_compute |
| `mat_A_eq_Arat` | CertL2.v | Slow rewrite | ~50-90 min, >= 16 GB |
| `charpoly_int_Dq_scaled` | CertL2.v | Slow rewrite | ~40-80 min, >= 16 GB |
| `charpoly_int_Dq_scaled` | Cert.v | Local copy | Closed by CertL2.v |
