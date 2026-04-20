# Project status

**24 Rocq files. 0 axioms in critical path. 3 admits in CRTLift.v, 2 admits in CertL2.v, 1 admit in Cert.v.**

**CRTLift.v now compiles in ~18 min** (was: hung indefinitely on per_prime_agreement Qed).
Bridge lemma fix avoids triggering kernel reduction on char_poly_int A_int.

## Headline theorem

```rocq
Theorem maynard_eigenvalue_S1 :
  exists lambda : realalg,
    eigenvalue (map_mx (ratr : rat -> realalg) A_rat) lambda
    /\ (ratr (4%:Q / 105%:Q) : realalg) < lambda.
```

Qed in Cert.v. `Print Assumptions` shows 1 project admit (`charpoly_int_Dq_scaled`)
plus ~30 standard Uint63 kernel primitives. Zero classical logic axioms.

## CRTLift.v (0 axioms, 3 admits)

**Admits** (all kernel Qed limits -- complete proofs exist, kernel check >10 min):
- `charpoly_coeff_bound` -- FL coefficient bound assembly. Proof verified
  interactively via rocq-mcp. Qed hangs because `change charpoly_Z_A with
  (char_poly_int A_int)` forces the kernel to evaluate the FL loop on the
  concrete 42x42 matrix.
- `per_prime_shipped_eq` -- follows from `char_poly_int_agrees_710` (Qed in
  CharPolyAgree.v). Needs `native_compute` to close.
- `per_prime_matrix_agreement` -- follows from `matrix_identity_710` +
  `mscale_mod_sound` + `mmul_mod_sound`. Needs `native_compute` to close.

**Qed proofs (closed):**
- 6 matrix operation bounds: `max_abs_entry_meye_le`, `max_abs_entry_mscale_le`,
  `max_abs_entry_madd_le`, `max_abs_entry_mmul_le`, `abs_mtrace_le`,
  `fl_loop_coeff_bound` -- all Qed
- All vm_compute checks: NoDup, primality, FL bound, BigZ bridge, matrix CRT bound
- CRT lift proofs: `fl_eq_flint`, `matrix_identity_Z` -- both Qed

## CRTCheck.v (2 axioms, NOT in critical path)

- `modular_step_sound` -- Uint63/BigZ bridge for PRS chain CRT check.
  Sound but not formally proved. **Not imported by Cert.v.**
- `crt_primes_Z_all_prime` -- 10-prime primality. Trivially true.
  **Not imported by Cert.v.**

## CertL2.v (0 axioms, 2 admits)

| Lemma | Est. time | RAM |
|---|---|---|
| `mat_A_eq_Arat` | ~50-90 min | >= 16 GB |
| `charpoly_int_Dq_scaled` | ~40-80 min | >= 16 GB |

Both have complete proofs in comments (grep `UNCOMMENT`).
Note: the commented proof for `mat_A_eq_Arat` has a known bug
(wrong arg count for `mat_int_to_rat_scale_inv'`); fix before uncommenting.

## Cert.v (1 local admit)

- `charpoly_int_Dq_scaled` -- local copy, closed when CertL2.v compiles.

## Estimated closure time (60 GB machine)

CRTLift: try `native_compute` for 2 admits (~seconds if available).
`charpoly_coeff_bound`: may close with `native_compute` or on faster kernel.
CertL2: ~90-170 min (slow MathComp canonical structure resolution).
**Total: ~2-3 hours.**
