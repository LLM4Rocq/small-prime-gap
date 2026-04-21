# Project status

**25 Rocq files. Headline proof is NOT complete: it depends on 1 project admit.**

- 0 explicit `Axiom` declarations in critical path (the 2 Axioms in CRTCheck.v are not imported by Cert.v).
- 1 `Admitted` lemma on the critical path: `CertL2.charpoly_int_Dq_scaled`. From the kernel's view (via `Print Assumptions`), this IS an axiom.
- 0 admits in CRTLift.v, 0 admits in Cert.v.

**CRTLift.v now compiles fully** (no more admits). Key fixes:
1. **per_prime_agreement** (was slow Qed): bridge lemma `charpoly_Z_A_eq` via
   `reflexivity` avoids kernel reducing `char_poly_int A_int`.
2. **charpoly_coeff_bound** (was hanging Qed): extract
   `A_int_fl_all_divisible` and `A_int_fl_loop_coeff` as separate Qed helpers
   so the main proof uses opaque references.
3. **per_prime_shipped_eq + per_prime_matrix_agreement** (closed without
   native_compute): `Strategy opaque [list_eqb63 mmat_eqb char_poly_mod ...]`
   prevents the kernel from iota-reducing the equality predicates during
   conversion, which would otherwise trigger WHNF descent into the 42x42
   matrix operations and 42-iteration FL loop. With these constants opaque,
   the kernel stops at syntactic match. Closes in milliseconds (was: hung >25 min).
4. **ModularArith.v** (new shared file): the duplicated definitions of
   addmod63/mmat/reduce_mat_Z/.../char_poly_mod across CharPolyAgree.v and
   CRTBridge.v are now in one canonical file imported by both. (Not strictly
   required for the Strategy fix but eliminates a class of similar issues.)

## Headline theorem

```rocq
Theorem maynard_eigenvalue_S1 :
  exists lambda : realalg,
    eigenvalue (map_mx (ratr : rat -> realalg) A_rat) lambda
    /\ (ratr (4%:Q / 105%:Q) : realalg) < lambda.
```

Qed in Cert.v. `Print Assumptions` shows 1 project admit (`charpoly_int_Dq_scaled`)
plus ~30 standard Uint63 kernel primitives. Zero classical logic axioms.

## CRTLift.v (0 axioms, 0 admits)

Both per_prime admits are now closed via Strategy opaque (see headline).

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

## Cert.v (0 admits)

Cert.v now imports CertL2.v directly. The local duplicate of
`charpoly_int_Dq_scaled` has been removed. All theorem assembly
(L1, L2, L3, L4) is Qed in Cert.v itself.

## Estimated closure time (60 GB machine)

CRTLift: try `native_compute` for 2 admits (~seconds if available).
`charpoly_coeff_bound`: may close with `native_compute` or on faster kernel.
CertL2: ~90-170 min (slow MathComp canonical structure resolution).
**Total: ~2-3 hours.**
