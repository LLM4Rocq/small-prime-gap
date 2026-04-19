# Closing the remaining admits

**0 axioms in critical path. 3 admits in CRTLift.v, 2 admits in CertL2.v, 1 in Cert.v.**

All 3 CRTLift admits are kernel Qed limits (proofs exist but kernel
check is too slow on current hardware). The 2 CertL2 admits need a
machine with >= 16 GB RAM.

## CRTLift.v: 3 kernel Qed limits

### `charpoly_coeff_bound` (line 569)

Complete proof exists in the file (lines 569-605). Verified
interactively via rocq-mcp. Qed hangs because `change charpoly_Z_A
with (char_poly_int A_int)` forces the kernel to evaluate the FL
loop on the concrete 42x42 matrix.

**To close**: try `native_compute` or accept slow Qed.

### `per_prime_shipped_eq` (line 691)

Follows from `char_poly_int_agrees_710` (Qed in CharPolyAgree.v).
Replace `Proof. Admitted.` with `Proof. native_compute. reflexivity. Qed.`

### `per_prime_matrix_agreement` (line 877)

Follows from `matrix_identity_710` + `mscale_mod_sound` + `mmul_mod_sound`.
Replace `Proof. Admitted.` with:
`Proof. Transparent mat_lhs_opaque mat_rhs_opaque. native_compute. reflexivity. Qed.`

## CertL2.v: 2 slow MathComp rewrites

### `mat_A_eq_Arat` (line 250, ~50-90 min, >= 16 GB)

Uncomment the proof below (grep `UNCOMMENT`).
**Known bug**: remove the `[| ... | ... | ...]` clause from
`rewrite mat_int_to_rat_scale_inv'` (lemma takes no extra args).

### `charpoly_int_Dq_scaled` (line 293, ~40-80 min, >= 16 GB)

Depends on `mat_A_eq_Arat`. Uncomment the proof below.
**Known bug**: change `CharPolyScale.char_poly_scale_coef` to
`CharPolyScale.char_poly_scale`.

## Cert.v: 1 local admit

`charpoly_int_Dq_scaled` (line 60) -- closed automatically when
CertL2.v compiles.
