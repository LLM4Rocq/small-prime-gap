# Closing the remaining admits

**Status: CRTLift.v compiles in ~18 min** (was infinite hang).
**3 admits in CRTLift.v, 2 in CertL2.v, 1 in Cert.v = 6 total.**

## Key insight: the bridge lemma technique

The `per_prime_agreement` Qed used to hang forever because:
```coq
Transparent charpoly_Z_A.
unfold charpoly_Z_A.       (* exposes char_poly_int A_int in goal *)
Opaque charpoly_Z_A.
rewrite (per_prime_mod_eq ...).
```
After the `unfold`, the proof term contained `char_poly_int A_int`,
which the kernel tried to reduce on the concrete 42×42 matrix.

**Fix**: prove a small bridge lemma BEFORE Opaque:
```coq
Lemma charpoly_Z_A_eq : charpoly_Z_A = char_poly_int A_int.
Proof. reflexivity. Qed.
Opaque charpoly_Z_A.
```
Then use `rewrite charpoly_Z_A_eq` (opaque rewrite) instead of `unfold`.
The proof term references the opaque equation, no kernel reduction.

## Remaining admits — same kernel-reduction problem

All 3 CRTLift admits hang Qed >25 min for similar reasons:

### `charpoly_coeff_bound` (line 606)
The proof applies `fl_loop_coeff_bound 42 ... A_int ...` with
`fl_all_divisible_from_L2 A_int 42 ...` as an argument.
The kernel tries to verify the type involving `fl_all_divisible 42 ...`
on the concrete A_int (42 levels of `(k | mtrace ...)` conjunction).

**Possible fixes**:
- Wrap `fl_all_divisible_from_L2 A_int 42 ...` in a separate Qed lemma
- Make `fl_all_divisible` opaque BEFORE the lemma (already done via `Opaque fl_all_divisible`)
- Try `Strategy 1000` for fl_loop, mtrace, mscale, mmul, meye
- Use native_compute (currently disabled at configure)

### `per_prime_shipped_eq` (line 693)
The proof extracts a per-prime fact from `char_poly_int_agrees_710`
(forallb over 710 primes). Both `unfold check_charpoly_710` and direct
`forallb_forall` cause kernel hang.

**Possible fixes**:
- Add per-element extraction lemma in CharPolyAgree.v as a separate Qed
- Use `pose proof` and avoid exposing the 710-element forallb

### `per_prime_matrix_agreement` (line 908)
Helper lemmas exist (mmat_eqb_get, reduce_mat_Z_get) but the full
proof using mscale_mod_sound + mmul_mod_sound triggers similar slow
kernel verification.

## CertL2.v: 2 slow MathComp rewrites (need ≥16 GB RAM machine)

- `mat_A_eq_Arat` (~50-90 min)
- `charpoly_int_Dq_scaled` (~40-80 min)

Use the proofs from git commit ad3b1ca (with bug fixes):
- Remove `[| ... | ... | ...]` from rewrite mat_int_to_rat_scale_inv'
- Change `char_poly_scale_coef` to `char_poly_scale`

## Cert.v: 1 local admit

`charpoly_int_Dq_scaled` (line 60) — closed when CertL2.v compiles.
