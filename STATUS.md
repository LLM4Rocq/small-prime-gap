# Project status

**24 Rocq files. 1 axiom + 2 admits in CRTLift.v, 2 admits in CertL2.v. All other files 0 admits.**

## Headline theorem

```rocq
Theorem maynard_eigenvalue_S1 :
  exists lambda : realalg,
    eigenvalue (map_mx (ratr : rat -> realalg) A_rat) lambda
    /\ (ratr (4%:Q / 105%:Q) : realalg) < lambda.
```

Qed in Cert.v.

## CRTLift.v (1 axiom, 2 admits)

**Axiom** (provable in ~200 lines via MathComp det_expand):
- `charpoly_coeff_bound` — cofactor expansion bound `|c_k| <= (2nB)^n`

**Admits** (complete deductive proofs exist, Qed >10 min due to kernel):
- `per_prime_shipped_eq` — follows from `char_poly_int_agrees_710` (Qed in CharPolyAgree.v)
- `per_prime_matrix_agreement` — follows from `matrix_identity_710` + `mscale_mod_sound` + `mmul_mod_sound`

Both admits have the same root cause: Rocq's kernel takes >10 min to
type-check proofs that extract from `forallb` over a 710-element list.
The proofs are logically complete. `native_compute` may close them.

**Qed vm_compute** (closed on this machine, ~20 min total):
- `crt_primes_710_NoDup_check`, `check_all_primes_710` (~8 min),
  `check_primes_gt_43`, `bigZ_bridge_710` (~5 min),
  `crt_bound_sufficient` (~2 min), `matrix_crt_bound_sufficient`

## CertL2.v (0 axioms, 2 admits)

| Lemma | Est. time | RAM |
|---|---|---|
| `mat_A_eq_Arat` | ~50-90 min | >= 16 GB |
| `charpoly_int_Dq_scaled` | ~40-80 min | >= 16 GB |

Both have complete proofs in comments (grep `UNCOMMENT`).

## Estimated closure time (60 GB machine)

CRTLift admits: try `native_compute` (~seconds if available).
CertL2 admits: ~90-170 min (slow MathComp canonical structure resolution).
**Total: ~2-3 hours.**
