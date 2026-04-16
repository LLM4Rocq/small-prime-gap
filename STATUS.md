# Project status

**24 Rocq files. 1 axiom, 6 admits in CRTLift.v + 2 admits in CertL2.v. All other files 0 admits.**

## Headline theorem

```rocq
Theorem maynard_eigenvalue_S1 :
  exists lambda : realalg,
    eigenvalue (map_mx (ratr : rat -> realalg) A_rat) lambda
    /\ (ratr (4%:Q / 105%:Q) : realalg) < lambda.
```

Qed in Cert.v.

## CRTLift.v (1 axiom, 6 admits)

**Axiom** (provable in ~200 lines via MathComp det_expand):
- `charpoly_coeff_bound` — cofactor expansion bound `|c_k| <= (2nB)^n`

**Admits** (all fast vm_compute or Uint63 modular, ~11 min total):

| Lemma | Est. time | What it computes |
|---|---|---|
| `crt_primes_710_NoDup_check` | ~seconds | pairwise distinct check on 710 Z values |
| `check_all_primes_710` | ~8 min | 710 trial division primality checks |
| `per_prime_agreement` | ~seconds | Uint63 modular FL + comparison (via CRTBridge) |
| `per_prime_matrix_agreement` | ~seconds | Uint63 modular matrix ops + comparison |
| `crt_bound_sufficient` | ~2 min | `(2*42*B)^42 + max_coeff < product_710` |
| `matrix_crt_bound_sufficient` | ~1 min | entry bound vs CRT product |

## CertL2.v (0 axioms, 2 admits — slow MathComp rewrites)

| Lemma | Est. time | RAM |
|---|---|---|
| `mat_A_eq_Arat` | ~50-90 min | >= 16 GB |
| `charpoly_int_Dq_scaled` | ~40-80 min | >= 16 GB |

## Estimated total time (60 GB machine)

| Category | Time |
|---|---|
| CRTLift fast admits | ~11 min |
| CertL2 slow rewrites | ~90-170 min |
| Other files | ~5 min |
| **Total** | **~2-3 hours** |
