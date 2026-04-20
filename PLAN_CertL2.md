# Plan: Close the 2 remaining CRTLift admits without native_compute

## Executive summary

The 2 CRTLift admits (`per_prime_shipped_eq`, `per_prime_matrix_agreement`)
hang on Qed NOT because of computation volume, but because of a structural
issue: `check_charpoly_710` uses an **inline lambda**, forcing the kernel's
lazy reducer to expose `char_poly_mod p A_int` during conversion checks.

**The fix is simple and has already proven to work** — the same pattern
works for `check_mat_identity_710` (closes in ms) which uses a NAMED
function. We just need to factor the inline lambda out into a named
definition.

## Root cause (from `/tmp/qed_hang_investigation.md`)

When extracting `P p = true` from `forallb P L = true` via `forallb_forall`:
- If `P` is a **named** function (like `check_mat_identity_one_prime`):
  the kernel keeps `P` folded during conversion. Works in milliseconds.
- If `P` is an **inline lambda** (like in `check_charpoly_710`):
  every β-step exposes `char_poly_mod`, `A_int`, `charpoly_of_A_int_bigZ`
  to the kernel's lazy reducer, which explores 42×42 matrix terms
  symbolically. Hangs >25 min.

**Critical insight**: `vm_compute` is used at the SOURCE Qed only; the
cast is opaque, and downstream uses cannot reuse it. The downstream Qed
does plain lazy reduction.

## The fix — structural rewrite

### Step 1: Refactor `check_charpoly_710` in CharPolyAgree.v

Change from:
```coq
Definition check_charpoly_710 : bool :=
  List.forallb (fun p =>
    let computed := char_poly_mod p A_int in
    let shipped := List.map (bigZ_to_mod63 p) charpoly_of_A_int_bigZ in
    list_eqb63 computed shipped
  ) crt_primes_all.
```

To:
```coq
Definition check_charpoly_one_prime (p : Uint63.int) : bool :=
  let computed := char_poly_mod p A_int in
  let shipped := List.map (bigZ_to_mod63 p) charpoly_of_A_int_bigZ in
  list_eqb63 computed shipped.

Definition check_charpoly_710 : bool :=
  List.forallb check_charpoly_one_prime crt_primes_all.
```

The `char_poly_int_agrees_710` proof stays the same (`vm_compute. reflexivity. Qed.`).

### Step 2: Close `per_prime_shipped_eq` in CRTLift.v

Mirror the working `matrix_per_prime` pattern:
```coq
Lemma check_charpoly_as_forallb :
  check_charpoly_710 = List.forallb check_charpoly_one_prime crt_primes_all.
Proof. reflexivity. Qed.

Lemma shipped_per_prime (p : Uint63.int) (Hin : In p crt_primes_all) :
  check_charpoly_one_prime p = true.
Proof.
  assert (H : List.forallb check_charpoly_one_prime crt_primes_all = true).
  { rewrite <- check_charpoly_as_forallb. exact char_poly_int_agrees_710. }
  exact ((proj1 (List.forallb_forall _ _) H) p Hin).
Qed.

Lemma per_prime_shipped_eq p (Hin : In p crt_primes_all) :
  char_poly_mod p A_int = List.map (bigZ_to_mod63 p) charpoly_of_A_int_bigZ.
Proof.
  apply list_eqb63_sound. exact (shipped_per_prime p Hin).
Qed.
```

### Step 3: Close `per_prime_matrix_agreement` in CRTLift.v

The `matrix_per_prime` helper already uses the named-predicate pattern
and works. The full proof is drafted in comments but the Qed hangs due
to another issue: the later `mscale_mod_sound`/`mmul_mod_sound` rewrites
expose concrete matrix terms.

Strategy:
1. Extract `matrix_per_prime p Hin` to get `check_mat_identity_one_prime p = true`.
2. Use `vm_cast_no_check` at the END of the proof, once the goal is a
   ground Uint63 entry equality.

Alternatively: add `Strategy 1000` declarations for heavy constants:
```coq
Strategy 1000 [mmat_scale mmat_mul mmat_trans Z_to_mod63 bigZ_to_mod63
               reduce_mat_Z A_int M1_int M2_int char_poly_mod
               charpoly_of_A_int_bigZ list_eqb63].
```

This biases the kernel to NEVER unfold these during conversion.

### Step 4: Verify all files compile

```bash
rocq compile -Q theories/S1 PrimeGapS1 theories/S1/CharPolyAgree.v  # ~30 min (rebuilds vm_compute)
rocq compile -Q theories/S1 PrimeGapS1 theories/S1/CRTLift.v        # ~18 min
rocq compile -Q theories/S1 PrimeGapS1 theories/S1/CertL2.v         # ~seconds
rocq compile -Q theories/S1 PrimeGapS1 theories/S1/Cert.v           # ~seconds
```

## Risk assessment

- **Risk 1**: Rebuilding CharPolyAgree.v requires re-running the 710-prime vm_compute
  for `char_poly_int_agrees_710`. This is known to take ~10-20 min.
- **Risk 2**: The named-predicate refactor might break other proofs that reference
  `check_charpoly_710`'s inline structure. Need to grep.
- **Risk 3**: `per_prime_matrix_agreement` might still hang even with Strategy
  declarations because its proof is more complex. Need `Strategy` + possibly
  `vm_cast_no_check` at the end.

## Implementation team

- **Agent A (CharPolyAgree)**: Refactor `check_charpoly_710` with named
  predicate. Rebuild CharPolyAgree.v (~20 min vm_compute).
- **Agent B (CRTLift)**: Close `per_prime_shipped_eq` using the new named
  predicate. Close `per_prime_matrix_agreement` using Strategy declarations
  and/or vm_cast_no_check.

Since these two steps are sequential (B depends on A), a single agent
can handle both. The compile cycle is ~40 min total per iteration.

## Success criteria

- 0 admits in CRTLift.v
- All files compile
- Commit each step (CharPolyAgree refactor; per_prime_shipped_eq close; per_prime_matrix_agreement close)
