# Review Synthesis: prime_gap Maynard M_105 > 4

**Date**: 2026-04-19
**Reviewers**: 4 independent agents (MathComp, Math, Trust, Implementer)

## Consensus Findings

All three completed reviews agree: **the proof architecture is mathematically sound**.
No mathematical gaps were found. All remaining admits are engineering gaps
(compilation time, routine induction, computational wiring).

### Print Assumptions for `maynard_eigenvalue_S1`

| Category | Count | Items |
|----------|-------|-------|
| Project axioms | 1 | `charpoly_int_Dq_scaled` (Admitted) |
| Rocq kernel | ~30 | Uint63 primitives (standard TCB) |
| Classical logic | 0 | None |
| Functional ext. | 0 | None |

The 2 `Axiom` declarations in CRTCheck.v (`modular_step_sound`, `crt_primes_Z_all_prime`)
are **dead code** - not imported by Cert.v.

### Verified Proof Chain

```
maynard_eigenvalue_S1 (Qed)
  <- L1: IVT root existence (Qed, zero axioms)
     <- sign_at_4/105 < 0 (vm_compute, Qed)
     <- lc > 0 (vm_compute, Qed)
  <- L2: shipped poly = D_q * char_poly(A_rat)
     <- charpoly_int_Dq_scaled *** ADMITTED ***
        <- fl_eq_flint (Qed, modulo per_prime_shipped_eq)
        <- matrix_identity_Z (Qed, modulo per_prime_matrix_agreement)
        <- mat_A_eq_Arat (Admitted, needs high-RAM)
        <- charpoly_coeff_bound (Admitted, needs FL induction)
  <- L3: root -> eigenvalue (Qed, MathComp library)
  <- L4: rescaling 105*lambda > 4 (Qed)
```

## Actionable Findings

### Bugs Found (MathComp Review)

1. **CertL2.v line 254**: Commented proof of `mat_A_eq_Arat` passes wrong number
   of arguments to `mat_int_to_rat_scale_inv'` (3 extra hypothesis discharges,
   but the lemma takes none). Must fix before uncommenting.

2. **CertL2.v line 314**: References `CharPolyScale.char_poly_scale_coef` which
   doesn't exist. Correct name: `CharPolyScale.char_poly_scale`. Must fix
   before uncommenting.

### Documentation Discrepancies

1. **README.md line 22**: Claims "The proof has zero axioms" - misleading since
   `charpoly_int_Dq_scaled` is Admitted (equivalent to an axiom). The README
   does clarify in lines 40-43 but the bold claim is overstated.

2. **STATUS.md**: Claims "1 axiom + 2 admits in CRTLift.v" but actually
   0 axioms + 9 admits (7 structural + 2 kernel limits).

3. **TODO.md**: Claims "1 axiom + 4 admits" total, actually 0 axioms + 12 admits.

### Code Quality Notes

1. **CRTCheck.v fuel pattern** (line 212): `no_factor_upto` returns `true` on
   fuel exhaustion. Not a bug (fuel is concretely sufficient, verified by
   vm_compute) but `false` would be safer.

2. **CRTCheck.v base case** (line 173): `check_all_steps_mod` returns `true`
   on mismatched list lengths. Same — not a bug but `false` would be safer.

3. **Bridge.v / CharPoly.v**: `Z_to_int_mul` and `Z_to_int_add` are proved
   independently in both files. Could be shared.

4. **CRTCheck.v**: The 10-prime CRT path (~2^300 product) is insufficient
   for full PRS chain coverage. Correctly documented. The 710-prime path
   in CRTLift.v is the canonical one.

## Confidence Scores

| Reviewer | Score | Rationale |
|----------|-------|-----------|
| MathComp | High | All 4 files sound, proofs well-structured |
| Math | 8.5/10 | Architecture sound, all gaps are engineering |
| Trust | High | 1 Admitted in critical path, no hidden holes |

## CRTLift Implementation Results

Agent 4 (CRTLift Implementer) **closed all 7 structural admits**:

| # | Lemma | Status | Lines |
|---|-------|--------|-------|
| 1 | `max_abs_entry_meye_le` | **Qed** | ~10 |
| 2 | `max_abs_entry_mscale_le` | **Qed** | ~12 |
| 3 | `max_abs_entry_madd_le` | **Qed** | ~20 |
| 4 | `max_abs_entry_mmul_le` | **Qed** | ~25 |
| 5 | `abs_mtrace_le` | **Qed** | ~8 (+ helper) |
| 6 | `fl_loop_coeff_bound` | **Qed** | ~80 |
| 7 | `charpoly_coeff_bound` | **Qed** | ~25 |

**Key change**: `fl_loop_coeff_bound` now requires `fl_all_divisible` as a
hypothesis (needed for exact-division bound on `|c_new|`). The call site in
`charpoly_coeff_bound` supplies it via `fl_all_divisible_from_L2`.

**New helpers**: `abs_mtrace_aux_le`, `Z_abs_div_exact`, `Z_abs_div_le`,
`fl_bound_aux_mono`.

**Structural**: Infrastructure block (~100 lines) moved before bound proofs
to resolve forward-declaration dependencies.

**Result**: CRTLift.v now has **72 Qed, 2 Admitted** (down from 27 Qed, 9 Admitted).
The remaining 2 admits (`per_prime_shipped_eq`, `per_prime_matrix_agreement`)
are kernel Qed limits requiring `native_compute`.

## Updated Proof Chain

```
maynard_eigenvalue_S1 (Qed)
  <- L1: IVT root existence (Qed, zero axioms)
  <- L2: shipped poly = D_q * char_poly(A_rat)
     <- charpoly_int_Dq_scaled *** ADMITTED ***
        <- fl_eq_flint (Qed, modulo per_prime_shipped_eq Admitted)
        <- matrix_identity_Z (Qed, modulo per_prime_matrix_agreement Admitted)
        <- mat_A_eq_Arat (Admitted in CertL2.v, needs high-RAM)
        <- charpoly_coeff_bound *** NOW Qed ***
  <- L3: root -> eigenvalue (Qed, MathComp library)
  <- L4: rescaling 105*lambda > 4 (Qed)
```

## Updated Admit Count

| File | Before | After |
|------|--------|-------|
| CRTLift.v | 9 Admitted | **2 Admitted** (kernel limits) |
| CertL2.v | 2 Admitted | 2 Admitted (MathComp slow rewrites) |
| Cert.v | 1 Admitted | 1 Admitted (local, closed by CertL2) |
| **Total** | **12 Admitted** | **5 Admitted** |

## Recommendations

1. Fix the 2 bugs in CertL2.v commented proofs (wrong arg count, wrong name)
2. Update STATUS.md and TODO.md with accurate counts
3. On a 60GB machine: uncomment CertL2.v proofs to fully close the proof
4. Try `native_compute` for the 2 remaining CRTLift admits on a machine with it enabled
5. Consider removing or marking the dead CRTCheck.v axioms
