# Review & Closure Plan for prime_gap

## Project Summary

Formal verification of Maynard's M_105 > 4 eigenvalue bound.
24 Rocq files, ~18,930 lines. **281 Qed, 10 Admitted, 2 Axioms (97% verified).**
Headline theorem `maynard_eigenvalue_S1` is Qed.

## Current Gaps

| # | File | Name | Type | Category |
|---|------|------|------|----------|
| 1 | CRTLift.v:120 | `max_abs_entry_madd_le` | Admitted | Z-level matrix bound |
| 2 | CRTLift.v:124 | `max_abs_entry_mscale_le` | Admitted | Z-level matrix bound |
| 3 | CRTLift.v:129 | `max_abs_entry_mmul_le` | Admitted | Z-level matrix bound |
| 4 | CRTLift.v:132 | `max_abs_entry_meye_le` | Admitted | Z-level matrix bound |
| 5 | CRTLift.v:137 | `abs_mtrace_le` | Admitted | Z-level trace bound |
| 6 | CRTLift.v:205 | `fl_loop_coeff_bound` | Admitted | FL recurrence induction |
| 7 | CRTLift.v:216 | `charpoly_coeff_bound` | Admitted | Assembly |
| 8 | CRTLift.v:303 | `per_prime_shipped_eq` | Admitted | Kernel Qed limit |
| 9 | CRTLift.v:499 | `per_prime_matrix_agreement` | Admitted | Kernel Qed limit |
| 10 | CertL2.v:250 | `mat_A_eq_Arat` | Admitted | MathComp slow rewrite |
| 11 | CertL2.v:293 | `charpoly_int_Dq_scaled` | Admitted | MathComp slow rewrite |
| 12 | CRTCheck.v:529 | `modular_step_sound` | Axiom | Uint63/BigZ bridge |
| 13 | CRTCheck.v:553 | `crt_primes_Z_all_prime` | Axiom | Primality bridge |

## Review Team

### Agent 1: CRTLift Implementer
- **File ownership**: `theories/S1/CRTLift.v` (exclusive)
- **Task**: Close admits #1-#7 (the 5 matrix bounds + 2 FL proofs)
- **Strategy**: Use `max_abs_entry_le_bound` (converse of `max_abs_entry_get`), 
  `dot_int_bound`, `mat_get_mmul_sq`, `nth_Z_vadd`, etc. from CharPoly.v.
  Add `fl_all_divisible` hypothesis to `fl_loop_coeff_bound` for exact division.
  Helpers needed: move infrastructure lemmas before bounds, add `abs_mtrace_aux_le`,
  `Z_abs_div_divides`, `fl_bound_aux_mono`.
- **Constraint**: File must compile with admits for #8-#9 (kernel limits).
- **Uses**: rocq-mcp for interactive proof development

### Agent 2: MathComp Reviewer
- **File ownership**: Read-only on `CharPoly.v`, `CertL2.v`, `CharPolyScale.v`, `Bridge.v`
- **Task**: Review the MathComp integration layer for correctness:
  - Is the Z-to-rat bridge (`mat_int_to_rat`, `Z_to_int`) sound?
  - Are the FL loop divisibility proofs (`fl_divisibility_L2`) correct?
  - Does `char_poly_int_sound` correctly relate `char_poly_int` to MathComp's `char_poly`?
  - Is the Sturm chain verification in Bridge.v complete?
  - Would the CertL2.v admits (`mat_A_eq_Arat`, `charpoly_int_Dq_scaled`) close on a 60GB machine?
- **Deliverable**: Written findings in `/tmp/review_mathcomp.md`

### Agent 3: Trust Base Auditor (Devil's Advocate)
- **File ownership**: Read-only on `CRTCheck.v`, `Cert.v`, `Fermat.v`, `PrimeCheck.v`
- **Task**: Adversarial review of the trust base:
  - Are the 2 axioms in CRTCheck.v truly sound? Could they be exploited?
  - Does `modular_step_sound` correctly axiomatize Uint63 modular arithmetic?
  - Does `crt_primes_Z_all_prime` correctly bridge to `Znumtheory.prime`?
  - Does the headline theorem actually state what it claims?
  - What is the Rocq `Print Assumptions` output for the headline theorem?
  - Are there any hidden uses of `admit`, `Axiom`, `Variable`, `Parameter` 
    that could weaken soundness?
- **Deliverable**: Written findings in `/tmp/review_trust.md`

### Agent 4: Mathematical Correctness Reviewer
- **File ownership**: Read-only on all files
- **Task**: End-to-end mathematical review:
  - Does the proof chain correctly implement the strategy from Maynard's paper?
  - Is the CRT lift argument (small_multiple_zero) applied correctly?
  - Is the eigenvalue characterization via Sturm chains + IVT mathematically valid?
  - Are the matrix dimensions (42x42) and the M_105 formula correct?
  - Do the 710 CRT primes provide sufficient bit-width for the coefficient bound?
- **Deliverable**: Written findings in `/tmp/review_math.md`

## Execution Rules

1. **No two agents work on the same file** (read-only sharing is fine)
2. **Only Agent 1 modifies files** (CRTLift.v only)
3. **All agents use rocq-mcp** for interactive checking when possible
4. **Project must compile after Agent 1's changes** (admits #8-#9 remain)
5. **Agents report findings as markdown files in /tmp/**

## Success Criteria

- Admits #1-#7 closed with Qed (Agent 1)
- No soundness issues found by trust auditor (Agent 3)
- Mathematical chain validated end-to-end (Agent 4)
- MathComp integration reviewed (Agent 2)
- Documentation discrepancies flagged and fixed
