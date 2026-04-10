# Computational Verification Audit: Uint63/BigZ/CRT Layer

## 1. CRTCheck.v -- 42-step PRS chain verification

**Identity checked.** `check_prs_step_mod` verifies `lc(B)^d * A = Q*B + beta*C` with `d = S(Nat.sub (mpsize A) (mpsize B))`, i.e., `d = deg(A) - deg(B) + 1`. Since every consecutive pair in the chain drops by exactly degree 1 (chain comments: "degree 42, degree 41, ..."), this gives `d = 2` at every step. This is the standard Knuth pseudo-division convention and is correct for the shipped quotients and betas.

**CRITICAL: The 10-prime check is NOT a proof.** The product of the 10 primes is ~2^300. The maximum coefficient in the chain is ~293,217 bits (per the file's own comments). The CRT theorem requires the product to exceed twice the maximum coefficient magnitude, i.e., ~2^293,218. The gap is ~293,000 bits, requiring ~9,776 primes. With only 10 primes, the check is a probabilistic sanity test: it rules out errors that happen to be non-zero modulo all 10 primes, but it does NOT constitute a mathematical proof. An adversarial or buggy witness could pass this check while being wrong. The file is honest about this (lines 185-192), and `crt_correctness` has conclusion `True` -- it proves nothing.

**Primality verification is sound.** `is_prime_uint63` tests all factors from 2 to 46340. Since 46340 > sqrt(1073741953) (the largest prime), the trial division covers all possible factors. Fuel of 46340 nat suffices. The `vm_compute` discharge is genuine.

**Uint63 overflow analysis: safe.** Residues < 2^31, so products < 2^62 < 2^63. Addition/subtraction intermediate values < 2^32 < 2^63.

**`mpdrop_zeros` is correct.** On first reading it appears buggy (returns `x :: xs` instead of `x :: rest`), but this is intentional: it strips the leading run of zeros and returns the entire remaining suffix unchanged. Identical semantics to IntPoly's `drop_leading_zeros`.

## 2. CRTSigns.v -- Sign vector verification

**`signs_at_x0_bigZ` is sound.** It computes `peval_bigZ p 4 105` for each chain entry and checks sign against `signs_at_x0`. The Horner evaluation `peval_bigZ_aux` is proved equivalent to `peval_at_rat_aux` from IntPoly via `peval_bigZ_aux_spec` (fully proved, Qed). The BigZ-to-Z bridge is established by spec lemmas (`BigZ.spec_add`, `BigZ.spec_mul`, `BigZ.spec_compare`, `BigZ.spec_eqb`) -- all standard from rocq-bignums.

**Sign bridge is complete.** `signs_at_inf_shipped` and `signs_at_x0_shipped` are both Qed. They establish that the shipped sign vectors match evaluation of the shipped chain. No Admitted lemmas in this file.

**Horner argument order is correct.** The low-to-high convention is handled by recursion: `a :: rest` processes `a + (num/den) * rest_eval`, scaling by `den` to clear denominators. This matches IntPoly's `peval_at_rat_aux`.

## 3. PRSCheck.v -- list-Z PRS checker

**d convention discrepancy with CRTCheck.** `check_all_prs_steps` calls `check_prs_step` which uses `d = psize A - psize B` (no +1). CRTCheck uses `d = S(psize A - psize B)` (+1). These are different algebraic identities (subresultant vs Knuth). Both can be correct if the quotients and betas are computed for the respective convention. The full chain check `check_all_prs_steps` is exercised only on toy data in PRSCheck.v; the actual 42-step verification runs through CRTCheck.v with the Knuth convention (`d = S(...)`). The discrepancy is not a bug, but it means PRSCheck's `check_all_prs_steps` is NOT the function used for the real verification.

**Toy tests are correct.** The cubic example `X^3 - 6X^2 + 11X - 6` with its Sturm chain is standard and verifiable by hand. The negative test (wrong quotient -> false) is a good sanity check.

## 4. IntPoly.v -- Polynomial arithmetic

**`prem` is correctly implemented.** The pseudo-division loop normalizes at each step and terminates when `deg A < deg B`. Fuel is `S(length A')`, which is adequate since degree drops strictly. The `prem_step` correctly computes `lcB * A - lcA * X^(degA-degB) * B`.

**`peval_at_rat` is correct.** Returns `(den^(len p) * p(num/den), den^(len p))`. Note: it scales by `den^(length p)`, not `den^(deg p)`. This means for a polynomial `[1; 2; 3]` (length 3, degree 2) at `1/2`, it returns `8 * p(1/2) = 8 * (1 + 1 + 3/4) = 22`, which matches the test. The sign is preserved when `den > 0` because `den^n > 0`. This is correct but subtle -- downstream code must use positive denominators.

**No overflow risk.** All computation is in stdlib Z (arbitrary precision).

## 5. IntMat.v -- Matrix arithmetic

**Bareiss `det_int` has a known fuel bug.** Each row-swap consumes a fuel unit, so on an n x n matrix needing swaps, the loop can run out of fuel and return 0 instead of the correct determinant. Example: `det_int [[0;1];[1;0]]` returns 0, not -1. The workaround `bareiss_no_swap` predicate restricts the correctness claim to matrices that never need swaps (e.g., SPD matrices). The project's target matrix M1 is SPD, so this is adequate for the intended use.

**`mmul` is correct.** Uses the transpose-trick: `map (fun row => map (fun col => dot_int row col) (mtrans B)) A`. Standard and well-tested by sanity checks including identity multiplication.

## 6. Trust base and axioms

**Axioms in the verified computations.** The `vm_compute. reflexivity.` proofs in CRTCheck.v and CRTSigns.v rely on Rocq's kernel reduction, which trusts:
- Uint63 primitive operations (Uint63.mul, Uint63.mod, etc.) -- standard axioms in Rocq 9.0+, part of the trusted kernel.
- BigZ spec lemmas -- from rocq-bignums, proved against the kernel-trusted Uint63 layer.

No non-standard axioms are introduced by the computational files (CRTCheck.v, CRTSigns.v, PRSCheck.v, IntPoly.v, IntMat.v). The `crt_correctness` lemma in CRTCheck.v has an Admitted, but its conclusion is literally `True`, so it introduces no axiom. The `full_prs_chain_verified` lemma and `signs_at_x0_bigZ` / `signs_at_inf_bigZ` are all Qed.

**Broader project axiom status.** Files downstream (CharPoly.v, Bridge.v, CertL1.v, Cert.v) contain many Admitted lemmas -- these are the actual proof gaps, not in the computational layer.

## Summary verdict

| Component | Status |
|---|---|
| CRT 10-prime check | **Probabilistic only** -- ~300 bits vs ~293,000 bits needed. Not a proof. |
| Uint63 primality | Sound (Qed) |
| Uint63 overflow | Safe (residues < 2^31, products < 2^62) |
| BigZ sign computation | Sound, fully bridged to Z (Qed) |
| IntPoly arithmetic | Correct, well-tested |
| Bareiss determinant | Known fuel bug, workaround sound for SPD |
| Axiom base | Standard Uint63 kernel axioms only |

**Bottom line.** The computational layer is well-engineered and the code is correct, but the CRT check covers only ~0.1% of the required bits. It is an honest probabilistic sanity test, not a mathematical proof. The project acknowledges this explicitly. Completing the proof requires either scaling to ~9,776 primes (estimated 6+ hours under vm_compute) or an alternative approach (native_compute, external precomputation with in-Rocq re-verification).
