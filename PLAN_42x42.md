# Plan: Closing the 42x42 Computational Gaps in the Maynard M_105 Formalization

## Problem Summary

Two key lemmas remain `Admitted` because `vm_compute` cannot handle the scale:

1. **`signs_at_x0_agree`** / **`signs_at_inf_agree`**: verifying that precomputed sign
   data matches `BrownTraub.sturm_chain charpoly_int` -- a 43-step pseudo-remainder
   sequence (PRS) where coefficient sizes grow from ~1.4 kbit (chain[0]) to ~100 kbit
   (chain[42]), with each step performing polynomial `prem` on polynomials whose
   coefficients are ~2.6 kbit larger than the previous step.

2. **`char_poly_int_agrees_with_flint`**: verifying that `char_poly_int A_int`
   (Faddeev-LeVerrier on a 42x42 matrix with ~1.4 kbit entries) matches the
   FLINT-shipped characteristic polynomial. This requires 42 full matrix-matrix
   multiplications with exploding intermediate entries.

## Empirical Findings

- **BigZ.mul at 200 kbit**: 82 ms under `vm_compute`. Individual large-integer
  operations are fast.
- **Stdlib Z.mul at 200 kbit**: 47 ms under `vm_compute`. Also fast -- the bottleneck
  is not single multiplications but the sheer number and cumulative growth across 42
  PRS steps.
- **native_compute**: `COQ_NATIVE_COMPILER_DEFAULT=no` and no `nativelib` files are
  present. The current Rocq 9.0.1 installation on opam switch `4.14.2+flambda` was
  built with native_compute disabled at configure time.
- **Chain structure**: 43 polynomials, degrees 42 down to 0, max coefficient bits
  growing linearly (~2600 bits per step) to 100,578 bits at chain[42].

---

## Approach Assessments (Ranked by Feasibility)

### 1. Polynomial Evaluation Certificate (RECOMMENDED -- Implement First)

**Idea**: Instead of asking Rocq to recompute the entire 42-step PRS from scratch,
ship the precomputed chain polynomials `R_0, ..., R_42` AND per-step certificates
`(Q_i, R_i)` such that `lc(q_i)^delta * q_{i-1} = Q_i * q_i + R_i` (the
pseudo-division identity). Rocq verifies each step by checking ONE polynomial
multiplication + ONE addition, not by running the full `prem` algorithm.

**Feasibility**: HIGH. Each verification step requires multiplying two polynomials
whose coefficients are at most ~100 kbit (the largest chain entry). A degree-d
times degree-d polynomial multiplication is O(d^2) coefficient multiplications --
at most 42*42 = 1764 multiplications of ~100 kbit integers. At 47 ms per 200 kbit
multiply, the per-coefficient cost is negligible; the bottleneck is the number of
coefficients and the overhead of `vm_compute` term construction. Conservatively,
each of the 42 verification steps should take 1-5 seconds, for a total of
1-4 minutes.

**Implementation**: ~200 lines of new Rocq (a `check_prem_step` function and a
loop over the certificate), ~100 lines of Python to emit `(Q_i, R_i)` pairs from
FLINT. The chain polynomials are already shipped in `certificate_chain.json`.
A new `WitnessPremCert.v` file would define the Q_i / R_i data, and a
`CertPrem.v` would verify each step by `vm_compute`.

**Trust**: Only Rocq's kernel. The external computation (FLINT) is untrusted --
Rocq verifies the algebraic identity from scratch.

**Wall-clock estimate**: 1-4 minutes total compilation.

---

### 2. Streaming / Chunked Verification

**Idea**: Break the 42-step PRS into individual `.v` files. File `Step_k.v` loads
`chain[k-1]` and `chain[k]` from compiled `.vo` files, then verifies `prem
chain[k-1] chain[k] = chain[k+1]` by `vm_compute`. Each file handles one step, so
the working set of large integers is bounded.

**Feasibility**: MEDIUM-HIGH. This is simpler than approach 1 (no Q_i/R_i
certificates needed -- just ship the chain polynomials and verify `prem` directly),
but `prem` on polynomials with 50-100 kbit coefficients may still be slow because
`prem` internally performs O(degree_difference) iterations, each involving full
polynomial arithmetic. For the later steps (where coefficients are ~80-100 kbit but
degrees are small, 5-10), each `prem` call should complete in seconds. For earlier
steps (high degree, moderate coefficients), it could take 10-30 seconds per step.

**Implementation**: ~50 lines of Rocq per step file (could be auto-generated),
plus a Makefile rule. A Python script generates 42 `.v` files.

**Trust**: Only Rocq's kernel.

**Wall-clock estimate**: 5-15 minutes total (parallelizable across files).

---

### 3. Reflect to Bool (`Z.eqb` Instead of Structural `reflexivity`)

**Idea**: Replace `vm_compute. reflexivity.` with `vm_compute` on a boolean
expression `Z.eqb lhs rhs` that reduces to `true`. The advantage: `vm_compute`
on `Z.eqb` can short-circuit comparison without fully normalizing both sides
into canonical term form, and the final `reflexivity` compares `true = true`
instead of two enormous `Z` terms.

**Feasibility**: MEDIUM. This helps with the final comparison step but does NOT
reduce the cost of computing `prem` itself. If the bottleneck is `prem`
computation (not term comparison), this alone won't help. However, combined with
approach 2 (chunked verification), it could reduce per-step overhead by 2-5x.
For the `char_poly_int_agrees_with_flint` lemma, this is less helpful since the
Faddeev-LeVerrier computation itself is the bottleneck.

**Implementation**: ~10 lines of change (wrap the equality in `Z.eqb` / `list_beq
Z.eqb`, prove `Is_true (list_beq Z.eqb lhs rhs) -> lhs = rhs`).

**Trust**: Only Rocq's kernel.

**Wall-clock estimate**: Marginal improvement alone; useful as a modifier on other
approaches.

---

### 4. native_compute (Rebuild Rocq)

**Idea**: Rebuild Rocq 9.0.1 with `native_compute` enabled. The native code path
compiles Gallina terms to OCaml, then to native machine code via `ocamlopt`,
yielding 10-100x speedup over `vm_compute` for computation-heavy proofs.

**Feasibility**: MEDIUM. The opam configuration requires rebuilding `rocq-core`
with `-native-compiler yes` passed to `./configure`. On `4.14.2+flambda`, this
should work but requires rebuilding the entire Rocq + MathComp dependency tree
(~30-60 minutes of opam compilation). The expected speedup for large-integer
arithmetic is 10-30x (native `Z.mul` benefits from OCaml's native int64
operations and optimized GC). This could make the full `sturm_chain` computation
take 30-60 seconds instead of 300+ seconds -- potentially tractable.

For the Faddeev-LeVerrier (`char_poly_int`), even a 30x speedup on a multi-hour
computation yields ~5-15 minutes, which may be acceptable but is not guaranteed.

**Implementation**: ~0 lines of Rocq change. ~30-60 minutes of opam rebuilding.
Risk: `native_compute` has known issues with some MathComp constructs and may
introduce subtle bugs (though it is kernel-verified).

**Trust**: Rocq's kernel + the OCaml native compiler correctness (same trust as
`vm_compute` + OCaml bytecode compiler).

**Wall-clock estimate**: Sturm chain: 30-60s. Faddeev-LeVerrier: 5-15 min (uncertain).

---

### 5. Modular Arithmetic Certificate

**Idea**: Factor verification through small primes. Compute `prem(p, q) mod p_i`
for several primes `p_i`, verify each residue by `vm_compute` (fast because entries
fit in 63 bits), then reconstruct via CRT.

**Feasibility**: LOW-MEDIUM. The chain's largest coefficients are ~100 kbit, so we
need primes whose product exceeds 2^100000. Using 31-bit primes, that's
ceil(100000/31) = ~3226 primes. Each prime requires a full 42-step PRS computation
on small polynomials (fast: <1s each). Total: ~3226 seconds = ~54 minutes just for
the modular computations, plus CRT reconstruction in Rocq. The CRT reconstruction
itself involves multiplying ~3226 31-bit numbers, which is tractable but requires
careful implementation.

The real issue: implementing CRT-based polynomial verification in Rocq is a
significant engineering effort (~500-1000 lines), and the total wall-clock time
(~1 hour) is worse than the certificate approach.

**Implementation**: ~800 lines of Rocq (CRT library, modular PRS, reconstruction
proof), ~200 lines of Python for prime selection.

**Trust**: Only Rocq's kernel.

**Wall-clock estimate**: ~1 hour.

---

### 6. BigZ-Based Computation

**Idea**: Rewrite `IntPoly` to use `BigZ` instead of stdlib `Z` for all arithmetic,
potentially gaining speed from the word-array representation.

**Feasibility**: LOW. Empirical testing shows stdlib `Z` is actually slightly
*faster* than `BigZ` for individual operations at the 200 kbit scale (47 ms vs 82 ms
for multiplication). The `vm_compute` bytecode for `Z` is highly optimized. The
bottleneck is not per-operation speed but the number of operations in the 42-step
PRS cascade. Switching to `BigZ` would require rewriting `IntPoly.v` and all
downstream files for no clear performance benefit.

**Implementation**: ~300 lines of rewriting. No expected speedup.

**Wall-clock estimate**: Same as current (too slow).

---

### 7. Kernel-Level Trusted Computation (Plugin / External Oracle)

**Idea**: Write a Rocq plugin (in OCaml) that calls FLINT via FFI to compute `prem`
natively, then injects the result into Rocq's kernel. Alternatively, use
`Declare Reduction` with a custom reduction strategy.

**Feasibility**: LOW. Rocq plugins that inject computational results require either
`native_compute` infrastructure or careful use of `vm_cast_no_check` (which is
axiom-level trust). A FLINT-calling plugin would be ~500 lines of OCaml and would
introduce a dependency on FLINT's correctness into the TCB. This is the "nuclear
option" and undermines the goal of a machine-checked proof.

**Implementation**: ~500 lines of OCaml plugin code.

**Trust**: Rocq kernel + FLINT + the plugin's OCaml code. Unacceptable for a
formalization intended to be independently verifiable.

**Wall-clock estimate**: Milliseconds (but high trust cost).

---

### 8. Pre-Normalize and Cache

**Idea**: Ship both input AND expected output, verify `prem input_p input_q =
expected_output` by `vm_compute. reflexivity.` for each step.

**Feasibility**: This is essentially approach 2 (chunked verification) without the
file-splitting. The question is whether `vm_compute` on a single `prem` call
(one PRS step) completes in reasonable time. For the early steps (degree 42, 41;
coefficients ~1-4 kbit), `prem` involves ~1-3 iterations of degree reduction, each
doing polynomial arithmetic on ~42 coefficients -- should take <1s. For the later
steps (degree 5-10; coefficients ~80-100 kbit), `prem` involves ~1-5 iterations on
small polynomials with large coefficients -- should also take <5s. The middle steps
(degree ~20; coefficients ~50 kbit) are the worst case: ~20 iterations on ~20
coefficients of ~50 kbit, roughly 20*20 = 400 multiplications of 50 kbit numbers at
~20 ms each = ~8 seconds per step.

**Implementation**: This is the simplest approach -- just ship chain[i] for all i,
and verify each `prem` step. ~100 lines of Rocq, ~50 lines of Python.

**Trust**: Only Rocq's kernel.

**Wall-clock estimate**: 2-8 minutes total.

---

## Concrete Recommendation

**Implement Approach 1 (Polynomial Evaluation Certificate) first**, with Approach 8
(Pre-Normalize / direct `prem` per step) as a fallback.

**Rationale**:

1. Approach 1 converts each verification step from "run the `prem` algorithm" (which
   has quadratic internal iteration) to "check one multiplication + one addition"
   (a single pass). This is asymptotically better and provides the strongest
   guarantee of tractability.

2. The data pipeline already exists: `certificate_chain.json` ships the chain
   polynomials; we only need to additionally emit the quotient `Q_i` for each step
   (FLINT computes this as a byproduct of `prem`).

3. If Approach 1 proves more complex to implement than expected, Approach 8 (direct
   per-step `prem` verification with pre-shipped expected outputs) requires almost no
   new infrastructure and -- based on the coefficient size analysis -- should complete
   in under 10 minutes.

4. For `char_poly_int_agrees_with_flint`, the certificate approach generalizes: ship
   the intermediate Faddeev-LeVerrier matrices `M_1, ..., M_42` and verify each step
   `M_{k+1} = A * M_k + c_k * I` by a single matrix multiplication check. Each step
   involves one 42x42 matrix multiply with entries growing up to ~60 kbit
   (42 * 1.4 kbit). A 42x42 matrix multiply is 42^3 = 74088 multiplications of
   ~60 kbit integers at ~30 ms each under `vm_compute` -- roughly 2200 seconds per
   step, which is too slow. Therefore, for the charpoly agreement, Approach 4
   (native_compute) or a hybrid modular-certificate approach may be needed as a
   second phase.

**Immediate next step**: Write a Python script to emit `(Q_i, R_i)` certificates
from FLINT for each PRS step, then build `CertPremStep.v` to verify each step by
`vm_compute` on the identity `lc(q)^delta * p = Q * q + R`.
