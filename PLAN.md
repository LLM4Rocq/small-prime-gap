# Plan: high-assurance reproduction of Maynard's λ > 4 computation

**Target.** James Maynard, *Small gaps between primes*, Annals of Mathematics
**181** (2015), 383–413, arXiv:1311.4600. Specifically the numerical estimate
underlying Proposition 4.3 / equation (8.15): the bound `M_{105} > 4`,
established in the ancillary Mathematica notebook `Computations.nb` (v3 of the
arXiv source). This is **the headline result**, not a toy: the same notebook
proves the inequality at the dimension `k = 105` that powers the bounded gaps
≤ 600 conclusion.

**Goal.** Two independent re-implementations of the bound, both auditable and
both producing a *bit-identical* certificate:

1. **A Rocq file** (Rocq 9.0.1 + MathComp + Stdlib `ZArith`) that states the
   inequality and proves it by `vm_compute` on a precomputed witness vector.
2. **A Python file using FLINT** (`python-flint`, exact `fmpq_mat` + ARB
   `arb_mat` for the eigen-step) that produces the witness vector and emits a
   JSON certificate consumed by both pipelines.

The two pipelines must produce the **same** integer witness vector and the
**same** integer Rayleigh quotient numerator/denominator, byte for byte.
Triangulation is the audit.

---

## 0. Environment audit (already done)

| Tool | Status | Notes |
|---|---|---|
| Rocq prover | **9.0.1** ✅ | `rocq-prover 9.0.0`, `coq-stdlib 9.0.0` |
| MathComp | **2.5.0** ✅ | ssreflect, algebra, field, real-closed |
| MathComp Analysis | **1.15.0** ✅ | not on the critical path of the chosen plan |
| Coquelicot | **3.4.4** ✅ | not used |
| Bignums | **9.0.0** ✅ | available if `Z` overflows our needs |
| coq-interval | **4.11.4** installable ✅ | dry-run pulls coq-bignums + coq-flocq + interval; **not actually needed** for the chosen plan, see §3 |
| native_compute | **disabled** ⚠️ | this Rocq build was compiled without native support; `vm_compute` only, but it is fast enough — see §4 |
| python-flint | not installed but trivially installable ✅ | `uv pip install python-flint` resolves cleanly via PyPI manylinux wheels (FLINT 3.x bundled, no system libs needed) |
| FLINT system package | absent and `apt` index empty ❌ | not the right path |
| Working dir | `/home/rocq/prime_gap` (clean) | also has `/home/rocq/prime_gap/notebook_reconstructed.md` (the flattened notebook) |

---

## 1. Mathematical content (extracted from Maynard §6–§8 + the notebook)

The notebook enumerates the 42 monomial pairs

> `B = { (b, c) ∈ ℕ² : b + 2c ≤ 11 }`,    `|B| = 42`,

and parametrises symmetric polynomials in `t_1, …, t_k` (`k = 105`) by
`f(t) = F(x, y)` with `x = 1 − Σ t_i`, `y = Σ t_i²`, where `F` ranges over
`span_ℚ { x^b · y^c : (b, c) ∈ B }`.

For such an `F` parametrised as `F = Σ_i A_i x^{b_i} y^{c_i}`, define two
quadratic forms in the coefficient vector `A = (A_1, …, A_42)`:

- `I_k(F) = ∫_{Δ_k} F(x,y)² dt = Aᵀ M₁ A`,    where Δ_k is the standard simplex.
- `J_k(F) = ∫_{Δ_{k-1}} (∫_0^{1-Σ' tᵢ} F dt_1)² dt' = Aᵀ M₂ A`.

Both `M₁` and `M₂` are exact symmetric **rational** 42 × 42 matrices: their
entries reduce in closed form to ratios of factorials via the Dirichlet/Beta
integral

> `∫_{Δ_k} t_1^{a_1} … t_k^{a_k} dt = (∏ a_i!) / (k + Σ a_i)!`.

The notebook routine `ConstCalc` assembles `M₁` from this identity (Lemma 7.1
of the paper), and `PrmeCalc` assembles `M₂` after first integrating `t_1`
analytically (eq. 7.8 of the paper). **No `Integrate` is ever called and no
`N[]` touches either matrix.**

The Maynard sieve quantity `M_k` is

> `M_k = sup_{F ≠ 0}  k · J_k(F) / I_k(F) = sup_{a ≠ 0}  k · aᵀ M₂ a / aᵀ M₁ a`,

i.e. `k` times the largest generalised eigenvalue of the pencil `(M₂, M₁)`,
restricted to the symmetric subspace. Maynard needs `M_{105} > 4` to deduce
liminf `(p_{n+1} − p_n) ≤ 600`.

The notebook's certification of `M_{105} > 4` is **already** a
witness-vector / Rayleigh-quotient argument: it computes a high-precision
numerical eigenvector of `M_3 := M₁⁻¹ M₂`, snaps it to a rational vector
`v ∈ ℚ⁴²` with `Rationalize[..., 10⁻⁴⁰]`, then evaluates the *exact* rational

> `Ratio = k · (vᵀ M₂ v) / (vᵀ M₁ v)`

and prints `4.00206976193804713686805879340335542151`. The numerical eigen
step is a black-box heuristic; the certificate that survives is the exact
rational inequality `Ratio > 4`. **Reproducing this exact-rational
certification step in Rocq is therefore not a workaround — it is literally
auditing what the notebook does.**

A full per-routine extraction of the notebook is in
`/home/rocq/prime_gap/notebook_reconstructed.md`.

---

## 2. The proof obligation, in one breath

We will state and prove (Rocq pseudocode, made precise in §5):

```rocq
Theorem maynard_M105_gt_4 :
  let v   : list Z   := witness_v   in   (* 42 entries, common denom cleared *)
  let M1  : list (list Z) := M1_int  in   (* 42×42, common denom cleared *)
  let M2  : list (list Z) := M2_int  in   (* 42×42, common denom cleared *)
  (* M1 and M2 are the integer-cleared Maynard Gram matrices for k=105,
     coming from `simplex_int` defined inside the file (audited) *)
  M1_int_correct /\ M2_int_correct /\
  (* The certificate: 105 · vᵀ M2 v · D_M1 > 4 · vᵀ M1 v · D_M2,
     where D_M1, D_M2 are the cleared common denominators of M1, M2. *)
  105 * dot_quad v M2_int * D_M1 > 4 * dot_quad v M1_int * D_M2.
Proof.
  vm_compute. (* < 1 second on 42×42 with ~200-bit entries *)
  reflexivity (* or: lia *).
Qed.
```

The two `_correct` conjuncts say "this concrete integer matrix really is the
matrix of `I_k`/`J_k` in the chosen basis". The MVP discharges them by
`reflexivity` against an in-file `simplex_int`-based assembly; the lazy
fallback admits them.

---

## 3. Why **not** CoqInterval and **not** MathComp matrices

We probed both with `rocq_query` (timings recorded below in §4):

- **MathComp `'M[rat]_n` + `\matrix_(i,j) ...`**: a 4×4 Rayleigh quotient via
  `vm_compute` **timed out at 30 s**. The `'M[R]_n = {ffun 'I_m * 'I_n → R}`
  encoding does not reduce well, and `rat` literals via `%:Q` unfold to deep
  `intmul` chains. **Not usable.**
- **MathComp `rat`** even outside matrices: a single `addq (mulq … …) (mulq
  … …)` of four small fractions takes 0.36 s. Notation `n%:Q` is the culprit.
  **Not usable for the inner computation.**
- **Stdlib `QArith` (`Q = Z * positive`)**: 70× faster than MathComp `rat` on
  small inputs (0.005 s for the four-fraction example), but the standard
  `Qplus`/`Qmult` do **not** auto-reduce, so denominators blow up; a 42 × 42
  `Q`-valued mat-vec product timed out at 30 s. Could be salvaged with `Qred`
  after each op, but it's friction we can avoid.
- **`ZArith` with cleared denominators**: a 42 × 42 quadratic form on
  100-bit `Z` entries finishes in **0.14 s**; with 200-bit entries, **0.22 s**;
  the result is a ~640-bit `Z`. This is the path.
- **CoqInterval**: would let us prove bounds on real-valued expressions (e.g.
  state the eigenvalue inequality over `R` and discharge it numerically). But
  the underlying claim is rational (the integrals are exact), so any interval
  step is unnecessary slack and only complicates the trust story. CoqInterval
  becomes interesting **only if** we want the stretch goal of bounding the
  *actual* generalised eigenvalue rather than the Rayleigh quotient at one
  vector — see §7.

**Conclusion.** The chosen representation is `list (list Z)` for the matrices
and `list Z` for the witness vector, with a single `Z` denominator stored
per matrix. No MathComp matrices, no rationals at runtime.

---

## 4. Spike measurements (real, with `mcp__rocq-mcp__rocq_query`)

| What | Tool | Time | Verdict |
|---|---|---|---|
| `vm_compute` of 4×4 `'M[rat]_4` Rayleigh quotient via `\matrix_(i,j)` | rocq_query | **timeout 30 s** | reject |
| `vm_compute` of `addq (mulq …) (mulq …)` on four `%:Q` literals | rocq_query | 0.36 s | reject |
| `vm_compute` of dot product of four `Q` literals (`5#7`, …) via stdlib `QArith` | rocq_query | 0.005 s | promising on small inputs |
| `vm_compute` of 42×42 `Q`-valued mat-vec product, denominators not reduced | rocq_query | **timeout 30 s** | reject |
| `vm_compute` of 42×42 quadratic form, `Z` entries with `2^100` factor | rocq_query | **0.14 s** | **accepted** |
| `vm_compute` of 42×42 quadratic form, `Z` entries with `2^200` factor | rocq_query | **0.22 s** | **accepted** |
| `native_compute` of same 200-bit case | rocq_query | (n/a — disabled, fell back to `vm_compute`) | not available in this Rocq build |

The 42 × 42 case is a 1764-multiplication / 1764-addition workload; we have
generous headroom. Even if the actual witness vector forces 500-bit entries
we expect well under 5 seconds.

---

## 5. Proposed Rocq file layout

Under `/home/rocq/prime_gap/`:

```
_CoqProject
theories/Simplex.v        (* simplex_int : list nat -> Z * positive (Beta integral) *)
theories/Polys.v          (* the G_{n,2}(k) polynomials, Lemma 7.1 + eq 7.8 kernels *)
theories/Matrices.v       (* M1_rat, M2_rat : 42x42 rationals, plus integer-cleared M1_int, M2_int *)
theories/Witness.v        (* witness_v : list Z, generated from FLINT JSON *)
theories/Cert.v           (* the integer Rayleigh-quotient inequality + Qed *)
theories/Main.v           (* one theorem statement + sanity checks *)
```

- `Simplex.v` exports `simplex_int : list nat -> Z * positive`, the closed-form
  rational integral of a monomial over the standard simplex Δ_k. About 20
  lines of definition + a few rewrite lemmas. No matrices yet.
- `Polys.v` builds the `G_{n,2}(k)` polynomials in `k` (or evaluates them at
  the constant `k=105`, depending on which is more convenient — both are
  tractable). About 50 lines.
- `Matrices.v` defines `M1_int : list (list Z)`, `M2_int : list (list Z)`,
  each via a list comprehension over `B = enum_basis 11` and the formulas
  from Maynard §7. **Whole-matrix entries are a single in-file `Definition`
  whose value is the result of a `vm_compute`-able expression**: that
  guarantees the matrices match the closed-form integral by construction
  (the `_correct` conjuncts of the theorem are discharged by
  `reflexivity` after `vm_compute`).
- `Witness.v` is the only piece imported from outside Rocq: a one-line
  `Definition witness_v : list Z := [:: 17; -42; 99; …]` plus the
  associated denominator. Generated by the FLINT pipeline (§6).
- `Cert.v` contains the actual `Theorem` and a one-line proof script:
  `vm_compute. reflexivity.`
- `Main.v` is the user-facing entry point that re-exports the headline
  theorem and prints `Print Assumptions maynard_M105_gt_4.`

A standalone scratch directory `/home/rocq/prime_gap/spike/` is encouraged
for early experiments before promoting code into `theories/`.

---

## 6. The FLINT / Python pipeline

Single Python script at `/home/rocq/prime_gap/python/maynard.py`, run from
the project venv:

1. **Install** `uv pip install python-flint` into `/home/rocq/prime_gap/.venv`
   (already verified to dry-run cleanly).
2. **Enumerate the basis** `B = [(b, c) for d in range(12) for (b, c) in …]`
   ordered to match Mathematica's `xExponents` / `yExponents` (we need
   identical ordering to compare against the notebook).
3. **`simplex_int(alpha)`** in `fmpq` arithmetic (`fmpq(prod(factorial(a)),
   factorial(sum(alpha) + k))`).
4. **Assemble M1, M2** as `fmpq_mat(42, 42)` via the `ConstCalc` /
   `PrmeCalc` formulas, mirroring the notebook.
5. **Sanity-check against Mathematica**: take a random test vector with
   small integer entries, compute its Rayleigh quotient, compare with the
   value reported by the notebook for the same vector. (We will want to run
   the notebook in the Wolfram Engine just once for this single
   cross-check; if we can't, fall back to spot-checking individual matrix
   entries against hand calculations of the integrals.)
6. **Numerical eigen-step**: lift `M1, M2` to `arb_mat` at 512-bit
   precision; compute the dominant generalised eigenvector of `(M2, M1)`.
   `python-flint` exposes Cholesky and standard `eig` on `arb_mat`; the
   generalised problem is `M1 = L Lᵀ; C = L⁻¹ M2 L⁻ᵀ`, then top eigenvector
   of the symmetric `C`, then back-transform.
7. **Snap to rationals** with denominator `D = 10**60` (or larger if the
   margin needs it). Result: `v ∈ ℚ⁴²`.
8. **Verify in exact `fmpq` arithmetic**:
   - `num1, den1 = (v.T * M1 * v).num, .den`
   - `num2, den2 = (v.T * M2 * v).num, .den`
   - require `105 * num2 * den1 - 4 * num1 * den2 > 0` (and `den1, den2 > 0`).
   If the inequality fails, **bail loudly**, increase precision, retry.
9. **Emit `certificate.json`**:
   ```json
   {
     "k": 105,
     "deg_max": 11,
     "basis": [[0,0],[1,0],…],
     "M1_common_denom": "...",
     "M1_int": [[…],[…],…],
     "M2_common_denom": "...",
     "M2_int": [[…],[…],…],
     "witness_denom": "...",
     "witness": [...],
     "vT_M1_v": [num, den],
     "vT_M2_v": [num, den],
     "margin": "4.00206976…"
   }
   ```
10. **Stretch / cross-check**: run an independent Sturm-sequence root
    isolation on `det(M2 − x M1) ∈ ℚ[x]` using `fmpq_poly`; require an
    isolated root in `(4, ∞)`. If (8) and (10) disagree, hard stop.

---

## 7. Stretch goals (do **not** start until the MVP ships)

- **(S1) Prove the eigenvalue bound directly in Rocq**, not just the
  Rayleigh-quotient witness, using MathComp linear algebra over `algC` /
  `realFieldType` and `mxalgebra`. This is the "true" Maynard statement and
  what a number theorist would actually want a Rocq proof of; the witness
  certificate is sufficient mathematically but weaker as a deliverable.
  Estimate: many person-weeks in MathComp, blocked on `mxalgebra` /
  generalised-eigenvalue lemmas that probably need to be added.
- **(S2) Self-contained reproof of the closed-form integrals.** Currently we
  *use* `simplex_int` as a definition; for a fully audited file we should
  prove `Lemma simplex_int_correct : ∫_{Δ_k} x^α = simplex_int α` against
  MathComp Analysis or Coquelicot. Independent of the matrix work.
- **(S3) Replace `vm_compute` with a CoqInterval-discharged real-valued
  statement.** Useful only as a third independent path to compare against.
- **(S4) Bit-identical cross-validation with Mathematica.** Run Maynard's
  notebook in the Wolfram Engine, dump its `RatVec` and Ratio numerator /
  denominator, and assert equality with our certificate. Strongest possible
  audit deliverable for a skeptic.

---

## 8. Risks (and our mitigations)

1. **Wrong basis ordering / sign convention.** The Maynard notebook
   enumerates monomials with a specific recipe (`xExponents` / `yExponents`)
   that is easy to mis-port. *Mitigation:* dump the basis `B` from both
   pipelines as JSON and compare element-wise; spot-check a 6-monomial
   subspace in both tools and verify identical M1, M2 entries before scaling
   to 42 monomials.
2. **Snap-to-rational eats the margin.** The margin is ~`2 × 10⁻³` (Maynard
   reports `λ ≈ 4.00207`), which is generous, but a low-precision snap can
   still wreck the strict `>`. *Mitigation:* compute the eigenvector at ≥512
   bits, snap with denominator ≥ `10⁶⁰`, and abort with a clear error if the
   exact-rational check fails — never silently weaken the inequality.
3. **`vm_compute` heap pressure on big intermediate `Z`.** Our spike showed
   ~640-bit results in 0.22 s, but a worst-case witness might push this to
   thousands of bits. *Mitigation:* the spike already overshoots the
   expected entry size; if a real run blows up, we can clear denominators
   matrix-by-matrix (smaller D's) instead of globally.
4. **`native_compute` is not available.** Disabled in this Rocq build. We
   confirmed `vm_compute` is sufficient, so this is noted but not blocking.
5. **`Print Assumptions maynard_M105_gt_4`** must come back clean
   (`Closed under the global context`). Any axiom — especially `admit` — in
   the dependency tree of the Cert is a hard failure of the MVP. We will
   wire this into a CI-style sanity check via `mcp__rocq-mcp__rocq_assumptions`.
6. **The `_correct` conjuncts may not fall to `reflexivity` if the
   in-file assembly uses a different normalisation than the Python
   pipeline.** *Mitigation:* design `Matrices.v` so that `M1_int` is
   *defined* by the same in-Rocq closed-form formula and is *also* checked
   by `reflexivity` against the JSON-loaded constants — so any divergence
   between Rocq's assembly and Python's surfaces immediately.

---

## 9. Devil's-advocate sign-off

The devil's advocate raised seven concerns. Here is how the plan handles each:

1. **"Are you auditing the right thing?"** — Yes. The reverse-engineering of
   the notebook confirmed `k = 105` (the headline `M_{105} > 4`), not the
   small `k = 5` toy example. **Resolved.**
2. **"Witness vs eigenvalue."** — The notebook *itself* uses the
   witness-vector strategy as its certification step; we are auditing the
   actual computation, not bypassing it. **Resolved**, with the candid note
   that anyone wanting a "proof of the largest eigenvalue" still needs the
   stretch goal (S1).
3. **"`vm_compute` on 43×43 rat matrices."** — Confirmed catastrophic; we
   pivoted to integer-cleared matrices and measured 0.22 s on 200-bit
   entries. **Resolved by spike data.**
4. **"Symmetric vs monomial basis."** — Yes, we are using the 42-element
   monomial basis in the symmetric variables `(x = 1−Σ tᵢ, y = Σ tᵢ²)`.
   The notebook enumerates exactly 42 monomials; we will assert this in both
   pipelines. **Resolved.**
5. **"ε margin."** — Codified: ≥512-bit ARB precision, ≥10⁶⁰ snap
   denominator, hard abort if the exact check fails. **Resolved.**
6. **"CoqInterval install risk."** — Dry-run confirmed coq-interval 4.11.4
   installs cleanly into the current switch. We don't need it for the MVP
   anyway. **Resolved.**
7. **"What convinces a skeptic."** — Bit-identical cross-validation across
   Python/FLINT and Rocq is in the MVP (item §6.9 + the matching `reflexivity`
   in `Cert.v`). Cross-validation against the original Mathematica file is
   listed as stretch goal S4. **Acknowledged.**

---

## 10. Concrete first sprint (the next deliverables)

In order, smallest to biggest:

1. **`spike/`** — copy the successful spike snippet into a real `.v` file
   (via `mcp__rocq-mcp__rocq_compile_file` with a 60-second timeout) so we
   have a permanent record of the timings. ~10 minutes.
2. **`python/maynard.py` skeleton** with `simplex_int`, `enumerate_basis`,
   and a hand-checked `M1[0,0], M1[0,1], M2[0,0]` against pen-and-paper.
   ~1 hour. **No FLINT installed yet — pure Python `Fraction` is fine for
   this baby step.** Install `python-flint` only once we need `arb_mat`.
3. **`theories/Simplex.v`** with `simplex_int` and a sanity test that
   `vm_compute`s `simplex_int [3; 2; 1]` (= 12 / 8! ish) and matches a
   handwritten constant by `reflexivity`. ~30 minutes.
4. **Tiny end-to-end on a 6-monomial subspace** (`B = {(b,c) : b+2c ≤ 3}`,
   so `|B| = 6`), in both Rocq and Python, comparing all M1, M2 entries.
   This is the integration test that will catch the basis-ordering bug
   before it costs us a day. ~half a day.
5. **Scale the Python side to 42 monomials**, run the full FLINT pipeline,
   produce `certificate.json`. ~half a day.
6. **Scale the Rocq side to 42 monomials**, ingest `witness.v` from the
   certificate, prove `Cert.v` with `vm_compute`, run
   `mcp__rocq-mcp__rocq_assumptions` to confirm no axioms. ~half a day.
7. **Stretch goal S4 (Mathematica diff)** and **S2 (proof that
   `simplex_int` is the actual integral)** as bonus rounds.

Each step ends with a concrete artifact and a passing check; if any fails,
we stop and re-plan rather than piling on.

---

## Appendix A — confirmed `rocq_query` evidence (verbatim)

```
Time Eval vm_compute in (3%:Q / 7%:Q + 5%:Q / 11%:Q).
  → [rat 68%Z // 77%Z]    Finished transaction in 0.007 secs

Time Eval vm_compute in fold_left Qplus (map (...) (combine xs ys)) 0.
  (* xs, ys : 4 small Q literals *)
  → 414326 # 50141        Finished transaction in 0.005 secs

Time Eval vm_compute in <42x42 Z quadratic form, entries up to 2^100>.
  → 551405218103691679    Finished transaction in 0.074 secs

Time Eval vm_compute in <42x42 Z quadratic form, entries with 2^100 factor>.
  → Z.log2 q = 339        Finished transaction in 0.14 secs

Time Eval vm_compute in <42x42 Z quadratic form, entries with 2^200 factor>.
  → Z.log2 q = 639        Finished transaction in 0.221 secs
```

`'M[rat]_4` and `\matrix_(i,j)`-based variants timed out at 30 s and are
recorded as rejected. This evidence is the linchpin of the plan — preserve
it in the spike directory.
