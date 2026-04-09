# Plan S1 — a Rocq theorem of `M_{105} > 4` that mentions an *eigenvalue*

**Target.** A Rocq theorem whose statement genuinely says "the matrix has a
real eigenvalue greater than `4/105`", not just "this Rayleigh quotient is
> 4". Setting: 42 × 42 rational symmetric matrices `M1, M2` from
Maynard's *Small gaps between primes* (arXiv:1311.4600) Proposition 4.3 /
formula 8.15. `M1` SPD; we want `M_{105} = 105 · λ_max((M2, M1)) > 4`.

This document supersedes §S1 of `PLAN.md` (the earlier MVP plan), which
is now reclassified as the *witness* MVP and should still be built first.

---

## 0. Inputs and constraints (verified, not assumed)

### Available libraries (already installed)

| Tool | Version | Used as |
|---|---|---|
| Rocq prover | 9.0.1 | host |
| MathComp ssreflect / algebra / field | 2.5.0 | spec types: `'M[rat]_n`, `char_poly`, `eigenvalue` |
| MathComp **real-closed** | **2.0.3** | spec types: `realalg`, `polyrcf`, `qe_rcf_th` (`mods`, `cindex`, `taq_taq_itv`) |
| MathComp Analysis | 1.15.0 | not on the critical path |
| Coquelicot | 3.4.4 | not used |
| Stdlib `ZArith`, `List` | 9.0 | **all heavy computation lives here** |
| python-flint | 0.8.0 | external oracle that ships the polynomial + Sturm chain |
| FLINT | 3.x | bundled with python-flint |

### Hard performance constraints, all freshly measured with `mcp__rocq-mcp__rocq_query`

These are the linchpins of the architecture. They are not speculation.

| Probe | Result |
|---|---|
| `vm_compute` of size of `\matrix_(i,j) … : 'M[rat]_4`, Rayleigh quotient | **timeout 30 s** |
| `vm_compute` of size of `Poly [::-5; 0; 1] : {poly int}` | **timeout 30 s** |
| `vm_compute` of size of `'X^2 - (5%:Q)%:P : {poly rat}` | **timeout 30 s** |
| `vm_compute` of `mods (p : {poly realalg}) p^`()` for degree-2 `p` | **timeout 30 s** |
| `vm_compute` of `addq (mulq …) …` on four `%:Q` literals | 0.36 s |
| `vm_compute` of stdlib `QArith` 4-term dot product | 0.005 s |
| `vm_compute` of 42 × 42 quadratic form on `list Z` with 200-bit entries | **0.22 s** |
| `vm_compute` of `length`, `last` on `list Z` of length 3 | **0.000 s** |
| `native_compute` | **disabled** at configure time in this Rocq build |

**Conclusion drawn from the table above.** Every MathComp container type
(`'M[R]_n`, `{poly R}` for any `R`, `realalg`) is **dead** for `vm_compute`.
The only representations that compute at usable speed are
- `Z` integers (Stdlib),
- `list Z` (polynomials, treated as coefficient lists),
- `list (list Z)` (matrices).

Therefore the MathComp side is for **specifications only**, never for
running. Anything we want to *compute* in Rocq must live on `list Z`. The
two worlds are connected by hand-written homomorphism lemmas, proved once
and for all without any `vm_compute` on the abstract side.

This single observation is what shapes the rest of the plan.

---

## 1. The theorem to aim at

Picked by the mathematician (`/home/rocq/prime_gap/math_eigenvalue_target.md`):

```rocq
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.real_closed Require Import realalg.
Import GRing.Theory Num.Theory.
Open Scope ring_scope.

Section MaynardS1.

Variable M1_rat M2_rat : 'M[rat]_42.
Hypothesis M1_unit : M1_rat \in unitmx.

Definition A_rat : 'M[rat]_42 := invmx M1_rat *m M2_rat.

Theorem maynard_eigenvalue_S1 :
  exists lambda : realalg,
    eigenvalue (map_mx (ratr : rat -> realalg) A_rat) lambda
 /\ (ratr (4%:Q / 105%:Q) : realalg) < lambda.

End MaynardS1.
```

Why form (III) (standard char poly of `A = M₁⁻¹ M₂`) over forms (I) "M₂ v = λ M₁ v"
or (II) "root of `det(M₂ − x M₁)`":

- `eigenvalue : forall (F : fieldType) (n : nat), 'M_n → pred F` is a
  MathComp predicate already, with `eigenvalueP` and `eigenvalue_root_char`
  reducing it to `root (char_poly A)` for free.
- `map_char_poly` already commutes `ratr : rat → realalg` with `char_poly`,
  so we can do all rational/integer work in ℚ and lift to `realalg` only
  at the very end.
- (II) would force a polynomial-matrix determinant; (I) would force us
  into a generalised-eigenvalue infrastructure that MathComp does not ship.
- Note **`4 / 105`, not `4`**. Maynard's `M_k = k · λ_max`; the
  eigenvalue threshold is `4/k = 4/105`. The headline `M_{105} > 4`
  follows from L4 below by multiplication.

The four bridge lemmas connecting this `Theorem` to a `vm_compute` are
listed in §3.

---

## 2. The FLINT-side oracle (already verified end-to-end)

Full report: `/home/rocq/prime_gap/flint_sturm_plan.md`. Headline numbers,
all measured on `python-flint 0.8.0`:

| step | wall time | size |
|---|---|---|
| Build `M1, M2` (rational, exact) | 90 s (one-off) | 320 kB pickle |
| `A = M1⁻¹ M2` | 0.05 s | — |
| `q(x) = det(xI − A)` via `fmpq_mat.charpoly()` | **0.19 s** | coefs ≤ 1354 bits |
| `gcd(q, q')` | < 10 ms | degree 0 (simple spectrum confirmed) |
| Brown–Traub subresultant PRS, 43 polys | **2.1 s** | terminal coef ≈ 100 kbits |
| `V(4/105) − V(+∞)` sign-variation count | < 1 ms | **= 1** ✓ |
| Arb 256-bit cross-check | < 0.1 s | `k · top = 4.00206976193804713…` ✓ |

So FLINT is happy to ship us:

1. The integer-cleared char poly `p_int : list Z` (43 ints, ≤ 1354 bits each).
2. The 43-step subresultant PRS chain `chain_int : list (list Z)` (~100 kbit terminal coef, total ~16 MB raw / ~35 MB JSON).
3. The PRS audit trail `audit : list (Z * Z)`: per step, the multiplier `β_i` and the leading-coefficient power `lc(f_i)^δ`.
4. The integer-cleared matrices `M1_int, M2_int : list (list Z)` and a denominator `D : Z`.
5. The sign vectors `signs_at_θ`, `signs_at_∞` (each a `list Z` of values in `{-1, 0, +1}`) and the integers `V_θ, V_∞, V_θ - V_∞ ≥ 1`.

The Rocq side will re-derive everything from `M1_int, M2_int, D` — FLINT
is an *untrusted* oracle that only suggests the witness data; every
piece is verified inside `vm_compute`. See §4.

**Naive Sturm chain is fatal**: terminal coefficient ≈ 1.65 Mbits. Always
ship the Brown–Traub subresultant chain.

---

## 3. The four bridge lemmas

Let
- `M1_rat, M2_rat : 'M[rat]_42` be the in-Rocq specification matrices,
- `M1_int, M2_int : list (list Z)` and `D : Z` be the integer-cleared
  shadow of M1, M2 (so `M1_rat[i,j] = M1_int[i][j] / D` etc.),
- `p_int : list Z` be the FLINT-shipped char poly of `A = M1⁻¹ M2`,
- `chain_int : list (list Z)` be the FLINT-shipped Brown–Traub PRS chain,
- `q_RA : {poly realalg}` be `map_poly (ratr : rat → realalg) (char_poly A_rat)`,
- `θ : realalg := ratr (4%:Q / 105%:Q)`.

### L1 — Sturm count = real-root count

> `n_sturm = #{ r : realalg | root q_RA r ∧ θ < r }`

The right-hand side uses `polyrcf.roots q_RA θ B` for some upper bound
`B` greater than `cauchy_bound q_RA`. From `taq_taq_itv` (with `q := 1`)
plus `changes_itv_mods_cindex`, the number of real roots of `q_RA` in
`(θ, B)` equals `changes_itv_poly θ B (mods q_RA q_RA^`())`. Combined
with the homomorphism lemma L1' below, this equals our integer
computation.

**L1' (homomorphism — hand-written, no `vm_compute` on the abstract side).**

```rocq
Lemma sturm_int_morph (p : list Z) :
  let p_RA := map_poly (intr : int → realalg) (poly_of_int_list p) in
  ∀ θ B : Z * positive (* rationals as Z/positive *),
    sign_variations_at_int (mods_int p (deriv_int p)) θ
  − sign_variations_at_int (mods_int p (deriv_int p)) B
  = changes_itv_poly (rat_of θ : realalg) (rat_of B : realalg)
                     (mods p_RA p_RA^`()).
```

Proved by induction on the chain. Uses only ring-homomorphism lemmas of
`intr : int → realalg`. Reduces `mods_int` (our list-of-list-of-Z PRS)
to abstract `mods` over `realalg`. **No `vm_compute` is invoked in the
proof of L1'.**

**Effort.** Medium. The most subtle piece is that `qe_rcf_th.mods` uses
`next_mod p q := - lc(q)^{rscalp p q} *: rmodp p q` (a *rational* PRS
with rscalp accounting), whereas Brown–Traub keeps things in ℤ[x] via
the `β_i` divisor sequence. The two chains differ by polynomial scalars.
A separate lemma `mods_brown_traub_eq` shows that they have the same
sign variations at every rational point — this is exactly what we need
because variations are sign-only.

### L2 — shipped polynomial equals `char_poly A_rat`

> `Poly (map intr p_int) = D ^+ 42 *: char_poly A_rat`

(or whatever exact denominator-clearing scaling is correct; use the
FLINT pipeline to set the convention and stick to it.)

**This is the load-bearing bridge.** It's the *only* place we have to
believe that the integer polynomial we're verifying really is the right
char poly. Two routes considered:

- **(A) Faddeev–Leverrier shadow**. Define `char_poly_int : list (list Z) → Z → list Z`
  ourselves (40 lines), prove `char_poly_int_correct` once-and-for-all
  abstractly via Faddeev–Leverrier identities — *no `vm_compute` on the
  abstract side*. Per instance, `Lemma p_int_eq : p_int = char_poly_int M_int D.`
  is then a single `vm_compute; reflexivity` on `list Z` (≈ 1 second).
- **(B) Bypass `char_poly`**. Work directly with the polynomial-pencil
  Cauchy index, never form `char_poly` symbolically.

**We pick (A).** It cleanly hits `char_poly A_rat`, which makes L3
trivial via `eigenvalue_root_char`. (B) would require inventing a
custom `cindex`-pencil lemma with no MathComp counterpart and would also
force re-deriving L3 by hand.

**Effort.** Medium–hard. Faddeev–Leverrier on `list (list Z)` is a 40–60
line reflective implementation; the abstract correctness lemma is a
40-line induction; the per-instance equality is `vm_compute; reflexivity`
in seconds. The hardest part is the bookkeeping of denominator powers.

### L3 — root of char poly ↔ eigenvalue

> `eigenvalue (map_mx ratr A_rat) λ ↔ root q_RA λ`

Direct combination of two MathComp lemmas:

- `eigenvalue_root_char : eigenvalue A a = root (char_poly A) a`
- `map_char_poly : map_poly f (char_poly A) = char_poly (map_mx f A)`

**Effort.** Trivial. One-line proof.

### L4 — Maynard bridge

> `(∃ λ, eigenvalue A λ ∧ θ < λ) → M_{105} > 4`

By definition `M_k := k · λ_max((M2, M1))` and for SPD `M1` this equals
`k · λ_max(A)` where `A = M1⁻¹ M2`. We **do not need "largest"** — *some*
eigenvalue with `λ > θ = 4/105` suffices, because by the definition of
sup `λ_max ≥ λ > 4/105 ⟹ λ_max > 4/105 ⟹ k · λ_max > 4`.

**Effort.** Easy *if* we are willing to *define* `M_k` in Rocq as
`k * λ_max((M2, M1))`. If we instead insist on the function-space
definition `M_k = sup_F k J_k(F) / I_k(F)`, we additionally need
Rayleigh-Ritz; that lemma is the *same* one the witness MVP carries, so
it is "free" once both branches exist.

---

## 4. Architecture in files

Under `/home/rocq/prime_gap/theories/S1/`:

```
_CoqProject
S1/IntPoly.v        — list Z polynomial library: padd, psub, pmul, pneg,
                       eval (Horner at Q), deriv, prem (pseudo-rem), pgcd
S1/IntMat.v         — list (list Z) matrix library: madd, msub, mmul, mneg,
                       transpose, det (cofactor or Bareiss), faddeev_leverrier
S1/BrownTraub.v     — Brown-Traub subresultant PRS over list Z
S1/SignChain.v      — sign_at_int, variations_int, V_minus_V_int
S1/CharPoly.v       — char_poly_int : list (list Z) -> Z -> list Z
                       Lemma char_poly_int_correct (the abstract bridge)
S1/Bridge.v         — the four lemmas L1' L2 L3 L4 above, plus glue
                       to qe_rcf_th and char_poly
S1/Witness.v        — generated from FLINT JSON: p_int, chain_int, audit,
                       M1_int, M2_int, D, signs_at_theta, signs_at_inf
S1/Cert.v           — Lemma sturm_count_ge_1 : V_θ - V_∞ >= 1.
                       Proof. vm_compute. exact (refl_equal _). Qed.
S1/Main.v           — Theorem maynard_eigenvalue_S1 (the §1 statement)
                       Proof. (* combine L1..L4 + Cert *) Qed.
S1/Smoke.v          — sanity tests on a 4x4 toy pencil end-to-end
```

**`Witness.v` is generated** from `certificate.json` by a small Python
script `tools/json_to_v.py`. Never hand-edit. The `.v` should declare
each constant on a single line so that diffs are reviewable:

```rocq
(* AUTOGENERATED — do not edit *)
Definition D : Z := 73...0.    (* common denominator *)
Definition M1_int : list (list Z) := [...].
Definition M2_int : list (list Z) := [...].
Definition p_int : list Z := [...].
Definition chain_int : list (list Z) := [...].
Definition audit : list (Z * Z) := [...].
Definition signs_at_theta : list Z := [...].
Definition signs_at_inf   : list Z := [...].
```

The PRS chain is the largest object (~16 MB raw integers / ~35 MB JSON).
If `coqc` elaboration of literals that large becomes painful, we split
`Witness.v` into one `.v` per chain entry and `Load` them.

---

## 5. Spike measurements that bound the rest of the plan

These are exact numbers from `mcp__rocq-mcp__rocq_query`. They define the
budget the file structure has to fit inside.

| Operation | Workload | `vm_compute` time | Verdict |
|---|---|---|---|
| 42 × 42 quadratic form, 100-bit `Z` entries | 1764 muls + 1764 adds | **0.14 s** | ✅ |
| 42 × 42 quadratic form, 200-bit `Z` entries | same | **0.22 s** | ✅ |
| 4 × 4 Rayleigh quotient via `'M[rat]_4` | tiny | **timeout 30 s** | ❌ |
| `size (Poly [::-5; 0; 1] : {poly int})` | trivial | **timeout 30 s** | ❌ |
| `size (mods (p : {poly realalg}) p^`())` for `p = X² − 5` | trivial | **timeout 30 s** | ❌ |
| `length`, `last` on `list Z` of small length | trivial | **0 s** | ✅ |

Our actual workloads:

- **Cert.v `vm_compute` of `V_θ - V_∞`**: ≤ 43 polynomials of degree ≤ 42 with
  coefs ≤ 100 kbits = ~13 KB each. Per-polynomial sign at a rational: 42 ×
  multiply-add + sign-test. Total: ≤ 43 × 42 × (100 kbit × 100 kbit
  multiplication). Stdlib BigZ does Karatsuba above ~8 kbit; 100 kbit ≈
  1600 limbs is ~20–40× slower per op than the 200-bit case. Estimate:
  **a few seconds, conservatively a few minutes**. Mitigation: spike one
  step before committing.
- **PRS audit (per step verification)**: 42 steps, each one polynomial
  multiplication + subtraction in `list Z`, coefficients growing from
  1354 bits at step 1 to 100 kbits at step 42. Estimate: **tens of
  seconds total**. Mitigation: cache results in `.vo` per step so that
  re-running `coqc` doesn't redo it.
- **`char_poly_int` of a 42 × 42 integer matrix via Faddeev-Leverrier**:
  42 iterations, each needing a 42 × 42 matrix multiplication on `Z`
  entries growing from 200 bits to ~10000 bits (matrix powers grow
  polynomially). Estimate: **seconds to a minute**. This is the L2
  per-instance check.

So the **whole pipeline runs in `vm_compute` in well under 5 minutes**,
end-to-end, on a single `coqc` invocation. If anything blows past that
on the actual data, split into multiple `.v` files and let `make` cache.

---

## 6. Risks (specific to S1, distinct from the MVP risks)

1. **L2 (Faddeev–Leverrier correctness) is the load-bearing piece.**
   If we cannot prove `char_poly_int_correct` against MathComp's
   `char_poly` without invoking `vm_compute` on the MathComp side, the
   plan collapses. Mitigation: **first deliverable** on the Rocq side
   is the abstract Faddeev–Leverrier correctness lemma at *symbolic*
   dimension (not 42 specifically, but `forall n`). If that proof
   doesn't close in two days of work, drop S1 architecture (A) and
   reach for (B).
2. **`changes_itv_mods_cindex` side conditions**. The lemma in
   `qe_rcf_th` requires that `p` and the chain entries are nonzero at
   `a` and `b` (or has a sign-handling clause). `4/105` is very unlikely
   to be a root of `q` or any chain entry, but the Rocq proof needs an
   integer check `vm_compute (sign_at q (4/105) ≠ 0)` per chain entry.
   For `+∞` we use `sgp_pinfty` which only inspects leading coefficients
   — trivial. Plan: bake the per-entry "nonzero at θ" check into Cert.v
   alongside the variation count.
3. **Brown–Traub PRS vs `qe_rcf_th.mods` are not the same chain.** They
   differ by rational scalar factors. They have the same sign-variation
   count at every rational point, but the equality `mods_brown_traub p q
   = mods p q` is *not* literal. We need a separate lemma
   `Lemma BT_mods_var_eq : variations_at_int BT p q a = changes_horner (mods p q) (intr a).`
   This is provable by induction on the chain; budget half a day.
4. **`coqc` choking on multi-MB literals**. The 16 MB integer chain may
   make `coqc` parse phase slow. Mitigation: `Load` indirection, one
   `.v` per chain entry. The `vm_compute` itself is fine on big literals
   once parsed.
5. **`realalg` is constructively defined and we are *only* using its
   abstract properties**. We never compute on `realalg` elements; we
   never witness an explicit `realalg` value. The existential in
   `maynard_eigenvalue_S1` is discharged via `polyrcf.roots`, which is
   defined classically via `projT1` of an existence proof — exactly what
   we want. Confirm the resulting proof has no axioms via
   `Print Assumptions maynard_eigenvalue_S1`. Some MathComp Analysis /
   real-closed lemmas use `Reals` axioms (`functional_extensionality`,
   `proof_irrelevance`); these are already part of the MathComp Analysis
   trust base and acceptable. Anything beyond that is a hard fail.
6. **`vm_compute` of `char_poly_int` on a 42 × 42 matrix may exceed
   memory**. Faddeev–Leverrier intermediate matrices have entries that
   are polynomials in trace-of-powers, can grow to 10000+ bits. Spike
   on a 10 × 10 first.
7. **Matrix inversion `invmx`** in `eigenvalue_root_char A_rat` requires
   `M1_rat \in unitmx`. This is a `Hypothesis` in our `Section`, so
   `Main.v` will need to discharge it from the concrete `M1_rat`. Since
   M1 is SPD, `det M1 ≠ 0`. To close the theorem at M1 = the actual
   Maynard matrix we need to either (a) ship `det M1` from FLINT and
   verify nonzero in `vm_compute`, or (b) add the `M1_unit` hypothesis
   to the headline theorem and handle it in a satellite lemma.

---

## 7. Concrete first sprint (weeks, not hours)

Roughly in dependency order. Each item ends in a tangible artifact that
the next item can consume.

1. **`S1/IntPoly.v`**: `list Z`-based polynomial library with `padd`,
   `psub`, `pmul`, `pneg`, `peval` (Horner at `Z` and at `Z × positive`),
   `pderiv`, `pscalar_mul`, `psign_at_rat`, plus a few small reflexivity
   tests via `vm_compute`. ~150 lines. **Goal**: every primitive
   computes in `vm_compute` in < 10 ms on degree-42 / 200-bit inputs.
2. **`S1/IntMat.v`**: `list (list Z)` matrix library with `madd`,
   `msub`, `mmul`, `mneg`, `mtranspose`, `meval_quad_form`. ~150 lines.
   **Goal**: 42 × 42 mat-mul of 200-bit-entry matrices in < 1 s
   (extrapolation from the existing spike).
3. **`S1/BrownTraub.v`**: pseudo-remainder, `prs_step`, `brown_traub_chain`.
   ~80 lines. **Goal**: derives one PRS step from the previous one in
   `list Z` form, all `vm_compute`-able.
4. **`S1/SignChain.v`**: `sign_at_int`, `variations`, `V`. ~50 lines.
5. **`S1/CharPoly.v`** — define `char_poly_int` via Faddeev–Leverrier
   *and prove it correct against MathComp's `char_poly`*. **The make-or-break
   abstract proof of S1.** ~200 lines. **Budget two days; if it doesn't
   close, retreat to (B) bypass-charpoly.**
6. **Generate `S1/Witness.v` from FLINT**. Wire up
   `tools/json_to_v.py`. End-to-end on a 4 × 4 toy pencil first
   (not 42 × 42), to debug the format and the JSON encoding.
7. **`S1/Cert.v` on the 4 × 4 toy.** End-to-end Rocq proof of
   `∃ λ, eigenvalue A_toy λ ∧ θ < λ`. Should compile in well under a
   minute. Run `Print Assumptions` and confirm closed (modulo MathComp
   Analysis's standard real-axiom set).
8. **Scale `Cert.v` to the actual 42 × 42 Maynard data**. Spike the
   most expensive `vm_compute`s independently first; if any single one
   exceeds 10 minutes, split.
9. **`S1/Bridge.v`**: prove L1, L1', L3, L4 (in that order). L2 is
   already done in step 5. ~150 lines.
10. **`S1/Main.v`**: assemble `maynard_eigenvalue_S1`. Should be ~15
    lines including an `auto`/`reflexivity` finisher.

The MVP witness plan (`PLAN.md`) and the S1 plan **share the same
`S1/IntPoly.v` and `S1/IntMat.v` infrastructure**. Build the MVP first;
S1 reuses every line of the integer-arithmetic core.

---

## 8. Stretch beyond S1

- **S1' — an explicit witness eigenvector in `realalg`**: not just `∃ λ`,
  but `∃ λ ∃ v, M2 v = λ M1 v ∧ v ≠ 0`. Requires building a
  representable element of `realalg^42`, which is heavy.
- **S1'' — Rayleigh-Ritz lemma in MathComp**: `λ_max(M2, M1) =
  max_{v≠0} R(v)`. Connects S1 to the witness MVP by a bidirectional
  bridge instead of two parallel proofs.
- **S1''' — Cholesky factorisation for SPD rational matrices**: derive
  the full real spectral theorem from MathComp Analysis machinery.
  Useful if anyone wants the *actual* spectral theorem in MathComp,
  rather than just for S1.
- **Cross-validation**: emit a single `certificate.json` that BOTH
  pipelines (the MVP witness branch AND the S1 Sturm branch) consume.
  `Cert.v` of the MVP and `Cert.v` of S1 should both `vm_compute` to
  the same conclusion on the same data. Bit-identical agreement.

---

## 9. Devil's-advocate sign-off (S1-specific)

The MVP devil's advocate has been heard (`PLAN.md` §9). New objections
specific to S1:

1. **"You're betting everything on Faddeev–Leverrier closing abstractly."**
   Acknowledged. The two-day budget on step 5 is the explicit
   exit ramp. If it doesn't close, the witness MVP is still standing —
   S1 only adds value.
2. **"Even if everything works, the `Print Assumptions` will list
   `Reals.functional_extensionality` and friends."** Yes; this is the
   MathComp Analysis trust base, which is an order of magnitude better
   than what Mathematica gives. Document it explicitly.
3. **"You're not actually computing the eigenvalue."** Correct. The
   theorem says *some real eigenvalue is > 4/105*. It does not produce
   a `realalg` value. For Maynard's purpose this is enough — the
   inequality `M_{105} > 4` is the only thing the rest of the paper
   uses. If a follow-up paper needs the *value*, that's the S1' stretch.
4. **"You haven't proved that M1 is SPD inside Rocq."** Hypothesis on
   the section. To close at the headline level, we'll either (a) verify
   `det M1_int > 0` via `vm_compute` plus a separate "minors" certificate
   (since SPD ⟺ all leading principal minors > 0), or (b) settle for
   `M1 \in unitmx` (which is enough for `invmx` to make sense). Plan
   on (b) for the MVP and (a) as a small extra deliverable.
5. **"Brown–Traub vs `qe_rcf_th.mods` mismatch will eat a week."** Risk
   #3 above. The two chains differ only by rational scalars; the
   per-step bridge lemma is mechanical. Budget two days; longer means
   we should have used (B).

---

## 10. What this plan does NOT promise

- **It does not compute the eigenvalue.** It only proves existence. The
  numerical value `4.00206976193804713686805879340335542151` lives in
  the FLINT cross-check, not in the Rocq theorem.
- **It does not avoid all axioms.** MathComp Analysis / real-closed
  pull in `Reals.functional_extensionality` and a couple of related
  classical axioms. These are *standard* and acceptable, but if you
  want a truly axiom-free proof, this plan is not it.
- **It does not formalise the connection from the matrices `M1, M2` to
  Maynard's actual quadratic forms `I_k, J_k`** beyond what `PLAN.md` §1
  already proposes (the `simplex_int_correct` stretch goal). That
  bridge is *separate* from S1 and *also separate* from the witness
  MVP; it is a paper-level proof that has to be done once and is reused
  by both.
- **It does not promise that `coqc` will be fast on the chain `.v`
  files.** Parsing a 16 MB integer literal is not what `coqc` was
  designed for. We may have to generate one `.v` per chain step.

---

## Appendix A — verbatim `mcp__rocq-mcp__rocq_query` evidence (S1-specific)

```text
Check (forall n, 'M[rat]_n).
  → forall n : nat, 'M_n : Type                              ✅ types ok

Check (fun n M v => (v^T *m M *m v) 0 0 : rat).
  → ok                                                       ✅ types ok

Time Eval vm_compute in <4×4 'M[rat] Rayleigh quotient>.
  → timeout 30 s                                             ❌ 'M[rat] dead

Time Eval vm_compute in (3%:Q / 7%:Q + 5%:Q / 11%:Q).
  → [rat 68%Z // 77%Z]      Finished in 0.007 secs           OK at small scale

Time Eval vm_compute in addq (mulq (5%:Q/7%:Q) (3%:Q/11%:Q))
                              (mulq (2%:Q/13%:Q) (4%:Q/17%:Q)).
  → [rat 3931%Z // 17017%Z]  Finished in 0.358 secs          rat literals SLOW

Time Eval vm_compute in <42×42 list Z quad form, 100-bit entries>.
  → 339-bit Z              Finished in 0.14 secs             ✅ accepted

Time Eval vm_compute in <42×42 list Z quad form, 200-bit entries>.
  → 639-bit Z              Finished in 0.221 secs            ✅ accepted

About mods.
  → mods : forall [R : rcfType], {poly R} -> {poly R} -> seq {poly R}
  → mods is transparent                                      ✅ exists in qe_rcf_th

Time Eval vm_compute in size (mods (p : {poly realalg}) (deriv p))
  for p = X^2 - 5%:R%:P.
  → timeout 30 s                                             ❌ realalg dead

Time Eval vm_compute in size (Poly [::-5; 0; 1] : {poly int}).
  → timeout 30 s                                             ❌ {poly int} dead

Definition pol := list Z. Definition lc p := List.last p 0%Z.
Definition deg p := pred (length p).
Time Eval vm_compute in deg ((-5)%Z :: 0%Z :: 1%Z :: nil).
  → 2                       Finished in 0 secs               ✅ list Z FAST
```

These eight observations are the *entire* basis for the architecture
above. Preserve them in the `S1/Smoke.v` directory and re-run them on
every Rocq upgrade.

## Appendix B — how to generate the certificate

```bash
cd /home/rocq/prime_gap
source .venv/bin/activate
uv pip install python-flint            # one-time
python python/maynard.py                # ~2 minutes; emits certificate.json
python tools/json_to_v.py certificate.json > theories/S1/Witness.v
make -j -C theories                     # compiles everything
```

The whole pipeline is one command after the bootstrap.
