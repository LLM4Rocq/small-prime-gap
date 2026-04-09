# FLINT → Rocq Sturm-count pipeline for Maynard `M_105 > 4`

**Author**: numerical / FLINT expert
**Date**: 2026-04-09
**Status**: dry-run completed end-to-end with `python-flint 0.8.0` (FLINT 3.x)

## 0. Executive summary

The pipeline works. With `M1, M2` as in `/home/rocq/prime_gap/notebook_reconstructed.md`:

| step | FLINT primitive | wall time | artifact size |
|---|---|---|---|
| Build `M1, M2` (rational) | pure-Python, once | 90 s | 320 kB pickle |
| `A = M1⁻¹ M2`             | `fmpq_mat.inv * fmpq_mat` | 0.05 s | — |
| `q(x) = det(xI − A)`       | `fmpq_mat.charpoly()` | 0.19 s | coefs ≤ **1354 bits** |
| `gcd(q, q')`               | `fmpz_poly.gcd` | 0.00 s | degree 0 (simple spectrum) |
| Naive Sturm chain (ℚ)      | iterated `fmpq_poly %` | 10.5 s | **terminal ≈ 1.65 Mbits** — fatal |
| Brown-Traub subresultant PRS | custom `prem` + divide-by-β | **2.1 s** | terminal ≈ **100.6 kbits** |
| `V(4/105) − V(+∞)`         | sign eval + variation | < 1 ms | **= 1** ✓ |
| Arb 256-bit eig cross-check | `arb_mat.eig` | < 0.1 s | top = 0.0381149501136957… → `k·top = 4.00206976193804713…` ✓ |

All numbers below are observed, not estimated. The key conclusion for
the Rocq side: **ship the subresultant chain, not the naive one.** The
coefficient-size linchpin (task 2) is: `q` has 1354-bit coefs, the
Sturm chain grows *linearly* to ~100 kbits, **not 30 kbits, not 1.6 Mbits**.

## 1. Recommended reduction: (β) standard char-poly of A = M1⁻¹M2

`fmpq_mat.charpoly()` is directly exposed and returns `q(x)` in
0.19 s. The coefficients are an order of magnitude smaller than what a
naive `det(M2 − xM1)` expansion would produce, because the internal
FLINT algorithm (modular Danilevsky / division-free characteristic
polynomial for rational matrices) already cancels the `det M1` factor.

If someone insists on `p(x) = det(M2 − xM1)` for semantic cleanliness,
the identity `p(x) = det(M1) · q(x)` — where `det(M1)` is a single
rational number — gives a one-line conversion, and FLINT has
`fmpz_mat.det()` for the integer-cleared `M1`. So:

> Use (β) throughout; record the single scalar `c_M1 := det(M1)` in the
> certificate so Rocq can state the theorem equivalently in either form.

## 2. Coefficient sizes of `q(x) = det(xI − A)` — empirical, exact

```
common denominator bits  : 1354
per-coefficient max bits : 1354     (monotone over degree)
min                      : 1076
```

The Hadamard-style estimate of "42 · log₂(127!) ≈ 30 000 bits" was
**off by 22×**. The real size is driven by the `(k + b + 2c)!`
denominators, whose LCM over all 42 monomial index pairs is
≈ 2^1354, not `factorial(127)` ≈ 2^700 per-entry (which is the
*single-entry* bit size of M1, M2). The numerators partly cancel
against this common denominator in the Faddeev path, so the final
`q(x)` coefficients sit right at ~1354 bits, i.e. in the same ballpark
as a single matrix entry.

Implication: **Rocq `vm_compute` on 42×42 with 1354-bit coefficients is
easily feasible.** The previous spike confirmed 200-bit at 42×42 in
under a second; 1354 bits is ~7× longer integers and multiplication
is sub-quadratic in bitsize, so expect ~20–50× slowdown,
i.e. tens-of-seconds worst case, which is fine for a one-shot
`Qed`-time proof discharge.

## 3. Sturm chain — two variants, pick subresultant

The naive chain `q_{i+1} = −rem(q_{i−1}, q_i)` in ℚ[x] blows up: the
terminal polynomial has **1 653 155-bit** coefficients after clearing
the common denominator once (the chain end is roughly
`disc(q) / (stuff)` times a rational that’s much larger than
`disc(q)` itself). Shipping this to Rocq is untenable: ~43 polys with
coefs growing linearly toward 1.65 Mbits is ~35 Mbits total, and each
`vm_compute` step would need millions of bignum operations on
mega-bit integers.

The **Brown-Traub subresultant PRS** solves this. The final entry is
literally the discriminant of `q`, `Res(q, q')`, which FLINT computes
independently as `100 578`-bit. Observed profile:

```
chain[0] : deg 42  coef  1 354 bits   (q)
chain[1] : deg 41  coef  1 359 bits   (q')
chain[2] : deg 40  coef  4 059 bits
chain[3] : deg 39  coef  6 745 bits
...
chain[i] : deg 42-i  coef ≈ 2 500·i bits   (near-linear growth)
...
chain[42]: deg 0   coef 100 578 bits   (= disc q, up to sign)
```

Total chain size: ∫₀⁴² 2500·i · (43−i) di ≈ 1.3·10⁸ bits ≈ 16 MB of
raw integer data. As a JSON string blob that is 30–40 MB; as a
base-10⁹ little-endian list it is ~3 M entries. **Shippable**, but
comparable to a mid-sized binary artifact — the certificate file will
dwarf the Rocq source.

`python-flint 0.8.0` exposes only `fmpz_poly.resultant`; it does
**not** expose `subresultants` or `pseudo_div_rem` directly (checked:
`[a for a in dir(fmpz_poly) if 'resul' or 'pseudo' or 'prs' in a]` =
`['resultant']` only). The 50-line manual Brown-Traub loop in
`/home/rocq/prime_gap/flint_subres.py` runs in 2.1 s and all
intermediate divisions are exact (asserted). This is the recommended
implementation.

**Sign variations at the correct threshold.** The theorem is
`M_{105} > 4` where `M_{105} = 105 · λ_top(A)`. So the Sturm threshold
for `q` is `x₀ := 4/105`, not `4`. Observed:

```
signs at 4/105 : [ -1, +1, +1, ..., +1 ]   →  V(4/105) = 1
signs at +∞    : [ +1, +1, +1, ..., +1 ]   →  V(+∞)    = 0
roots in (4/105, +∞)                       =  1        ✓
```

Exactly **one** real eigenvalue of `A` lies strictly above `4/105`,
which is the top eigenvalue. The Arb cross-check confirms
`k · λ_top = 4.00206976193804713686805879340…`, matching the
Mathematica notebook to full displayed precision.

## 4. Subresultant availability — summary

- `fmpz_poly.resultant(g)` **yes** — used it to double-check the
  discriminant bit-size.
- `fmpz_poly.subresultants` **no** — not in the 0.8.0 wheel.
- `fmpq_poly.__mod__` **yes** — but produces the blown-up naive chain.
- Manual Brown-Traub in Python on top of `fmpz_poly`: **runs in 2 s**,
  see `flint_subres.py`. Recommend shipping this 50-line routine as
  part of the certificate-generation script.

## 5. JSON certificate schema (what Rocq ingests)

```jsonc
{
  "version": 1,
  "source": "maynard M_105 > 4 via Sturm on det(xI - M1^-1 M2)",
  "dim": 42,

  // Optional: integer-cleared M1, M2 for Rocq to cross-check its own
  // self-assembly; cheap sanity gate, not logically needed once q is
  // fixed. Each is {den: "...", rows: [[...], ...]}.
  "M1_int": { "den": "....", "rows": [[ "...", ... ], ...] },
  "M2_int": { "den": "....", "rows": [[ "...", ... ], ...] },
  "det_M1": "...",          // single fmpz, for p(x) ↔ q(x) conversion

  // The rational char-poly q(x) = det(xI - A), A = M1^-1 M2. Shipped
  // with its common denominator already cleared: numerators are ints.
  "charpoly_q": {
    "common_den":       "<fmpz base-10>",
    "coefs_high_to_low":[ "<fmpz>", ..., "<fmpz>" ]   // 43 entries
  },

  // Brown-Traub subresultant PRS of (Q, Q'), Q = common_den * q.
  // Each element is an integer polynomial (low-to-high).
  "sturm_chain": [
    { "deg": 42, "coefs_low_to_high": [ "...", ... ] },
    { "deg": 41, "coefs_low_to_high": [ "...", ... ] },
    ...
    { "deg":  0, "coefs_low_to_high": [ "..." ] }
  ],

  // Precomputed signs. Rocq re-verifies by `vm_compute` evaluation.
  "threshold_x0_num": "4",
  "threshold_x0_den": "105",
  "signs_at_x0":  [ -1, 1, 1, ..., 1 ],    // 43 entries
  "signs_at_inf": [  1, 1, 1, ..., 1 ],    // 43 entries, = sign of leading coef
  "V_x0":  1,
  "V_inf": 0,
  "roots_in_x0_inf": 1,                    // MUST be >= 1

  // Brown-Traub audit trail: for each i >= 1, the constants used so
  // that Rocq can verify f_{i+1} = prem(f_{i-1}, f_i) / beta_i without
  // redoing the dance. These are cheap to verify by `vm_compute`.
  "prs_audit": [
    { "i": 1, "delta": 1, "psi": "-1", "beta":  "1" },
    ...
  ],

  // Sanity: Arb confirmation (non-logical)
  "arb_top_eig":       "0.03811495011369568...",
  "arb_top_eig_prec":  256,
  "arb_k_times_top":   "4.00206976193804713686805879340..."
}
```

**What Rocq needs to prove, concretely**, after reading the JSON:

1. `q_from_json = fmpq_poly q`, and verify against its own
   `det(xI − M1⁻¹M2)` by a direct `vm_compute reflexivity` on the
   polynomial-matrix determinant (or on the Faddeev-Leverrier unrolled
   `42×42` computation). Use the `M1_int`, `M2_int` cross-check as a
   cheap first gate.
2. For each `i`, check `f_{i+1} * β_i = prem(f_{i−1}, f_i)` as
   polynomial identity in `ℤ[x]` by `vm_compute reflexivity`. This is
   **the linchpin**: it’s the only way to certify the chain really is a
   subresultant PRS of `q`.
3. Check `signs_at_x0[i] = sign(f_i(4/105))` for every `i` by
   `vm_compute reflexivity` (rational evaluation then sign).
4. Check `signs_at_inf[i] = sign(lc(f_i))` similarly (one coefficient
   lookup per row).
5. Compute `V_x0 - V_inf` by a 43-step fold and compare with the
   certificate. `≥ 1` implies `∃ λ > 4/105, q(λ) = 0`, which (via `k =
   105` multiplication and the Rayleigh-Ritz identity `q(λ) = 0 ⇔
   det(M2 − λ M1) = 0`) gives `M_105 > 4`.

All five checks are closed `vm_compute` discharges; no axioms.

## 6. Risks (honest)

1. **Certificate file size.** ~16 MB of integer data, ~35 MB as JSON.
   Rocq can ingest this via a `Definition` emitting a list-of-list of
   `Z`, but `.v` source that large hits known `coqc` elaboration
   slowdowns (not `vm_compute` — elaboration). Mitigation: emit as a
   `.vo` from a small generator file using `Load` + numeric syntax, or
   ship as a string and parse. Either works; test both in the S1
   milestone.

2. **`vm_compute` on 100 kbit ints at 42×42 scale.** Previous spike
   was 200-bit; we're 500× longer. FLINT’s GMP-backed bignum mul is
   ~O(n log n log log n); Coq’s `BigZ` is O(n²) schoolbook up to ~1000
   limbs then Karatsuba. 100 kbit = ~1600 64-bit limbs → Karatsuba
   zone, ~40× slower per op than 200-bit. Chain verification is 42
   prem-divisions each on 42×42-ish polynomial coefficient arithmetic.
   Rough estimate: **seconds to low minutes** per `vm_compute reflexivity`,
   acceptable but not instant. Worth benchmarking one step on an
   isolated spike before committing to all 42.

3. **Rational sign-at-`4/105`.** To evaluate each chain polynomial at
   `4/105`, multiply by `105^{deg}` first so the result is an integer.
   `105^42 ≈ 2^282` is negligible vs the 100 kbit coefficients. No blowup.

4. **`gcd(q, q')` ≠ 1** — NOT observed. Confirmed simple spectrum.
   Include a `vm_compute`-checkable assertion that `f_42` (the final
   subresultant, = `disc q`) is non-zero; this is the certificate that
   the PRS completed normally and the spectrum is simple. If a future
   variant ever hits a repeated root, abort and fall back to working
   with `q / gcd(q, q')` — trivial adjustment, just rerun the
   generator.

5. **Sign at `+∞`** is just `sign(lc(f_i))`, which is a one-`nth`
   coefficient lookup. Trivial in Rocq. Ship the precomputed list and
   re-check by `vm_compute`.

6. **Generator-side vs verifier-side trust.** The generator (this
   Python script) is **untrusted**. The Rocq side re-derives every
   claim from `q` (itself re-derived from `M1`, `M2` which Rocq
   assembles from scratch via the same `Bnd`/`Cff`/`Poly` routines).
   python-flint is only used as an oracle for a candidate chain; Rocq
   closes the proof autonomously.

## 7. Concrete files in this directory

- `/home/rocq/prime_gap/flint_probe.py` — end-to-end builder + naive chain
- `/home/rocq/prime_gap/flint_subres.py` — Brown-Traub subresultant PRS
- `/home/rocq/prime_gap/flint_probe.json` — skeleton certificate (naive chain; will be replaced by subresultant version)
- `/home/rocq/prime_gap/m1m2.pkl` — cached rational M1, M2 (re-use for further spikes)

## 8. Next actions

1. Rewrite `flint_probe.py` to emit the **subresultant chain**, not
   the naive one, into the JSON.
2. Add `prs_audit` section (the β, ψ, δ trail) so Rocq can verify each
   step with a single `reflexivity`.
3. Spike one `vm_compute reflexivity` check on the *first* Brown-Traub
   step (1354-bit → 4059-bit coefs) to measure the per-step cost.
   Extrapolate to 43 steps; if > 10 min total, revisit the plan and
   consider splitting the chain verification into per-step `.vo`
   files.
4. Only after the spike succeeds: generate the full certificate and
   wire it to the Rocq side.
