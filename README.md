# FLINT certificate for Maynard's `M_{105} > 4`

This archive contains a self-contained, independently auditable FLINT
re-implementation of the numerical computation underlying **Proposition 4.3
/ formula (8.15)** of James Maynard's *Small gaps between primes*
([arXiv:1311.4600](https://arxiv.org/abs/1311.4600), Annals of Mathematics
**181** (2015), 383–413), namely the inequality

> `M_{105} = 105 · λ_max((M₂, M₁)) > 4`

where `(M₁, M₂)` is the 42 × 42 generalised eigenpair built from the
multidimensional Selberg–GPY sieve weights restricted to the symmetric
polynomial subspace `span_ℚ { x^b · y^c : b + 2c ≤ 11 }` with `k = 105`
simplex variables.

The original published proof relies on an **unrefereed Mathematica
notebook** (`Computations.nb`) shipped as an arXiv ancillary file. This
archive replaces that notebook with:

1. an exact-rational re-implementation in Python + FLINT (`python-flint`),
2. a Brown–Traub subresultant Sturm chain on the integer-cleared
   characteristic polynomial of `A = M₁⁻¹ M₂`, certifying that there is
   exactly one real eigenvalue above `4 / 105`,
3. a JSON certificate consumable by an independent Rocq verifier, and
4. four Rocq files that ingest the certificate and machine-check, by
   `vm_compute`, that the data round-trips and that the basic invariants
   hold.

It does **not** ship a complete Rocq proof of `M_{105} > 4` — that is the
"S1" stretch goal of the broader project (see `PLAN_S1.md` in the parent
project, not included here). What it does ship is the entire FLINT side
of S1: the certificate, the emitter, and the witness data the Rocq
proof will eventually consume.

## What's in the archive

```
flint-task/
├── README.md                      ← this file
├── _CoqProject                    ← Rocq build configuration
│
├── flint_probe.py                 ← exact-rational builder for M₁, M₂
│                                    (only used on the "cold" path; the
│                                    cached pickle below is enough for
│                                    everyday re-runs)
│
├── python/
│   └── build_certificate.py       ← main pipeline: assembles, verifies,
│                                    cross-checks, and emits the JSON
│                                    certificate
│
├── tools/
│   └── json_to_v.py               ← JSON → Rocq source emitter
│
├── m1m2.pkl                       ← cached exact-rational M₁, M₂ (320 KB)
│
├── certificate.json               ← small certificate (133 KB):
│                                    integer-cleared M₁, M₂, char poly,
│                                    sign vectors, V counts
│
├── certificate_chain.json         ← heavy certificate (11 MB):
│                                    full Brown–Traub PRS chain (43 polys)
│                                    and the 41 β scalars used at each step
│
├── theories/S1/
│   ├── Recompose.v                ← bigZ → stdlib-Z conversion helpers
│   ├── Witness.v                  ← M1_int, M2_int, charpoly_int, sign
│   │                                vectors, V counts (auto-generated)
│   ├── WitnessChain.v             ← Brown–Traub chain + βs as `bigZ`
│   │                                (auto-generated, 11 MB)
│   └── Smoke.v                    ← `vm_compute` round-trip tests
│
├── notebook_reconstructed.md      ← prose reverse-engineering of the
│                                    original Mathematica notebook, for
│                                    independent comparison
│
└── flint_sturm_plan.md            ← design report for the FLINT pipeline
                                     (coefficient-size estimates, the
                                     Brown–Traub vs naive Sturm comparison,
                                     PRS audit format)
```

## Prerequisites

- **Python ≥ 3.11**.
- **`python-flint` 0.8.0** or compatible. Installs cleanly via:
  ```bash
  python -m venv .venv && source .venv/bin/activate
  pip install python-flint        # or: uv pip install python-flint
  ```
  The wheel ships FLINT 3.x, GMP, MPFR, and Arb bundled — no system
  libraries needed.
- **Rocq 9.0** (the prover formerly known as Coq), with these packages:
  - `rocq-stdlib` (Stdlib library)
  - **`rocq-bignums`** — load-bearing; the `WitnessChain.v` file uses
    `BigZ` because stdlib `Z` literal elaboration stack-overflows above
    ~10 000 bits, while `BigZ` handles 100 000-bit literals in ~0.4 s.
  - All available via `opam install rocq-stdlib rocq-bignums` against
    a standard Rocq 9.0 switch.

## How to use

### 1. Verify the FLINT computation independently

Run the Python pipeline. It rebuilds (or loads the cache of) `M₁, M₂`,
sanity-checks five entries against closed-form Beta integrals, computes
the characteristic polynomial of `A = M₁⁻¹ M₂` via FLINT's
`fmpq_mat.charpoly()`, computes the Brown–Traub subresultant PRS chain,
verifies every PRS step independently in pure Python, computes the sign
vectors at `4 / 105` and `+∞`, asserts that `V(4/105) − V(+∞) ≥ 1`, and
cross-checks the top eigenvalue at 256-bit precision via Arb against
Maynard's published value `4.00206976193804713…`.

```bash
source .venv/bin/activate
python python/build_certificate.py
```

Expected runtime: ~7 s with the cached `m1m2.pkl`, ~90 s on a cold run
(the `prime_gram` integral assembly dominates the cold path).
Re-emits `certificate.json` and `certificate_chain.json` in place.

### 2. Regenerate the Rocq witness files

```bash
python tools/json_to_v.py --with-chain
```

Runs in well under a second; emits `theories/S1/Witness.v` and
`theories/S1/WitnessChain.v`. The `--with-chain` flag is what produces
the heavy 11 MB `WitnessChain.v`; omit it for a quick sanity build that
only emits the small `Witness.v`.

### 3. Verify in Rocq

```bash
coqc -Q theories/S1 PrimeGapS1 theories/S1/Recompose.v
coqc -Q theories/S1 PrimeGapS1 theories/S1/Witness.v
coqc -Q theories/S1 PrimeGapS1 theories/S1/WitnessChain.v
coqc -Q theories/S1 PrimeGapS1 theories/S1/Smoke.v
```

Expected runtime on a modest laptop:

| File              | Build time |
|-------------------|-----------:|
| `Recompose.v`     | < 1 s       |
| `Witness.v`       | ~3 s        |
| `WitnessChain.v`  | ~21 s       |
| `Smoke.v`         | ~2 m 10 s   |
| **Total**         | **~2 m 35 s** |

`Smoke.v`'s runtime is dominated by the single `lift_bigZ chain_42`
`vm_compute` that converts the 100 000-bit terminal Sturm chain entry
from `bigZ` to stdlib `Z`. All other smoke checks complete in
sub-second time.

### 4. Inspect what was verified

After `coqc theories/S1/Smoke.v` succeeds, the following lemmas have
been machine-checked under `vm_compute` (no axioms, no `Admitted`):

- **Shape** — `dim = 42`, `k_param = 105`, `sturm_chain_len = 43`,
  `length sturm_betas_bigZ = 41`, all matrix rows length 42, etc.
- **Charpoly** — `length charpoly_int = 43` (degree 42 + 1), the
  leading coefficient is nonzero.
- **Sign-variation invariant** — `signs_at_x0_head = -1`,
  `roots_in_x0_inf = 1` (exactly one real eigenvalue above `4 / 105`),
  and the round-tripped sign-at-+∞ vector is non-trivially positive.
- **bigZ ↔ Z round trip** — the load-bearing test:
  `lift_bigZ chain_0 = charpoly_int`. The bigZ-encoded Sturm chain entry
  `chain[0]`, after `vm_compute` conversion to stdlib `Z`, equals the
  independently-shipped char poly `charpoly_int` byte-for-byte. This
  proves that the bigZ encoding chosen for the heavy chain agrees with
  the stdlib-`Z` view used by the rest of the proof system.
- **Simple spectrum** — `chain_42` is a singleton with a nonzero
  coefficient, i.e. the discriminant of the char poly is nonzero,
  confirming inside Rocq that Maynard's matrix has a simple spectrum.

These tests are *not* a proof of `M_{105} > 4`. They are a proof that
the certificate the FLINT pipeline ships round-trips through Rocq
correctly. The actual S1 theorem `∃ λ : realalg, eigenvalue (map_mx
ratr A) λ ∧ ratr (4/105) < λ` is built on top of this in the Rocq side
of the project (not included in this archive).

## What is being computed (one-paragraph version)

`M₁` is the Gram matrix `⟨f_i, f_j⟩_I` where the inner product is
`⟨f, g⟩_I = ∫_{Δ_{105}} f g dt` over the standard 105-simplex, and
`{f_i}` is the basis `{x^b y^c}` with `x = 1 − Σtᵢ`, `y = Σtᵢ²`, and
`(b, c)` ranging over the 42 lattice points satisfying `b + 2c ≤ 11`.
`M₂` is the analogue Gram matrix for `⟨f, g⟩_J = ∫_{Δ_{104}} (∫₀^{1−Σ′tᵢ}
f dt₁) (∫₀^{1−Σ′tᵢ} g dt₁) dt'`, with the inner integral in `t₁`
performed analytically via Maynard's eq. 7.8. Both inner products reduce
to closed-form rationals via the Dirichlet/Beta integral
`∫_{Δ_k} ∏ tᵢ^{aᵢ} dt = (∏ aᵢ!)/(k+Σaᵢ)!`, so `M₁` and `M₂` are exact
rational matrices and the entire pipeline avoids floating point on the
critical path. The Arb cross-check at the end is *advisory* — it
agrees with Mathematica to 12+ digits but is not used in the certificate.

## Sanity checks the FLINT pipeline runs internally

`python/build_certificate.py` aborts loudly on any of these failing:

| Check | What it asserts |
|---|---|
| `M1[0][0] = 1/105!` | `F = 1`, `I_105(F) = 1/105!` |
| `M1[0][1] = 1/106!` | `F = x`, `I_105(x) = 1/106!` |
| `M1[0][2] = 210/107!` | `F = y`, with `G_{1,2}(105) = 210` |
| `M1[1][1] = 2/107!` | `F = x²`, `I_105(x²) = 2/107!` |
| `M2[0][0] = 2/106!` | `J_105(F = 1) = 2/106!` |
| `M1, M2` symmetric | for all `i ≠ j` |
| every PRS step audit | `prem(chain[i−1], chain[i]) = β_i · chain[i+1]` exactly in `ℤ[x]`, for all 41 steps |
| `gcd(q, q') = 1` | simple spectrum (otherwise abort) |
| `V(4/105) − V(+∞) ≥ 1` | Sturm count produces ≥ 1 root above the threshold |
| Arb top eigenvalue | `\| 105 · λ_top − 4.00206976193804713 \| < 10⁻¹²` |

## Why is `WitnessChain.v` written in `bigZ` and not `Z`?

The Brown–Traub Sturm chain has individual integer coefficients up to
**~200 000 bits** (≈ 60 000 decimal digits). Stdlib `Z`'s number
notation elaborates each literal in super-linear time and stack-overflows
above ~10 000 bits per literal. We measured this directly:

| literal width | stdlib `Z` | `bigZ` (rocq-bignums) |
|---:|---:|---:|
| 1 000 bits | 0.47 s | < 0.05 s |
| 5 000 bits | 2.37 s | < 0.05 s |
| 10 000 bits | 8.18 s | < 0.05 s |
| 20 000 bits | **stack overflow** | < 0.05 s |
| 100 000 bits | (intractable) | **0.42 s** |

`bigZ` from `rocq-bignums` uses a base-`2³¹` word array internally and
parses huge literals in roughly linear time. We therefore ship the
chain in `bigZ` and convert to stdlib `Z` lazily via `BigZ.to_Z` only
where downstream proofs need it. The lifting helpers
`lift_bigZ : list bigZ → list Z` and
`lift_bigZ2 : list (list bigZ) → list (list Z)` live in `Recompose.v`.

## Reproducibility

The pipeline is deterministic: re-running `build_certificate.py` on the
same machine produces byte-identical `certificate.json` and
`certificate_chain.json`. The only platform sensitivity is in the
`Arb` cross-check, which uses 256-bit ball arithmetic and produces
slightly different ball-radius hex strings on different FLINT builds —
but the rational data the Rocq side consumes is invariant.

## License and provenance

Source for the Mathematica notebook being audited:
- [arXiv:1311.4600v3](https://arxiv.org/abs/1311.4600), ancillary file
  `Computations.nb`. CC-BY-4.0 (per arXiv default).

The Python and Rocq files in this archive are original work for this
audit and are released under the same CC-BY-4.0 license.
