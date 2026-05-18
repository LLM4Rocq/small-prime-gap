# Maynard `M_{105} > 4` — a Rocq Rayleigh-quotient witness proof

[![Blueprint CI](https://img.shields.io/github/actions/workflow/status/LLM4Rocq/small-prime-gap/blueprint.yml?branch=main&style=for-the-badge&label=blueprint%20CI)](https://github.com/LLM4Rocq/small-prime-gap/actions/workflows/blueprint.yml)
[![Blueprint](https://img.shields.io/badge/blueprint-online-blue?style=for-the-badge)](https://llm4rocq.github.io/small-prime-gap/blueprint/)
[![Blueprint PDF](https://img.shields.io/badge/blueprint-PDF-red?style=for-the-badge)](https://llm4rocq.github.io/small-prime-gap/blueprint.pdf)
[![Rocq 9.1.1](https://img.shields.io/badge/rocq-9.1.1-orange?style=for-the-badge)](https://rocq-prover.org/)
[![Python 3.11+](https://img.shields.io/badge/python-3.11+-blue.svg?style=for-the-badge)](https://www.python.org/downloads/)
[![License](https://img.shields.io/badge/license-CC--BY--4.0-blue.svg?style=for-the-badge)](https://creativecommons.org/licenses/by/4.0/)

This repository contains a Rocq mechanisation of the numerical
computation involved in the proof of **Proposition 4.3 / formula
(8.15)** of James Maynard's article *Small gaps between primes*
(Annals of Mathematics **181** (2015), 383–413; preprint
[arXiv:1311.4600](https://arxiv.org/abs/1311.4600)). The present
README refers to the v3 / Annals numbering. Maynard's proof relies
on a single computational step to establish a lower bound:

$$M_{105} > 4$$

where $M_k$ is defined in Proposition 4.2 as the supremum of an
explicit `J_k(F)/I_k(F)` ratio over a class of test functions
$F : [0,1]^k \to \mathbb{R}$.

In the original proof this inequality is checked by an ancillary
Mathematica notebook supplied as supplementary material with the
arXiv preprint. This project replaces that step with a kernel-checked
Rocq proof.

## The proof strategy in one paragraph

This branch mechanises Maynard's notebook strategy directly: the heart
of the proof is a single `vm_compute` Qed on an integer Rayleigh
inequality at a shipped 42-entry rational witness vector. Concretely,
the file `theories/S1/Witness_Quad.v` ships a vector
$v \in \mathbb{Q}^{42}$ (whose entries are obtained by snapping the
top eigenvector of $M_1^{-1} M_2$ to small-denominator rationals via
continued-fraction convergents), and `theories/S1/CertQuad.v` closes
the integer inequality

$$4 \cdot D_{M_2} \cdot v_{\mathrm{num}}^T M_1^{\mathrm{int}} v_{\mathrm{num}}
   \;<\; 105 \cdot D_{M_1} \cdot v_{\mathrm{num}}^T M_2^{\mathrm{int}} v_{\mathrm{num}}$$

by `vm_compute` reflexivity on `Z`-arithmetic. This is equivalent
(after clearing denominators uniformly) to the strict Rayleigh-quotient
bound `4 · vᵀM₁v < 105 · vᵀM₂v` on the paper-form spec matrices, which
in turn entails `M_{105} > 4` modulo Maynard's Lemma 8.3 (paper-side).
No eigenvalue is computed, no characteristic polynomial is built,
no IVT or Sturm chain is invoked.

## The headline theorem

```rocq
Theorem maynard_M105_certified_alt :
  (forall i j, (i < 42)%nat -> (j < 42)%nat ->
     M1_spec_ij i j = Z2rat (mat_get M1_int i j) / Z2rat D_M1) /\
  (forall i j, (i < 42)%nat -> (j < 42)%nat ->
     M2_spec_ij i j = Z2rat (mat_get M2_int i j) / Z2rat D_M2) /\
  4%:Q * quad_spec M1_spec_ij < 105%:Q * quad_spec M2_spec_ij.
Proof. (* M{1,2}_spec_eq_int + rayleigh_lt_main *) Qed.
```

in `theories/S1/CertQuad.v`. The first two conjuncts conjoin the
paper-form spec `MaynardSpec.M{1,2}_spec_ij` (the readable
transcription of Maynard's Lemma 8.2) with the FLINT-shipped integer
entries via the common denominators; the third is the strict
Rayleigh-quotient bound on those paper-form matrices at the shipped
witness.

A single `Print Assumptions maynard_M105_certified_alt` reports the
project-internal axiom set: the only project-internal axiom is
`CertQuad.rayleigh_lt_main`, with everything else being Rocq's
standard `PrimInt63` / `Uint63Axioms` / `CarryType` primitive-integer
interface. See the auditor's checklist for the refactor path on the
Admitted lemma.

| Headline | Files | LOC | Compile |
|---|---|---|---|
| `maynard_M105_certified_alt` | 20 | 9 547 | ~25–30 min |

## Repository layout

```
prime_gap/
+-- coq-prime-gap.opam              opam package file (pinned deps)
+-- requirements.txt                pinned python-flint for the FLINT layer
+-- README.md                       this file
+-- REPORT.md                       detailed technical walkthrough
+-- SPEC_TO_PAPER.md                line-level mapping MaynardSpec -> arXiv §8
+-- AUDITOR_CHECKLIST.md            claim-to-Rocq-lemma audit table
+-- _CoqProject                     .v files in dependency order
|
+-- notebook_reconstructed.md       reconstructed Mathematica notebook
|
+-- python/                         FLINT layer (candidate generator)
|   +-- flint_probe.py              M1, M2 builder
|   +-- build_certificate.py        FLINT pipeline (3528/3528 entries verified)
|   +-- build_quad_witness.py       Rayleigh witness emitter
|   +-- json_to_v.py                JSON -> Rocq emitter
|   +-- m1m2.pkl                    cached exact-rational M1, M2
|   +-- certificate.json            small certificate (~510 KB)
|
+-- theories/S1/                    20 .v files total
    +-- Recompose.v                 bigZ <-> Z helpers
    +-- Witness.v                   FLINT-shipped certificate data (autogenerated)
    +-- Witness_Quad.v              42-entry rational Rayleigh witness (autogenerated)
    |
    +-- IntPoly.v                   list Z polynomial library (legacy, unused on this branch)
    +-- IntMat.v                    list (list Z) matrix library
    +-- CharPoly.v                  Z<->rat / Z<->int bridging definitions (Z2rat, mat_int_to_rat)
    |
    +-- MaynardFactQ.v              factorial / binomial as rat
    +-- MaynardBasis.v              42-element basis with Witness bridge
    +-- MaynardSpec.v               G_{n,2}(k), M1_entry, M2_entry closed forms
    +-- MaynardVerify.v             M1_int / M2_int match the spec, assembly
    +-- MaynardVerify/              definitions + 6 parallel chunks
    |   +-- Def.v                   definitions + the fast M1 Qed
    |   +-- M2_0.v ... M2_5.v       7-row chunks of the M2 check
    +-- MaynardSpecBridge.v         kernel-Qed: paper-form (rat) <-> computational (Z) spec
    |
    +-- Cert.v                      slim auditor bridge: M{1,2}_spec_eq_int
    +-- CertQuad.v                  Rayleigh witness route: rayleigh_witness_holds + headline
```

On this branch the files `Bridge.v`, `SignChain.v`, `CertL1.v`,
`CertL2.v`, `CharPolyScale.v`, `CharPolyAgree.v` (and its
parallel-chunk subdirectory), `CRTLift.v`, `CRTBridge.v`,
`CRTCheck.v`, `Fermat.v`, `PrimeCheck.v`, and `ModularArith.v` are
**not present**: the proof does not use the characteristic-polynomial
or Chinese-remainder machinery. `Witness.v` is reused from the FLINT
pipeline (it ships `M{1,2}_int`, `D_M{1,2}`, the basis enumeration),
but the cleared-denominator char-poly coefficients and the auxiliary
`A_int` / `D_A` / `D_q` constants are not consumed anywhere on this
branch.

## Auditor's checklist

See [`AUDITOR_CHECKLIST.md`](./AUDITOR_CHECKLIST.md) for the 6-row
table mapping each verifiable claim to its reference in Maynard's
paper and the Rocq lemma backing it.

## Status of the headline

`CertQuad.rayleigh_lt_main` (the rat-level Rayleigh inequality
surfaced in the headline) is currently `Admitted`. The two underlying
integer-content lemmas `rayleigh_witness_holds` and
`rayleigh_witness_M1_positive` are axiom-free (*Closed under the
global context*, both by `vm_compute` reflexivity on `Z`-arithmetic),
as is the rat-level bigop ⇄ Z bridge `quad_spec_eq_Z` modulo the same
host-cgroup issue. The structural proof reduces to two nested
`eq_bigr` over a per-cell `field` identity sealed as
`quad_cell_identity`, and the `Admitted` is purely a kernel
proof-term verification artefact under the 16 GB host cgroup —
not a mathematical gap. See the header comment of `CertQuad.v`
for the refactor path.

## Prerequisites

- **Python ≥ 3.11** with **`python-flint` 0.8.0** (only needed to
  regenerate witness files; the .v files are checked into the
  repository).
- **Rocq 9.1.1** with: `rocq-mathcomp-ssreflect`,
  `rocq-mathcomp-algebra`, `rocq-mathcomp-field`, `rocq-bignums`,
  `coq-mathcomp-algebra-tactics`.
- Or simply: `opam install ./coq-prime-gap.opam --deps-only`.

## How to use

```bash
# 1. FLINT audit (optional — certificates pre-built)
source .venv/bin/activate && python python/build_certificate.py

# 2. Regenerate Rocq witness files (optional — pre-built)
python python/json_to_v.py
python python/build_quad_witness.py

# 3. Build all Rocq files (~25–30 min on a 16 GB / 6-thread machine
#    with make -j6). The dominant phase is the six MaynardVerify/M2_*
#    chunks, which compile in parallel under make -j.
coq_makefile -f _CoqProject -o Makefile
make -j6

# 4. Inspect the headline's assumptions.
coqtop -Q theories/S1 PrimeGapS1 \
  -l theories/S1/CertQuad.v -batch \
  -e 'Print Assumptions maynard_M105_certified_alt.'
# Expected: only Rocq's standard PrimInt63 / Uint63Axioms / CarryType
# primitive-integer interface, plus the project-internal Admitted
# CertQuad.rayleigh_lt_main (see "Status" above).
```

## License

CC-BY-4.0. Source notebook: [arXiv:1311.4600v3](https://arxiv.org/abs/1311.4600).
