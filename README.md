# Maynard `M_{105} > 4` — a Rocq replacement for the Mathematica notebook

[![Blueprint CI](https://img.shields.io/github/actions/workflow/status/LLM4Rocq/small-prime-gap/blueprint.yml?branch=main&style=for-the-badge&label=blueprint%20CI)](https://github.com/LLM4Rocq/small-prime-gap/actions/workflows/blueprint.yml)
[![Blueprint](https://img.shields.io/badge/blueprint-online-blue?style=for-the-badge)](https://llm4rocq.github.io/small-prime-gap/blueprint/)
[![Blueprint PDF](https://img.shields.io/badge/blueprint-PDF-red?style=for-the-badge)](https://llm4rocq.github.io/small-prime-gap/blueprint.pdf)
[![Rocq 9.1.1](https://img.shields.io/badge/rocq-9.1.1-orange?style=for-the-badge)](https://rocq-prover.org/)
[![Python 3.11+](https://img.shields.io/badge/python-3.11+-blue.svg?style=for-the-badge)](https://www.python.org/downloads/)
[![License](https://img.shields.io/badge/license-CC--BY--4.0-blue.svg?style=for-the-badge)](https://creativecommons.org/licenses/by/4.0/)

This repository mechanises the numerical computation behind **Proposition 4.3 /
formula (8.15)** of James Maynard's *Small gaps between primes* (Annals of
Mathematics **181** (2015), 383–413; preprint
[arXiv:1311.4600](https://arxiv.org/abs/1311.4600); we use the v3 / Annals
numbering). Maynard's argument relies on a single computational step to
establish a lower bound:

$$M_{105} > 4$$

where $M_k$ is defined in Proposition 4.2 as the supremum of an explicit ratio
$J_k(F)/I_k(F)$ over a class of test functions $F : [0,1]^k \to \mathbb{R}$.

In the original proof this bound is obtained by an ancillary **Mathematica
notebook**, shipped as supplementary material with the preprint. The point of
this project is to **replace that trusted computer-algebra step with a
machine-checked Rocq proof of the same fact**, so that the lower bound no
longer depends on an external Mathematica session. It is organised in two
layers:

1. **A FLINT layer** (`python/`) — a `python-flint` re-implementation of the
   notebook's exact-rational computation. It doubles as an **oracle**: it
   emits the matrices, the rational witness vector, and the characteristic
   polynomial as JSON, which are converted to Rocq source files. These data
   are *untrusted certificates* — the Rocq proof re-checks every one of them,
   so nothing the FLINT code outputs is part of the trusted base.

2. **A Rocq / MathComp layer** (`theories/`) — the machine-checked proof of
   (8.15). The guarantee rests on the correctness of the Rocq kernel and on
   the accurateness of the mechanised high-level statement — that the theorem
   really says $M_{105} > 4$ — which a human reviewer must audit
   (see [`AUDITOR_CHECKLIST.md`](./AUDITOR_CHECKLIST.md)). The
   FLINT-produced data enters only as certificates, re-verified inside the
   proof, and the development introduces no project-specific axioms.

## Relation to Maynard's notebook

Maynard's notebook `Computations.nb` builds a 42×42 matrix from the closed
forms of Lemmas (8.1)–(8.2), computes its top eigenvector, snaps it to a
small-denominator rational vector $v$, and evaluates the **Rayleigh quotient**
of the matrix at $v$ in exact rational arithmetic. The value exceeds $4$,
which bounds the largest eigenvalue — hence $M_{105}$ — from below.

This project mechanises exactly that computation. `Witness_Rayleigh.v` ships
the rational witness $v$, and `CertRayleigh.rayleigh_lt_main` discharges the
cleared-denominator integer form of the same Rayleigh inequality

$$4 \cdot D_{M_2}\, v^{T} M_1^{\mathrm{int}} v \;<\; 105 \cdot D_{M_1}\, v^{T} M_2^{\mathrm{int}} v$$

by `vm_compute` on `Z`. This single kernel-checked evaluation **is** the
formal counterpart of the notebook's numerical step — the same matrices, the
same witness, the same quotient — now reduced by Rocq's kernel instead of
being trusted to Mathematica. It is not a separate "trusted core": like
everything else here it is fully proved; it is singled out only because it is
the part that stands in for the notebook.

The development then goes one step beyond the notebook and turns that quotient
bound into an **explicit eigenvalue**, matching Maynard's characterisation of
$M_k$ as ($k$ times) the largest eigenvalue of the generalised problem
$M_2 v = \lambda M_1 v$ — i.e. the largest eigenvalue of
$M_{105} = 105\,(M_1^{-1} M_2)$. Two ingredients sit on top of the Rayleigh
inequality:

- **$M_1$ is positive-definite**, so the generalised problem reduces to an
  ordinary eigenvalue problem. This is certified by a
  characteristic-polynomial argument over `Z`: the characteristic polynomial
  of $M_1$ — recomputed in Rocq with a Faddeev–Le Verrier / Hessenberg
  routine modulo a prime and lifted across 200 primes by the Chinese
  Remainder Theorem — has strictly alternating signs, so all eigenvalues are
  positive. The shipped coefficients are, again, a FLINT-produced certificate
  re-checked by the kernel.
- a **Hermitian spectral bridge** (`SpectralCrux.herm_crux`): through $M_1$'s
  spectral square root and MathComp's complex spectral theorem, the strict
  Rayleigh positivity becomes a genuine eigenvalue of `M105` above `4`.

(For contrast, the `faddeev-leverrier` branch of this repository proves the
same bound by a *different* route — an intermediate-value argument on the
characteristic polynomial itself — rather than following the notebook's
Rayleigh-quotient computation.)

## The headline theorem

`MaynardEigen.maynard_M105_certified` exhibits the eigenvalue:

```rocq
(* with  C := algC  and  ratrM := map_mx (ratr : rat -> C) *)
Theorem maynard_M105_certified :
  matches_closed_forms M105 /\
  exists lam : C, eigenvalue (ratrM M105) lam /\ (4 < lam).
```

in `theories/S1/MaynardEigen.v`, where `M105 = 105 *: (invmx M1_rat *m M2_rat)`.
`matches_closed_forms` conjoins the closed-form identity with the entrywise
agreement between the paper-form spec (Lemma 8.2) and the FLINT-shipped integer
matrices; the existential exhibits a real eigenvalue strictly above `4`. Lemmas
(8.1)–(8.2) are not re-derived — they are taken as the definitions of the
matrix entries (the line-level mapping is in
[`SPEC_TO_PAPER.md`](./SPEC_TO_PAPER.md)).

The notebook's own conclusion — $M_{105} > 4$ read directly off the Rayleigh
quotient, without the eigenvalue reformulation — is also available on its own
as `CertRayleigh.maynard_M105_certified_rayleigh`, a short proof that uses
neither the spectral theorem nor the CRT layer.

`Print Assumptions` on either theorem reports *Closed under the global
context*: no project-specific axioms — and, since every reduction runs in `Z`
arithmetic, not even Rocq's native 63-bit primitive-integer interface appears.

| Theorem | Files | LOC | Compile |
|---|---|---|---|
| `maynard_M105_certified` (+ standalone `maynard_M105_certified_rayleigh`) | 43 | ~15 300 | clean `make -j8` ≈ 8.6 min |

## Repository layout

Some of these scripts are still rough around the edges and not yet up to the
standards of the libraries they build on. The generated layout:

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
+-- python/                         FLINT layer (candidate generator / oracle)
|   +-- flint_probe.py              M1, M2 builder
|   +-- build_certificate.py        FLINT pipeline (3528/3528 entries verified)
|   +-- build_quad_witness.py       Rayleigh witness emitter
|   +-- json_to_v.py                JSON -> Rocq emitter
|   +-- certificate.json            small certificate (~510 KB)
|
+-- theories/S1/                    43 .v files total
    |   -- shared data & helpers --
    +-- Recompose.v                 bigZ <-> Z helpers
    +-- Witness.v                   FLINT-shipped matrix data (autogenerated)
    +-- IntMat.v                    list (list Z) matrix library
    +-- IntPoly.v                   list Z polynomial library (used by CharPoly)
    +-- CharPoly.v                  list-Z char poly (char_poly_int) + Z->rat bridge
    |
    |   -- paper spec & FLINT parity --
    +-- MaynardFactQ.v              factorial / binomial as rat
    +-- MaynardBasis.v              42-element basis with Witness bridge
    +-- MaynardSpec.v               G_{n,2}(k), M1_entry, M2_entry closed forms
    +-- MaynardVerify.v (+ Def.v, M2_0..5.v)  M1_int / M2_int match the spec
    +-- MaynardSpecBridge.v         paper-form (rat) <-> computational (Z) spec
    +-- Cert.v                      slim auditor bridge: M{1,2}_spec_eq_int
    |
    |   -- the Rayleigh inequality (the notebook computation) --
    +-- Witness_Rayleigh.v          42-entry rational Rayleigh witness (autogenerated)
    +-- CertRayleigh.v              rayleigh_lt_main + standalone maynard_M105_certified_rayleigh
    |
    |   -- lifting it to an eigenvalue --
    +-- EigenBridge.v               M1_rat/M2_rat/A_rat/M105 + matches_closed_forms
    +-- SpectralCrux.v              Hermitian variational crux (complex spectral theorem)
    +-- ModularFL.v                 char_poly_modZ (Faddeev-Le Verrier mod p) + soundness
    +-- ModularHess.v               O(n^3) Hessenberg modular char-poly + soundness
    +-- Fermat.v / FLDiv.v / PrimeCheck.v   modular-inverse / primality support
    +-- Bound.v                     Hadamard-style char_poly coefficient bound
    +-- CRTCheck.v                  Chinese-remainder reconstruction
    +-- WitnessM1CharPoly.v         data: 200 CRT primes + char_poly coefficients
    +-- CRTFrameDefs.v + CRTFrame_part0..7.v  200-prime check, sharded for make -j8
    +-- CRTFrame.v                  recombines the shards
    +-- M1CharPoly.v                char_poly_int(M1_int) = shipped coefficients
    +-- M1PosDef.v                  M1 positive-definite + spectral factor
    +-- MaynardEigen.v              assembles maynard_M105_certified (headline)
```

## Auditor's checklist

See [`AUDITOR_CHECKLIST.md`](./AUDITOR_CHECKLIST.md) for the table mapping each
verifiable claim to its reference in Maynard's paper
([arXiv:1311.4600v3](https://arxiv.org/abs/1311.4600); Annals **181** (2015),
383–413) and the Rocq lemma backing it.

## Prerequisites

- **Python ≥ 3.11** with **`python-flint` 0.8.0** (only needed to regenerate
  the witness files; the `.v` files are checked into the repository).
- **Rocq 9.1.1** with `rocq-mathcomp-ssreflect`, `rocq-mathcomp-algebra`,
  `rocq-mathcomp-field`, `coq-mathcomp-analysis`, `rocq-bignums`,
  `coq-mathcomp-algebra-tactics` (see `coq-prime-gap.opam` for exact pins).
- Or simply: `opam install ./coq-prime-gap.opam --deps-only`.

## How to use

Running the Rocq verification does **not** require executing the FLINT code
first — the certificates are checked into the repository.

```bash
# 1. FLINT audit (optional -- certificates pre-built)
source .venv/bin/activate && python python/build_certificate.py

# 2. Regenerate the Rocq witness files (optional -- pre-built)
python python/json_to_v.py
python python/build_quad_witness.py

# 3. Build all Rocq files (clean `make -j8` ~ 8.6 min on a modern multicore
#    machine). The heaviest phases compile in parallel under make -j:
#    the six MaynardVerify/M2_* spec chunks and the eight CRTFrame_part*
#    per-prime CRT checks.
coq_makefile -f _CoqProject -o Makefile
make -j8

# 4. Inspect the headline's assumptions (and, if you like, the standalone one).
coqtop -Q theories/S1 PrimeGapS1 -l theories/S1/MaynardEigen.v -batch \
  -e 'Print Assumptions maynard_M105_certified.'
# Expected: Closed under the global context.

# Or the canonical clean-rebuild + Print Assumptions script:
./verify.sh
```

## License

CC-BY-4.0. Source notebook: [arXiv:1311.4600v3](https://arxiv.org/abs/1311.4600).
