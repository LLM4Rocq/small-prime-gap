# Maynard `M_{105} > 4` — an axiom-free Rocq proof

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

## The proof strategy

The development proves `M_{105} > 4` in Maynard's eigenvalue form,
matching his characterisation of $M_k$ as ($k$ times) the largest
eigenvalue of the generalised problem $M_2 v = \lambda M_1 v$. The
headline `theories/S1/MaynardEigen.v` *exhibits* a real eigenvalue
strictly above `4` of `M105 = 105 *: (invmx M1_rat *m M2_rat)` over
`algC`. It is `Qed` and reports *Closed under the global context*; every
reduction runs in stdlib `Z` arithmetic, so it never touches the native
63-bit primitive-integer interface.

**The computational core** is a single integer Rayleigh inequality. The
file `theories/S1/Witness_Rayleigh.v` ships a vector
$v \in \mathbb{Q}^{42}$ (its entries obtained by snapping the top
eigenvector of $M_1^{-1} M_2$ to small-denominator rationals via
continued-fraction convergents), and `CertRayleigh.rayleigh_lt_main`
closes the integer inequality

$$4 \cdot D_{M_2} \cdot v_{\mathrm{num}}^T M_1^{\mathrm{int}} v_{\mathrm{num}}
   \;<\; 105 \cdot D_{M_1} \cdot v_{\mathrm{num}}^T M_2^{\mathrm{int}} v_{\mathrm{num}}$$

by `vm_compute` reflexivity on `Z`-arithmetic. This is equivalent (after
clearing denominators uniformly) to the strict Rayleigh-quotient bound
`4 · vᵀM₁v < 105 · vᵀM₂v` on the paper-form spec matrices.

Turning that strict quotient bound into a positive *eigenvalue* needs two
axiom-free ingredients on top of it:

1. **`M1` positive-definite**, certified by a
   characteristic-polynomial / CRT argument over `Z`:
   `char_poly_int(M1_int)` equals a shipped, strictly-sign-alternating
   coefficient list (⟹ all eigenvalues `> 0` ⟹ `M1` positive-definite),
   proved by agreement modulo 200 primes whose product exceeds twice a
   Hadamard-style coefficient bound — a deterministic CRT, not a
   probabilistic one (fast Hessenberg modular char-poly).
2. the **Hermitian spectral bridge** `SpectralCrux.herm_crux` (if `A` is
   Hermitian and `wᵀAw > 0` then `A` has a positive eigenvalue), via
   mathcomp's complex spectral theorem, which through `M1`'s spectral
   square root reduces the generalised problem to a standard one and
   transfers the Rayleigh positivity to a positive eigenvalue.

So the proof does build a characteristic polynomial (mod p), perform a
Chinese-remainder lift, and exhibit an eigenvalue — all kernel-checked
and axiom-free. It invokes no IVT or Sturm chain, and no `realalg`
decision procedure.

**Minimal-trust shortcut.** The same Rayleigh inequality is also
packaged standalone as
`CertRayleigh.maynard_M105_certified_rayleigh` — a proof of `M_{105} > 4`
whose only kernel obligations are the matrix transcription and one
integer `vm_compute`, needing neither the spectral theorem nor the CRT
certificate. It is a minimal-trust audit anchor and itself uses no
eigenvalue, no characteristic polynomial, and no Chinese-remainder lift.

## The headline theorem

`MaynardEigen.maynard_M105_certified`:

```rocq
(* with  C := algC  and  ratrM := map_mx (ratr : rat -> C) *)
Theorem maynard_M105_certified :
  matches_closed_forms M105 /\
  exists lam : algC, eigenvalue (ratrM M105) lam /\ (4 < lam).
```

in `theories/S1/MaynardEigen.v`, where
`M105 = 105 *: (invmx M1_rat *m M2_rat)`. `matches_closed_forms` bundles
the closed-form identity `M = M105` with the entrywise agreement of the
paper-form spec and the FLINT-shipped integer matrices; the existential
exhibits a real eigenvalue strictly above `4`.

The minimal-trust audit anchor is the standalone Rayleigh theorem
`CertRayleigh.maynard_M105_certified_rayleigh`:

```rocq
Theorem maynard_M105_certified_rayleigh :
  (forall i j, (i < 42)%nat -> (j < 42)%nat ->
     M1_spec_ij i j = Z2rat (mat_get M1_int i j) / Z2rat D_M1) /\
  (forall i j, (i < 42)%nat -> (j < 42)%nat ->
     M2_spec_ij i j = Z2rat (mat_get M2_int i j) / Z2rat D_M2) /\
  4%:Q * quad_spec M1_spec_ij < 105%:Q * quad_spec M2_spec_ij.
Proof. (* M{1,2}_spec_eq_int + rayleigh_lt_main *) Qed.
```

in `theories/S1/CertRayleigh.v`. The first two conjuncts conjoin the
paper-form spec `MaynardSpec.M{1,2}_spec_ij` (the readable
transcription of Maynard's Lemma 8.2) with the FLINT-shipped integer
entries via the common denominators; the third is the strict
Rayleigh-quotient bound on those paper-form matrices at the shipped
witness. It establishes `M_{105} > 4` from the matrix transcription and
the single integer `vm_compute` alone, with no eigenvalue, no
characteristic polynomial, and no Chinese-remainder lift.

`Print Assumptions` on either theorem —
`maynard_M105_certified` or `maynard_M105_certified_rayleigh` — reports
*Closed under the global context*: zero axioms, including zero kernel
primitives (every reduction runs in `Z` arithmetic, so `vm_compute`
never touches the native 63-bit `PrimInt63` / `Uint63Axioms` /
`CarryType` interface). There are no `Admitted`, no `Axiom`, and no
`Parameter` declarations anywhere in `theories/S1/`.

| Headline | Files | LOC | Compile |
|---|---|---|---|
| `maynard_M105_certified` (+ standalone `maynard_M105_certified_rayleigh`) | 43 | ~15 300 | clean `make -j8` ≈ 8.6 min |

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
+-- theories/S1/                    43 .v files total
    |   -- shared data & helpers --
    +-- Recompose.v                 bigZ <-> Z helpers
    +-- Witness.v                   FLINT-shipped certificate data (autogenerated)
    +-- IntMat.v                    list (list Z) matrix library
    +-- IntPoly.v                   list Z polynomial library (used by CharPoly)
    +-- CharPoly.v                  list-Z char poly (char_poly_int) + Z->rat bridge (mat_int_to_rat)
    |
    |   -- paper spec & FLINT parity --
    +-- MaynardFactQ.v              factorial / binomial as rat
    +-- MaynardBasis.v              42-element basis with Witness bridge
    +-- MaynardSpec.v               G_{n,2}(k), M1_entry, M2_entry closed forms
    +-- MaynardVerify.v             M1_int / M2_int match the spec, assembly
    +-- MaynardVerify/              definitions + 6 parallel chunks
    |   +-- Def.v                   definitions + the fast M1 Qed
    |   +-- M2_0.v ... M2_5.v       7-row chunks of the M2 check
    +-- MaynardSpecBridge.v         kernel-Qed: paper-form (rat) <-> computational (Z) spec
    +-- Cert.v                      slim auditor bridge: M{1,2}_spec_eq_int
    |
    |   -- Rayleigh inequality (computational core + standalone anchor) --
    +-- Witness_Rayleigh.v          42-entry rational Rayleigh witness (autogenerated)
    +-- CertRayleigh.v              rayleigh_lt_main + standalone maynard_M105_certified_rayleigh
    |
    |   -- eigenvalue chain --
    +-- EigenBridge.v               M1_rat/M2_rat/A_rat/M105 + matches_closed_forms
    +-- SpectralCrux.v              Hermitian variational crux herm_crux (complex spectral thm)
    +-- ModularFL.v                 char_poly_modZ (Faddeev-LeVerrier mod p) + soundness
    +-- ModularHess.v               O(n^3) Hessenberg modular char-poly + soundness (both bridge
    |                               lemmas hess_reduce_similar / hess_recurrence_sound proven)
    +-- Fermat.v / FLDiv.v / PrimeCheck.v   modular-inverse / primality support
    +-- Bound.v                     Hadamard-style char_poly coefficient bound
    +-- CRTCheck.v                  crt_reconstruct (deterministic CRT uniqueness)
    +-- WitnessM1CharPoly.v         data: 200 CRT primes + char_poly coefficient list
    +-- CRTFrameDefs.v              CRT-frame definitions
    +-- CRTFrame_part0.v .. part7.v 200-prime per-prime check, sharded for make -j8
    +-- CRTFrame.v                  recombines the shards (per_prime_hess_all)
    +-- M1CharPoly.v                char_poly_int(M1_int) = shipped coefficient list
    +-- M1PosDef.v                  M1 positive-definite + spectral factor M1_rat_factor
    +-- MaynardEigen.v              assembles maynard_M105_certified (headline)
```

On top of the shared spec/parity layer and the Rayleigh inequality, the
eigenvalue chain adds a list-`Z` characteristic polynomial, a modular
(mod p) char-poly with a deterministic 200-prime Chinese-remainder lift,
and a complex spectral decomposition that exhibits the eigenvalue. The
standalone `maynard_M105_certified_rayleigh` anchor stays on a short,
linear chain that uses none of those. Nothing in the development invokes
an IVT or Sturm chain, or a `realalg` decision procedure. `Witness.v` is
the matrix data shipped from the FLINT pipeline.

## Auditor's checklist

See [`AUDITOR_CHECKLIST.md`](./AUDITOR_CHECKLIST.md) for the table
mapping each verifiable claim to its reference in Maynard's paper and the
Rocq lemma backing it.

## Axiom status

The headline `MaynardEigen.maynard_M105_certified`, the standalone
anchor `CertRayleigh.maynard_M105_certified_rayleigh`, and every
auditor-checklist lemma report *Closed under the global context*: zero
axioms across the whole proof chain. No `Admitted`, no `Axiom`, no
`Parameter` anywhere in `theories/S1/`. Because every reduction is in
`Z` arithmetic, `vm_compute` never touches the native 63-bit
primitive-integer interface either — not even `PrimInt63` /
`Uint63Axioms` / `CarryType` appear in `Print Assumptions` output.

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

# 3. Build all Rocq files (clean `make -j8` ≈ 8.6 min on a modern
#    multicore machine). The dominant phases are the six
#    MaynardVerify/M2_* spec chunks and the eight CRTFrame_part*
#    per-prime CRT checks, all of which compile in parallel under make -j.
coq_makefile -f _CoqProject -o Makefile
make -j8

# 4. Inspect each headline's assumptions.
coqtop -Q theories/S1 PrimeGapS1 \
  -l theories/S1/MaynardEigen.v -batch \
  -e 'Print Assumptions maynard_M105_certified.'
coqtop -Q theories/S1 PrimeGapS1 \
  -l theories/S1/CertRayleigh.v -batch \
  -e 'Print Assumptions maynard_M105_certified_rayleigh.'
# Expected (both): Closed under the global context (zero axioms — not even
# PrimInt63 / Uint63Axioms / CarryType, since the proof chain operates in
# Z arithmetic only).
```

## License

CC-BY-4.0. Source notebook: [arXiv:1311.4600v3](https://arxiv.org/abs/1311.4600).
