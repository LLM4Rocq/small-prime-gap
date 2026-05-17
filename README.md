# Maynard `M_{105} > 4` — a Rocq mechanisation via the pencil-determinant identity

[![Blueprint CI](https://img.shields.io/github/actions/workflow/status/LLM4Rocq/small-prime-gap/blueprint.yml?branch=main&style=for-the-badge&label=blueprint%20CI)](https://github.com/LLM4Rocq/small-prime-gap/actions/workflows/blueprint.yml)
[![Blueprint](https://img.shields.io/badge/blueprint-online-blue?style=for-the-badge)](https://llm4rocq.github.io/small-prime-gap/blueprint/)
[![Blueprint PDF](https://img.shields.io/badge/blueprint-PDF-red?style=for-the-badge)](https://llm4rocq.github.io/small-prime-gap/blueprint.pdf)
[![Rocq 9.1.1](https://img.shields.io/badge/rocq-9.1.1-orange?style=for-the-badge)](https://rocq-prover.org/)
[![Python 3.11+](https://img.shields.io/badge/python-3.11+-blue.svg?style=for-the-badge)](https://www.python.org/downloads/)
[![License](https://img.shields.io/badge/license-CC--BY--4.0-blue.svg?style=for-the-badge)](https://creativecommons.org/licenses/by/4.0/)

This repository contains a standalone Rocq mechanisation of the
numerical step in the proof of **Proposition 4.3 / formula (8.15)**
of James Maynard's article *Small gaps between primes*
(Annals of Mathematics **181** (2015), 383--413), also available as a preprint ([arXiv:1311.4600](https://arxiv.org/abs/1311.4600)). The present README refers to the labels used in this published version of the article. Maynard's proof relies on a (single) computational proof in order to establish a lower bound:

 $$M_{105}  > 4$$

where $M_k$ is defined in Proposition 4.2 as the supremum of some expression $E(F)$ over the set of Riemann-integrable functions $F : [0, 1]^k \rightarrow R$ .

In order to obtain this bound, the original proof resorts to an ancillary Mathematica notebook, distributed as supplementary material with
the [arXiv:1311.4600](https://arxiv.org/abs/1311.4600) preprint.

This re-implementation aims at improving the reproducibility of the calculations, and the confidence in the proof of formula (8.15) by proposing two natures of alternatives:

1. **A FLINT layer** — This code can be used to perform an analogue computation to the original Mathematica session. In addition, it is used as an **oracle**, producing data that can be loaded as (untrusted) certificates by an independent verifier, in our case a formal proof. The current FLINT code produces several such data, and emits JSON certificates then converted to Rocq source files.

2. **A Rocq/MathComp layer** — which provides a mechanized version of the (8.15) inequality. The corresponding formal proof is machine-checked by Rocq's kernel. The guarantee relies on the correctness of the Rocq kernel, extended with Uint63 primitive integers and their standard axioms, as well as on the accurateness of the mechanized high-level statement of property (8.15), which has to be audited by a human reviewer. The data produced by the FLINT code is only used as certificates in the Rocq proof, and are thus **not** part of the trusted base of code. The formal verification does not rely on any specific axiom to this project.

## The headline theorems

```rocq
Theorem maynard_eigenvalue_S1_pencil :
  exists lambda : realalg,
    eigenvalue (map_mx (ratr : rat -> realalg) A_rat) lambda
    /\ (ratr (4%:Q / 105%:Q) : realalg) < lambda.
Proof. (* pencil-determinant signs + IVT *) Qed.
```

The following variant conjoins the spectral bound with the closed-form match of the input matrices, based on Lemmas (8.1) and (8.2). This last step consists in checking that the computation-friendly version of each matrix agrees with its deduction-friendly version, which in turn essentially consists in changing the datastructure respectively used for integers and for matrices.

Note that Lemmas (8.1) and (8.2) are **not** mechanized, but rather taken as definitions for the coefficients of matrices `M1` and `M2` :

```rocq
Theorem maynard_M105_certified_pencil :
  (forall i j : nat, (i < 42)%nat -> (j < 42)%nat ->
     M1_spec_ij i j = Z2rat (mat_get M1_int i j) / Z2rat D_M1) /\
  (forall i j : nat, (i < 42)%nat -> (j < 42)%nat ->
     M2_spec_ij i j = Z2rat (mat_get M2_int i j) / Z2rat D_M2) /\
  exists lambda : realalg,
    eigenvalue (map_mx (ratr : rat -> realalg) A_rat) lambda
    /\ (ratr (4%:Q / 105%:Q) : realalg) < lambda.
Proof. (* M{1,2}_spec_eq_int + maynard_eigenvalue_S1_pencil *) Qed.
```

A single `Print Assumptions maynard_M105_certified_pencil` therefore displays the axioms used for establishing both the correctness of the 1764+1764 input-matrix entries and the bound.

## Relation to Maynard's notebook

Maynard's original Mathematica notebook `Computations.nb` essentially defines a certain 42x42 matrix, from the formulas provided by Lemmas (8.1) and (8.2), and computes a well-chosen eigenvector. Then, its snaps this vector to a small-denominator rational vector `v`, and evaluates the Rayleigh quotient of the matrix at `v`, using exact rational arithmetic. The value obtained is greater than 4, which provides a rigorous lower bound on the eignevalues of the initial matrix, where rigorous here should be understood in the sense of rigorous computation.

The mechanized proof takes a different route.  Setting `A := M₁⁻¹·M₂`,
it uses the determinant-pencil identity (a generic fact of
commutative-ring algebra, provable in one line of mathcomp)

```
det(λ·M₁ − M₂) = det(M₁) · char_poly(A)(λ)
```

specialised at `λ = 4/105`: clearing denominators reduces the
eigenvalue bound to the sign of two integer determinants, namely
`det(M1_int)` (positive) and `det(pencil_int_clean)` (negative,
where `pencil_int_clean := D_pencil_clean · (4·M1_rat − 105·M2_rat)`
is the *clean* integer pencil scaled through the LCM of the
denominators of `4·M1_rat − 105·M2_rat`).  Both integer determinants
are closed by a per-prime modular CRT lift across the same 710
Uint63 primes (the clean pencil's determinant is 2613 bits, well
within the ~21300-bit `crt_product_710` headroom); the resulting
sign of `char_poly(A)(4/105)` is negative, while the leading
coefficient is `1 > 0`, so MathComp's intermediate value theorem
(`poly_ivtoo`) extracts a realalg eigenvalue strictly above `4/105`.
The Rocq layer compares each `char_poly_mod p (M1_int)` and
`char_poly_mod p (pencil_int_clean)` modulo each of the 710 primes
against the shipped constant terms `det_M1_int_value`,
`D_pencil_int_value` via a closed-form Hadamard-style coefficient
bound, and concludes via the Chinese Remainder Theorem.

## A single-line headline summary

| Headline                          | Files | LOC    | Compile     |
|-----------------------------------|-------|--------|-------------|
| `maynard_M105_certified_pencil`   | 41    | 15 964 | ~30-50 min  |

The 41 files / 15 964 LOC count covers `theories/S1/` in full; the
pencil-determinant proof itself adds roughly 1500–1900 LOC of
pencil-specific machinery
(`DetPencil.v`, `CertPencilDef.v`, `AbstractPencilHelper.v`,
`CRTPencilCheck.v`, `CRTPencilChecksProof.v`,
`CRTPencilHadamardGeneric.v`, `CRTPencilM1Bound.v`,
`CRTPencilPencilBound.v`, `PencilCleanGrid.v`,
`Witness_PencilDet.v`, `Witness_PencilClean.v`, `Witness_M1Bound.v`,
`Witness_PencilBound.v`, `AllRowsLenHelper.v`, `CertPencil.v`)
on top of a shared FLINT / MathComp / CharPoly / MaynardVerify base.

## Repository layout and disclaimer
Some proof scripts are still quite clumsy, and not yet on par with the expected standards of the libraries they are built upon. Here is the generated layout description:


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
|   +-- json_to_v.py                JSON -> Rocq emitter
|   +-- m1m2.pkl                    cached exact-rational M1, M2
|   +-- certificate.json            small certificate (~510 KB)
|
+-- theories/S1/                    41 .v files (incl. 7 in MaynardVerify/, 1 in CharPolyAgree/)
    +-- Recompose.v                 bigZ <-> Z helpers
    +-- Witness.v                   certificate data (autogenerated)
    +-- Witness_PencilDet.v         shipped det(M1_int)   integer literal
    +-- Witness_PencilClean.v       shipped clean pencil matrix + det literal
    +-- Witness_M1Bound.v           shipped Hadamard-bound literal for det(M1_int)
    +-- Witness_PencilBound.v       shipped Hadamard-bound literal for det(pencil)
    |
    +-- IntPoly.v                   list Z polynomial library
    +-- IntMat.v                    list (list Z) matrix library
    +-- AllRowsLenHelper.v          all_rows_len reflection helper
    |
    +-- CharPoly.v                  Faddeev-LeVerrier + rat bridges
    +-- CharPolyAgree/Def.v         710-prime list + per-prime modular toolkit
    |
    +-- ModularArith.v              shared Uint63 modular operations
    +-- CRTBridge.v                 FL modular soundness
    +-- CRTCheck.v                  CRT correctness lemmas (max_abs_coeff,
    |                               small_multiple_zero, all_primes_divide_product)
    +-- CRTLift.v                   CRT toolkit (Hadamard coefficient bounds)
    +-- Fermat.v                    Fermat's little theorem bridges
    +-- PrimeCheck.v                Z-level trial division + MathComp bridge
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
    +-- DetPencil.v                 det_pencil identity (generic mathcomp fact)
    +-- CertPencilDef.v             sealed det_M1_int / D_pencil_int / pencil_mat_int
    +-- AbstractPencilHelper.v      generic-n pencil cell / matrix bridge
    +-- PencilCleanGrid.v           1764-cell per-entry pencil cross-check
    +-- CRTPencilCheck.v            per-prime modular agreement for det(M1) / det(pencil)
    +-- CRTPencilChecksProof.v      710-prime vm_compute Qeds (check_M1_det_710 etc.)
    +-- CRTPencilHadamardGeneric.v  generic Hadamard chain for CRT-pencil bounds
    +-- CRTPencilM1Bound.v          bound vs. crt_product_710 for det(M1)
    +-- CRTPencilPencilBound.v      bound vs. crt_product_710 for det(pencil)
    |
    +-- CertL2.v                    A_rat / M1_1_unit / structural lemmas
    +-- Cert.v                      M{1,2}_spec_eq_int (composed paper-spec identity)
    +-- CertPencil.v                headline pencil-determinant assembly
```

## Auditor's checklist

See [`AUDITOR_CHECKLIST.md`](./AUDITOR_CHECKLIST.md) for the 7-row
table mapping each verifiable claim to its reference in Maynard's
paper ([arXiv:1311.4600v3](https://arxiv.org/abs/1311.4600); Annals
**181** (2015), 383–413) and the Rocq lemma backing it.

## Prerequisites
Here are the generated prerequisite informations:

- **Python >= 3.11** + **`python-flint` 0.8.0**
- **Rocq 9.1.1** with: `rocq-mathcomp-ssreflect`, `rocq-mathcomp-algebra`,
  `rocq-mathcomp-field`, `coq-mathcomp-real-closed`, `rocq-bignums`,
  `coq-mathcomp-multinomials`, `coq-mathcomp-algebra-tactics` (all 2.5.0
  for MathComp, 2.0.3 for real-closed; see `coq-prime-gap.opam` for
  exact pins validated by the most recent full rebuild).
- Or simply: `opam install ./coq-prime-gap.opam --deps-only`

## How to use
Here are the generated instructions. Note that running the Rocq verification **does not** require executing the FLINT code first. Timings are wall-clock measurements on a 16 GB / 6-thread machine.

```bash
# 1. FLINT audit (optional -- certificates pre-built)
source .venv/bin/activate && python python/build_certificate.py

# 2. Regenerate Rocq witness files (optional -- pre-built)
python python/json_to_v.py

# 3. Build all Rocq files (~30-50 min wall clock with `make -j6`).
#    The heaviest phase is the 42x42 M2 spec cross-check, split into
#    six parallel chunks (MaynardVerify/M2_0..5.v) so they overlap
#    under `make -j6`.
coq_makefile -f _CoqProject -o Makefile
make -j6

# 4. Verify the end-to-end theorem has no project-specific axioms.
#    `maynard_M105_certified_pencil` is the recommended target: it
#    conjoins the per-matrix paper-form spec identities (M{1,2}_spec_ij
#    = Z2rat(M_int[i,j]) / Z2rat D_M{1,2}, composed internally from
#    `all_match_M{1,2}Z = true` plus the rat<->Z bridge from
#    MaynardSpecBridge) with the eigenvalue bound, so a single
#    Print Assumptions covers the full pipeline.
coqtop -Q theories/S1 PrimeGapS1 \
  -l theories/S1/CertPencil.v -batch \
  -e 'Print Assumptions maynard_M105_certified_pencil.'
# Expected: only Rocq's standard PrimInt63 / Uint63Axioms primitive-integer
# interface (the footprint inherited by every vm_compute-driven proof).
# No project-specific axioms, no Admitted.

# Or: a single canonical "clean rebuild + Print Assumptions" script:
./verify.sh
```


## License

CC-BY-4.0. Source notebook: [arXiv:1311.4600v3](https://arxiv.org/abs/1311.4600).
