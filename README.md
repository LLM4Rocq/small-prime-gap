# Maynard `M_{105} > 4` — independent FLINT + Rocq audit

[![Blueprint](https://img.shields.io/badge/blueprint-online-blue)](https://gbaudart.github.io/prime_gap/blueprint/)
[![Blueprint PDF](https://img.shields.io/badge/blueprint-PDF-red)](https://gbaudart.github.io/prime_gap/blueprint.pdf)

An independently auditable re-implementation of the numerical
computation underlying **Proposition 4.3 / formula (8.15)** of James
Maynard's *Small gaps between primes*
([arXiv:1311.4600](https://arxiv.org/abs/1311.4600); Annals of
Mathematics **181** (2015), 383--413):

> **`M_{105} = 105 * lambda_max((M2, M1)) > 4`**

The original proof relies on an unrefereed Mathematica notebook. This
repository replaces it with two independent verification layers:

1. **A FLINT layer** (Python + `python-flint`): rebuilds the 42x42
   matrices from closed-form Beta integrals (100% of 3528 entries
   verified), computes the characteristic polynomial and Brown-Traub
   Sturm chain, and emits a JSON certificate.

2. **A Rocq layer** (Rocq 9.0/9.1 + MathComp 2.5 + `mathcomp-real-closed`):
   consumes the certificate, machine-verifies every computational fact
   via CRT over 710 Uint63 native primes and BigZ evaluation, and proves
   the headline eigenvalue theorem.

**The headline proof is complete.**

- 0 `Admitted` anywhere in the repository.
- 0 `Axiom` declarations anywhere in the repository.
- The only assumptions reported by `Print Assumptions
  maynard_M105_certified` (the recommended end-to-end target; see
  below) are Rocq's standard PrimInt63 kernel primitives
  (`Uint63Axioms.*`), which come with the compiler. The same holds
  for the spectral-only sibling `maynard_eigenvalue_S1`.
- The 42x42 input matrices `M1_int`, `M2_int` are themselves
  kernel-checked against Maynard's closed-form specification
  (Lemma 7.1 / eq. 7.8) — `MaynardVerify.all_match_M*Z_true` are Qed
  with `Print Assumptions: Closed under the global context`.
  The FLINT layer is no longer a trust dependency anywhere.

**No error was found in Maynard's computation.** The contribution is
the assurance level.

## The headline theorem

```rocq
Theorem maynard_eigenvalue_S1 :
  exists lambda : realalg,
    eigenvalue (map_mx (ratr : rat -> realalg) A_rat) lambda
    /\ (ratr (4%:Q / 105%:Q) : realalg) < lambda.
Proof. (* L1 + L2 + L3 + L4 *) Qed.
```

The full end-to-end trust contract is also packaged in a single Qed,
which conjoins the closed-form match of the input matrices with the
spectral bound:

```rocq
Theorem maynard_M105_certified :
  MaynardVerify.all_match_M1Z = true /\
  MaynardVerify.all_match_M2Z = true /\
  exists lambda : realalg,
    eigenvalue (map_mx (ratr : rat -> realalg) A_rat) lambda
    /\ (ratr (4%:Q / 105%:Q) : realalg) < lambda.
Proof. (* MaynardVerify.all_match_M{1,2}Z_true + maynard_eigenvalue_S1 *) Qed.
```

A single `Print Assumptions maynard_M105_certified` therefore covers
both the 1764+1764 input-matrix entries (each kernel-checked against
Maynard's closed form) and the eigenvalue-above-`4/105` statement.

## What this proves, and what stays paper-side

The contractual chain underlying `M_{105} > 4`:

```
   [ Rocq, kernel-checked  ]            [ Maynard's paper, Lemma 8.3 ]

   λ_max(M₁⁻¹M₂) > 4/105      ────►     M_{105} = 105·λ_max > 4
```

This Rocq project closes the **left box** with kernel assurance — the
same step the Mathematica notebook closes (notebook does it via a
rational Rayleigh-quotient witness; we do it via a Sturm-chain / IVT
witness on `char_poly(M₁⁻¹M₂)`). The right arrow is Maynard's Lemma 8.3
(`M_k = k · sup_F (J_k(F)/I_k(F)) = k · λ_max`), proved in the Annals
paper and refereed there; it is **not** formalised in this repository,
and the Mathematica notebook didn't formalise it either. The project's
scope is to replace the unrefereed *computational* black box, not to
re-formalise Maynard's paper.

Concretely:

- A reader who trusts **Rocq's kernel + Maynard's Annals paper** gets
  `M_{105} > 4` end-to-end.
- A reader who trusts **only Rocq's kernel** gets `λ_max > 4/105` for a
  specific kernel-verified 42×42 ℚ-matrix pencil — the harder-to-trust
  half of Maynard's original argument, now machine-checked.

In both readings, Lemma 8.2 (the closed-form matrix entries) is on the
Rocq side: `MaynardVerify.all_match_M{1,2}Z_true` checks all 1764+1764
entries against the paper's formulas (`MaynardSpec.{M1,M2}_entry`)
inside the kernel. See `SPEC_TO_PAPER.md` for the line-level mapping
from `MaynardSpec` to arXiv §8.

## Relation to Maynard's notebook

Maynard's `Computations.nb` certifies `M_{105} > 4` via the *eigenvector
route*: Mathematica numerically computes the top eigenvector of
`M₁⁻¹M₂`, snaps it to a small-denominator rational vector, and
evaluates the Rayleigh quotient `k · vᵀM₂v / vᵀM₁v` in exact rational
arithmetic — a true rigorous lower bound on `λ_max(M₁⁻¹M₂)` regardless
of how *v* was obtained. This project takes the *characteristic
polynomial route* instead: the Brown–Traub Sturm chain on
`char_poly(M₁⁻¹M₂)` certifies the existence of an eigenvalue strictly
above `4/105`, without ever constructing an eigenvector. Both routes
fit Maynard's §8 framework (Lemma 8.2 + Lemma 8.3); see `REPORT.md`
§1.4 for the detailed comparison.

## Repository layout

```
prime_gap/
+-- coq-prime-gap.opam              opam package file (pinned deps)
+-- requirements.txt                pinned python-flint for the FLINT layer
+-- README.md                       this file
+-- REPORT.md                       detailed technical walkthrough
+-- SPEC_TO_PAPER.md                line-level mapping MaynardSpec -> arXiv §8
+-- _CoqProject                     26 .v files in dependency order
|
+-- flint_probe.py                  M1, M2 builder
+-- m1m2.pkl                        cached exact-rational M1, M2
+-- certificate.json                small certificate (~510 KB)
+-- certificate_chain.json          heavy Sturm chain (~14 MB)
+-- notebook_reconstructed.md       reconstructed Mathematica notebook
|
+-- python/
|   +-- build_certificate.py        FLINT pipeline (3528/3528 entries verified)
+-- tools/
|   +-- json_to_v.py                JSON -> Rocq emitter
|
+-- theories/S1/                    27 Rocq files
    +-- Recompose.v                 bigZ <-> Z helpers
    +-- Witness.v                   certificate data (autogenerated)
    +-- WitnessChain.v              Sturm chain + quotients in bigZ
    +-- Smoke.v                     round-trip tests
    |
    +-- IntPoly.v                   list Z polynomial library
    +-- IntMat.v                    list (list Z) matrix library + det_int
    +-- BrownTraub.v                modified Sturm chain on list Z
    +-- SignChain.v                 sign-variation counting
    |
    +-- CharPoly.v                  Faddeev-LeVerrier + rat bridges
    +-- CharPolyAgree.v             CRT cross-validation, 710 primes
    +-- CharPolyScale.v             char_poly(c *: M) scaling formula
    |
    +-- ModularArith.v              shared Uint63 modular operations
    +-- CRTBridge.v                 FL modular soundness
    +-- CRTCheck.v                  42-step PRS verified via CRT
    +-- CRTSigns.v                  sign vectors verified via BigZ
    +-- CRTLift.v                   CRT lift: fl_eq_flint + matrix_identity_Z
    +-- Fermat.v                    Fermat's little theorem bridges
    +-- PrimeCheck.v                Z-level trial division + MathComp bridge
    |
    +-- MaynardFactQ.v              factorial / binomial as rat
    +-- MaynardBasis.v              42-element basis with Witness bridge
    +-- MaynardSpec.v               G_{n,2}(k), M1_entry, M2_entry closed forms
    +-- MaynardVerify.v             kernel-verifies M1_int, M2_int match the spec
    |
    +-- Bridge.v                    L1 Sturm bridge
    +-- CertL1.v                    L1 IVT proof
    +-- CertL2.v                    L2 assembly (charpoly_int_Dq_scaled)
    +-- Cert.v                      headline theorem
```

## Prerequisites

- **Python >= 3.11** + **`python-flint` 0.8.0**
- **Rocq 9.0 or 9.1** with: `rocq-mathcomp-ssreflect`, `rocq-mathcomp-algebra`,
  `rocq-mathcomp-field`, `coq-mathcomp-real-closed`, `rocq-bignums`,
  `coq-mathcomp-multinomials`, `coq-mathcomp-algebra-tactics` (all 2.5.0
  for MathComp, 2.0.3 for real-closed; see `coq-prime-gap.opam` for
  exact pins validated by the most recent full rebuild).
- Or simply: `opam install ./coq-prime-gap.opam --deps-only`

## How to use

```bash
# 1. FLINT audit (optional -- certificates pre-built)
source .venv/bin/activate && python python/build_certificate.py

# 2. Regenerate Rocq witness files (optional -- pre-built)
python tools/json_to_v.py --with-chain

# 3. Build all Rocq files (~37 min with `make -j` on a multi-core box;
#    ~80 min sequential).  Most of the wall-clock time is two
#    single-threaded vm_compute phases that overlap under `make -j`:
#      - CharPolyAgree.v + CRTLift.v: ~25 min combined (710-prime CRT checks)
#      - MaynardVerify.v: ~35 min for the 42x42 M2 spec cross-check
coq_makefile -f _CoqProject -o Makefile
make -j

# 4. Verify the end-to-end theorem has no project-specific axioms.
#    `maynard_M105_certified` is the recommended target: it conjoins
#    `all_match_M{1,2}Z = true` (the closed-form input-matrix check)
#    with the eigenvalue bound, so a single Print Assumptions covers
#    the full pipeline.  The spectral-only sibling
#    `maynard_eigenvalue_S1` reports the same assumption set.
coqtop -Q theories/S1 PrimeGapS1 \
  -l theories/S1/Cert.v -batch \
  -e 'Print Assumptions maynard_M105_certified.'
# Expected: only Uint63Axioms.* entries (standard Rocq primitive integers).
```

## Trust base

The Rocq verification trusts only:
- Rocq's kernel (including Uint63 primitive axioms for native int
  arithmetic, which are listed by `Print Assumptions`).

There are zero project-specific `Axiom` or `Admitted` lemmas anywhere
in the repository. This includes the 42x42 input matrices: `M1_int`
and `M2_int` are kernel-checked against Maynard's closed-form
specification in `theories/S1/MaynardVerify.v`. The denominator
`D_q` shipped alongside the integer-cleared characteristic polynomial
is also kernel-checked to be strictly positive (`Cert.D_q_pos`,
`vm_compute`-Qed), pinning sign hygiene of the FLINT-shipped data
against an otherwise-permissible sign-flip on `D_q`.

The shipped Sturm chain is now cross-validated against an independent
Rocq computation, not just self-consistent. `Smoke.sturm_chain_real_cross_check`
re-exports `CRTCheck.full_prs_chain_verified`, which checks the
Brown-Traub PRS identity `lc(B)^d * A == Q*B + beta*C (mod p)` for
every consecutive triple in the chain across 10 distinct ~2^30 primes
(themselves verified prime in Rocq via Uint63 trial division), giving
~300 bits of CRT cover on top of the chain-anchoring lemma
`chain_0_matches_charpoly`.

The FLINT layer is **not** in the trust base of the Rocq proof. It
serves only as (a) the candidate generator for the certificate data
and (b) an independent cross-check. If the FLINT layer shipped wrong
data, the Rocq build would fail at one of the `vm_compute` checks.

See `SPEC_TO_PAPER.md` for a line-level mapping from the
`MaynardSpec.{bnd, cff, G_2, alpha, M1_entry, M2_entry}` definitions
back to arXiv:1311.4600 v3 §8.

## License

CC-BY-4.0. Source notebook: [arXiv:1311.4600v3](https://arxiv.org/abs/1311.4600).
