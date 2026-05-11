# Maynard `M_{105} > 4` — a Rocq replacement for the Mathematica notebook

[![Blueprint](https://img.shields.io/badge/blueprint-online-blue)](https://gbaudart.github.io/prime_gap/blueprint/)
[![Blueprint PDF](https://img.shields.io/badge/blueprint-PDF-red)](https://gbaudart.github.io/prime_gap/blueprint.pdf)

An independently auditable re-implementation of the numerical
computation underlying **Proposition 4.3 / formula (8.15)** of James
Maynard's *Small gaps between primes*
([arXiv:1311.4600](https://arxiv.org/abs/1311.4600); Annals of
Mathematics **181** (2015), 383--413):

> **`M_{105} = 105 * lambda_max((M2, M1)) > 4`**

The original proof carries out this numerical step in a Mathematica
notebook (`Computations.nb`, distributed as supplementary material with
the arXiv preprint). This repository replaces that Mathematica-based
computation with two stages:

1. **A FLINT layer** (Python + `python-flint`) — the **candidate
   generator**: rebuilds the 42x42 matrices from closed-form Beta
   integrals (100% of 3528 entries internally verified), computes the
   characteristic polynomial and Brown-Traub Sturm chain, and emits a
   JSON certificate.

2. **A Rocq layer** (Rocq 9.1.1 + MathComp 2.5.0 + `mathcomp-real-closed` 2.0.3)
   — the **verification**: consumes the certificate, kernel-checks every
   entry against an independent Rocq-side derivation via CRT over 710
   Uint63 native primes and BigZ evaluation, and proves the headline
   eigenvalue theorem.

Only the Rocq layer is in the trust base; the FLINT outputs are inputs
that the Rocq build cross-checks before accepting.

**The headline proof is complete.**

- 0 `Admitted` anywhere in the repository.
- 0 `Axiom` declarations anywhere in the repository.
- The only assumptions reported by `Print Assumptions
  maynard_M105_certified` (the recommended end-to-end target; see
  below) are Rocq's standard PrimInt63 kernel primitives
  (`PrimInt63.*` / `Uint63Axioms.*`), which come with the compiler.
  The same holds for the spectral-only sibling
  `maynard_eigenvalue_S1`.
- The 42×42 input matrices `M1_int`, `M2_int` are themselves
  kernel-checked against Maynard's closed-form specification (§8,
  Lemma 8.2 / eq. 8.4); the FLINT layer is the candidate generator,
  not part of the trust base.

This project does not change Maynard's computation; the contribution
is the assurance level.

## The headline theorem

```rocq
Theorem maynard_eigenvalue_S1 :
  exists lambda : realalg,
    eigenvalue (map_mx (ratr : rat -> realalg) A_rat) lambda
    /\ (ratr (4%:Q / 105%:Q) : realalg) < lambda.
Proof. (* L1 + L2 + L3 *) Qed.
```

The full end-to-end trust contract is also packaged in a single Qed,
which conjoins the closed-form match of the input matrices with the
spectral bound:

```rocq
Theorem maynard_M105_certified :
  all_match_M1Z = true /\
  all_match_M2Z = true /\
  (forall i j : nat,
     MaynardSpec.M1_spec_ij i j
     = MaynardSpecBridge.qfrac (MaynardSpec.m1_num_den_at i j)) /\
  (forall i j : nat,
     MaynardSpec.M2_spec_ij i j
     = MaynardSpecBridge.qfrac (MaynardSpec.m2_num_den_at i j)) /\
  exists lambda : realalg,
    eigenvalue (map_mx (ratr : rat -> realalg) A_rat) lambda
    /\ (ratr (4%:Q / 105%:Q) : realalg) < lambda.
Proof. (* assembled from the four Z-level / paper-form bridge facts
          and `maynard_eigenvalue_S1` *) Qed.
```

A single `Print Assumptions maynard_M105_certified` therefore covers
both the 1764 + 1764 input-matrix entries (each kernel-checked against
Maynard's closed form) and the eigenvalue-above-`4/105` statement.

## What this proves, and what stays paper-side

The contractual chain underlying `M_{105} > 4`:

```
   [ Rocq, kernel-checked  ]            [ Maynard's paper, Lemma 8.3 ]

   λ_max(M₁⁻¹M₂) > 4/105      ────►     M_{105} = 105·λ_max > 4
```

This Rocq project closes the **left box** with kernel assurance — the
same step the Mathematica notebook closes (the notebook uses a
rational Rayleigh-quotient witness; we use IVT on
`char_poly(M₁⁻¹M₂)`). The right arrow is Maynard's Lemma 8.3
(`M_k = k · sup_F (J_k(F)/I_k(F)) = k · λ_max`), proved in the Annals
paper and refereed there; it is **not** formalised here. The
project's scope is to replace the Mathematica computation, not to
re-formalise Maynard's paper.

Concretely:

- A reader who trusts **Rocq's kernel + Maynard's Annals paper** gets
  `M_{105} > 4` end-to-end.
- A reader who trusts **only Rocq's kernel** gets `λ_max > 4/105` for
  a specific kernel-verified 42×42 ℚ-matrix pencil — the
  harder-to-trust half of Maynard's original argument, now
  machine-checked.

## Auditor's checklist

See [`AUDITOR_CHECKLIST.md`](./AUDITOR_CHECKLIST.md) for the full
8-row table mapping each claim to its Maynard-paper reference and the
Rocq lemma backing it.

## Relation to Maynard's notebook

Maynard's `Computations.nb` certifies `M_{105} > 4` via the *eigenvector
route*: Mathematica numerically computes the top eigenvector of
`M₁⁻¹M₂`, snaps it to a small-denominator rational vector, and
evaluates the Rayleigh quotient `k · vᵀM₂v / vᵀM₁v` in exact rational
arithmetic — a true rigorous lower bound on `λ_max(M₁⁻¹M₂)` regardless
of how *v* was obtained. This project takes the *characteristic
polynomial route* instead: IVT on `char_poly(M₁⁻¹M₂)` (using
mathcomp-real-closed's `poly_ivtoo`) certifies a real-algebraic root
strictly above `4/105`, without ever constructing an eigenvector. The
IVT proof evaluates `charpoly_int` directly at the lower endpoint
`4/105` (sign `-1`, by `vm_compute`) and uses the positivity of the
leading coefficient at MathComp's `cauchy_bound`; no shipped Sturm
chain is consumed. Both routes fit Maynard's §8 framework (Lemma 8.2
+ Lemma 8.3); see `REPORT.md` §1.4 for the detailed comparison.

## Repository layout

```
prime_gap/
+-- coq-prime-gap.opam              opam package file (pinned deps)
+-- requirements.txt                pinned python-flint for the FLINT layer
+-- README.md                       this file
+-- REPORT.md                       detailed technical walkthrough
+-- SPEC_TO_PAPER.md                line-level mapping MaynardSpec -> arXiv §8
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
+-- theories/S1/                    Rocq files (22 .v files)
    +-- Recompose.v                 bigZ <-> Z helpers
    +-- Witness.v                   certificate data (autogenerated)
    |
    +-- IntPoly.v                   list Z polynomial library
    +-- IntMat.v                    list (list Z) matrix library
    +-- SignChain.v                 sign-variation counting (sgn_Z, sign_at_*)
    |
    +-- CharPoly.v                  Faddeev-LeVerrier + rat bridges
    +-- CharPolyAgree.v             710-prime CRT assembly
    +-- CharPolyAgree/              definitions + 6 parallel chunks
    |   +-- Def.v                   definitions (modular arith, prime list)
    |   +-- Chunk_0.v ... Chunk_5.v 119-prime chunks (proved by `make -j`)
    +-- CharPolyScale.v             char_poly(c *: M) scaling formula
    |
    +-- ModularArith.v              shared Uint63 modular operations
    +-- CRTBridge.v                 FL modular soundness
    +-- CRTCheck.v                  CRT correctness lemmas (max_abs_coeff,
    |                               small_multiple_zero, all_primes_divide_product)
    +-- CRTLift.v                   CRT lift: fl_eq_flint + matrix_identity_Z
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
    +-- Bridge.v                    L1 bridge to MathComp real-closed
    +-- CertL1.v                    L1 IVT proof
    +-- CertL2.v                    L2 assembly (charpoly_int_Dq_scaled)
    +-- Cert.v                      headline theorem
```

## Prerequisites

- **Python >= 3.11** + **`python-flint` 0.8.0**
- **Rocq 9.1.1** with: `rocq-mathcomp-ssreflect`, `rocq-mathcomp-algebra`,
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
python python/json_to_v.py --with-chain

# 3. Build all Rocq files (~24 min with `make -j` on a multi-core box).
#    The two heaviest phases each split into 6 parallel chunks:
#      - CharPolyAgree/Chunk_0..5.v    710-prime CRT checks
#      - MaynardVerify/M2_0..5.v       42x42 M2 spec cross-check (7 rows each)
coq_makefile -f _CoqProject -o Makefile
make -j

# 4. Verify the end-to-end theorem has no project-specific axioms.
#    `maynard_M105_certified` is the recommended target: it conjoins
#    `all_match_M{1,2}Z = true` (the Z-level closed-form input-matrix
#    check), `M{1,2}_spec_rat_eq` (the Z-level <-> rat-level paper-form
#    bridge from MaynardSpecBridge), and the eigenvalue bound, so a
#    single Print Assumptions covers the full pipeline. The
#    spectral-only sibling `maynard_eigenvalue_S1` reports the same
#    assumption set minus the matrix-pinning bool facts.
coqtop -Q theories/S1 PrimeGapS1 \
  -l theories/S1/Cert.v -batch \
  -e 'Print Assumptions maynard_M105_certified.'
# Expected: only Rocq's standard PrimInt63 / Uint63Axioms primitive-integer
# interface (the footprint inherited by every vm_compute-driven proof).
# No project-specific axioms, no Admitted.

# Or: a single canonical "clean rebuild + Print Assumptions" script:
./verify.sh
```

## Trust base

The Rocq verification trusts only:
- Rocq's kernel, including its standard `PrimInt63` / `Uint63Axioms`
  primitive-integer interface. This footprint is the unavoidable cost
  of any `vm_compute`-driven proof in modern Rocq and is listed by
  `Print Assumptions` on every `vm_compute`-using lemma in this
  project. **No project-specific axioms are introduced.**

There are zero `Axiom` or `Admitted` lemmas anywhere in the repository.
This includes the 42x42 input matrices: the headline
`maynard_M105_certified` conjoins (i) the Z-level cross-multiplication
match `all_match_M{1,2}Z = true` (`MaynardVerify.v`, vm_compute), (ii)
the rat-level paper-form bridge `M{1,2}_spec_rat_eq` from
`MaynardSpecBridge.v` (Qed, *Closed under the global context* — no
axioms at all, not even `Uint63`), and (iii) the eigenvalue bound. So a
single `Print Assumptions maynard_M105_certified` certifies that the
FLINT-shipped integer matrices `M1_int`, `M2_int` agree with the
rat-level paper-form `MaynardSpec.M{1,2}_entry` (which transcribes
Maynard's Lemma 8.2 character-for-character) and that the resulting
rational pencil has a real-algebraic eigenvalue strictly above `4/105`.

The basis itself is also kernel-pinned: `MaynardBasis.maynard_basis_spec`
certifies that the 42-element list contains exactly the multiset
`{(b, c) ∈ ℕ² : b + 2c ≤ 11}` (a reviewer reads only the predicate
`b + 2c ≤ 11`, not the literal list), and `maynard_basis_eq_witness`
pins the *ordering* to the FLINT-shipped indexing (a vm_compute-Qed,
needed because matrix rows/columns are read by integer index).

The FLINT layer is **not** in the trust base of the Rocq proof. It
serves only as (a) the candidate generator for the certificate data
and (b) an independent cross-check. If the FLINT layer shipped wrong
data on any of the *load-bearing* artefacts (the M1/M2 matrix entries
or the cleared characteristic polynomial), the build would fail at one
of the `vm_compute` checks. The IVT proof in `CertL1.v` evaluates
`charpoly_int` directly at `4/105` (sign read by `vm_compute`) and at
MathComp's `cauchy_bound` (sign from leading coefficient); no shipped
Sturm chain or sign-vector data is consumed.

See `SPEC_TO_PAPER.md` for a line-level mapping from the
`MaynardSpec.{compositions, cff, G_2, alpha, M1_entry, M2_entry}` definitions
back to arXiv:1311.4600 v3 §8.

## License

CC-BY-4.0. Source notebook: [arXiv:1311.4600v3](https://arxiv.org/abs/1311.4600).
