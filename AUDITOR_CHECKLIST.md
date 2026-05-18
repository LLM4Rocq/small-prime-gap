# Auditor's checklist

What an auditor must verify to be convinced this Rocq development
genuinely proves `M_{105} > 4`. Each row is either **kernel-Qed by
Rocq** (the auditor only checks the lemma statement reads as
expected, and that `Print Assumptions` reports *Closed under the
global context* — for the whole proof chain, no `PrimInt63` /
`Uint63Axioms` / `CarryType` primitives appear either; this proof
performs every reduction in `Z`-arithmetic, not native 63-bit
arithmetic) or **paper-side** (carried over from Maynard's
published proof). Maynard references use the v3 / Annals
numbering ([arXiv:1311.4600v3](https://arxiv.org/abs/1311.4600);
Annals **181** (2015), 383–413).

The proof is the **Rayleigh-quotient witness route**: it evaluates a
single Rayleigh quotient at a shipped 42-entry rational witness
vector `v_witness` and shows it exceeds the threshold `4 / 105`.
There is no eigenvalue computation, no characteristic polynomial,
no IVT, no Sturm chain, and no Chinese-remainder lift anywhere in
the development. The headline theorem
`CertQuad.maynard_M105_certified_alt` is `Qed` and reports
*Closed under the global context* — zero axioms, including zero
kernel primitives. There are no `Admitted`, no `Axiom`, and no
`Parameter` declarations anywhere in `theories/S1/`.

| # | Claim | Maynard ref | Rocq backing |
|---|---|---|---|
| 1 | The 42-element basis is exactly the multiset `{(b, c) ∈ ℕ² : b + 2c ≤ 11}` | §8, paragraph defining `P_k` for `k = 11` | `MaynardBasis.maynard_basis_spec` (predicate match) + `maynard_basis_uniq` (no duplicates) + `maynard_basis_size = 42` |
| 2 | The literal 42-pair list matches the FLINT-shipped enumeration ordering | — (implementation choice; rows/columns are read by integer index) | `MaynardBasis.maynard_basis_eq_witness` (`vm_compute` Qed) |
| 3 | The closed-form `M_{i,j}` formulas transcribe Maynard's matrix entries | Lemma 8.2 + eq. 8.4 (the formula `b! · G_{c,2}(n) / (n+b+2c)!` is correct for all `b ≥ 0` with `0! = 1`; no separate `b = 0` case — see `SPEC_TO_PAPER.md` §8) | Read `MaynardSpec.{M1_entry, M2_entry, G_2, alpha, compositions, cff}` against the paper; line-level map in `SPEC_TO_PAPER.md` |
| 4 | The shipped 42×42 integer matrices `M1_int` / `M2_int`, scaled by the common denominators `D_M1` / `D_M2`, agree with the paper-form spec entry-by-entry: `M_{i,j}_spec = Z2rat(M_int[i][j]) / Z2rat(D_M)` for `i, j < 42` | — (kernel cross-check + rat-level transcription equivalence, composed) | `Cert.M1_spec_eq_int`, `Cert.M2_spec_eq_int` — surfaced directly in the headline `CertQuad.maynard_M105_certified_alt` |
| 5 | A 42-entry rational witness vector `v_witness ∈ ℚ^{42}` satisfies the strict Rayleigh-quotient bound `4 · vᵀM₁v < 105 · vᵀM₂v` at the paper-form spec matrices (and `vᵀM₁v > 0`, so the quotient is well-defined) | Lemma 8.3 inputs — the supremum of `J_k(F)/I_k(F)` is at least the quotient at any individual `F` | `CertQuad.rayleigh_witness_holds` (`vm_compute` Qed, ~5 s, *Closed under the global context*) plus `CertQuad.rayleigh_witness_M1_positive` (similarly Closed); both lifted to the rat-level inequality `4 * quad_spec M1_spec_ij < 105 * quad_spec M2_spec_ij` by `CertQuad.rayleigh_lt_main` (`Qed`, *Closed under the global context*) — see drill-down for item 5 |
| 6 | `M_{105} > 4` follows from item (5) via Lemma 8.3 | **Lemma 8.3** (`M_k = k · sup_F J_k(F)/I_k(F)`) | **paper-side** — Maynard's Lemma 8.3 says `M_k` is `k` times the supremum of `J_k(F)/I_k(F)` over an admissible function space; the supremum is at least any individual quotient |

The headline `CertQuad.maynard_M105_certified_alt` conjoins items (4)
and (5) into a single Qed. Items (1)–(3) and (6) are read alongside
the headline.

**Drill-down inside item (4).** `M{1,2}_spec_eq_int` factors through
two independently-`Print Assumptions`-able Qeds, both *Closed under
the global context*:

  - `MaynardSpecBridge.M1_spec_rat_eq` and `M2_spec_rat_eq` — *Closed
    under the global context, no axioms at all*. Each says the
    rat-level paper-form spec equals a computation-friendly Z-pair
    form by pure rational arithmetic. Inspecting these confirms the
    paper-form transcription introduces no kernel axiom.
  - `MaynardVerify.Def.all_match_M1Z_true` and
    `MaynardVerify.all_match_M2Z_true` — 1764 + 1764 cross-multiplied
    integer equalities by `vm_compute`. Both *Closed under the global
    context*. Inspecting these confirms exactly which integer
    arithmetic is verified by the kernel.
  - `Cert.D_M1_pos` and `Cert.D_M2_pos` — `vm_compute` `Qed` on `Z`,
    *Closed under the global context*. The matrix denominator
    positivity inputs to the `qfrac_eq_div` lift inside
    `M{1,2}_spec_eq_int`.

**Drill-down inside item (5).** The Rayleigh-witness row factors
through six independently-`Print Assumptions`-able Qeds plus the
shipped witness data, all *Closed under the global context*:

  - `CertQuad.rayleigh_witness_holds` — the integer Rayleigh
    inequality `4 · D_M2 · v_numᵀ M1_int v_num < 105 · D_M1 · v_numᵀ
    M2_int v_num` at the shipped scaled-integer witness `v_num`,
    closed by `vm_compute` reflexivity in ~5 s. *Closed under the
    global context*: pure-Z arithmetic, no `Uint63` primitives.
  - `CertQuad.rayleigh_witness_M1_positive` — `v_numᵀ M1_int v_num >
    0`, closed by `vm_compute`. *Closed under the global context*.
  - `CertQuad.quad_cell_identity` — the per-cell algebraic identity
    `dm * vd^2 * (vi/vd * (mij/dm) * (vj/vd)) = vi * mij * vj` under
    nonzero hypotheses, Qed-sealed by `field`. *Closed under the
    global context*. Kept Qed-sealed at top level so the bigop walk
    in `quad_spec_eq_Z` references it by name instead of inlining a
    fresh `field` proof term per cell.
  - `CertQuad.quad_spec_eq_Z` — the rat-level bigop ⇄ Z bridge
    `Z2rat D_M * Z2rat v_den^2 * quad_spec M_spec = Z2rat (quad
    M_int v_num)`. Structurally a `Z2rat_quad_eq_sum` invocation
    followed by two nested `eq_bigr` applications of
    `quad_cell_identity`. `Qed`, *Closed under the global context*.
    The specialisations `quad_M{1,2}_spec_eq_Z` (also Closed)
    apply it with the well-formedness hypotheses discharged by
    `M{1,2}_int_rows`, `M{1,2}_int_cols`, `D_M{1,2}_pos`, and
    `@M{1,2}_spec_eq_int`.
  - `CertQuad.rayleigh_lift_generic` — an abstract Rayleigh-quotient
    lift over a section in `CertQuad.v`. Given two scaled-quad
    identities `Z2rat d_k * v^2 * q_k = Z2rat a_k` (k = 1, 2) and
    the integer inequality `4·d2·a1 < 105·d1·a2`, it deduces
    `4·q1 < 105·q2`. `Qed`, *Closed under the global context*. The
    abstraction keeps the `ring` calls inside operating on small
    abstract scalars instead of the concrete `quad_spec
    M{1,2}_spec_ij` bigops.
  - `CertQuad.rayleigh_lt_main` — the rat-level Rayleigh-quotient
    bound `4 * quad_spec M1_spec_ij < 105 * quad_spec M2_spec_ij`
    that the headline surfaces. A one-line `exact:` application of
    `rayleigh_lift_generic` to `quad_M{1,2}_spec_eq_Z` and
    `rayleigh_witness_holds_rat` (the integer inequality lifted via
    `Z2rat_lt`). `Qed`, *Closed under the global context*.
  - `Witness_Quad.v_witness` — the 42-entry rational witness vector
    itself, autogenerated by `python/build_quad_witness.py`. Each
    entry is a `(num, den) : Z × Z` pair in lowest terms. Verified
    slack `≈ +2.07e-3` (the relative margin
    `(105·vᵀM₂v − 4·vᵀM₁v)/vᵀM₁v` over the rationals). The auditor
    inspects the file header for the generator's provenance and
    the `vm_compute` Qeds for the inequalities the kernel enforces.

An auditor who trusts the kernel reads only the composed headline.
An auditor partitioning trust between "rat-level algebra" and
"integer cross-check" inspects the sub-Qeds; both groups are axiom-
free.

For (3) — the only paper-conformance step that is read rather than
machine-checked — the line-level map in `SPEC_TO_PAPER.md` reduces
it to checking that ~30 lines of `MaynardSpec.v` match Maynard's eq.
8.4 character-for-character.
