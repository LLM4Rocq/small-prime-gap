# Auditor's checklist

What an auditor must verify to be convinced this Rocq development
genuinely proves `M_{105} > 4`. Each row is either **kernel-Qed by
Rocq** (the auditor only checks the lemma statement reads as
expected, and that `Print Assumptions` is empty / `PrimInt63.*` /
`Uint63Axioms.*` only) or **paper-side** (carried over from
Maynard's published proof). Maynard references use the v3 / Annals
numbering ([arXiv:1311.4600v3](https://arxiv.org/abs/1311.4600);
Annals **181** (2015), 383–413).

| # | Claim | Maynard ref | Rocq backing |
|---|---|---|---|
| 1 | The 42-element basis is exactly the multiset `{(b, c) ∈ ℕ² : b + 2c ≤ 11}` | §8, paragraph defining `P_k` for `k = 11` | `MaynardBasis.maynard_basis_spec` (predicate match) + `maynard_basis_uniq` (no duplicates) + `maynard_basis_size = 42` |
| 2 | The literal 42-pair list matches the FLINT-shipped enumeration ordering | — (implementation choice; rows/columns are read by integer index) | `MaynardBasis.maynard_basis_eq_witness` (`vm_compute` Qed) |
| 3 | The closed-form `M_{i,j}` formulas transcribe Maynard's matrix entries | Lemma 8.2 + eq. 8.4 (the formula `b! · G_{c,2}(n) / (n+b+2c)!` is correct for all `b ≥ 0` with `0! = 1`; no separate `b = 0` case — see `SPEC_TO_PAPER.md` §8) | Read `MaynardSpec.{M1_entry, M2_entry, G_2, alpha, compositions, cff}` against the paper; line-level map in `SPEC_TO_PAPER.md` |
| 4 | The shipped 42×42 integer matrices `M1_int` / `M2_int`, scaled by the common denominators `D_M1` / `D_M2`, agree with the paper-form spec entry-by-entry: `M_{i,j}_spec = Z2rat(M_int[i][j]) / Z2rat(D_M)` for `i, j < 42` | — (kernel cross-check + rat-level transcription equivalence, composed) | `Cert.M1_spec_eq_int`, `Cert.M2_spec_eq_int` — surfaced directly in the headline `Cert.maynard_M105_certified` |
| 5 | The shipped char-poly equals `char_poly` of `A_int = M₁⁻¹·M₂·D_A` over ℤ | — (kernel cross-check) | `CRTLift.fl_eq_flint` + `CRTLift.matrix_identity_Z` (710-prime CRT lift, then Hadamard-style coefficient bound) |
| 6 | There exists a real-algebraic eigenvalue `λ > 4/105` of `A_rat = M₁⁻¹·M₂` | Proposition 4.3 / eq. 8.15 (the project's headline claim) | `Cert.maynard_eigenvalue_S1` — IVT on `char_poly_int` (= `char_poly` of `A_int` after sign hygiene), using mathcomp-real-closed's `poly_ivtoo` |
| 7 | `M_{105} = 105 · λ_max > 4` follows from the eigenvalue bound | **Lemma 8.3** (`M_k = k · sup_F (J_k(F)/I_k(F)) = k · λ_max`) | **paper-side** — refereed in the Annals paper, not formalised |

The headline `Cert.maynard_M105_certified` conjoins items (4) and (6)
into a single Qed.  Items (1)–(3), (5), and (7) are read alongside
the headline.

**Drill-down inside item (4).**  `M{1,2}_spec_eq_int` factors through
two independently-`Print Assumptions`-able Qeds:

  - `MaynardSpecBridge.M{1,2}_spec_rat_eq` — *Closed under the global
    context, no axioms at all*.  Says the rat-level paper-form spec
    equals a computation-friendly Z-pair form by pure rational
    arithmetic.  Inspecting this confirms the paper-form
    transcription introduces no kernel axiom; `Uint63` enters the
    trust base only through the FLINT cross-check below.
  - `MaynardVerify.all_match_M{1,2}Z_true` — 1764 + 1764
    cross-multiplied integer equalities by `vm_compute`.  Reports the
    standard `PrimInt63` / `Uint63Axioms` footprint.  Inspecting this
    confirms exactly which integer arithmetic is verified by the
    kernel.

An auditor who trusts the kernel reads only the composed headline.
An auditor partitioning trust between "rat-level algebra" and "Uint63
cross-check" inspects the two sub-Qeds.

For (3) — the only paper-conformance step that is read rather than
machine-checked — the line-level map in `SPEC_TO_PAPER.md` reduces
it to checking that ~30 lines of `MaynardSpec.v` match Maynard's eq.
8.4 character-for-character.
