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
| 3 | The closed-form `M_{i,j}` formulas transcribe Maynard's matrix entries | Lemma 8.2 + eq. 8.4 (the `b ≠ 0` caveat is documented in `SPEC_TO_PAPER.md`) | Read `MaynardSpec.{M1_entry, M2_entry, G_2, alpha, compositions, cff}` against the paper; line-level map in `SPEC_TO_PAPER.md` |
| 4 | The shipped 42×42 integer matrices `M1_int`, `M2_int` agree with that closed form | — (kernel cross-check) | `MaynardVerify.all_match_M1Z_true`, `MaynardVerify.all_match_M2Z_true` — 1764 + 1764 cross-multiplied integer equalities by `vm_compute` |
| 5 | The Z-level twin spec equals the rat-level paper-form spec (no formula divergence between the two transcriptions) | — (transcription equivalence) | `MaynardSpecBridge.M1_spec_rat_eq`, `MaynardSpecBridge.M2_spec_rat_eq` (Qed, *Closed under the global context* — no axioms at all) |
| 6 | The shipped char-poly equals `char_poly` of `A_int = M₁⁻¹·M₂·D_A` over ℤ | — (kernel cross-check) | `CRTLift.fl_eq_flint` + `CRTLift.matrix_identity_Z` (710-prime CRT lift, then Hadamard-style coefficient bound) |
| 7 | There exists a real-algebraic eigenvalue `λ > 4/105` of `A_rat = M₁⁻¹·M₂` | Proposition 4.3 / eq. 8.15 (the project's headline claim) | `Cert.maynard_eigenvalue_S1` — IVT on `char_poly_int` (= `char_poly` of `A_int` after sign hygiene), using mathcomp-real-closed's `poly_ivtoo` |
| 8 | `M_{105} = 105 · λ_max > 4` follows from the eigenvalue bound | **Lemma 8.3** (`M_k = k · sup_F (J_k(F)/I_k(F)) = k · λ_max`) | **paper-side** — refereed in the Annals paper, not formalised |

The headline `Cert.maynard_M105_certified` conjoins a *composed* form
of items (4) + (5) — the merged "paper-form `M_{i,j}` equals
`zrat(FLINT entry) / zrat(D)`" identity, factored through the helper
lemmas `Cert.M1_spec_match_FLINT` / `Cert.M2_spec_match_FLINT` (which
chain `MaynardSpecBridge.M{1,2}_spec_rat_eq` with
`MaynardVerify.all_match_M{1,2}Z_true` via a `qfrac_eq_div` lifting
helper) — together with item (7), into a single Qed. Items (1)–(3),
(6), and the standalone (4) / (5) Qeds remain separately verifiable
and are read by an auditor alongside the headline.

For (3) — the only paper-conformance step that is read rather than
machine-checked — the line-level map in `SPEC_TO_PAPER.md` reduces
it to checking that ~30 lines of `MaynardSpec.v` match Maynard's eq.
8.4 character-for-character.
