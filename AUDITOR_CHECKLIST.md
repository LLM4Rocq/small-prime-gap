# Auditor's checklist

What an auditor must verify to be convinced this Rocq development
genuinely proves `M_{105} > 4`. Each row is either **kernel-Qed by
Rocq** (the auditor only checks the lemma statement reads as
expected, and that `Print Assumptions` is empty / `PrimInt63.*` /
`Uint63Axioms.*` only) or **paper-side** (carried over from
Maynard's published proof). Maynard references use the v3 / Annals
numbering ([arXiv:1311.4600v3](https://arxiv.org/abs/1311.4600);
Annals **181** (2015), 383–413).

This checklist describes the **pencil-determinant route** that lives
on this `quad` branch.  The canonical proof on `main` follows a
Sturm/IVT route with a different items 5–6; see the equivalent
checklist on that branch.  Both routes share items 1–4 and 7 and end
with the same headline trust contract.

| # | Claim | Maynard ref | Rocq backing |
|---|---|---|---|
| 1 | The 42-element basis is exactly the multiset `{(b, c) ∈ ℕ² : b + 2c ≤ 11}` | §8, paragraph defining `P_k` for `k = 11` | `MaynardBasis.maynard_basis_spec` (predicate match) + `maynard_basis_uniq` (no duplicates) + `maynard_basis_size = 42` |
| 2 | The literal 42-pair list matches the FLINT-shipped enumeration ordering | — (implementation choice; rows/columns are read by integer index) | `MaynardBasis.maynard_basis_eq_witness` (`vm_compute` Qed) |
| 3 | The closed-form `M_{i,j}` formulas transcribe Maynard's matrix entries | Lemma 8.2 + eq. 8.4 (the formula `b! · G_{c,2}(n) / (n+b+2c)!` is correct for all `b ≥ 0` with `0! = 1`; no separate `b = 0` case — see `SPEC_TO_PAPER.md` §8) | Read `MaynardSpec.{M1_entry, M2_entry, G_2, alpha, compositions, cff}` against the paper; line-level map in `SPEC_TO_PAPER.md` |
| 4 | The shipped 42×42 integer matrices `M1_int` / `M2_int`, scaled by the common denominators `D_M1` / `D_M2`, agree with the paper-form spec entry-by-entry: `M_{i,j}_spec = Z2rat(M_int[i][j]) / Z2rat(D_M)` for `i, j < 42` | — (kernel cross-check + rat-level transcription equivalence, composed) | `Cert.M1_spec_eq_int`, `Cert.M2_spec_eq_int` — surfaced directly in the headline `CertPencil.maynard_M105_certified_pencil` |
| 5 | The shipped determinant numerals match `det(M1_int)` and `det(pencil_mat_int)` (where `pencil_mat_int := pencil_int_clean = D_pencil_clean · (4·M1_rat − 105·M2_rat)` is the *clean* integer pencil; per-entry cross-check `D_M1·D_M2·pencil_int_clean[i,j] = D_pencil_clean·(4·D_M2·M1_int[i,j] − 105·D_M1·M2_int[i,j])` ties it to the FLINT data) over ℤ | — (kernel cross-check) | `CRTPencilCheck.det_M1_int_eq` and `CRTPencilCheck.D_pencil_int_eq` — both 710-prime CRT lifts on the SAME `crt_product_710` (the clean pencil's determinant is 2613 bits, well within the 710-prime product's ~21300-bit headroom), each composing per-prime modular agreement with a closed-form Hadamard coefficient bound; plus `PencilCleanGrid.all_pencil_clean_match_true` (1764-cell `vm_compute` Qed) for the per-entry cross-check |
| 6 | There exists a real-algebraic eigenvalue `λ > 4/105` of `A_rat = M₁⁻¹·M₂` | Proposition 4.3 / eq. 8.15 (the project's headline claim) | `CertPencil.maynard_eigenvalue_S1_pencil` — `DetPencil.det_pencil` identity (`det(λ M₁ − M₂) = det M₁ · char_poly(M₁⁻¹M₂)(λ)`) combined with the integer-determinant signs of (5), then IVT on `char_poly A_rat` via mathcomp-real-closed's `poly_ivtoo` and Cauchy bound |
| 7 | `M_{105} = 105 · λ_max > 4` follows from the eigenvalue bound | **Lemma 8.3** (`M_k = k · sup_F (J_k(F)/I_k(F)) = k · λ_max`) | **paper-side** — refereed in the Annals paper, not formalised |

The headline `CertPencil.maynard_M105_certified_pencil` conjoins
items (4) and (6) into a single Qed.  Items (1)–(3), (5), and (7)
are read alongside the headline.

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

**Drill-down inside item (5).**  The determinant cross-checks
factor through:

  - `CRTPencilChecksProof.check_M1_det_710_true` and
    `CRTPencilChecksProof.check_pencil_det_710_true` — 710 + 710
    per-prime `vm_compute` Qeds comparing `List.nth 0 (char_poly_mod
    p _) 0` against `Z_to_mod63 p (det_*_value)`.  Both run against
    the same 710-prime list (`crt_primes_all` from
    `CharPolyAgree/Def.v`).  Roughly ten-minute cached vm_compute on
    the clean pencil; reports the standard `PrimInt63` /
    `Uint63Axioms` footprint.
  - `PencilCleanGrid.all_pencil_clean_match_true` — 1764-cell
    `vm_compute` Qed for the per-entry cross-check
    `D_M1·D_M2·pencil_int_clean[i,j] =
    D_pencil_clean·(4·D_M2·M1_int[i,j] − 105·D_M1·M2_int[i,j])`,
    tying the shipped `pencil_int_clean` literal (from
    `Witness_PencilClean.v`) to the FLINT-shipped M1/M2 data.
    ~30 s cached vm_compute; same `PrimInt63` / `Uint63Axioms`
    footprint.
  - `CRTPencilM1Bound.crt_bound_M1_sufficient_literal` and
    `CRTPencilPencilBound.crt_bound_pencil_sufficient_literal` —
    `vm_compute` discharges of `2·bound + 2·|literal| <
    crt_product_710` for each determinant (clean pencil's bound is
    5830 bits, well under the ~21300-bit `crt_product_710`).  The
    shipped bound literals `fl_coeff_bound_{M1,pencil}_value` are
    precomputed (`Witness_M1Bound.v`, `Witness_PencilBound.v`) and
    tied back via `vm_compute` equality to the closed-form
    `fl_coeff_bound 42 (max_abs_entry _)`.

An auditor who trusts the kernel reads only the composed headline.
An auditor partitioning trust between "rat-level algebra" and
"Uint63 cross-check" inspects the per-step sub-Qeds.

For (3) — the only paper-conformance step that is read rather than
machine-checked — the line-level map in `SPEC_TO_PAPER.md` reduces
it to checking that ~30 lines of `MaynardSpec.v` match Maynard's eq.
8.4 character-for-character.

For (6) — the determinant-pencil identity `DetPencil.det_pencil` is a
generic mathcomp-algebra fact (`\det (l *: M₁ − M₂) = \det M₁ ·
(char_poly (M₁⁻¹ *m M₂)).[l]` for `M₁` invertible).  An auditor
verifies it reads as expected; its proof is one line.
