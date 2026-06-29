# Auditor's checklist

What an auditor needs to check to be convinced this development really
proves `M_{105} > 4`. Each row below is either **kernel-Qed** (the
auditor only confirms that the lemma statement reads as expected) or
**paper-side** (carried over from Maynard's published proof). Two
things are genuinely read by a human rather than machine-checked:

  - the **matrix transcription** — that the closed-form spec entries
    in `MaynardSpec.v` match Maynard's paper, and that they agree
    entrywise with the FLINT-shipped integer matrices (items 3–4);
  - the **high-level statement** — that the headline theorem really
    says `M_{105} > 4`.

Maynard references use the v3 / Annals numbering
([arXiv:1311.4600v3](https://arxiv.org/abs/1311.4600); Annals **181**
(2015), 383–413). `Print Assumptions` on either theorem below reports
*Closed under the global context* — no project-specific axioms, and,
since every reduction runs in stdlib `Z`, no native 63-bit primitives.

## The headline

The development proves `M_{105} > 4` in Maynard's eigenvalue form: the
constant is `k` times the largest eigenvalue of the generalized problem
`M_2 v = λ M_1 v`. The headline theorem
`MaynardEigen.maynard_M105_certified` (`MaynardEigen.v:372`) states,
with `C := algC`, `ratrM := map_mx (ratr : rat -> C)`,
`A_rat := invmx M1_rat *m M2_rat`, and `M105 := 105%:Q *: A_rat`:

```
  matches_closed_forms M105 /\
  exists lam : C, eigenvalue (ratrM M105) lam /\ (4 < lam).
```

The first conjunct is the matrix transcription: `M105` is the closed
form `105 · M1⁻¹ M2`, and the paper-form spec entries match the
FLINT-shipped integer matrices entrywise. The second exhibits a genuine
eigenvalue of the generalized problem strictly above `4`.

Its computational heart is a single integer Rayleigh inequality at a
shipped rational witness — the same matrices, witness, and quotient that
Maynard's Mathematica notebook evaluated, now reduced by the Rocq
kernel. Turning that quotient bound into a positive eigenvalue adds two
ingredients on top: a CRT-over-`Z` proof that `M_1` is positive
definite, and a Hermitian spectral bridge. The route uses no
intermediate-value argument, Sturm chain, or `realalg` (the
`faddeev-leverrier` branch takes the intermediate-value route instead).

## The checklist

Rows are in dependency order: matrix transcription, the Rayleigh
inequality (the notebook computation), `M_1` positive-definite via CRT,
the spectral bridge, then the composed headline.

| # | Claim | Maynard ref | Rocq backing |
|---|---|---|---|
| 1 | The 42-element basis is exactly the multiset `{(b, c) ∈ ℕ² : b + 2c ≤ 11}` | §8, paragraph defining `P_k` for `k = 11` | `MaynardBasis.maynard_basis_spec` (predicate match) + `maynard_basis_uniq` (no duplicates) + `maynard_basis_size = 42` |
| 2 | The literal 42-pair list matches the FLINT-shipped enumeration ordering | — (implementation choice; rows/columns are read by integer index) | `MaynardBasis.maynard_basis_eq_witness` (`vm_compute`) |
| 3 | The closed-form `M_{i,j}` formulas transcribe Maynard's matrix entries | Lemma 8.2 + eq. 8.4 (the formula `b! · G_{c,2}(n) / (n+b+2c)!` is correct for all `b ≥ 0` with `0! = 1`; no separate `b = 0` case — see `SPEC_TO_PAPER.md` §8) | **read** `MaynardSpec.{M1_entry, M2_entry, G_2, alpha, compositions, cff}` against the paper; line-level map in `SPEC_TO_PAPER.md` |
| 4 | **Matrix transcription.** The shipped 42×42 integer matrices `M1_int` / `M2_int`, scaled by the denominators `D_M1` / `D_M2`, agree with the paper-form spec entry-by-entry; `M105` is the closed form `105 · M1⁻¹ M2` | — (kernel cross-check + rat-level transcription equivalence) | `EigenBridge.matches_closed_forms` (`EigenBridge.v:38`) + `matches_closed_forms_M105` (`EigenBridge.v:45`); same facts as `Cert.M1_spec_eq_int` / `Cert.M2_spec_eq_int`, and the headline's first conjunct |
| 5 | **The notebook computation.** A 42-entry rational witness `v_witness ∈ ℚ^{42}` satisfies the strict Rayleigh bound `4 · vᵀM₁v < 105 · vᵀM₂v` at the paper-form spec matrices (and `vᵀM₁v > 0`, so the quotient is well-defined) | Lemma 8.3 inputs — `sup_F J_k(F)/I_k(F)` is at least the quotient at any individual `F` | `CertRayleigh.rayleigh_lt_main` (`CertRayleigh.v:402`), driven by `CertRayleigh.rayleigh_witness_holds` (`:114`) + `rayleigh_witness_M1_gt0` (`:107`), both `vm_compute` over `Z`; consumed inside `MaynardEigen` as the positivity input — see drill-down |
| 6 | `M_k` is `k` times the largest eigenvalue of the generalized problem `M_2 v = λ M_1 v`; so a generalized eigenvalue `> 4` certifies `M_{105} > 4` | **Lemma 8.3** (`M_k = k · sup_F J_k(F)/I_k(F)`, attained at the largest generalized eigenvalue) | **paper-side** — Maynard's Lemma 8.3 |
| 7 | `M_1` is positive definite, via a CRT-over-`Z` characteristic-polynomial sign argument: the integer char-poly of `M1_int` equals a shipped coefficient list whose signs strictly alternate, so all eigenvalues are `> 0` | Lemma 8.2 makes `M_1` a Gram matrix, hence PD | `M1CharPoly.char_poly_int_M1_eq` (`M1CharPoly.v:162`: `char_poly_int M1_int = cp_M1_value`) + `M1CharPoly.cp_M1_alternates` (`M1CharPoly.v:188`: `alternating_signs cp_M1_value`) ⟹ `M1PosDef` spectrum `> 0` |
| 8 | The CRT lift is deterministic, not probabilistic: each char-poly coefficient is pinned by agreement modulo 200 distinct primes (~2³⁰ each) whose product exceeds `4 ×` a Hadamard-style coefficient bound | — (kernel CRT; standard a-priori coefficient bound) | `CRTCheck.crt_reconstruct` (`CRTCheck.v:167`, needs `2·\|c−d\| < ∏ primes`) fed by `Bound.char_poly_int_coeff_bound` (`Bound.v:573`, Hadamard-style) and the `vm_compute`'d margin `4 * cp_bound < ∏ crt_primes_M1` (`M1CharPoly.v:153`); 200 primes + the 43-entry coefficient list in `WitnessM1CharPoly.{crt_primes_M1, cp_M1_value}`; primality / distinctness / `> 43` by `CRTFrame.{crt_primes_M1_all_prime, crt_primes_M1_NoDup, crt_primes_M1_gt43}` |
| 9 | The fast `O(n³)` Hessenberg modular char-poly used by the per-prime checks agrees with the slow, proven integer char-poly reduced mod `p` | — (algorithm correctness) | `ModularHess.char_poly_hess_sound` (`ModularHess.v:2246`), built from `ModularHess.hess_recurrence_sound` (`:2147`, the upper-Hessenberg leading-principal-minor determinant recurrence) and `ModularHess.hess_reduce_similar` (`:2213`, char-poly is conjugation-invariant), with `ModularFL.char_poly_modZ_sound` (`ModularFL.v:535`) as the bad-pivot fallback. The 200-prime mass check `CRTFrame.per_prime_hess_all` (`CRTFrame.v:166`) is sharded across 8 `CRTFrame_part*.v` for `make -j8` |
| 10 | **The spectral bridge.** A Hermitian matrix with a strictly positive value of its sesquilinear form on some vector has a strictly positive eigenvalue — this turns the positive Rayleigh value (item 5) into an eigenvalue `> 4` | variational principle behind Lemma 8.3 | `SpectralCrux.herm_crux` (`SpectralCrux.v:77`: `A \is hermsymmx -> 0 < (w *m A *m w^t*) 0 0 -> exists2 a, eigenvalue A a & 0 < a`), via mathcomp-analysis' spectral theorem over `algC`; combined with `M1PosDef.M1_rat_factor` (`M1PosDef.v:369`: a complex congruence factor `R \in unitmx`, `R^t* *m R = ratrM M1_rat`) to reduce the generalized problem to a standard one |
| 11 | The composed headline conjoins the matrix transcription with a witnessed eigenvalue `> 4` | **Lemma 8.3** | `MaynardEigen.maynard_M105_certified` (`MaynardEigen.v:372`) |

The headline conjoins item (4) and the eigenvalue-existence assembly
(items 5–10) into a single Qed. Items (1)–(3) and (6) are read
alongside it.

## The standalone Rayleigh theorem

`CertRayleigh.maynard_M105_certified_rayleigh` (`CertRayleigh.v:429`)
states `M_{105} > 4` the way the notebook does — the Rayleigh quotient
read directly off the matrices, without the eigenvalue reformulation.
It conjoins the matrix transcription (item 4) with the Rayleigh
inequality (item 5) and nothing else: its kernel obligations are the
matrix transcription and one integer `vm_compute`. It uses neither the
positive-definite / CRT certificate (items 7–9) nor the spectral bridge
(item 10), and exhibits no eigenvalue. The full headline adds the
eigenvalue characterization on top of the same computation.

## Drill-downs

**Inside item (4).** The matrix transcription factors through two
independently `Print Assumptions`-able Qeds:

  - `MaynardSpecBridge.M1_spec_rat_eq` (`:355`) and `M2_spec_rat_eq`
    (`:542`) — each says the rat-level paper-form spec equals a
    computation-friendly Z-pair form by pure rational arithmetic.
    Inspecting these confirms the paper-form transcription introduces no
    kernel axiom.
  - `MaynardVerify.Def.all_match_M1Z_true` (`:81`) and
    `MaynardVerify.all_match_M2Z_true` (`:89`) — 1764 + 1764
    cross-multiplied integer equalities by `vm_compute`. Inspecting
    these confirms exactly which integer arithmetic the kernel checks.
  - `Cert.D_M1_pos` / `Cert.D_M2_pos` (`Cert.v:35–36`) — the matrix
    denominator positivity inputs to the `qfrac_eq_div` lift inside
    `M{1,2}_spec_eq_int`.

**Inside item (5).** The Rayleigh row factors through the witness data
plus a handful of Qeds:

  - `CertRayleigh.rayleigh_witness_holds` (`:114`) — the integer
    inequality `4 · D_M2 · v_numᵀ M1_int v_num < 105 · D_M1 · v_numᵀ
    M2_int v_num` at the shipped scaled-integer witness `v_num`, closed
    by `vm_compute` reflexivity (~5 s, pure `Z`).
  - `CertRayleigh.rayleigh_witness_M1_gt0` (`:107`) — `v_numᵀ M1_int
    v_num > 0` (`num_M1 > 0`), by `vm_compute`.
  - `CertRayleigh.quad_cell_identity` (`:273`) — the per-cell algebraic
    identity `dm * vd² * (vi/vd · mij/dm · vj/vd) = vi · mij · vj` under
    nonzero hypotheses, sealed by `field`. Kept Qed-sealed so the bigop
    walk references it by name instead of inlining a fresh `field` term
    per cell.
  - `CertRayleigh.quad_spec_eq_Z` (`:280`) — the rat-level bigop ⇄ Z
    bridge `Z2rat D_M · Z2rat v_den² · quad_spec M_spec = Z2rat (quad
    M_int v_num)`: a `Z2rat_quad_eq_sum` invocation followed by two
    nested `eq_bigr` applications of `quad_cell_identity`. The
    specialisations `quad_M{1,2}_spec_eq_Z` apply it with the
    well-formedness hypotheses discharged by `M{1,2}_int_rows`,
    `M{1,2}_int_cols`, `D_M{1,2}_pos`, `@M{1,2}_spec_eq_int`.
  - `CertRayleigh.rayleigh_lift_generic` (`:379`) — an abstract
    Rayleigh-quotient lift: given two scaled-quad identities `Z2rat d_k
    · v² · q_k = Z2rat a_k` (k = 1, 2) and `4·d2·a1 < 105·d1·a2`, it
    deduces `4·q1 < 105·q2`. The abstraction keeps the `ring` calls
    operating on small abstract scalars.
  - `CertRayleigh.rayleigh_lt_main` (`:402`) — the rat-level bound
    `4 * quad_spec M1_spec_ij < 105 * quad_spec M2_spec_ij` surfaced by
    both theorems; a one-line `exact:` application of
    `rayleigh_lift_generic` to `quad_M{1,2}_spec_eq_Z` and
    `rayleigh_witness_holds_rat` (`:354`, the integer inequality lifted
    via `Z2rat_lt`).
  - `Witness_Rayleigh.v_witness` (`:39`) — the 42-entry rational witness,
    autogenerated by `python/build_quad_witness.py`; each entry a
    `(num, den) : Z × Z` pair in lowest terms. Verified slack `≈
    +2.07e-3` (relative margin `(105·vᵀM₂v − 4·vᵀM₁v)/vᵀM₁v`). The
    auditor inspects the file header for provenance and the `vm_compute`
    Qeds for the inequalities the kernel enforces.

An auditor who trusts the kernel reads only the headline (or the
standalone Rayleigh theorem); one partitioning trust between "rat-level
algebra" and "integer cross-check" inspects the sub-Qeds above.

For (3) — the one paper-conformance step that is read rather than
machine-checked — the line-level map in `SPEC_TO_PAPER.md` reduces it to
checking that ~30 lines of `MaynardSpec.v` match Maynard's eq. 8.4
character-for-character.

**Files behind the eigenvalue chain:** `SpectralCrux.v` (the variational
crux), `EigenBridge.v` (`M1_rat` / `M2_rat` / `A_rat` / `M105` +
`matches_closed_forms`), `CharPoly.v` and `IntPoly.v` (the list-`Z`
characteristic polynomial), `ModularFL.v` (Faddeev–LeVerrier mod `p`),
`ModularHess.v` (the fast Hessenberg pass), `Bound.v` (the coefficient
bound), `CRTCheck.v` (CRT uniqueness), `WitnessM1CharPoly.v` (the 200
primes and the coefficient list), `CRTFrame.v` + `CRTFrameDefs.v` +
`CRTFrame_part0..7.v` (the sharded per-prime check), `M1CharPoly.v`
(`char_poly_int M1_int = cp_M1_value`), `M1PosDef.v` (PD + the spectral
factor), and `MaynardEigen.v` (the assembled headline). The Rayleigh
core and its witness live in `CertRayleigh.v` / `Witness_Rayleigh.v`,
shared with the standalone theorem.
