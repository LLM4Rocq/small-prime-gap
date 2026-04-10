# SPEC LAYER AUDIT: Maynard M_{105} > 4 eigenvalue bound

Auditor: Claude Opus 4.6 (automated)
Date: 2026-04-09
Scope: theories/S1/{Cert,Bridge,CharPoly,CharPolyHelpers,CertL1}.v

---

## 1. Headline theorem (`Cert.v :: maynard_eigenvalue_S1`)

**Statement:**
```
exists lambda : realalg,
  eigenvalue (map_mx ratr A_rat) lambda
  /\ (ratr (4%:Q / 105%:Q) : realalg) < lambda
```

where `A_rat := invmx (mat_int_to_rat M1_int D_M1 42) *m mat_int_to_rat M2_int D_M2 42`.

**Verdict: CORRECTLY STATED, modulo one semantic caveat.**

The statement says exactly what Maynard's argument needs: there exists a realalg eigenvalue of the 42x42 matrix `M1^{-1} * M2` strictly above `4/105`. The `eigenvalue` predicate is MathComp's standard one (from mxalgebra). The lifting via `map_mx ratr` correctly embeds the rational matrix into the real-closed field `realalg`.

**Axiom audit (via `Print Assumptions`):** The theorem depends on exactly 2 non-standard axioms:
- `sturm_count_correct` (L1: a root of the char poly exists above 4/105)
- `charpoly_int_eq_charpoly` (L2: the shipped integer polynomial equals the true char poly)

Neither `A_rat_unitmx` nor `maynard_bridge_L4` feed into the headline theorem. This is honest. The `eigenvalue_of_root_realalg` bridge (L3) is fully closed (`Qed`), proved in 2 lines via `map_char_poly` + `eigenvalue_root_char`. This usage is correct: `eigenvalue_root_char` gives `eigenvalue A a = root (char_poly A) a` over a field, and `map_char_poly` pushes `ratr` through `char_poly`.

**Caveat:** `invmx` is total in MathComp -- if `M1_rat` is not invertible, `A_rat` is the zero matrix and the theorem becomes vacuously about eigenvalues of the zero matrix. The `A_rat_unitmx` admit is honest but MUST be discharged for the result to have mathematical content. In practice M1 is SPD so this will hold; the team is aware.

---

## 2. Soundness of Bridge.v (0 admits, ~2036 lines)

**Grep for `Axiom`, `Parameter`, `Admitted`: ZERO matches.** Every lemma in Bridge.v ends with `Qed.` Bridge.v is genuinely admit-free.

**Key proved results and their correctness:**

- **`pol_to_polyralg_pneg/pnorm/padd/psub/pscale/pshift`**: All proved by structural induction. These are the foundational building blocks. Checked: the statements correctly relate `list Z` polynomial operations to `{poly realalg}` algebra. The `pnorm` invariance lemma (`pol_to_polyralg_pnorm`) is critical and correctly proved: `pnorm` strips trailing zeros, and `Poly` already normalizes, so both sides agree.

- **`prem_rmodp_rat`** (line 1107): This is the crown jewel -- our Brown-Traub `prem` equals MathComp's `rmodp` over `rat` after lifting. Proved by strong induction on fuel, with a careful size-decrease argument showing `prem_step` reduces polynomial degree. The proof is 150+ lines but structurally sound: it unfolds `redivp_rec` and matches it step-by-step against `prem_loop`.

- **`prem_rmodp_eq`** (line 1265): Lifts `prem_rmodp_rat` to `realalg` via `redivp_map`. Correct use of `redivp_map` from MathComp's polydiv.

- **`next_mod_scaled_morph`** (line 1290): Shows our `next_mod` equals MathComp's `qe_rcf_th.next_mod` up to a nonzero scalar. The scalar is `lc(Q)^{-rscalp}`, which accounts for the difference between our negated pseudo-remainder and MathComp's `- lc(Q)^d *: rmodp`. The `exists k, k != 0 /\ ...` formulation is the RIGHT weakening -- strict chain equality is indeed unprovable (chains differ by per-entry scalars), and the team correctly abandoned `mods_int_morph`.

- **`lead_coef_pol_to_polyralg`** (line 719): Proved that leading coefficient of the lifted polynomial equals the lifted `plead`. Proof by strengthened induction with an accumulator. This is the key bridge for sign-matching.

- **`variation_at_rat_morph` / `variation_at_pinf_morph`** (lines 1507, 1528): Proved that `variation` (Z-valued, skips zeros) equals `changes` (realalg, does not skip) under the "no zero entries" hypothesis. Correct: both reduce to `sgn_matches_prod`, which converts Z-sign comparisons to realalg-sign comparisons.

- **`sturm_count_above_correct`** (line 1759): The main bridge, proved using `taq_taq_itv` from `qe_rcf_th`. Usage is correct: `taq_taq_itv` requires `a < b`, all chain evals nonzero at `a` and `b`, and gives `taq (roots p a b) q = taq_itv a b p q`. With `q := 1`, `taq z 1 = size z` (proved in `taq_one`). The hypotheses are propagated honestly.

- **`sturm_count_above_pos_concrete`** (line 2004): Consumer wrapper that discharges `pderiv_morph`, `changes_pinfty_eq_at_cauchy_bound`, and `roots_in_cauchy_eq_filter` internally. Sound.

**One minor concern:** `rootsR_in_root` (line 1914) is proved with a case split on `P = 0` rather than carrying `P != 0` as a hypothesis. This works but is slightly fragile.

---

## 3. Faddeev-LeVerrier implementation (`CharPoly.v`)

**`char_poly_int`**: Correctly implements the FL recurrence as `fl_loop`. The accumulator builds coefficients low-to-high, and the final `++ [1]` appends the monic leading term. **Sanity tests pass via `vm_compute`** for 2x2, 3x3, and 10x10 identity matrices, which gives confidence the implementation is correct.

**`Z_to_int`**: Correctly maps `Z0 -> 0`, `Zpos p -> Posz (Pos.to_nat p)`, `Zneg p -> Negz (Pos.to_nat p - 1)`. The `Negz` encoding in MathComp uses `Negz n = -(n+1)`, so `Zneg p` (which is `-(Pos.to_nat p)`) maps to `Negz (Pos.to_nat p - 1)`. This is correct.

**`mat_int_to_rat`**: Defined as `\matrix_(i,j) (Z_to_int (mat_get M i j))%:~R / (Z_to_int D)%:~R`. Correct: each entry is the integer entry divided by the common denominator, lifted to `rat`.

**`pol_to_polyrat`**: `Poly (map (fun z => (Z_to_int z)%:~R) p)`. Correct low-to-high coefficient embedding.

**`char_poly_int_correct` (L2, the key Admitted lemma):**
```
pol_to_polyrat (char_poly_int M) = char_poly (mat_int_to_rat M D n)
```

**ISSUE: The stated form DROPS the D^n scaling factor.** The comment says the "intended precise form" is `pol_to_polyrat (char_poly_int M) = D^n *: char_poly (mat_int_to_rat M D n)`. Without the scaling, the lemma is FALSE for `D != 1`. This matters because `Cert.v` passes `D_M1` and `D_M2` (enormous integers) into `mat_int_to_rat`. The current statement only holds when `D = 1`, but the caller uses `D = D_M1` and `D = D_M2`.

**However**, looking at `Cert.v` more carefully: `A_rat = invmx(mat_int_to_rat M1_int D_M1 42) *m mat_int_to_rat M2_int D_M2 42`. The `charpoly_as_poly_realalg` is defined via `pol_to_polyrat charpoly_int` where `charpoly_int` from `Witness.v` is the integer-cleared char poly of `A_rat = M1^{-1} M2`. So the question is: does `char_poly_int_correct` need to handle the scaling? The L2 bridge `charpoly_int_eq_charpoly` in Cert.v simply states equality of the lifted `charpoly_int` and `char_poly A_rat` -- no scaling. This means L2 is implicitly asserting that the shipped `charpoly_int` is already the characteristic polynomial of the _rational_ matrix (no integer-clearing needed). This is a subtle design choice: `charpoly_int` is NOT `char_poly_int` applied to some integer matrix -- it is a pre-computed certificate. **The naming is misleading but the architecture is sound** if `charpoly_int` is verified independently.

---

## 4. CharPolyHelpers.v (0 admits)

Spot-checked:

- **`mat_int_to_rat_mzero`**: Proved via `matrixP`, reducing to `mat_get_mzero`. Correct.
- **`mat_int_to_rat_mscale`**: Proved via `matrixP` + `Z_to_int_mul` + `intrM`. Correct: `(c * a_ij) / D = c * (a_ij / D)` when factoring `c` out as a scalar.
- **`mat_int_to_rat_meye`**: Proved with diagonal/off-diagonal case split. Correct.
- **`mat_int_to_rat_madd`**: Requires extra `all_rows_len` hypotheses beyond what CharPoly.v declares. The lemma is STRONGER than the Admitted version in CharPoly.v (extra hypotheses). This is fine -- CharPoly.v's version (without `all_rows_len`) would need those hypotheses to be correct anyway.
- **`mtrace_int_to_rat`**: Proved via `mtrace_aux_diag_sum` + `raddf_sum`. Correct.

**`Z_to_int_mul` and `Z_to_int_add`**: Both proved by exhaustive case analysis on `Z` constructors. Correct and thorough.

---

## 5. CertL1.v: L1 consumer wiring

**3 remaining admits:**

1. **`shipped_chain_eq`**: `WitnessChain.sturm_chain = BrownTraub.sturm_chain charpoly_int`. This is a Z-level equality between a shipped certificate and a computed Sturm chain. It is a genuine obligation -- verifiable by CRT modular arithmetic (CRTCheck.v exists). NOT a cheat; it is the standard "certificate matches computation" check. Could potentially be discharged by `vm_compute` if the chain is small enough, but with degree-42 polynomials the chain entries have huge coefficients, making direct `vm_compute` infeasible. CRT is the right approach.

2. **`chain_is_mods`**: `map pol_to_polyralg (sturm_chain charpoly_int) = mods (pol_to_polyralg charpoly_int) (...)^'()`. This is the HARDEST remaining L1 admit. Bridge.v's `next_mod_scaled_morph` only gives scalar-multiple agreement, not strict equality. Two paths to close it: (a) prove the Brown-Traub PRS and MathComp's `mods` produce identical chains (hard: they use different scaling conventions), or (b) refactor the consumer to use a weaker "sign-equivalent chains" formulation. Path (b) is more promising but requires reworking `sturm_count_above_correct`.

3. **`no_root_at_cb`**: No chain polynomial has a root at or above the Cauchy bound. Should follow from the Cauchy bound property: for any root `r` of `p`, `|r| < cauchy_bound p`. This extends to all chain entries since they are divisors of `p` (in the `gcd`-chain sense). Provable but requires connecting divisibility in the `mods` chain with root containment.

**`Print Assumptions maynard_L1_concrete` also surfaces `signs_at_x0_shipped` and `signs_at_inf_shipped`** from CRTSigns.v. These are the CRT-verified sign equalities and are honest obligations (the CRT machinery to discharge them exists in CRTCheck.v/CRTSigns.v).

---

## 6. MathComp usage gaps

**Cayley-Hamilton** (`Cayley_Hamilton`): States `horner_mx A (char_poly A) = 0` for `A : 'M_{n'.+1}` over a `comNzRingType`. The team's L2 outline mentions using it for the FL abstract correctness (Step 3), which is correct: from `p(A) = 0` one can extract coefficient relations. However, the more direct route for FL is the adjugate identity.

**Adjugate identity** (`mul_mx_adj`): `A *m \adj A = (\det A)%:M`. This IS in MathComp. The team's CharPoly.v outline mentions "the adjugate identity `(lambda I - A) . adj(lambda I - A) = char_poly A . I`" for Step 3. In MathComp, `char_poly A = \det (char_poly_mx A)` where `char_poly_mx A = 'X%:M - A^polyC`. So `mul_mx_adj` applied to `char_poly_mx A` gives exactly `char_poly_mx A *m \adj(char_poly_mx A) = (char_poly A)%:M` over `{poly R}`. **This is the key identity the team needs for Step 3 and it is already in MathComp.** The team should use this more aggressively.

**`char_poly_trace` / `char_poly_det`**: Available and correctly documented in the team's survey. `char_poly_trace` gives the `n-1`-th coefficient; `char_poly_det` gives the constant term. These could provide sanity checks but are not directly needed for the FL proof.

**`eigenvalue_root_char`**: Used correctly in Cert.v's L3 proof. The statement `eigenvalue A a = root (char_poly A) a` is an iff over a fieldType, and `realalg` qualifies.

**`rootsR`, `roots_on_rootsR`**: Used correctly in Bridge.v's `roots_in_cauchy_eq_filter`. The `roots_on_rootsR` lemma gives that `rootsR p` captures all roots of `p` in `]-oo, +oo[`, which is exactly what is needed.

**`taq_taq_itv`**: Used correctly. The team correctly specializes it with `q := 1` to get the Sturm root count.

**Missing opportunity:** `mathcomp-real-closed` does NOT ship a ready-made "Sturm theorem" that directly gives root counts from sign variations. The `taq_taq_itv` lemma is the closest thing, and the team is using it. There is no shortcut that was missed.

---

## 7. Distance to closure

**L1 (Sturm count):** ~70% done. Bridge.v is fully proved. CertL1.v has 3 admits. `shipped_chain_eq` is closeable by CRT verification (infrastructure exists). `no_root_at_cb` is closeable with moderate effort (Cauchy bound + chain divisibility). **`chain_is_mods` is the blocker** -- it requires either proving strict PRS chain equality (hard) or refactoring the consumer (moderate). Estimate: 2-4 weeks of focused work.

**L2 (char poly correctness):** ~25% done. Step 0 is closed. Step 1 bridge lemmas are 5/6 proved in CharPolyHelpers.v (only `mat_int_to_rat_mmul` remains, plus they need to be wired back). Steps 2-4 are all Admitted. Step 3 (`fl_loop_rat_is_char_poly`) is the mathematical core and requires either Newton's identities (not in MathComp) or the adjugate expansion (available via `mul_mx_adj`). The placeholder definitions for `fl_M_int_k`, `fl_c_int_k`, etc. are dummy values that would need real implementations. **This is multi-week work.** However, there is a possible shortcut: if `charpoly_int` in Witness.v is treated as a pre-computed certificate (not derived from `char_poly_int`), then L2 reduces to showing `pol_to_polyrat charpoly_int = char_poly A_rat`, which could potentially be verified by a numerical/modular computation rather than proving the FL algorithm correct. Estimate: 4-8 weeks.

**Overall S1 headline theorem:** Depends on closing L1 (2-4 weeks) and L2 (4-8 weeks). The architecture is sound, the proof obligations are honestly stated, and no hidden axioms or cheats were found.
