# Mathematical Audit: Maynard `M_{105} > 4` Rocq Formalization

**Auditor:** Senior analytic-number-theory / linear-algebra reviewer
**Date:** 2026-04-27
**Scope:** Mathematical content of the Rocq formalization at `/home/rocq/prime_gap/`,
cross-checked against Maynard, *Small gaps between primes* (arXiv:1311.4600,
v1 Lemmas 7.1/7.2/7.3 ≡ v3 Lemmas 8.1/8.2/8.3, Annals 181 (2015) 383–413).

## Executive verdict

The formalized theorem `maynard_eigenvalue_S1` (file `theories/S1/Cert.v`)
is mathematically sound and does what the README claims. Concretely, the
proof establishes:

> ∃ λ ∈ realalg, λ is an eigenvalue of `A_rat = M1⁻¹ M2 ∈ ℚ^{42×42}` (lifted to the
> real algebraic numbers) and λ > 4/105.

The closed-form Beta–integral input matrices `M1` and `M2` are kernel-checked
entry-by-entry against a Rocq transcription of Maynard's Lemma 7.2 / 8.2
(`theories/S1/MaynardSpec.v` + `MaynardVerify.v`), and that transcription
matches the paper line-by-line. The IVT-based root-existence argument is correct
(`P(4/105) < 0` and `P(cauchy_bound) > 0` give a real root in between, hence a
real algebraic eigenvalue of `A_rat`). The CRT lift used to bridge the FLINT
witness polynomial to `char_poly A_rat` is sound. There are zero `Axiom` /
`Admitted` declarations, and `Print Assumptions maynard_eigenvalue_S1` returns
only the standard Rocq `Uint63Axioms.*` primitives (confirmed live during
this audit by running `coqtop -batch`).

Caveats — none of which threaten soundness, but they should be stated
explicitly when the theorem is presented as a replacement for the
Mathematica notebook:

1. The theorem produces *some* real eigenvalue > 4/105, not "the largest
   eigenvalue". Bridging that to Maynard's `M_{105} > 4` requires the
   well-known Lemma 7.3 / 8.3 (`max_F (J_k(F)/I_k(F)) = λ_max(M1⁻¹M2)`) and
   the simple monotonicity step `λ_max ≥ any real eigenvalue`. Neither is
   formalized in Rocq. The REPORT.md §1.4 already discloses this honestly;
   I confirm it is the only mathematical gap.

2. The `M2` in this project is the per-coordinate matrix
   `J_k^{(1)}` (single `m`), not `Σ_m J_k^{(m)}`. Because `F` is symmetric
   the `Σ_m` is just `k · J_k^{(1)}`, so `M_k = k · λ_max(M1⁻¹·M2)` —
   exactly what the proof statement is set up to consume. Worth pointing
   out because someone reading only the headline could think `M_k = λ_max`.

I would extend a high level of assurance to this proof. The combination
of (a) the kernel-level cross-check of `M1`, `M2` against the closed forms,
(b) the 710-prime CRT lift of the characteristic polynomial, (c) the
double-checked Sturm chain (FLINT + Rocq), and (d) the standard MathComp
`poly_ivtoo` for the final root extraction, is a substantially stronger
guarantee than Maynard's original Mathematica notebook.

## Findings, by severity

### Critical
None.

### Major

**M-1. The theorem statement is "exists eigenvalue > 4/105", not "λ_max > 4/105".**
*Statement:* `Cert.v:109–112` proves `∃ λ : realalg, eigenvalue (...) λ ∧ ratr(4/105) < λ`.
This is *weaker* than `λ_max > 4/105`. To get `M_{105} > 4`, one needs
Maynard's Lemma 7.3 / 8.3 — `M_k = k · λ_max(M1⁻¹M2)` — together with
`λ_max ≥ any real eigenvalue`. Neither step is in the Rocq layer.
*Why it matters:* A casual reader of the headline might think `M_{105} > 4`
is itself fully formalized. It is not. The bridging steps are well known
and appear in the paper as a single named lemma (8.3), but a downstream
formalization of Maynard's proof of bounded gaps would still need to
formalize them.
*Why it is not Critical:* (i) Lemma 8.3 is genuinely a one-paragraph fact
(Lagrange multipliers + symmetry + positive definiteness). (ii) The
forward direction "exists real eigenvalue > 4/105 ⟹ λ_max > 4/105" is
trivial (max ≥ any). (iii) The Rocq formalization `λ ∈ realalg` is real
algebraic, so we genuinely have a real eigenvalue, not a complex one.
(iv) REPORT.md §1.4 discloses this gap explicitly.
*Suggested fix:* Either (a) formalize Lemma 7.3 over rat (one short proof
in MathComp, `unitmx`+`mxalgebra`), or (b) restate the headline lemma to
include "for a 42×42 *symmetric positive-definite* pencil (M2, M1)" and
then point to Maynard for the remaining bridge.

### Minor

**Mn-1. `M2` is per-coordinate, not summed over `m`.**
*Statement:* `MaynardSpec.v:87–96` defines `M2_entry` as the integrand from
Maynard's Lemma 7.2 / 8.2 expression for `J_k^{(1)}(F)`, *not* `Σ_m J_k^{(m)}(F)`.
*Why it is OK:* By symmetry of `F` in `t_1, …, t_k` (Maynard p. 21–22 / p. 23),
all `J_k^{(m)}` are equal, so `Σ_m J_k^{(m)} = k · J_k^{(1)}`. Therefore
`λ_max(M1⁻¹ · M2_per_coord) = sup_F J_k^{(1)}/I_k = M_k / k`, which is
*exactly* the form `λ > 4/105 ⟺ M_k > 4` consumed by `Cert.v`. The factor
`k` is paid in the threshold, not in the matrix.
*Why it matters:* A reader might assume `M2` is `Σ_m`. The README and
REPORT do not call this out crisply. It is mathematically correct but
*notation-fragile*; in particular `flint_probe.py` lines 134–163 build
`M2` from `PrmeCalc` which is `J_k^{(1)}`, not `Σ_m J_k^{(m)}`.
*Suggested fix:* One sentence in REPORT.md §1.1 making this explicit.

**Mn-2. Maynard's `M_k = k · λ_max` (Lemma 7.3 / 8.3) is unformalized.**
*Statement:* The bridge `M_k = k · sup_F (J_k^{(1)}/I_k) = k · λ_max(M1⁻¹·M2)`
relies on Maynard's Lemma 7.3 / 8.3. This is not formalized.
*Why it is OK:* Standard linear algebra over a real field: for symmetric
PD `M1` and symmetric `M2` over ℝ, `sup_a (aᵀ M2 a) / (aᵀ M1 a)` is the
top eigenvalue of `M1⁻¹ M2` (Lagrange multipliers).
*Why it matters:* See M-1.

**Mn-3. Symmetry / positive-definiteness of `M1`, `M2` is not formally
established inside Rocq.**
*Statement:* The headline does not need it (the IVT root-existence proof is
sign-only), but Lemma 8.3 (the bridge to `M_k`) does.
*Why it is OK:* Maynard's M1 and M2 *are* symmetric PD by construction — they
are Gram matrices of `L^2`-inner products on a 42-dim subspace of polynomials.
Maynard says so on p. 22 / p. 23.
*Suggested fix:* If M-1 is closed by formalizing Lemma 8.3, symmetry-PD of
the kernel-checked `M1`, `M2` would also need formalization. Symmetry is
visible at the entry-formula level (`M1_entry bi ci bj cj = M1_entry bj cj
bi ci` because the formula is symmetric in (b_i, c_i) ↔ (b_j, c_j)).
Positive-definiteness is harder but available through `aᵀ M1 a = ∫ F² ≥ 0`.

**Mn-4. The shipped Sturm chain *beyond entry 0* is computationally checked
but not used by the soundness proof.**
*Statement:* `CertL1.maynard_L1_concrete` uses only `signs_at_x0[0] = -1`
(= sign of `charpoly_int(4/105)`) and `signs_at_inf[0] = +1` (= sign of
leading coef). The remaining entries of the chain and the count
`V(4/105) − V(+∞) = 1` are computed (`witness_root_count`) but the IVT
proof does not consume them.
*Why it is OK:* Mathematically the IVT alone is enough for "exists root
> threshold". The full Sturm count is stronger (gives an exact count of
roots above the threshold), but unnecessary here. REPORT.md §3.4 says so.
*Why it matters:* From a *formalization completeness* perspective, the
expensive `WitnessChain.sturm_chain` data and the `CRTSigns` cross-check
are not on the critical path. A leaner version of the proof could omit
them entirely and the headline would still hold. This is informative for
follow-on work that wants to extend to the Sturm-count regime.

**Mn-5. The IVT comparison endpoint `cauchy_bound` is a *strict* upper
bound only because `ge_cauchy_bound` says all roots lie in [-cb, +cb]
strictly when `cb` is the MathComp definition `1 + Σ|c_i|/|lc|`.**
*Statement:* `CertL1.charpoly_pos_at_cb` derives `P(cb) > 0` from
`sgp_pinftyP` plus `ge_cauchy_bound`. The latter, by MathComp's signature
(`{in [cauchy_bound p, +∞[, ¬ root p _}`), tells us no root lives at or
above `cb`. So `cb` itself is *not* a root and `sgr P(cb) = sgr lc(P) = +1`.
*Why it is OK:* Verified directly. Independent of the integer convention
on the polynomial.

### Note (positive findings)

**N-1. `MaynardSpec.G_2 n k` is a faithful transcription of Maynard's
`G_{n,2}(k)` (Lemma 7.1 / 8.1).**
Manual check against Maynard's `G_{b,j}(x) = b! Σ_{r=1}^b C(x,r) Σ_{b_1,…,b_r ≥ 1, sum=b}
Π_i (jb_i)!/b_i!`: the Rocq prefactor `n! · …` is absorbed into `cff`, the
`r=1` term gives `k·(2n)!`, and `r ≥ 2` decomposes as `Σ_{i=1}^{n-1} C(k, i+1)
Σ_a cff(a, n)` where `a = (b_1,…,b_i)`, `b_{i+1} = n − sumn(a)`, all `b_j ≥ 1`,
sum = n. Quick sanity checks:
- `G_{0,2}(x) = 1` (Rocq: `if n = 0 then 1`). Note: Maynard's stated formula
  gives `0! · (empty sum) = 0`, but his Lemma 7.1 / 8.1 actually requires
  `b ≥ 0` and `b = 0` is the implicit `1` case; the Rocq spec correctly
  branches.
- `G_{1,2}(k) = 2k`. Rocq: `k · 2! + 0 = 2k`. ✓
- `G_{2,2}(k) = 4k² + 20k`. Rocq: `4k · 6 + C(k,2) · 8 = 24k + 4k(k−1) = 4k² + 20k`. ✓

**N-2. `bnd i n` enumerates exactly `(b_1,…,b_i) ∈ ℕ^i` with `b_j ≥ 1` and
`Σ b_j ≤ n − 1`.**
Manual recursion check against the Mathematica `Bnd` function in
`notebook_reconstructed.md` §1: with `slots_left = i`, `remaining = n − 1`,
upper bound for slot 1 is `n − i = (n − 1) − (i − 1)`, matching Mathematica's
`tot − 1 − sum(earlier) − (Length[lst] − i_position)`. The base case at
`slots_left = 0` correctly returns `[[]]` (one empty composition, allowing
`sum < n − 1` since `b_{i+1} = n − sum ≥ 1`). ✓

**N-3. `M1_entry` matches Maynard 7.2 / 8.2 verbatim.**
`M1_entry bi ci bj cj = b! / (105 + b + 2c)! · G_{c, 2}(105)` with
`b = b_i + b_j`, `c = c_i + c_j`. Maynard (p. 19, A_1 entry):
`(b_i + b_j)! · G_{c_i + c_j, 2}(k) / (k + b_i + b_j + 2c_i + 2c_j)!`. ✓

**N-4. `M2_entry` matches Maynard 7.2 / 8.2 verbatim.**
Reading the Rocq M2_entry (`MaynardSpec.v:87–96`) and unfolding the `alpha`
factors, the per-term coefficient is
`C(c_i, c'_1) C(c_j, c'_2) · b_i! b_j! · (2c_i − 2c'_1)! · (2c_j − 2c'_2)! ·
(b_sum + 2)! / [(b_i + 2c_i − 2c'_1 + 1)! · (b_j + 2c_j − 2c'_2 + 1)! ·
(K2 + b_sum + 2 c_sum)!] · G_{c_sum, 2}(K2)`,
with `b_sum = b_i + b_j + 2c_i + 2c_j − 2c'_1 − 2c'_2 + 2` and `c_sum = c'_1 + c'_2`.
Maynard's `γ` factor exactly captures the first parenthesis; Maynard's
denominator `(k + b_i + b_j + 2c_i + 2c_j + 1)!` equals `(K2 + b_sum + 2 c_sum)!`
since `K2 = 104`, `K2 + b_sum + 2 c_sum = 104 + b_i + b_j + 2c_i + 2c_j + 2 = 106
+ b_i + b_j + 2c_i + 2c_j = 105 + b_i + b_j + 2c_i + 2c_j + 1`. ✓
`G_{c_sum, 2}(K2) = G_{c'_1 + c'_2, 2}(k − 1)` ✓.

**N-5. The 42-dim basis is the *full* set `{(b, c) ∈ ℕ² : b + 2c ≤ 11}`.**
Combinatorially: `Σ_{c=0}^5 (12 − 2c) = 12 + 10 + 8 + 6 + 4 + 2 = 42`. ✓
The Rocq `MaynardBasis.maynard_basis` is exactly the list of these 42 pairs in
the Mathematica enumeration order (re-derived independently in this audit
from `xExponents_mma(5)` and `yExponents_mma(5)` — match exact). ✓
This is **not** a symmetry-reduced subspace: Maynard explicitly restricts to
polynomials in the power sums `P_1, P_2` (paper p. 21 / p. 23), and the
42-dim basis is the full set of monomials `(1 − P_1)^b P_2^c` with
`b + 2c ≤ 11`. The reduction from "symmetric polys in 105 variables" to
"polys in P_1, P_2" is *Maynard's* simplification, made explicit in the
paper before Lemma 7.2 / 8.2 ("for simplicity"). It is a *lower bound*
restriction: the supremum over a subspace is ≤ the unrestricted supremum.
So `M_{105} ≥ k · λ_max(...)` from this 42-dim basis is a lower bound, which
is what we want. ✓

**N-6. `MaynardVerify` cross-checks all 1764 entries of `M1` and `M2`,
not a sample.** `theories/S1/MaynardVerify.v:99–107` (`forallb` over `seq 0 42 ×
seq 0 42`) closes by `vm_compute. reflexivity` for both `M1` and `M2`. The
check is `m_num · D = M_int · m_den` in ℤ, equivalent to `M_int / D = m_num /
m_den` because both `D` and `m_den` are nonzero positive integers (`m_den` is
either a single factorial for M1 or a product of factorials for M2 — both
positive). ✓

**N-7. The IVT chain has the right sign convention.**
- The proof works at the *cleared-denominator* polynomial `charpoly_int` ∈ ℤ[X].
- `pol_to_polyrat charpoly_int = D_q · char_poly A_rat` over ℚ
  (`CertL2.charpoly_int_Dq_scaled`, Qed).
- `D_q ≈ 2.8 × 10³³² > 0` (literal in `Witness.v`).
- The leading coefficient sign of `charpoly_int` is verified to be `+1`
  (`CertL1.sign_at_pinf_charpoly`, fed by `signs_at_inf[0] = 1` from the
  shipped data, in turn cross-checked by `CRTSigns.signs_at_inf_shipped`
  against direct BigZ evaluation of `lead_coef` on the shipped chain).
- So `charpoly_int(x)` and `char_poly A_rat(x)` have **the same sign for all
  rational `x`** (they differ by the positive scalar `D_q`).
- `charpoly_int(4/105) < 0` from `signs_at_x0[0] = −1` ⇒ `char_poly A_rat(4/105) < 0`.
- `charpoly_int(cb) > 0` from `lead_coef > 0` and `cb` above all roots ⇒
  `char_poly A_rat(cb) > 0`.
- IVT then gives a root strictly between `4/105` and `cb`. ✓

**N-8. The `cauchy_bound` from MathComp is a true upper bound on real roots.**
Confirmed via `coqtop` query: `ge_cauchy_bound : ∀ (R : realFieldType) (p : {poly R}),
p ≠ 0 → {in [cauchy_bound p, +∞[, ∀ x : R, ¬ root p x}`. Combined with
`sgp_pinftyP` to convert "no roots above `cb`" into "sign at `cb` = sign at +∞".
No reliance on monicity beyond MathComp's standard results. ✓

**N-9. The 710-prime CRT bound is safe.**
`fl_coeff_bound` is a *recurrence-tracking* upper bound on `|c_k|` produced by
the integer Faddeev–LeVerrier loop:
- `E_k ≥ max_abs_entry M_k` via `E_k = n·B·E_{k−1} + |C_{k−1}|`
  (correctly accounts for `M_k = A·M_{k−1} + c_{k−1} I`).
- `|c_k| ≤ ⌊n²·B·E_k / k⌋` because `|c_k| = |trace(A·M_k)/k| ≤ n·max|A·M_k|/k
  ≤ n²·B·E_k / k`. Integer-valued `c_k` then satisfies `|c_k| ≤ ⌊real bound⌋`.
- The use of `Z.div` (floor division on non-negative inputs) is *safe*:
  flooring a real upper bound to an integer can only decrease it, but `|c_k|`
  is itself integer and ≤ the real bound, hence ≤ the floor.

The product of 710 ≥ 2³⁰ primes is > 2²¹³⁰⁰, while
`2 · fl_coeff_bound + 2 · max_abs_coeff(charpoly_of_A_int) ≈ 2^(few thousand)`,
so the modular CRT lift is sound by `small_multiple_zero` +
`all_primes_divide_product`. The bound is *loose*, never tight, which is
the safe direction. ✓

**N-10. The 710 primes are individually proven prime.**
`crt_primes_710_all_prime` (file `CRTLift.v:102–110`) chains
`check_prime_Z_sound` (a verified trial-division Z-level primality
checker, file `PrimeCheck.v`) over all 710 entries, by `forallb`/`vm_compute`. ✓

**N-11. The `Print Assumptions` of the headline theorem is clean.**
I ran `coqtop -batch -l theories/S1/Cert.v -e 'Print Assumptions
maynard_eigenvalue_S1.'` (using the Rocq 9.1.1 toolchain present at
`/home/rocq/.opam/rocq-9.2/bin/coqtop`). The output lists *only* `Uint63Axioms.*`
and `PrimInt63.*` constants (`add_spec`, `mul_spec`, `div_spec`,
`compare_def_spec`, etc.). No project axiom, no admit. ✓

**N-12. The basis enumeration is independently re-derivable.**
`MaynardBasis.maynard_basis_eq_witness : maynard_basis = Witness.basis`
(`vm_compute.reflexivity`) provides a hand-readable basis list that a
reviewer can verify combinatorially against Maynard's recipe, without
having to read the autogenerated `Witness.v`. Cross-checked manually:
all 42 entries satisfy `b + 2c ≤ 11`, are pairwise distinct, and the
set equals `{(b,c) ∈ ℕ² : b + 2c ≤ 11}`. ✓

## Things I checked and confirmed are OK

(Itemized for the record; supplements the Notes above.)

- The `M2` formula correctly composes the eq. 7.10 / 8.8 substitution with
  Maynard's Lemma 7.1 / 8.1: integrating `t_1` first via the explicit
  anti-derivative in `(7.10) / (8.8)`, then applying the closed-form
  integral over the (k − 1)-simplex with the `G_{·,2}(k − 1)` polynomial.
  The Mathematica notebook's potentially confusing notational reuse of `x`
  and `y` for both the original and the post-`t_1`-integration variables
  is correctly resolved in `MaynardSpec.M2_entry`: the `alpha` coefficients
  index the new `(b', c')` pair `(b + 2c − 2c' + 1, c')`, and the second
  `G_2 csum K2` plays the same role as `G_{c, 2}(k)` did in the first
  layer, just at level `k − 1`. (Cross-verified against the python script's
  `_transform_monomial` + `closed_form_M2` in `python/build_certificate.py`.)
- The `realalg` field is the real algebraic closure of ℚ; an eigenvalue
  in `realalg` is automatically real. The proof never needs `λ_max` to be
  real "by hypothesis" — `realalg` enforces it.
- The headline lemma's quantifier is `∃ λ : realalg`. This is constructive
  with a witness produced by `poly_ivtoo`; no use of classical choice.
- `D_q ≠ 0` is discharged by direct destructuring on its `Z` representation
  (it is a positive literal, hence its `Z_to_int` image is `Posz (S _)`,
  which `intr_eq0` rules out as zero).
- `M1` invertibility is verified via a *single*-prime modular check
  (`M1_charpoly_hd_nz` in `CertL2.v:112`): if the constant term of
  `char_poly_mod p M1_int` is nonzero in `𝔽_p` for some prime `p`, then
  `det(M1_int) ≢ 0 (mod p)`, hence `det(M1_int) ≠ 0` over ℤ, hence M1 is
  invertible over ℚ. This is a lighter (single-prime) check than the
  full 710-prime CRT lift, and is sufficient because we only need a
  single non-zero witness.
- The Sturm-chain agreement is at the `BigZ` level (file `CRTSigns.v`),
  not in MathComp. This avoids the canonical-structure stalls described
  in REPORT.md §4d, but the *content* is just direct BigZ evaluation of
  each chain polynomial at `4/105` (or its leading coef for `+∞`).
  Mathematically equivalent to `peval` in MathComp.

## Open questions (could not resolve)

- I did not attempt to verify the `fl_eq_flint` per-prime check
  (`char_poly_int A_int = charpoly_of_A_int (mod p)`) by re-running
  `vm_compute` for any individual prime. The explicit instruction was
  not to do a full rebuild. The audit is conditional on `make -j`
  having previously closed `CharPolyAgree.char_poly_int_agrees_710` and
  `CRTLift.fl_eq_flint`. The .vo files are dated and present.
- I did not verify the *agreement* between the `BrownTraub.sturm_chain
  charpoly_int` (computed inside Rocq from the polynomial) and the
  `WitnessChain.sturm_chain` (shipped from FLINT). REPORT.md says the
  IVT proof uses only the *first* entry of the shipped chain
  (= `charpoly_int` itself, via `Smoke.chain_0_matches_charpoly`), so
  the rest of the chain is along for the ride and not on the soundness
  path. (See Mn-4.)
- `MaynardVerify.all_match_M2Z_true` is a 35-min `vm_compute` per
  REPORT. I did not re-run it; I read the boolean predicate
  (`M2_entry_matchZ`) and confirmed it is the correct cross-multiplication
  check, and that `MaynardSpec.M2_entry` is the correct closed-form.
  Conditional on the `vm_compute` having succeeded at build time, the
  M2 cross-check is sound.
- I did not formally verify Maynard's Lemma 7.3 / 8.3 in Rocq. It is
  unformalized; see M-1.

## Summary

The mathematics behind `maynard_eigenvalue_S1` is correct. The Rocq
formalization faithfully transcribes Maynard's closed-form integrals,
verifies them entry-by-entry inside the kernel, characterizes the
spectrum via a CRT-lifted characteristic polynomial, and establishes
the existence of a real algebraic eigenvalue strictly above `4/105`
via an entirely standard intermediate-value argument. The single
remaining mathematical step `M_k = k · λ_max` (Maynard's Lemma 7.3 /
8.3) is unformalized but uncontroversial. As a replacement for the
unrefereed Mathematica notebook, this proof represents a substantial
increase in assurance.
