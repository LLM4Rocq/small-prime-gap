# Critical Audit — Rocq Formalization of Maynard `M_{105} > 4`

**Project:** `/home/rocq/prime_gap/` (branch `main`, commit `63501f1`)
**Headline:** `PrimeGapS1.Cert.maynard_eigenvalue_S1`
**Date:** 2026-04-27
**Reviewers (independent, parallel):**
1. Mathematician — content vs. arXiv:1311.4600 (Lemmas 7.1/7.2/7.3 ≡ v3 8.1/8.2/8.3)
2. Devil's advocate — adversarial, hidden-gap hunting
3. Formal-methods specialist — kernel axioms, `Print Assumptions`, `vm_compute`/`native_compute` trust
4. Rocq/MathComp specialist — proof-engineering, idiom correctness, statement-vs-claim

Individual reports: `audit_mathematician.md`, `audit_devils_advocate.md`,
`audit_formal_methods.md`, `audit_rocq_specialist.md`.

---

## Top-line verdict

**No soundness bug was found.** The headline theorem `maynard_eigenvalue_S1`
is `Qed`, the kernel really verifies what its statement says, and `Print
Assumptions` reports only the standard Rocq `PrimInt63.*` /
`Uint63Axioms.*` primitives — verified live by all four reviewers. There
are zero `Admitted`s, zero project-specific `Axiom` declarations, no
classical-logic escape hatches, no global flags weakening kernel checks,
no shadowed MathComp definitions, and no stale `.vo` files.

**However**, the README's framing meaningfully oversells what a single
`Print Assumptions maynard_eigenvalue_S1` actually proves. The trust
contract is split across **three independent Qed facts plus one
unformalized math lemma**, not one. A careful reader of *both*
`README.md` and `REPORT.md` reconstructs the full picture; a casual
reader who runs only `Print Assumptions` on the headline does not.

The proof, read *honestly*, is:

> `maynard_eigenvalue_S1` (Qed) — given the FLINT-shipped `M1_int`,
> `M2_int`, the kernel certifies that `A_rat = M1⁻¹·M2 ∈ ℚ^{42×42}` has
> a *real* eigenvalue `λ` with `λ > 4/105`. PLUS:
> `MaynardVerify.all_match_{M1,M2}Z_true` (Qed, separate file, *not*
> imported by Cert.v) — the FLINT-shipped `M1_int / D_M1`, `M2_int /
> D_M2` agree entry-wise with the Rocq transcription of Maynard's
> Lemma 7.2/8.2 closed forms in `MaynardSpec.v`. PLUS, *unformalized*:
> Maynard's Lemma 7.3/8.3 (`M_k = k · λ_max(M₁⁻¹M₂)`) and the implicit
> "all eigenvalues of `M₁⁻¹M₂` are real, the largest is what we want".

Within those bounds, the proof is sound, the cross-checks are real, and
the kernel does verify the load-bearing arithmetic. As an independent
replacement of Maynard's Mathematica notebook the increase in assurance
is substantial: the unrefereed Mathematica computation has been
replaced by a kernel-checked Rocq derivation that re-does every
arithmetic step in the kernel (FL char poly, Sturm sign check, 710-prime
CRT, IVT root extraction, plus Maynard-spec cross-check on M1 and M2).

The recommendations below are what we believe is needed to make the
formalization *actually deliver* what the README first sentence claims.

---

## Findings consolidated by severity

### CRITICAL — None.

All four reviewers, after independent probing, found no defect that
would let a wrong number pass the kernel as currently configured.

### MAJOR

#### M-1. `MaynardVerify` is a leaf in the dependency DAG; the headline does not import it
*Reported by:* Devil's advocate (C1), Rocq specialist (M1). Confirmed by
the formal-methods reviewer's `Print Assumptions` audit (no Maynard-spec
symbol appears).

`Cert.v:22` requires `IntPoly IntMat CharPoly Witness CertL1 CertL2`.
`MaynardVerify`, `MaynardSpec`, `MaynardBasis`, `MaynardFactQ` are *not*
on that path. `grep -rn "MaynardVerify" theories/S1/*.v` shows that no
file imports `MaynardVerify`. Consequently `Print Assumptions
maynard_eigenvalue_S1` is silent about whether `M1_int` / `M2_int` are
Maynard's M1/M2 — that question is closed by `all_match_M1Z_true` /
`all_match_M2Z_true`, which a reviewer must `Print Assumptions`
*separately*.

The author of `MaynardVerify.v:58` is internally honest about this
("this file is a leaf in the dependency DAG and is not imported by
Cert.v"). But README §"Trust base" and the displayed headline create
the impression that one `Print Assumptions` call covers everything.

**Attack vector** (theoretical): a malicious or buggy `tools/json_to_v.py`
ships `M1_int := meye 42`, `M2_int := meye 42` plus a consistent
"char poly" certifying a root > 4/105. `maynard_eigenvalue_S1` still
Qeds (it would simply prove a true fact about *that* matrix). Without
also `Print Assumptions`-ing `all_match_M{1,2}Z_true` and inspecting
their *statements*, the bug ships.

**Fix:** Add `Require Import MaynardVerify.` to `Cert.v` and either
restate `maynard_eigenvalue_S1` to mention `M1_entry`/`M2_entry` directly,
or pair it with a co-located theorem
`maynard_input_consistent : all_match_M1Z = true /\ all_match_M2Z = true`
in `Cert.v`. (This *will* cost the ~36 min M2 `vm_compute` at every
`Cert.v` rebuild — but that is precisely the cost of making the headline
load-bearing for the whole trust loop.)

---

#### M-2. "Exists real eigenvalue > 4/105" is *strictly weaker* than `M_{105} > 4`
*Reported by:* Mathematician (M-1), Devil's advocate (C3). REPORT.md §1.4
discloses this; README does not.

The headline produces a `realalg` `λ` with `eigenvalue (...) λ ∧ ratr(4/105) < λ`.
Maynard's claim is `M_{105} = 105 · λ_max(M₁⁻¹M₂) > 4`. Two unformalized
steps stand between them:

1. **Lemma 7.3/8.3 (Rayleigh–Ritz)**: `sup_F (J_k(F)/I_k(F)) = λ_max(M₁⁻¹M₂)`.
   Standard linear algebra over a real field for symmetric PD `M1` and
   symmetric `M2`, but not in the Rocq layer.
2. **All eigenvalues of `M₁⁻¹M₂` are real**, and the one we found ≥ 4/105
   bounds `λ_max ≥ 4/105` (immediate). Reality requires the spectral
   theorem on `M₁^(-1/2) M₂ M₁^(-1/2)` — also not formalized.

Mathematically these are uncontroversial (M1 and M2 are Gram-style PD
by construction). Formally they are gaps. A future formalization of
Maynard's overall *bounded gaps* result that consumes the present
artefact would still need to formalize them.

**Devil's advocate stress test:** if `A_rat` had a complex eigenvalue
of larger magnitude than the real eigenvalue we found, `M_{105}` could
in principle fail to exceed 4 even though our Rocq theorem holds. This
cannot occur for the *actual* M1, M2 (they are PD Gram), but the Rocq
proof does not establish PD-ness — it relies on the user to know
Maynard's argument.

**Fix:** Either (a) state the headline as "the shipped FLINT certificate
has a real algebraic eigenvalue strictly above 4/105", admit the
8.3-bridge as a Note, and finish; or (b) formalize Lemma 8.3 over
`'M[rat]_42` plus a one-paragraph PD/symmetry proof on `M1_entry` and
`M2_entry`. (b) is a few hundred lines of MathComp; (a) is honest
documentation of the present scope.

---

#### M-3. The shipped Sturm chain (`WitnessChain.v`, `CRTSigns.v`) is **not load-bearing**
*Reported by:* Devil's advocate (C2). Math reviewer notes the same
(Mn-4). Rocq specialist confirms (Observations, item 3).

`maynard_L1_concrete` (`CertL1.v:409`) goes through `poly_ivtoo` (IVT)
using only:
- `signs_at_x0[0] = -1` ⟹ `charpoly_int(4/105) < 0`
- `signs_at_inf[0] = +1` ⟹ leading coefficient > 0 ⟹
  `charpoly_int(cauchy_bound) > 0`

The remaining 42 entries of the shipped chain, the 14 MB
`WitnessChain.sturm_chain`, the 710-prime primality verification, the
sign-variation count `witness_root_count : V(4/105) − V(+∞) = 1` — all
computed inside the kernel, all **unused** by the headline. `grep -nE
"chain_lc_nz_shipped|chain_th_nz_shipped|chain_nz_shipped|witness_root_count"`
finds no callers outside the definitions themselves.

This is **not** unsoundness. But it is a documentation issue: README
prominently advertises the Brown-Traub Sturm chain and its 710-prime
agreement check; a reviewer might reasonably believe the proof's
soundness depends on those checks. It does not. A pure-IVT proof
identical in soundness could ship `signs_at_x0[0]` and `signs_at_inf[0]`
as ~10 bytes of data, no chain.

(REPORT.md §3.4 *is* honest: "this is IVT, not the full Sturm theorem".
The README does not propagate that nuance.)

**Fix options:** (a) make the chain load-bearing by stating and using
`witness_root_count` as part of the headline (sharper claim: *exactly
one* real eigenvalue above 4/105); (b) trim the Sturm-chain machinery
out and ship a leaner artefact; (c) keep the chain as cross-validation
infrastructure but caveat it explicitly in README.

---

#### M-4. Spec faithfulness is to the Mathematica notebook, not directly to Maynard's paper
*Reported by:* Devil's advocate (M1).

`MaynardSpec.G_2`, `M1_entry`, `M2_entry`, `alpha`, `bnd`, `cff` were
transcribed line-by-line from `notebook_reconstructed.md` (which itself
was reconstructed from Mathematica's `Computations.nb`). The Devil's
advocate flagged a comment in `flint_probe.py:122-129` about variable
re-binding (`y'` meaning `(Σ t_i)²` vs. `Σ t_i²`) where Maynard's paper
justifies the substitution, but the Rocq-side cross-check does not
re-derive it.

The mathematician reviewer **independently re-derived** `G_2`,
`M1_entry`, `M2_entry` against the *paper* (arXiv:1311.4600 v1 §7,
equivalent to v3 §8) — finding all three faithful (audit_mathematician.md
N-1 through N-4, with explicit small-`n` checks `G_{0,2}=1`, `G_{1,2}=2k`,
`G_{2,2}(k) = 4k²+20k`). So the transcription chain is end-to-end:
paper → notebook → Rocq, all faithful.

But formally, the Rocq spec is not proven equal to Maynard's textbook
formulas; it is *equal-by-inspection*. A reviewer who wants to close
this gap must re-read both `MaynardSpec.v` and Maynard §8.

**Fix:** A short companion document mapping `MaynardSpec.G_2` →
Maynard's `G_{n,2}(k)` formula, `MaynardSpec.M{1,2}_entry` →
Maynard's `M_{1,ij}` / `M_{2,ij}` definitions, with arXiv equation
references, would close the math-trust loop without requiring deeper
Rocq surgery.

---

#### M-5. `D_q ≠ 0` is enforced; `D_q > 0` is not — sign of the cleared polynomial is invisible to the proof
*Reported by:* Devil's advocate (M2, M3). Math reviewer confirms `D_q`
is positive in the shipped data (N-7) but relies on the same chain.
Rocq specialist confirms `charpoly_root_transfer` (Cert.v:60-69) only
needs nonzeroness.

If FLINT shipped `D_q := -D_q_true` along with sign-flipped
`charpoly_int := -charpoly_int_true`, the proof would still go through
because `signs_at_x0[0]` is *also* `vm_compute`-derived from the
shipped polynomial — both flip in lockstep, no kernel objection. The
sign-flip is theoretical but exemplifies a common class of "consistency
attack": all the FLINT data flips together, the modular cross-checks
all agree, and the kernel never re-examines a sanity invariant that
is not part of any check.

**Fix:** One line. `Lemma D_q_pos : (0 < D_q)%Z. Proof. vm_compute.
reflexivity. Qed.` And use it in `charpoly_root_transfer`. Costs
nothing; closes the question.

---

#### M-6. Single `native_compute` puts the OCaml compiler in the trust base
*Reported by:* Formal-methods (M1).

`CRTLift.v:138` uses `native_compute` to discharge `fl_crt_bound`:
`(2·B + 2·B' < ∏ p_i)` over ~21300-bit Z constants. This compiles to
OCaml native code, links a shared object, and runs it; that OCaml
compiler is then in the trust base. `grep` confirms this is the
*only* `native_compute` in the project; everything else is
`vm_compute`.

The proven inequality is purely numerical; an erroneous OCaml compiler
would have to flip a comparison on a multi-thousand-bit literal — not
an empirically observed bug class for `native_compute`.

**Fix:** Replace `native_compute` with `vm_compute` (the REPORT
acknowledges that `vm_compute` "lives at the edge" of the same fact;
a few extra minutes is unlikely to be worth keeping the OCaml
compiler in the trust base).

---

### MINOR

These are non-soundness items worth fixing in a follow-up sprint.

| # | Description | Reporter |
|---|-------------|----------|
| m1 | `Cert.v:67` does `rewrite /Z_to_int /=`, which would fail if anyone added `Global Opaque Z_to_int`. The current `Opaque Z_to_int` in `CertL2.v:58` is file-local, so it works today; brittle to future cleanup. | Rocq M3 |
| m2 | `mat_int_to_rat M D n` is total: `D = 0` ⟹ zero matrix, `n ≠ mat_dim M` ⟹ zero-pads or truncates silently. A typo at the call site (e.g. `... 41` instead of `42`) gives a meaningful-looking wrong matrix. No defensive lemma constrains the inputs. | Rocq M4 |
| m3 | `maynard_bridge_L4` is dead code. README says `Proof. (* L1 + L2 + L3 + L4 *) Qed.` but `L4` is never invoked. REPORT clarifies (~line 1003) but READ.md does not. | Rocq M2 |
| m4 | L4's body uses `rewrite (_ : (4/105 : realalg) = ratr (4%:~R / 105%:~R))` which closes by reflexivity in MathComp 2.5 + realalg, but is fragile to canonical-structure migration. Replace with `rewrite -fmorph_div !rmorph_int.` | Rocq M2 / m4 |
| m5 | `_CoqProject` lists `Cert.v` *before* `CertL2.v` although `Cert.v` imports `CertL2`. `make` is dependency-driven so this works, but contradicts README's "26 .v files in dependency order". | FM m1 / Devil m2 |
| m6 | REPORT.md §6 example lists "`BigN.succ_spec`" as a sample assumption; the actual `Print Assumptions` output contains *no* `BigN.*` symbols. Bignums in Rocq 9.x is built on PrimInt63 with proved specs — zero new axioms. Documentation imprecision. | FM M2 |
| m7 | `MaynardVerify.v:43-60` describes axioms `M1_correct`/`M2_correct` removed in commit `e9de5e3`; comment is stale. `Bridge.v:104-110` describes `next_mod_scaled_morph` as "the only remaining admit" — there is no admit anywhere. Both are pre-rewrite comments. | Rocq m6 |
| m8 | The `Z.div` use in `fl_bound_aux` (CRTLift.v:122-129) is sound *only because* `fl_all_divisible` (the deep Newton-identity fact `k | trace(A·M_k)`) holds. A reviewer who only inspects `fl_bound_aux`'s body does not see the dependency. | Devil M4 |
| m9 | The `Strategy opaque/transparent` blocks in `CRTLift.v` (lines 723-731, 1033-1121) are kernel-reduction performance hacks. Sound today (verified both reverts are matched, `Print Assumptions` post-hoc clean), but fragile to Rocq version changes in `Strategy` semantics. | Devil m4 / FM m3 |
| m10 | M2 cross-check (`all_match_M2Z_true`) takes ~35 min `vm_compute` at every full rebuild. `Print Assumptions` reports "Closed under the global context" — even Uint63 is not used (pure stdlib `Z`); that explains the cost. Could be sped up with native int arithmetic at small loss to trust hygiene. | Devil m3 / FM table |
| m11 | Basis ordering coordination between Python (`xExponents_mma`/`yExponents_mma`) and Rocq (`MaynardBasis.maynard_basis`) is enforced by `MaynardVerify`, not by an independent invariant. A drift in either side would manifest as a *Maynard-spec mismatch*, not a basis error per se. A static-asserted hardcoded basis list on the Python side would catch it earlier. | Devil m6 |
| m12 | `BrownTraub.next_mod p q := pneg (prem p q)` matches MathComp's `mods` only up to a positive scalar at each chain step. `Bridge.v` admits this honestly; the strict equality `mods_int_morph` was removed because chains differ by polynomial scalars. Fine because the headline doesn't go through MathComp's Sturm machinery (it goes through `poly_ivtoo`), but worth noting if anyone resurrects the Sturm-bridge plan. | Rocq m5 |

---

## What was checked and confirmed sound

Each reviewer probed multiple potential failure modes; the union is:

### Trust base
- `Print Assumptions maynard_eigenvalue_S1` returns exactly **50 symbols**, all of which are `PrimInt63.*` (25 operators) + `Uint63Axioms.*` (25 specifications) shipped with `coq-stdlib`. Verified live via `coqc` wrapper by the formal-methods reviewer. (FM Assumption Inventory)
- Sub-lemma `Print Assumptions` checks all match expectations: `all_match_M{1,2}Z_true` are even stronger ("Closed under the global context" — pure stdlib Z, no Uint63 needed); `char_poly_int_agrees_710` uses only the 25 `PrimInt63.*` *constants* (no spec axioms, since `vm_compute. reflexivity.` doesn't reason *about* the operators); `realalg`, `cauchy_bound`, `poly_ivtoo`, `ratr`, `char_poly`, `eigenvalue`, `map_char_poly`, `eigenvalue_root_char` are all "Closed under the global context".
- Bignums (`BigZ`, `BigN`) brings zero new axioms; `BigN.spec_*` are theorems proved from `Uint63Axioms`.
- No `Admitted`, no `Axiom`, no `Parameter` declaration in `theories/S1/`. (Comment-only matches in `Cert.v:12`, `CharPoly.v:29`, `Bridge.v:11/353/615`.)
- Zero unsafe global flags (`Unset Guard`, `Allow StrictProp`, `Set Definitional UIP`, etc.). Only cosmetic: `Set Implicit Arguments`, `Unset Strict Implicit`, `Unset Printing Implicit Defensive`.
- `make -q` reports clean; no stale `.vo`.
- All 26 `.v` files are in `_CoqProject`.
- All `Section`s have matching `End`s; `Hypothesis`es are properly scoped.
- All `Strategy opaque/transparent` blocks have matched reverts; semantics-preserving.

### Mathematics
- `MaynardSpec.G_2 n k` is a faithful transcription of Maynard's `G_{n,2}(k)` (Lemma 7.1 / 8.1). Verified at small `n`:
  - `G_{0,2}(x) = 1` ✓
  - `G_{1,2}(k) = 2k` ✓
  - `G_{2,2}(k) = 4k² + 20k` ✓
- `MaynardSpec.M1_entry` matches Maynard `(b_i+b_j)! · G_{c_i+c_j,2}(k) / (k+b_i+b_j+2(c_i+c_j))!` verbatim.
- `MaynardSpec.M2_entry` correctly implements the eq. 7.10/8.8 substitution + Lemma 7.1/8.1 closed form at level `k-1`. The variable re-binding is internally consistent (verified against Mathematica's `_transform_monomial` + `closed_form_M2`).
- `MaynardBasis.maynard_basis` enumerates the full set `{(b,c) ∈ ℕ²: b+2c ≤ 11}`, 42 elements (combinatorially `Σ_{c=0..5} (12-2c) = 42`); cross-checked against Mathematica's `xExponents_mma(5)` / `yExponents_mma(5)`.
- `MaynardVerify.all_match_M{1,2}Z_true` covers all **1764 entries** (`forallb` over `seq 0 42 × seq 0 42`), not a sample; the cross-multiplication check `m_num · D = M_int · m_den` is over `Z` (so `_ ≠ 0` divisors are handled by integer arithmetic), `Print Assumptions` is empty.
- `D_q` literal is a 333-digit positive `Z` constant in `Witness.v:5689` (verified by direct inspection: no leading minus). So the cleared polynomial has the same sign as `char_poly A_rat` everywhere.
- The leading coefficient of `charpoly_int` is verified `+1` (`signs_at_inf[0] = 1`, cross-checked via direct BigZ evaluation in `CRTSigns.signs_at_inf_shipped`).
- `cauchy_bound` from MathComp `polyrcf` is a verified strict upper bound on real roots: `ge_cauchy_bound : p ≠ 0 → ∀ x ≥ cauchy_bound p, ¬ root p x`. Combined with `sgp_pinftyP`, IVT applies.
- `poly_ivtoo` returns an *open* interval `]a, b[` — `signs_at_x0[0] = -1` plus this strictness gives `4/105 < λ` (not just ≤). Verified by direct probe.
- The 710 CRT primes are individually proven prime via `crt_primes_710_all_prime` (`forallb check_prime_Z_sound`).
- The CRT bound `2B < ∏ p_i` is a *loose* over-approximation: `fl_coeff_bound` recurrence-tracks `|c_k|` via the safe over-bound `E_k = n·B·E_{k-1} + |C_{k-1}|`, `|c_k| ≤ ⌊n²·B·E_k/k⌋`. Floor is sound because `c_k` is integer (and `Z.div` is exact thanks to `fl_all_divisible`).

### Rocq engineering
- `eigenvalue` is the standard MathComp predicate `λ ↦ eigenspace λ ≠ 0` (mxalgebra.v:2208).
- `4%:Q / 105%:Q : rat` is genuinely `4/105 : rat` (not truncated-int division). `rat.v:524` notation table verified.
- `ratr (4%:Q / 105%:Q) : realalg` is *definitionally* equal to `(4 : realalg) / (105 : realalg)`; spot-compile confirms `reflexivity` succeeds.
- Dimensions throughout are consistent: `'M[rat]_42`, `map_mx ratr A_rat : 'M[realalg]_42`, `eigenvalue` invoked at `n=42, F=realalg`.
- `mat_identity_rat`'s scalar factors `D_M2 *: (M1·A) = (D_M1 · D_A) *: M2` correctly clear the three denominators of the algebraic identity `M1 · A = M2`.
- `char_poly_scale` (`CharPolyScale.v:49-81`) correctly proves `(char_poly (c *: M))_k = c^(n-k) · (char_poly M)_k` for `k ≤ n`, via `detZ` + composition.
- `charpoly_root_transfer` correctly handles the `D_q ≠ 0` case-bash on `Z = Z0 | Zpos p | Zneg p` (only the `Z0` branch contributes; the others give `False` by constructor disjointness on `Posz` vs `Negz`).
- `abstract_mat_scale` / `char_poly_scale_rat42` / `mat_cancel_helper` is exemplary MathComp 2.5 + HB engineering: expensive canonical-structure resolution is isolated to abstract-`n` lemmas, specialized to `n=42` only at the call site. Documented and justified in `CertL2.v:318-339`.
- `pol_to_polyrat` and `pol_to_polyralg` are *definitionally* coherent (`pol_to_polyralg p := map_poly ratr (pol_to_polyrat p)` in Bridge.v:56), so `exact maynard_L1_concrete` works without a bridge lemma.
- `Strategy opaque [...]/transparent` blocks are matched, sound (kernel-reduction-order hint only, cannot affect soundness), and `Print Assumptions` post-hoc is clean.
- No shadowing of `eigenvalue`, `map_mx`, `ratr`, `realalg`, `char_poly`, `invmx`, `*m`, `*:`, `\matrix`. `M1_int`, `M2_int`, `A_int` defined exactly once each in `Witness.v` (lines 70, 1925, 3780).

---

## Open questions / things not closed

1. **`coqchk` re-verification.** The formal-methods reviewer started `coqchk PrimeGapS1.Cert` against the `.vo` files; it was still running (~177 MB read) at report time. `coqchk`'s output, if clean, is the strongest available external check (independent kernel reimplementation in OCaml). No reason to expect failure, but the result was not observed. **Recommendation:** run to completion in CI as the gold-standard cross-check.

2. **OCaml compiler trust** for `fl_crt_bound`'s single `native_compute`. Eliminable by switching to `vm_compute`. (M-6 above.)

3. **Maynard Lemma 8.3 (`M_k = k·λ_max`)** is not formalized. (M-2 above.)

4. **PD/symmetry of `M1`, `M2`** as Gram matrices is not formalized. Required if Lemma 8.3 is to be formalized inside Rocq; mathematically standard, formally absent.

5. **The `BrownTraub.sturm_chain charpoly_int`** computed *inside Rocq* is not proven equal to the `WitnessChain.sturm_chain` shipped from FLINT. Only the *first entry* of the shipped chain is checked (via `Smoke.chain_0_matches_charpoly`). Because the rest of the chain is not on the soundness path (M-3 above), this is moot, but a reviewer who believes the chain matters might assume the equality.

6. **Re-deriving Maynard's closed forms from the integral.** No reviewer attempted this; it is the analytic step "from `R_F`-integral to closed form" that was originally Mathematica's job. Currently the trust chain is *paper → notebook → Rocq*, not *integral → kernel-checked closed form*. Closing this would require an analytic-integration formalization, which is outside scope.

---

## Recommendations, in priority order

1. **(M-1)** Add `Require Import MaynardVerify.` to `Cert.v` and either restate the headline to mention the closed-form match, or pair it with a sibling theorem `maynard_input_consistent`. This is the single most important change; it is the difference between "the headline implies the Maynard claim" and "the headline implies *something* about *some* matrix".

2. **(M-5)** Add `Lemma D_q_pos : (0 < D_q)%Z. Proof. vm_compute. reflexivity. Qed.` and use positivity (not just nonzeroness) in `charpoly_root_transfer`. One-line cost.

3. **(M-3)** Decide: either (a) trim the unused Sturm-chain machinery (`witness_root_count`, `chain_lc_nz_shipped`, the 14 MB `WitnessChain.v`) since it is not load-bearing for the headline; or (b) make it load-bearing by stating `exactly one real eigenvalue above 4/105`. Either is honest; the current state is a documentation mismatch.

4. **(M-2)** Tighten the README to match REPORT.md §1.4 — explicitly note that "exists real eigenvalue > 4/105" is the formal claim and that Lemma 8.3 is the un-formalized one-paragraph step bridging to `M_k > 4`.

5. **(M-6)** Replace the single `native_compute` with `vm_compute` to remove the OCaml compiler from the trust base. Build-time cost is ~minutes per run, paid once.

6. **(M-4)** Add a short companion document (5–10 pages) that maps `MaynardSpec.{G_2, alpha, M1_entry, M2_entry}` to Maynard arXiv:1311.4600 v3 §8 equations *directly*, with line-level citations. This closes the math-trust loop without code surgery.

7. **(m3, m4)** Either delete `maynard_bridge_L4` or invoke it from the headline. Replace its fragile `(_ : ... = ...)` reflexivity with `rewrite -fmorph_div !rmorph_int.`.

8. **(m6, m7)** Update README §"Trust base" to match the `Print Assumptions` output verbatim (no `BigN.succ_spec`); remove the stale comments in `MaynardVerify.v:43-60` and `Bridge.v:104-110`.

9. **(m11)** Add a static `BASIS == [(0,0), (1,0), (0,1), ...]` assertion in `python/build_certificate.py` to catch basis-ordering drift earlier than the `make` build.

10. **(m5)** Reorder `_CoqProject` so `CertL2.v` precedes `Cert.v` (cosmetic, but matches the README's "dependency order" claim).

11. **(open Q1)** Run `coqchk` to completion in CI as a separate trust check.

---

## Summary

The Rocq formalization is **sound and substantially delivers a Maynard
M_{105} > 4 audit** at the level of "the FLINT-shipped 42×42 matrices
have a real eigenvalue > 4/105, those matrices are kernel-checked
against Maynard's closed forms, and the closed forms are
hand-transcribed from Maynard §8". No critical defect was found by
any of four independent reviewers. The kernel-axiom budget is exactly
the standard Rocq native-integer primitives — nothing more.

The README does, however, present the project as a more end-to-end
artefact than it is. The headline theorem alone does not certify
"Maynard's M_{105} > 4"; that conclusion requires composing **three Qed
facts** (`maynard_eigenvalue_S1`, `all_match_M1Z_true`,
`all_match_M2Z_true`) plus **one unformalized math lemma** (Maynard
8.3). Three small structural changes (recommendations 1, 2, and 4
above) would close the documentation-vs-substance gap and make the
project genuinely deliver, in code, what its first sentence claims.

As an independent replacement of Maynard's unrefereed Mathematica
notebook, this proof represents a **substantial** assurance increase.
The increase is real, the kernel checks are real, and the cross-checks
between FLINT and Rocq are real. With the recommended fixes, it would
be one of the more impressive numerical formalizations in the Rocq
ecosystem.

---

*Reports by:*
- `audit_mathematician.md` (~3000 words)
- `audit_devils_advocate.md` (~3500 words)
- `audit_formal_methods.md` (~2800 words)
- `audit_rocq_specialist.md` (~2200 words)
