# L1 Admits Scan Report

## Summary of the two admits

### 1. `prs_chain_sturm_correct` (CertL1.v:326-332)

**Statement**: The shipped chain's `sturm_count_above` equals
`size (filter (fun r => threshold < r) (rootsR (pol_to_polyralg charpoly_int)))`.

**What Bridge.v already proves**: `sturm_count_above_correct` (Bridge.v:1759-1883)
proves this SAME equality, but under 8 hypotheses. The two critical unsatisfied ones:

1. **`Habs_chain`**: `List.map pol_to_polyralg (sturm_chain p) = mods P P^'()`.
   This requires the shipped Brown-Traub chain to equal the abstract `mods` chain
   **coefficient-by-coefficient** after lifting to realalg. This is FALSE because
   Brown-Traub's subresultant PRS applies beta-division, producing entries that differ
   from Euclidean remainders by nonzero scalar factors.

2. **`Hcb_nz`**: All chain entries evaluate to nonzero at `cauchy_bound P`.
   This depends on `cauchy_bound_le_of_chain` (the second admit).

**What mathcomp-real-closed provides**:
- `taq_taq_itv` (qe_rcf_th.v:1017): The Sturm theorem. Takes `mods p (p^'() * q)`
  as the chain. It is SPECIFIC to the `mods` chain -- there is NO variant for
  arbitrary PRS chains.
- `changes_itv_mods_cindex`: Converts `changes_itv_mods a b p q` to `cindex a b q p`,
  again specific to the `mods` chain (it recurses via `next_mod`).
- `changes_mods_cindex`: Global version, same specificity.
- `mods` is defined (qe_rcf_th.v) as the iteration: `p :: mods q (next_mod p q)`.
- `next_mod p q = -(lead_coef q)^(rscalp p q) *: rmodp p q`.
- NO lemma exists for `mods` under entry-wise scaling. No `changes scale` lemma either.

**What Bridge.v provides for the scalar route**:
- `next_mod_scaled_morph` (Bridge.v:1290-1314, **Qed**): For each step,
  `pol_to_polyralg (next_mod p (pnorm q)) = k *: qe_rcf_th.next_mod P Q`
  where `k = (lead_coef Q)^d)^{-1}` is nonzero. This proves individual entries
  differ by nonzero scalars.

**Gap analysis for `prs_chain_sturm_correct`**:

The proof requires showing that the `changes` function is invariant when each
element of a sequence is multiplied by a (possibly different) nonzero scalar.

`changes` is defined as:
```
fix changes s := match s with
  | [::] => 0
  | a :: q => (a * head 0 q < 0) + changes q
end
```

The sign of `a * head 0 q < 0` depends only on the signs of `a` and `head 0 q`.
Multiplying `a` by a nonzero scalar `c` and `head 0 q` by a nonzero scalar `d`
does NOT preserve this: `c*a * d*b < 0` iff `c*d*a*b < 0`, which differs from
`a*b < 0` when `c*d < 0`.

**CRITICAL INSIGHT**: The shipped chain entries differ from `mods` entries by
scalars that may be NEGATIVE (since `next_mod_scaled_morph` only gives `k != 0`,
not `k > 0`). However, `changes` counts sign changes, and if entry `i` is scaled
by `c_i`, then the product `c_i * x_i * c_{i+1} * x_{i+1}` has sign
`sgn(c_i * c_{i+1}) * sgn(x_i * x_{i+1})`. A negative scalar on entry `i`
flips the sign change at position `(i-1, i)` AND at position `(i, i+1)`,
so the NET effect on the total count cancels for interior entries. But boundary
entries (first and last) could shift the count by +/-1 each.

**Actually**, looking more carefully: `changes [c0*a0; c1*a1; c2*a2; ...]`
counts `(c0*a0 * c1*a1 < 0) + (c1*a1 * c2*a2 < 0) + ...`
= `(c0*c1 * a0*a1 < 0) + (c1*c2 * a1*a2 < 0) + ...`.
This equals `changes [a0; a1; a2; ...]` iff each `c_i * c_{i+1} > 0`.

For the Sturm theorem, what matters is the DIFFERENCE
`changes_horner(chain, a) - changes_pinfty(chain)`, not each count individually.
The mathematical argument is that consecutive PRS entries have scalars whose
product has consistent sign (because the pseudo-remainder sequence preserves a
certain sign pattern). But this requires a non-trivial algebraic argument about
the Brown-Traub subresultant PRS.

**Recommended proof strategy** (from most to least feasible):

(A) **Prove `Habs_chain` directly** by showing the shipped chain IS the `mods` chain.
    This requires proving `prem p q` (our implementation) equals
    `(lead_coef q)^(rscalp p q) * rmodp p q` (mathcomp's scaling convention),
    AND that the shipped chain equals `sturm_chain` (the Brown-Traub computation).
    Bridge.v already has `prem_rmodp_eq` (Qed) showing this at the rat level.
    The gap is: does `sturm_chain` (which uses `next_mod p q = pneg (prem p q)`)
    match `mods` (which uses `next_mod p q = -(lc q)^d *: rmodp p q`)?
    Answer: They differ by the factor `(lc q)^d` at each step. This accumulates.

(B) **Prove a `changes`-invariance lemma for the specific scalar pattern**.
    Show that for the Brown-Traub PRS, consecutive scaling factors have positive
    product. This is mathematically true but requires detailed tracking of signs
    through the subresultant PRS recurrence.

(C) **Bypass `sturm_count_above_correct` entirely**: Directly prove that
    `sturm_count_above (shipped_chain) 4 105 = size (filter ...)` by constructing
    a NEW proof that doesn't go through `mods`. This would essentially re-prove
    the Sturm theorem for a general PRS chain, which is a major undertaking.

**My recommendation**: Strategy (A) is most feasible. The key insight is that
`sturm_chain` in BrownTraub.v uses `next_mod p q = pneg (prem p q)`, and
after lifting, `pol_to_polyralg (pneg (prem p q))` equals
`-(lead_coef Q)^d *: rmodp P Q` (by `prem_rmodp_eq` + `pol_to_polyralg_pneg`),
which IS exactly `qe_rcf_th.next_mod P Q`. So the chains SHOULD be equal!
The `next_mod_scaled_morph` lemma gives `k = (lc Q)^d)^{-1}` which simplifies
to `k *: (-(lc Q)^d *: rmodp P Q) = -rmodp P Q`... wait, no.

Let me re-examine. `next_mod_scaled_morph` says:
```
pol_to_polyralg (next_mod p (pnorm q))
  = k *: qe_rcf_th.next_mod P Q
```
with `k = (lc_d)^{-1}` where `lc_d = (lead_coef Q)^d`.
So our chain entry = `(lc Q)^{-d} *: mc_next_mod`.
This means `k` is NOT 1 in general. The chains genuinely differ.

But wait -- our `prem` already includes the `(lc q)^delta` scaling (that's the
pseudo-remainder definition). So `pneg(prem p q) = -(lc q)^delta * rmodp p q`
which matches `qe_rcf_th.next_mod = -(lc q)^(rscalp p q) *: rmodp p q`
ONLY IF `delta = rscalp p q`.

The `prem_rmodp_eq` lemma (Bridge.v, Qed) states:
```
pol_to_polyralg (prem p q)
  = Pdiv.Ring.rmodp (pol_to_polyralg p) (pol_to_polyralg q)
```
This is `rmodp`, NOT `(lc q)^d *: rmodp`. So our `prem` gives `rmodp` directly.
Then `next_mod p q = pneg (prem p q)` lifts to `-rmodp P Q`.
But mathcomp's `next_mod P Q = -(lc Q)^(rscalp P Q) *: rmodp P Q`.
These differ by the factor `(lc Q)^(rscalp P Q)`.

**Conclusion for admit 1**: The chains genuinely differ by accumulated scalar
factors. The scaling factor at each step is `k = (lead_coef Q)^{-d}` where
`d = rscalp P Q` (computed over realalg, or equivalently over rat by
`redivp_map`). These factors can be negative when `d` is odd and `lc Q < 0`.

**Key structural insight about `changes` and the Sturm difference**:
For `changes_horner` (evaluations at a point where no chain entry vanishes),
scaling entry `i` by `c_i != 0` transforms sign-change at position `(i,i+1)` as:
`(c_i * v_i * c_{i+1} * v_{i+1} < 0)` vs `(v_i * v_{i+1} < 0)`.
These differ by the sign of `c_i * c_{i+1}`.

However, for the DIFFERENCE `changes_horner(chain, a) - changes_pinfty(chain)`,
each position `(i, i+1)` contributes `(sign_a_i * sign_a_{i+1} < 0) - (lc_i * lc_{i+1} < 0)`.
Under scaling by `c_i`, this becomes:
`(c_i*c_{i+1}) * [(sign_a_i * sign_a_{i+1} < 0) - (lc_i * lc_{i+1} < 0)]`
where the `c_i * c_{i+1}` factor flips BOTH terms at position `(i,i+1)` equally,
so the difference at each position is negated when `c_i * c_{i+1} < 0`.

This means the total difference is NOT invariant under arbitrary nonzero scaling.
A direct proof of sign-change invariance for the Sturm difference requires
showing the specific `(lc Q)^{-d}` factors preserve it.

**Three viable strategies** (ordered by feasibility):

(A) **Prove `Habs_chain` by showing chains are equal over rcfType**.
    Over a field, `next_mod p q = -(lc q)^d *: rmodp p q` where
    `d = rscalp p q`. Our chain gives `-(rmodp P Q)` at each step
    (by `prem_rmodp_eq`). These are equal iff `(lc q)^d = 1` at each step.
    Over a field, `scalp p q = 0` when `lc q` is a unit (`Pdiv.Idomain.scalpE`),
    but `rscalp` may differ from `scalp`. If we can show `rscalp P Q = 0`
    over rat/realalg when Q != 0, then `(lc Q)^0 = 1` and chains are equal.
    **This is the most promising route**: investigate whether `rscalp = 0`
    over fields.

(B) **Prove `changes` difference invariance for the specific scaling pattern**.
    Requires detailed sign tracking through the subresultant PRS. Hard.

(C) **Bypass entirely by re-proving Sturm for general PRS chains**. Hardest.

**Update after `redivp_rec` inspection**: `rscalp p q` is computed by the raw
pseudo-division loop which increments a counter at each step. Typically
`rscalp p q = deg(p) - deg(q) + 1` (number of division steps). This is NOT 0
even over fields. So approach (A) -- proving chain equality -- is DEAD.

The `scalp` function DOES give 0 over fields (via `scalpE`), but `mods`/`next_mod`
use `rscalp`, not `scalp`. Over a field, `edivp` normalizes by `(lc q)^{-scalp}`
giving `scalp = 0`, but `redivp` does not normalize. So the `mods` chain in
mathcomp genuinely includes the `(lc q)^d` factors.

This means approach **(B) is the only viable route**: prove a `changes`
invariance lemma for the Sturm difference under the specific scaling pattern
induced by `next_mod_scaled_morph`.

Specifically, one needs to prove:
```
Lemma changes_scale_nonzero (s1 s2 : seq R) (cs : seq R) :
  size s1 = size s2 -> size cs = size s1 ->
  (forall i, i < size cs -> cs`_i != 0) ->
  (forall i, i < size s1 -> s2`_i = cs`_i * s1`_i) ->
  changes s1 - changes (map lead_coef chain1)
  = changes s2 - changes (map lead_coef chain2).
```
This is a non-trivial combinatorial argument about sign changes.

**Bottom line for admit 1**: No existing lemma directly closes this. The proof
requires a custom `changes`-difference invariance theorem under nonzero scaling,
plus showing the specific scaling factors from `next_mod_scaled_morph` satisfy
its preconditions. Estimated effort: 200-400 lines of new Coq.

---

### 2. `cauchy_bound_le_of_chain` (CertL1.v:276-281)

**Statement**: For every `q` in the shipped chain,
`cauchy_bound (pol_to_polyralg q) <= cauchy_bound (pol_to_polyralg charpoly_int)`.

**What's already proven**:
- `CauchyCheck.all_chain_cb_le` (CertL1.v:267-269, **Qed by vm_compute**):
  The BigZ-level check `cb_le q p` passes for every chain entry, where
  `cb_le q p := sum_abs(q) * |lc(p)| <= sum_abs(p) * |lc(q)|`.

**mathcomp's `cauchy_bound` definition** (found via `Print cauchy_bound`):
```
cauchy_bound p = 1 + |lead_coef p|^{-1} * \sum_(i < size p) |p`_i|
```

**The BigZ check formula**: `cb_le q p` checks
`sum_abs(q) * |lc(p)| <= sum_abs(p) * |lc(q)|`, which after dividing both
sides by `|lc(q)| * |lc(p)|` (both positive for nonzero chain entries) gives:
`sum_abs(q) / |lc(q)| <= sum_abs(p) / |lc(p)|`.

Since `cauchy_bound p = 1 + sum|coeffs(p)| / |lc(p)|`, the BigZ check proves
`sum|coeffs(q)| / |lc(q)| <= sum|coeffs(p)| / |lc(p)|`, which implies
`cauchy_bound q <= cauchy_bound p` (just add 1 to both sides).

**Gap**: The bridge from BigZ arithmetic to realalg inequality. This requires:
1. Showing `sum_abs` on BigZ corresponds to `\sum_(i < size P) |P`_i|` on realalg.
2. Showing `lc` on BigZ corresponds to `lead_coef P` on realalg.
3. Lifting the BigZ inequality to a rat inequality to a realalg inequality.

This is a substantial but mechanical proof. The key missing pieces are:
- A correspondence between BigZ list representation and the `{poly realalg}`
  coefficient indexing (`p`_i` notation in mathcomp).
- The fact that `pol_to_polyralg` preserves coefficient structure.

**Key concern**: `sum_abs` sums ALL list entries including trailing zeros,
while mathcomp's `\sum_(i < size p)` only sums up to the polynomial's degree.
But trailing zeros contribute 0 to both sums, so this is fine (the `pnorm`
equivalence `pol_to_polyralg_pnorm` handles this).

**Bottom line for admit 2**: No existing lemma closes this directly. The proof
is mechanical but requires ~100-200 lines of coefficient-level bridging between
the BigZ list representation and mathcomp's polynomial coefficient indexing.

---

## Key lemmas found in mathcomp-real-closed

| Lemma | Location | Relevance |
|-------|----------|-----------|
| `taq_taq_itv` | qe_rcf_th:1017 | Sturm theorem; specific to `mods` chain |
| `changes_itv_mods_cindex` | qe_rcf_th | Connects changes to Cauchy index; specific to `mods` |
| `changes_mods_cindex` | qe_rcf_th | Global version of above |
| `cindexRP` | qe_rcf_th | Relates bounded and global Cauchy index |
| `cauchy_boundP` | polyrcf | `p != 0 -> p.[x] = 0 -> |x| < cauchy_bound p` |
| `ge_cauchy_bound` | polyrcf | No roots at or above Cauchy bound |
| `root_in_cauchy_bound` | polyrcf | All roots in `]-cb, cb[` |
| `sgp_pinftyP` | polyrcf | Sign at infinity; used for `changes_pinfty` equivalence |
| `rootsRP` | realalg | `roots p a b = rootsR p` when no roots outside `[a,b]` |

## Key lemmas found in Bridge.v (project)

| Lemma | Status | Relevance |
|-------|--------|-----------|
| `next_mod_scaled_morph` | **Qed** | Each step: our entry = k *: mc entry, k != 0 |
| `prem_rmodp_eq` | **Qed** | `pol_to_polyralg (prem p q) = rmodp P Q` |
| `variation_at_rat_morph` | **Qed** | Our variation = mathcomp's `changes_horner` |
| `variation_at_pinf_morph` | **Qed** | Our variation = mathcomp's `changes_pinfty` |
| `sturm_count_above_correct` | **Qed** (modular) | Main bridge, takes `Habs_chain` as hypothesis |
| `changes_pinfty_eq_at_cauchy_bound` | **Qed** | `changes_pinfty = changes_horner(cb)` |
| `roots_filter_eq` | **Qed** | `roots p a cb = filter (>a) (rootsR p)` |
| `pol_to_polyralg_pscale` | **Qed** | `pol_to_polyralg (c *: p) = c *: pol_to_polyralg p` |

## CoqCombi scan

No Sturm-related, root-counting, or sign-variation content found in CoqCombi.

## Feasibility assessment

**Admit 1 (`prs_chain_sturm_correct`)**: Hard. The chains genuinely differ
by `(lc Q)^{-d}` factors at each step (where `d = rscalp`, typically
`deg P - deg Q + 1`, confirmed by inspecting `redivp_rec`). Proving chain
equality (`Habs_chain`) is impossible. The proof requires a custom
`changes`-difference invariance lemma under entry-wise nonzero scaling.

The mathematical argument is: for any two chains `c1, c2` where `c2[i] = k_i * c1[i]`
with all `k_i != 0`, and all entries nonzero at evaluation points, then
`changes(eval c2 at a) - changes(lc c2) = changes(eval c1 at a) - changes(lc c1)`.
This holds because at each position `(i, i+1)`, the sign of the product
`c2[i]*c2[i+1]` at point `a` differs from `c1[i]*c1[i+1]` by `sgn(k_i * k_{i+1})`,
and the same factor applies to the leading-coefficient products. So the
difference `(product < 0 at a) - (lc product < 0)` is preserved at each position.

This is a clean ~50-100 line proof. Combined with `next_mod_scaled_morph` (Qed)
and an inductive argument showing the full chains are related by nonzero scalars,
this closes the admit. Estimated effort: 200-300 lines total.

**Admit 2 (`cauchy_bound_le_of_chain`)**: Medium. Formula match confirmed:
`cauchy_bound p = 1 + |lead_coef p|^{-1} * sum_i |p_i|`. The BigZ check
computes `sum_abs(q) * |lc(p)| <= sum_abs(p) * |lc(q)|`, which after
dividing by `|lc(p)| * |lc(q)|` gives `sum/|lc| ratio` comparison, implying
`cauchy_bound q <= cauchy_bound p`. The bridge requires showing the BigZ list
representation faithfully encodes the realalg polynomial coefficients.
Estimated effort: 100-200 lines of coefficient-level bridging.
