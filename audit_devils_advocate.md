# Adversarial Audit — `prime_gap` Maynard `M_{105} > 4` Rocq formalisation

Reviewer angle: *find what the other red-team members will miss*.
Date: 2026-04-27.

## Verdict

The formalisation **substantially delivers** what the README claims, but the
README's framing leaves three real gaps that a determined adversary could
exploit to slip a wrong number through. None of them break soundness in
the *current* repository (where the matrix data is faithful to Maynard),
but two of them shift trust off the kernel and onto external inspection,
and one is a documented but easily-misread limitation. A careful
reviewer who follows the explicit instructions in `REPORT.md` (not just
those in `README.md`) catches all three; a lazy reviewer who runs only
`Print Assumptions maynard_eigenvalue_S1` and stops there does not.

The proof is **not** as monolithic as the headline single-theorem
display suggests — closing the trust loop on the matrix data requires
two separate Qed facts (`all_match_M1Z_true`, `all_match_M2Z_true`)
that are *not* dependencies of `maynard_eigenvalue_S1`.

Read at the level the README claims (a one-shot replacement for the
Mathematica notebook, fully kernel-checked, no project axioms), the
formalisation **is not quite** what it presents itself as. Read at the
level `REPORT.md` actually states (two parallel Qed facts, plus an
explicit cross-check on the Maynard side, plus an external argument
that "any real eigenvalue > 4/105 ⇒ M_{105} > 4"), it is sound.

## Critical findings

### C1. `MaynardVerify` is a leaf — the headline theorem does *not* depend on it

`theories/S1/MaynardVerify.v:65` imports `Witness, IntMat, CharPoly,
MaynardSpec, MaynardBasis, MaynardFactQ`. Crucially, **no file imports
`MaynardVerify`**:

```
$ grep -n "MaynardVerify\|MaynardSpec\|MaynardBasis\|MaynardFactQ" \
    theories/S1/Cert.v theories/S1/CertL2.v theories/S1/CertL1.v \
    theories/S1/CRTLift.v
(empty)
```

Consequently:

- `Print Assumptions maynard_eigenvalue_S1` (Cert.v:109) tells us
  *nothing* about whether `M1_int`, `M2_int` are Maynard's M1, M2.
- A malicious or buggy `tools/json_to_v.py` could ship `M1_int :=
  meye 42`, `M2_int := meye 42`, autogenerate a "char poly"
  `(x-1)^{42}` plus a Sturm chain certifying that polynomial has a
  root > 4/105 (false in this case, but the *kernel check* would
  still pass for any consistent polynomial); the proof would still
  Qed — it would just prove that a *different* matrix has an
  eigenvalue > 4/105.
- The ONLY thing that closes this gap is `all_match_M1Z_true` /
  `all_match_M2Z_true` in MaynardVerify.v, which a reviewer must
  check *separately*.

The README (line 32–35) claims:

> The 42x42 input matrices `M1_int`, `M2_int` are themselves
> kernel-checked against Maynard's closed-form specification.

This is true *as a Qed*, but the kernel-check is in a leaf file that
the headline theorem does not depend on. A casual reader of just the
README who runs only `Print Assumptions maynard_eigenvalue_S1`
**does not** verify the matrix data; they verify only "some 42x42 ℚ
matrix has a real eigenvalue > 4/105", which without the matrix
check is content-free.

**Attack vector.** Submit a fork that silently changes the M1/M2
data and breaks `MaynardVerify` in a hard-to-spot way (e.g., make
`all_match_M1Z` use `=` over `bool` instead of `Z.eqb`, or limit the
range to `seq 0 41` instead of `seq 0 42`). The headline theorem
still Qeds. Without explicit instructions to also `Print Assumptions
all_match_M1Z_true` and `all_match_M2Z_true` and to inspect the
*statement* of those lemmas (not just the assumptions), the bug
ships.

**Mitigation.** Add a `Require Import MaynardVerify` to `Cert.v`,
and either restate `maynard_eigenvalue_S1` to mention `M1_entry` /
`M2_entry` explicitly, or include
`maynard_eigenvalue_S1_input_consistent : all_match_M1Z = true /\
all_match_M2Z = true` in the same file and prove both Qeds in a
single chain. Today this is rejected on compile-time grounds (the
M2 cross-check takes 35 minutes); but for the *trust contract* the
M2 check is the load-bearing fact, not an optional sanity layer.

### C2. The shipped Sturm chain `WitnessChain.v` is not actually load-bearing

`theories/S1/CertL1.v:103-167` defines `chain_nz_shipped`,
`chain_lc_nz_shipped`, `chain_th_nz_shipped` — useful-looking lemmas
that prove every entry of the shipped chain has nonzero leading
coefficient and nonzero value at 4/105. **None of them is invoked**
anywhere in the L1 proof:

```
$ grep -nE "chain_lc_nz_shipped|chain_th_nz_shipped|chain_nz_shipped" \
    theories/S1/*.v
theories/S1/CertL1.v:103: Lemma chain_nz_shipped : ...
theories/S1/CertL1.v:132: Lemma chain_lc_nz_shipped : ...
theories/S1/CertL1.v:151: Lemma chain_th_nz_shipped : ...
(no other references)
```

`witness_root_count : V(4/105) − V(+∞) = 1%nat` (CertL1.v:45) is
likewise dead code.

`maynard_L1_concrete` (CertL1.v:409) needs only:
- `charpoly_neg_at_threshold` — uses `signs_at_x0[0] = -1`
  (CertL1.v:315), which by `chain_0_matches_charpoly` (Smoke.v:119)
  reduces to `sign_at_rat charpoly_int 4 105 = -1`, which is just
  evaluating `charpoly_int` at 4/105.
- `charpoly_pos_at_cb` — uses `lc(charpoly_int) > 0`
  (CertL1.v:359), which is `signs_at_inf[0] = +1`, which is
  `plead charpoly_int > 0`.
- `threshold_lt_cb` — pure MathComp, no chain.

So the entire Brown–Traub Sturm-chain machinery — 14 MB of bigZ
data, ~1 minute of `vm_compute` for sign agreement, ~7 minutes for
710-prime primality — is **not used by the proof**. A polynomial
sign at one rational and the leading-coefficient sign would
suffice; a few hundred bytes of data and a few-second `vm_compute`
would close the same proof.

This is *not* an unsoundness — the proof is fine. But it is a major
mismatch with the README's framing, which prominently advertises
"the Brown-Traub Sturm chain" and "the headline result by Sturm
counting". A reviewer who concludes that the project is sound
*because* the Sturm chain is sound is asking the wrong question;
the Sturm chain is decoration. The actual L1 step is "show
`charpoly_int(4/105) < 0` and `charpoly_int(cauchy_bound) > 0`,
apply IVT".

The reason this matters for an audit: every additional layer of
machinery that "proves the same fact" but is not on the critical
path is an opportunity for the proof to *appear* sound on
inspection while the real gap lies elsewhere. The Sturm-chain
audit is impressive infrastructure but does not protect against
an attack on the polynomial coefficients themselves.

**REPORT.md §3.4** is honest about this: "this is **IVT, not the
full Sturm theorem**: we do not need the exact count, only the
existence of some root above the threshold." The README is not.

### C3. "Some real eigenvalue > 4/105" is not "M_{105} > 4"

The headline theorem proves *existence* of a real eigenvalue of
`A_rat = M1^{-1}M2` strictly above 4/105. Maynard's claim is `M_k =
k · λ_max(M_1^{-1} M_2) > 4`, i.e., the **largest real
eigenvalue**.

If `A_rat` had a complex eigenvalue with magnitude greater than the
real eigenvalue we found, the Rocq theorem would still hold and the
mathematical claim could fail. (This cannot happen because M_1 is
PD and M_1^{-1}M_2 is similar to a symmetric matrix, but **that
fact is not proved in this project**.)

REPORT.md §1.4 explicitly disclaims this:

> Lemma 8.3 (the generalised Rayleigh-quotient identity that gives
> M_k = k · λ_max) is *not* formalised here.

But the README simply says "M_{105} > 4 ... headline proof is
complete". A reader who treats "headline proof is complete" as "the
Annals claim is reduced to kernel-checked Rocq" overestimates what
the kernel checks. The kernel checks an existence statement. The
implication "exists real eigenvalue > 4/105 ⇒ M_{105} > 4" is left
to the reader; it requires both Lemma 8.3 (Rayleigh-quotient
identity) and the spectral theorem on M_1^{-1/2}M_2M_1^{-1/2}, both
unformalised.

**For an adversarial scenario**, this means: anyone constructing
matrices `M1_int, M2_int` such that `M1^{-1}M2` has both a real
eigenvalue ≤ 0.038 and a larger complex pair could pass
`MaynardVerify` (if the matrices match the closed form), pass L1
(IVT finds the small real eigenvalue), and prove the headline
theorem — while M_{105} (the *true* sup-of-Rayleigh-quotient for
the underlying integral problem) is `< 4`. This requires an
*adversarial paper*, not just an adversarial repo, because it
requires the closed-form spec itself to permit non-real
eigenvalues. Maynard's paper does not, but this Rocq project does
not prove that.

## Major findings

### M1. The Rocq spec is faithful to Mathematica, not to Maynard's *paper*

`MaynardSpec.v` transcribes Mathematica's `Cff`, `Bnd`, `Poly`,
`PrmeCalc`, `ConstCalc` (notebook_reconstructed.md §1) verbatim. The
suspicious-looking step in `flint_probe.py:122-129` —

> Actually the MMA code writes y^cp in the 1D integral formula --
> which only works if y represents (sum t_i)^2 (single squared), not
> sum t_i^2. Hmm. ... If the spectrum doesn't match ~4.002 we log
> it, but proceed.

— is a comment in the *probe* script, but the same algebraic step
is in `python/build_certificate.py` and in
`MaynardSpec.alpha`/`MaynardSpec.M2_entry`. The eq. 7.8 expansion
uses formal symbols `x'`, `y'` which (in the Mathematica framework)
are *re-bound* at each level of the recursion to mean different
things at different levels (the new `y'` is `sum_{i≥2} t_i^2`, but
the closed form treats it as if `y'^cp = (sum')^{2cp}`).

In ConstCalc-followed-by-PrmeCalc the algebra works out because
ConstCalc at level `K-1` integrates the same way regardless of what
"y" means physically (it just reads off a polynomial-coefficient
expression and looks up `G_{c,2}(K-1)`). But the analytic
identification of `M_2[i][j] = J_{105}(F)` for the *original*
function `F(t_1,...,t_{105})` requires that this re-binding of
variables is justified. Maynard's paper does justify it; the Rocq
formalisation does not — it just reproduces Mathematica's
computation.

So the formal claim is "the spec in MaynardSpec.v is faithful to
Mathematica's notebook". The mathematical claim "the spec equals
Maynard's M_2" is unformalised. The Annals refereeing nominally
covers this, but if there's a subtle sign or bracket error in
Maynard's paper that Mathematica replicates, this Rocq project
does not catch it.

The Arb 256-bit cross-check (`build_certificate.py:546-555`) at
least confirms `k·λ ≈ 4.002069761938047` matches Mathematica's
printed `4.00206976193804713`, so the Rocq spec computes the *same
number* as the notebook to >12 digits. Whether that number equals
the true `M_{105}` is unverifiable without re-deriving the closed
form.

### M2. `D_q > 0` is not a hypothesis anywhere; only `D_q ≠ 0` is used

`Cert.v:64-69` proves `D_q ≠ 0` by case on the `Z` constructor:
`Z0` is rejected by reflexivity, `Zpos p` by `Pos2Nat.is_pos`,
`Zneg p` by `discriminate Hz` on the `Negz` vs. `Posz` constructor
distinction. This works *regardless of D_q's sign*.

Why this matters: `D_q` is the LCM of the denominators of the
characteristic polynomial of `A`, so it should be positive by
construction; but the proof only checks nonzero. If FLINT shipped
`D_q := -D_q_true` and `charpoly_int := -charpoly_int_true` (sign
flip), then:

- `pol_to_polyrat charpoly_int = -pol_to_polyrat charpoly_int_true`
- `charpoly_int(4/105)` flips sign — the IVT step's sign data would
  *also* flip, so the kernel checks would still go through.

Crucially, `signs_at_x0[0] = -1` is ALSO a vm_compute fact
(verified directly from charpoly_int). If charpoly_int were sign-
flipped, signs_at_x0[0] would have to be `+1` to match — and the
shipped data agrees. So the sign-flip attack requires consistent
flipping of *both* `D_q`, `charpoly_int`, AND `signs_at_x0` — at
which point we're back to a normal cross-check.

This is not a soundness issue; it just means the proof relies on
consistency of the FLINT-shipped data, not on independent sign
sanity. A `vm_compute`-level check `0 <? D_q` would close the
question for free.

### M3. The `D_q ≠ 0` proof relies on D_q's *constructor*, but D_q is a 333-digit literal — it could be `Zneg p` and the proof would still discharge

In `Cert.v:67`, the `Zneg p` case is ruled out by `discriminate
Hz`. This works because `Z_to_int (Zneg p) = Negz (Pos.to_nat p -
1)`, which has constructor `Negz`, distinct from `Posz`. So a
syntactically-`Zneg`-prefixed literal would also pass nonzeroness.
That is — `D_q` could be negative without breaking `D_q ≠ 0`.

In the actual repo, `Witness.v:5689` ships `D_q : Z := <huge
positive literal>%Z`, no leading negation. So `D_q` is
constructively positive. But the proof doesn't *use* positivity —
sign of D_q is structurally invisible to the rest of the chain.

Combined with M2: a reviewer could verify just *D_q is positive*
by visual inspection of Witness.v, but the kernel does not
re-check this.

### M4. The 710-prime CRT bound uses `Z.div`, not `Z.cdiv`; over-approximation argument is needed

`fl_bound_aux` (CRTLift.v:122-129) computes the FL-coefficient
bound recurrence using `Z.div (n*n*B*E_k) k`. `Z.div` rounds
*down* for nonneg dividends, which makes the bound an *under-*
estimate of `(n²·B·E_k)/k` — but only in the floor sense. The
proof of `fl_loop_coeff_bound` (line 521) uses `Z_abs_div_le`
(line 441), which only works because the trace is **divisible** by
`k` (`fl_all_divisible`). Under that hypothesis,
`Z.abs (Z.div tr k) = Z.div (Z.abs tr) k`, and `Z.div_le_mono`
preserves the ≤. So if `|tr| ≤ n²·B·E_k`, then
`|tr/k| ≤ (n²·B·E_k)/k = Z.div (n²·B·E_k) k`. The bound is correct
*because the divisibility is exact*. If `fl_all_divisible` were
ever wrong (e.g., if Newton's identity were broken at integer
level), the bound would be off and the CRT product comparison
could be wrong without the kernel noticing. The divisibility itself
is proven from `fl_divisibility_L2`, which uses MathComp's
char-poly theory — sound.

So this is *not* an unsoundness, but it's a non-obvious dependency:
the FL coefficient bound is only guaranteed because of the deep
algebraic fact that `k | tr(A·M_k)`. A reviewer who only inspects
`fl_bound_aux`'s body will not see this.

## Minor findings

### m1. The `M1_int_dim'` proof in CertL2.v:29 uses `vm_compute` while `A_int_dim` (CharPolyAgree.v:23) does the same. There are two *different* kernel constants for the dimension-42 fact (`M1_int_dim'` is a `Lemma` defined locally; `A_int_dim` is exported). For nontrivial files this is the §4c "ModularArith" antipattern in miniature. Compile time impact only.

### m2. The `_CoqProject` lists `CertL2.v` *after* `Cert.v` (lines 25-26), which is unusual — `Cert.v` imports `CertL2`, so `CertL2.v` should typically be listed first. In practice `coq_makefile` resolves `Require` order, and `make` rebuilds correctly. But this is a foot-gun if anyone manually `coqc`s the files in order.

### m3. `MaynardVerify.v:69` says "Print Assumptions on each lemma reports `Closed under the global context`" — confirmed by direct probe (`Print Assumptions all_match_M1Z_true. → Closed under the global context`). However this means **the M1/M2 cross-check does not even invoke `vm_compute` on Uint63**, so it's fully kernel-reduced in pure ℤ. That is good for trust but explains why the M2 check takes 35 minutes (no native int speedup).

### m4. The `Strategy opaque` block in `CharPolyAgree.v` (REPORT.md §4b) is a kernel-reduction-time hack, not a soundness issue. But it does mean that "tests pass" depends on Rocq's reducer happening to short-circuit on `list_eqb63`'s opaque marker — if a future Rocq version changes how `Strategy` interacts with `Qed` conversion, the proof might break in non-obvious ways. Not an attack vector today, but a fragility.

### m5. `notebook_reconstructed.md` is the *only* document in the repo that derives the closed forms; if its derivation is wrong, MaynardSpec.v inherits the wrong forms. The MD file is not kernel-checked. The Annals paper §7-8 is the ground truth. A future audit should compare MaynardSpec.G_2 against Maynard 2015 Lemma 7.1 *directly*, not against notebook_reconstructed.md.

### m6. `MaynardBasis.v:33` proves `maynard_basis = Witness.basis` by `vm_compute. reflexivity.` This is a 42-element list compare — fast and sound. However, the basis ordering is *also* implicitly the order in which M1_int's rows are filled by `flint_probe.py` (via `xExponents_mma`/`yExponents_mma`). If the Python ordering ever drifts from the Rocq `maynard_basis`, the M1/M2 cross-check would fail (different basis ordering ⇒ different `(b_i, c_i)` pairing ⇒ different closed-form values). So consistency is enforced by `MaynardVerify`, not by independent specification. A test that pins the basis ordering on the Python side (a static assert in flint_probe.py against a hardcoded list) would harden this.

## What I tried to break and could not

1. **Open vs closed interval in `poly_ivtoo`.** Confirmed by direct
   `coqc` probe (probe1.v) that `poly_ivtoo` returns
   `{x | x \in `]a, b[ & root p x}` — *open* interval. The
   `move: Hx; rewrite inE /= => /andP []` extracts the strict
   `a < x` correctly. **Strictness is sound.**

2. **Print Assumptions of headline theorem.** Ran `Print Assumptions
   maynard_eigenvalue_S1` directly via coqc on the built `.vo` files;
   the result is *exclusively* `Uint63Axioms.*` and `PrimInt63.*`
   primitives, no project-specific axioms. README claim verified.

3. **Print Assumptions of `all_match_M{1,2}Z_true`.** Both report
   `Closed under the global context`. The Z-level cross-check
   doesn't even invoke Uint63.

4. **No `Admitted` / `Axiom` / `Parameter` anywhere.** `grep -nE
   "Admitted|^Axiom |^Parameter " theories/S1/*.v` returns only
   inline mentions in comments. Verified.

5. **D_q's sign.** Inspected literal in `Witness.v:5689` — clearly
   positive (no leading minus, all-digit literal). `Z_to_int D_q` is
   `Posz (Pos.to_nat p)` for some positive `p`. The
   `charpoly_root_transfer` proof handles the negative case but
   never reaches it.

6. **MaynardSpec faithfulness to MMA notebook.** Compared
   `MaynardSpec.alpha`, `M1_entry`, `M2_entry`, `cff`, `bnd`, `G_2`
   line-by-line against `python/build_certificate.py` and against
   the literal Mathematica source in `notebook_reconstructed.md`.
   Match exactly. The Rocq-side `bnd` enumerates compositions of
   length `i` summing to ≤ `n−1` with parts ≥ 1 (`enum_bnd_aux`)
   in a different order than Mathematica's `Bnd`, but the result
   is summed (commutative), so order doesn't matter. **The MMA →
   Rocq transcription is faithful**.

7. **Basis ordering vs. matrix ordering.** `MaynardBasis.maynard_basis`
   = `Witness.basis` (vm_compute Qed). Python's
   `BASIS = list(zip(_xExponents(5), _yExponents(5)))` reproduces
   the same ordering — verified by spot-check (first three entries:
   `(0,0), (1,0), (0,1)` match in all three places).

8. **Symmetry of M1, M2.** Each `(i,j)` cell is checked
   independently — both `mat_get M1_int i j` and
   `mat_get M1_int j i` are compared against
   `m1_num_den_at i j` and `m1_num_den_at j i` respectively (since
   the closed form is symmetric in the swap). So even if `M1_int`
   were silently transposed, the check would pass — but a
   transpose of a symmetric matrix is the same matrix. No
   exploitation possible.

9. **Squareness of `M1_int`, `M2_int`, `A_int`.** All three are
   verified via `forallb (fun row => Nat.eqb (length row) 42)` plus
   `mat_dim _ = 42`, both by `vm_compute`. No row-length
   discrepancy can hide in the data.

10. **CRT bound floor-vs-ceiling.** Confirmed (M4 above) that the
    `Z.div` use is sound thanks to the divisibility hypothesis;
    floor of an exact-multiple equals the true quotient.

11. **`MaynardVerify` covers all 1764 entries.** `seq 0 42` =
    `[0..41]`; the `forallb` traverses the full 42×42 grid. No
    off-by-one in the index range.

12. **`signs_at_x0_shipped` cross-check.** The vm_compute ties the
    shipped `signs_at_x0` to *direct evaluation* of the chain at
    4/105 (CRTSigns.v:72). Since `chain[0] = charpoly_int`
    (Smoke.v:119), `signs_at_x0[0] = sign_at_rat charpoly_int 4
    105`. Independent of the rest of the chain.

13. **`Strategy opaque` blocks.** Reviewed CharPolyAgree.v's
    explanation in REPORT.md §4b. The trick is sound: it makes the
    kernel accept proofs by head-constant matching without descent.
    A wrong fact cannot hide here because the underlying Qed
    (`shipped_per_prime p Hin`) was already established by
    vm_compute on the actual list-equality.

## Recommendations

1. **Add a `Require Import MaynardVerify` to `Cert.v`** and either
   restate `maynard_eigenvalue_S1` to range over the verified
   matrices, or pair it with an explicitly-co-located theorem
   `maynard_input_correct : all_match_M1Z = true /\ all_match_M2Z =
   true`. This eliminates the "leaf file" critique from C1.

2. **Replace `D_q ≠ 0` with `0 < D_q` in `charpoly_root_transfer`**.
   Add `Lemma D_q_pos : (0 < D_q)%Z. Proof. vm_compute. reflexivity.
   Qed.` Use it. Costs nothing; makes the proof robust to data
   sign-flips.

3. **Either delete the unused chain lemmas or make them load-
   bearing.** Right now, the README and REPORT both prominently
   feature the Sturm chain, but the proof uses only `signs_at_x0[0]`
   and `signs_at_inf[0]`. Either reduce the marketing (state
   plainly that L1 is an IVT proof, the chain machinery is for
   independent cross-validation only) or invoke
   `witness_root_count` in the proof (e.g., to get *exact*
   eigenvalue count, not just existence).

4. **Formalise "all eigenvalues of `M_1^{-1} M_2` are real"** —
   this is one MathComp lemma about positive-definite Gram matrices
   that closes C3 cleanly. Without it, "real eigenvalue > 4/105"
   does not imply "M_{105} > 4" inside Rocq.

5. **Static-assert the basis ordering on the Python side** in a way
   that's checked at every certificate regeneration. Currently the
   Python script regenerates the basis via `xExponents_mma` /
   `yExponents_mma`; if anyone edits those functions, the Rocq
   side's `maynard_basis_eq_witness` will fail loudly *only if*
   somebody re-runs `make` on a fresh checkout. A
   `BASIS == [(0,0), (1,0), (0,1), ...]` assert in
   `build_certificate.py` would catch the drift earlier.

6. **Cross-check `MaynardSpec` against arXiv:1311.4600 directly**, not
   against `notebook_reconstructed.md`. A short companion document
   that quotes Maynard's Lemma 7.1 and equation 7.8 verbatim and
   maps each symbol to a Rocq definition would close the M1
   transcription concern.

7. **Add `Lemma maynard_input_round_trip : forall i j, (i < 42 ->
   j < 42 -> ratr (M1_int[i][j])/ratr D_M1 = M1_entry ...)`** at
   the rat level. The current MaynardVerify only proves the Z-level
   cross-multiplication; the rat-level matrix equality is left to
   the reader. A 50-line proof that uses already-Qed facts +
   `unfold M1_entry; ring; ...` would close the loop.

## Summary

The formalisation does what a careful reader of *both* README and
REPORT.md will conclude it does: kernel-checks two parallel facts
(maynard_eigenvalue_S1 + all_match_MZ), with one external
mathematical step (real eigenvalues ⇒ M_k = k · λ_max) deferred to
Maynard's paper. Within those bounds, no soundness gap was found.
The soundness *was tested* by direct kernel probes (Print
Assumptions, coqc on the built .vo's, and grep for axioms /
admits), not just trusted from the README.

The README's framing oversells the level of formalisation by
implying that a single `Print Assumptions` covers everything; the
actual trust contract is split between three Qed facts and one
unformalised lemma. A more candid README, plus the structural
changes in recommendations 1, 2, and 4 above, would close the gap
between marketing and substance — at which point the project would
genuinely deliver what its first sentence claims.
