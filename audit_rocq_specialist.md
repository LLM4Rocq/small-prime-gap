# Rocq / MathComp Proof-Engineering Audit — `prime_gap`

Auditor: Rocq + MathComp idiom specialist (red-team, four-person panel)
Subject: `theories/S1/`, `Theorem maynard_eigenvalue_S1` in `Cert.v`
MathComp 2.5.0, mathcomp-real-closed 2.0.3, Rocq 9.1.1.
All findings cross-checked by reading source and by spot-compiling
small replicas; `Print Assumptions maynard_eigenvalue_S1` was rerun
locally for this audit.

## Verdict

The proof closes what it claims: `maynard_eigenvalue_S1` is `Qed`,
and `Print Assumptions` shows only `Uint63Axioms.*` / `PrimInt63.*`
kernel primitives — zero project-specific axioms, zero `Admitted`s
on the path. The headline statement is mathematically exactly the
Maynard-style claim "ratr (4/105) < some eigenvalue λ of A_rat in
realalg". The pieces I sampled (`abstract_mat_scale`,
`charpoly_int_Dq_scaled`, `char_poly_scale`, `maynard_L1_concrete`,
the IVT chain, `mat_identity_rat`) are all *mathematically correct*
and use MathComp idioms appropriately.

There are, however, several **non-soundness findings** worth flagging:
two are documentation/scoping discrepancies between the README and
what the code actually does, three are minor proof-engineering smells
that survive only because of Rocq's robust elaboration of MathComp
canonical structures, and one is a structural observation about
`MaynardVerify` that the project itself partially documents.

I found **no** soundness bug.

## Critical findings

None.

## Major findings

### M1. `MaynardVerify.v` is decoupled from the headline (file:line)

Confirmed: `Cert.v` at line 22 imports
`IntPoly IntMat CharPoly Witness CertL1 CertL2`. None of
`MaynardVerify`, `MaynardSpec`, `MaynardBasis`, `MaynardFactQ` is on
that import path (`grep -rn "MaynardVerify\|MaynardSpec" theories/S1/*.v`
shows MaynardVerify imports MaynardSpec/Basis/FactQ, and nobody
imports MaynardVerify). I confirmed this by running
`Print Assumptions maynard_eigenvalue_S1` after a fresh
`coqc Cert.v`: the output contains only Uint63 axioms — no Maynard
spec, no `M1_correct`, no `M2_correct`.

Consequence: the headline theorem proves "the FLINT-shipped 42×42
matrices `M1_int / D_M1` and `M2_int / D_M2` define an `A_rat` whose
char poly has a realalg root above 4/105". That is genuinely true
about the shipped data. But it is **not** equivalent to "Maynard's
M_{105} is > 4". Connecting the two requires the entry-wise
identification `M1_int[i][j] / D_M1 = M1_entry(b_i,c_i,b_j,c_j)`
done in `MaynardVerify.v` (`all_match_M1Z_true`,
`all_match_M2Z_true`).

The author of `MaynardVerify.v` explicitly states this:
- `MaynardVerify.v:58`: *"The headline theorem
  `maynard_eigenvalue_S1` does not depend on them either — this
  file is a leaf in the dependency DAG and is not imported by
  Cert.v."*

So the project is internally honest. But:
- `README.md` lines 40–48 present the headline + `Print Assumptions`
  as evidence that the *Maynard claim* (not merely "this A_rat has
  this property") is closed end-to-end. A careful reader has to
  follow the dependency graph to discover that one would also need
  to invoke `all_match_M1Z_true` / `all_match_M2Z_true`, and that
  the analytic identification of `M1_entry` (resp. `M2_entry`) with
  Maynard's textbook closed forms is not formalised at all
  (`MaynardSpec.v:6-9`).
- `REPORT.md` §3.7 / §6 do mention this, but the README does not.

**Recommendation**: state the headline truthfully as
*"The shipped FLINT certificate is internally consistent: it produces
an A_rat with eigenvalue > 4/105"*, and call out the residual trust
items (Maynard-spec correctness; FLINT generator correctness for
M1_int / M2_int) as separate. Or extend `Cert.v` to additionally
state and use `all_match_M1Z_true` / `all_match_M2Z_true`, so that
the headline includes "and these matrices match Maynard's closed
form". This would tie MaynardVerify into the trust loop.

### M2. L4 (`maynard_bridge_L4`) is dead code

`Cert.v:89-100` defines `maynard_bridge_L4` but the headline
theorem `maynard_eigenvalue_S1` (`Cert.v:109-120`) does not call
it. `grep -n "maynard_bridge_L4"` in the entire codebase returns
exactly two lines (the definition itself and a comment header).

`REPORT.md:603` says *"Four small lemmas glue L1–L4 together"* and
`README.md:47` writes `Proof. (* L1 + L2 + L3 + L4 *) Qed.` Both
overstate. `REPORT.md:998-1003` does correctly clarify *"included for
reference; the headline states the 4/105 < λ form directly"*, so
the disagreement is internal to the documentation.

**Subtle technical note** — L4's body uses
```
by rewrite (_ : (4 / 105 : realalg) = ratr (4%:~R / 105%:~R)).
```
A naive reading would expect `by rewrite (_ : A = B)` to leave the
side condition `A = B` for `done` to discharge. I sanity-checked
in a small replica: the equality really *is* reflexive in MathComp
2.5/realalg, because `4 : realalg` elaborates through the same
canonical-structure chain as `ratr (4%:~R)` and the `mulrV` /
`fmorphV` / `rmorph_div` morphism applications cancel under the
`%:~R` int cast. So this rewrite does close the goal cleanly. But
it is *fragile*: a future MathComp release that adds a coercion or
a canonical instance could break the convertibility, leaving a
silently-failing `by`. Replacing it with an explicit
`rewrite -fmorph_div -!rmorph_int.` would be safer and not
significantly more verbose.

### M3. `Z_to_int` opacity is file-local; downstream proofs depend on it being transparent

`CertL2.v:58` declares `Opaque Z_to_int.` (without `Global`).
This setting is local to the *compilation* of `CertL2.v` and does
not propagate to `Cert.v` (I verified: file-level `Opaque foo` does
not cross `Require Import`). `Cert.v` line 67 then unfolds with
`rewrite /Z_to_int /=`:
```
have : D_q = BinNums.Z0
  by destruct D_q as [|p|p];
     [reflexivity
     |exfalso; rewrite /Z_to_int /= in Hz;
      injection Hz => Hz';
      have := Pos2Nat.is_pos p; rewrite Hz';
      exact (Nat.lt_irrefl 0)
     |exfalso; discriminate Hz].
```
This works in the current build. But if anyone added
`Global Opaque Z_to_int` (a tempting move for build-time speed,
since `Z_to_int D_q` is a 250-digit constant), this proof would
fail with `Z_to_int is opaque`. The right fix is either:
- promote `Opaque Z_to_int` to `Global Opaque` in `CharPoly.v` (its
  defining file) and replace the `rewrite /Z_to_int` in `Cert.v`
  with explicit `change` / a small lemma (e.g. `Z_to_int_pos :
  Z_to_int (Zpos p) = Posz (Pos.to_nat p)`); or
- add a comment in `Cert.v` warning that `Z_to_int` is needed
  transparent here.

### M4. `mat_int_to_rat M D n` is total even when D = 0 or `n != mat_dim M`

The defining clause (`CharPoly.v:146-149`) is
```
\matrix_(i, j) ((Z_to_int (mat_get M (nat_of_ord i) (nat_of_ord j)))%:~R
                / (Z_to_int D)%:~R)
```
where `mat_get` returns 0 on out-of-range and `_ / 0 = 0` in
MathComp's convention. So `mat_int_to_rat M 0 n` is the zero matrix,
and `mat_int_to_rat M D 100` for a 42×42 list-of-list would zero-pad
to 100×100. This is fine — the call sites `M1_int 1 42` etc. are all
well-formed — but the defensive defaulting means a *typo* (e.g.
`mat_int_to_rat M1_int D_M1 41` instead of `42`) would silently
produce a meaningful-looking matrix that is not what was intended.
There is no positive lemma in `CharPoly.v` saying
`mat_int_to_rat M 0 n = 0` or `n = mat_dim M ->
mat_int_to_rat M ...` — those would be defensive, but no correctness
issue.

## Minor findings

### m1. `Hk : (k < 43)%coq_nat` then converted to MathComp `(k <= 42)%N`

`CertL2.v:407` does
```
have Hk' : (k < 43)%coq_nat by apply/ltP; rewrite ltnS.
```
The MathComp/Stdlib nat type is the same, but the comparison operators
disagree, and round-tripping `apply/ltP` / `ltnS` works but is the
sort of thing that goes wrong silently when a future `Set Implicit
Arguments` or `Set Bullet Behavior` change. Since this is the only
crossover point at this call site, a single
`Lemma kbnd : (k <= 42)%N` would be cleaner.

### m2. `mat_int_to_rat_scale_inv'` proof reaches inside MathComp

`CertL2.v:84`: `apply/matrixP => i j. rewrite /mat_int_to_rat !mxE
GRing.mulr1. by rewrite GRing.mulrC.` This unfolds the definition
and reasons per-entry. Cleaner would be a one-line proof going
through `linearZ` / `scalemxAl`. Not a correctness issue.

### m3. `change` in `M1_1_unit` tactically fragile

`CertL2.v:166`:
```
change (horner_eval 0 (\det (char_poly_mx (mat_int_to_rat M1_int 1 42))) = 0).
```
`change` requires definitional equality with the current goal.
The goal at this point is `(pol_to_polyrat (char_poly_int M1_int))`_0
= 0`, and the `change` invokes the equation
`pol_to_polyrat (char_poly_int M1_int) = char_poly (mat_int_to_rat M1_int 1 42)`
that has been derived as `Hcpi`, but only via a previous `Hcpi` rewrite.
Actually: line 164 does `rewrite -horner_coef0 Hcpi /char_poly` first,
so by the time `change` runs at 166 the goal is already in
char-poly form. The `change` then folds the `\det / horner_eval / map_mx`
unfolding chain. This works, but a `set` on a smaller subterm and
explicit equational reasoning would be more robust. Not a soundness
issue, just engineering quality.

### m4. The "L4 fmorph reflexivity" relies on `4 = ratr 4%:~R` being convertible

(Same root cause as M2's "subtle technical note".) I tested in a
small file — *yes*, in MathComp 2.5 + realalg the equality
`(4 / 105 : realalg) = ratr (4%:~R / 105%:~R)` is reflexive. So
`by rewrite (_ : ... = ...)` succeeds. This is convenient but
brittle; if MathComp ever changes a `Numeral Notation` or a
`Coercion` so that `4 : realalg` lands at a slightly different
canonical form, the proof breaks with no easy diagnostic (the
error message will be "tactic failure: cannot rewrite", not
"the side condition is non-reflexive"). Suggestion: replace
with the explicit one-liner

```
by rewrite -fmorph_div !rmorph_int.
```

which makes the proof robust to canonical-structure migration.
This is doubly true given that L4 is dead code (M2): there is no
external pressure to keep it short.

### m5. `BrownTraub.next_mod p q := pneg (prem p q)` matches MathComp's `mods` only up to a positive scalar at each step

This is not a finding against the headline (the headline doesn't
go through `BrownTraub.mods_int` — see Observation O2 below), but
worth flagging in case a future sprint resurrects the Sturm-bridge
plan. `Bridge.v:106-110` admits this honestly: *"From this the
equality `mods_int_morph` itself cannot be recovered directly (the
chains differ by scalars), but the sign-variation counts ARE
invariant under positive scaling."* The strict equality
`mods_int_morph` was *removed* from `Bridge.v` (see line 118,
`(* The strict equality `mods_int_morph` was removed from this
file (it is unprovable: chains differ by polynomial scalars). *)`).
Good.

### m6. Documentation/code lemma-naming discrepancies

- `MaynardVerify.v:43-60` describes axioms `M1_correct` /
  `M2_correct` that have since been removed (commit `e9de5e3
  "MaynardVerify: drop unused rat-level matrix axioms"`). The
  comment is stale: there are no such axioms in the file today.
  `grep -n "Axiom\|Parameter\|Conjecture" MaynardVerify.v` returns
  nothing.
- `Bridge.v:104-110` describes `next_mod_scaled_morph` as the
  "STRUCTURAL STEP lemma (hardest, and the only one actually
  admitted inside the proof)". I could not find an
  `Admitted`-marked lemma anywhere in the project (`grep -rn
  "Admitted\|^Axiom\|^Parameter" theories/S1/*.v` returns only
  comment hits and definitions). The comment looks pre-rewrite.
- `REPORT.md:603` and `README.md:47` claim L4 is part of the
  headline assembly; in fact it is not (M2).

These are aesthetic, but matter for a reviewer reading
`MaynardVerify.v` or `Bridge.v` head comments to understand the
trust state.

## Observations on proof engineering quality

- **Dimension separation.** The `abstract_mat_scale` /
  `char_poly_scale_rat42` / `expf_neq0_rat` / `mat_cancel_helper`
  pattern (CertL2.v) is excellent. The author isolates expensive
  MathComp canonical-structure resolution to abstract-`n` lemmas
  and only specialises to `n = 42` at the `Qed` step, both
  documenting the pattern and justifying it (CertL2.v:318-339).
  This is exactly the right idiom for working at concrete dim 42
  with MathComp 2.5's HB elaboration.

- **`pol_to_polyrat` ↔ `pol_to_polyralg` coherence.** Definitionally
  identical — `pol_to_polyralg p := map_poly ratr (pol_to_polyrat p)`
  in `Bridge.v:56`, and `charpoly_as_poly_realalg` in `Cert.v:41`
  is the same expression. So `exact maynard_L1_concrete` works in
  `sturm_count_correct` by convertibility. No bridge lemma needed.

- **Decoupling Sturm chain from the headline.** The Sturm-chain
  scaffolding (`BrownTraub.v`, `SignChain.v`, `WitnessChain.v`,
  `CRTSigns.v`, the `mods_int_morph` plan in `Bridge.v`) was
  superseded: the headline now goes through IVT
  (`maynard_L1_concrete` uses `poly_ivtoo`), needing only the
  *single-point* sign verification at `4/105` and the leading-
  coefficient sign at `+∞`. Both come from `signs_at_x0_shipped`
  /`signs_at_inf_shipped` (`CRTSigns.v:139-150`), which compute
  signs entry-by-entry on the chain and then expose the *head*
  entry (which equals `charpoly_int` by `shipped_chain_hd`). The
  sign-variation count and Sturm correctness are *not used*. This
  is a major design simplification that I want to call out
  positively.

- **`charpoly_int_Dq_scaled` proof structure.** The `polyP =>`
  apply/`coefZ`/`leqP k 42` split, the
  `nth_default + size_pol_to_polyrat_bound` for the high-coeff
  branch, and the `mat_cancel_helper` for the low-coeff branch
  is a clean factorisation. The proof is robust and reads well.

- **Sign and scalar handling in `abstract_mat_scale`.** The lemma
  is stated in the form `c1^-1 *: M1_1` to mirror exactly the
  shape of `mat_int_to_rat M D n =
  (Z_to_int D)%:~R^-1 *: mat_int_to_rat M 1 n`. The math
  (`A = (c1*cA/c2) *: invmx M1_1 *m M2_1` matched against
  `cA *: invmx (c1^-1 *: M1_1) *m (c2^-1 *: M2_1)`) checks out.

## What I checked and confirmed correct

1. `eigenvalue` is the standard MathComp predicate
   `fun a => eigenspace a != 0` where
   `eigenspace a := kermx (g - a%:M)` (mxalgebra.v:2208-2212).
   Combined with `eigenvalue_root_char` it is exactly "λ is an
   eigenvalue of A iff λ is a root of `char_poly A`". The headline's
   use is the standard one.
2. `4%:Q / 105%:Q : rat` really is the rational `4/105` (not a
   truncated-int division). Ground truth: `rat.v:524`,
   `Notation "n %:Q" := ((n : int)%:~R : rat)`. So
   `4%:Q = (4 : int)%:~R : rat = 4 : rat`, and the slash is
   field division. Verified by reading the notation table.
3. `ratr (4%:Q / 105%:Q) : realalg` equals
   `(4 : realalg) / (105 : realalg)` *definitionally* (verified
   by spot-compile; `reflexivity` succeeds). Hence the
   `(_ : ... = ...)` rewrite in L4 closes by `done`.
4. `A_rat` lives in `'M[rat]_42`; `map_mx ratr A_rat` lives in
   `'M[realalg]_42`; `eigenvalue` is invoked with `n = 42` and
   `F = realalg`. Dimensions are consistent throughout.
5. `D_q`, `D_M1`, `D_M2`, `D_A` are concrete positive `Z` values
   (`Witness.v:68, 1923, 3778, 5689`). All `Z_to_int` casts
   correctly produce positive `Posz n` int-values.
6. `mat_identity_rat` has the right scalar factors:
   `D_M2 *: (M1_1 *m A_1) = (D_M1 * D_A) *: M2_1` corresponds to
   the cleared identity `M1 * A = M2` after multiplying through
   by the three denominators.
7. `char_poly_scale` (`CharPolyScale.v:49-81`) correctly proves
   `(char_poly (c *: M))`_k = c^(n-k) * (char_poly M)`_k`
   for `k ≤ n`, using the standard `detZ` + composition argument.
8. `charpoly_root_transfer` (`Cert.v:60-69`) correctly handles
   sign cases for `D_q ≠ 0`. The case-bash on `D_q : Z`
   (`Z0 / Zpos / Zneg`) treats `Z0` as the trivially-true target
   (`reflexivity`), and gives `False` for the other two via
   `injection`/`Pos2Nat.is_pos` (positive case) and `discriminate`
   (negative case). The final `discriminate` exploits the fact
   that `D_q : Z` is a concrete `Zpos` literal so `D_q = Z0` is
   constructor-disjoint.
9. `Print Assumptions maynard_eigenvalue_S1` shows only Uint63
   kernel primitives (verified by `coqc`-ing a small wrapper in
   `/tmp/test_assumptions.v`, ~30 s).

## Open questions / things I could not fully verify

- I did not exhaustively read `CRTLift.v` (1236 lines); I
  confirmed `matrix_identity_Z`, `fl_eq_flint`,
  `length_char_poly_int_A` are the relevant exports and that they
  proceed via 710-prime CRT cross-checks plus a Hadamard-style
  bound on coefficients. The auditor would want to spot-check the
  bound (`max_abs_entry_mzero`, `charpoly_fl_recurrence_bound`)
  and the FL recurrence bookkeeping carefully.
- I did not run `Print Assumptions` on `all_match_M1Z_true` /
  `all_match_M2Z_true` (the M2 one takes ~35 min by author's
  estimate; the M1 one ~90 s). The author claims they show only
  Uint63 axioms.
- I did not formally verify that `MaynardSpec.v`'s `M1_entry` /
  `M2_entry` rat-valued formulas correctly transcribe Maynard's
  paper. The file itself states (line 8-9) *"the analytic
  identification is not proved in this project"*. This is a math
  audit question, not a Rocq one.
- I did not check that `cauchy_bound` from
  `mathcomp.real_closed.polyrcf` is the *strict* upper bound used
  by `ge_cauchy_bound` (audit point: does
  `charpoly_pos_at_cb` rely on `cauchy_bound P` being a *root-
  free* upper bound, vs just an upper bound on root *moduli*?
  `CertL1.v:380-399` uses `ge_cauchy_bound` to argue P has no root
  ≥ b, then uses `sgp_pinftyP` to conclude
  `sgr P.[b] = sgp_pinfty P = +1`. Internally consistent, but I
  didn't trace the polyrcf API to verify
  `ge_cauchy_bound HP : forall x, x ∈ `[b, +oo[ -> ~~ root P x`
  has the orientation I'm assuming.) Worth a 10-minute spot check
  by a polyrcf-fluent reader.

## Summary

Soundness: clean. The headline theorem closes with only Uint63
kernel axioms. The proof engineering, while occasionally hand-tuned
to dodge MathComp 2.5 / HB canonical-structure timing pitfalls, is
overall well-factored and well-documented. The
`abstract_mat_scale` / `char_poly_scale_rat42` /
`mat_cancel_helper` pattern is exemplary.

The two main concerns are *documentation*:
- The headline does not actually invoke L4 (despite README's
  `(* L1+L2+L3+L4 *)` comment).
- `MaynardVerify.v` is *not* on the path to the headline. The
  README/REPORT mention this but only obliquely; a casual reader
  could be misled into thinking the headline carries Maynard-spec
  identification. It does not.

Both can be fixed by tightening the README and adding two lines to
`Cert.v` (a `Require Import MaynardVerify` and a clause in the
headline using `all_match_M1Z_true` and `all_match_M2Z_true`).
That would fully close the trust loop for the M1/M2 entries and
align the documentation with the actual dependency graph.
