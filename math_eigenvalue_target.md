# S1 stretch target: a Rocq theorem mentioning an eigenvalue

Audience: the team formalizing Maynard `M_{105} > 4` in Rocq. This note picks
the precise Rocq statement S1 should aim at, and lists the bridge lemmas
between the FLINT-shipped Sturm certificate and that statement. All MathComp
identifiers below were checked with `rocq_query`; none are guesses.

## 1. Three forms of the theorem

Let `M1_rat M2_rat : 'M[rat]_42`, both symmetric, `M1_rat` SPD. Let
`k := 105`, threshold `θ := (4%:Q / 105%:Q)`. Every form uses `realalg` as
the ambient rcf.

**(I) Operator-pencil form (generalised eigenvalue).**
English: there is a real `λ > 4/105` and a nonzero real 42-vector `v`
with `M2 v = λ · M1 v`.

```rocq
Theorem maynard_S1_pencil :
  exists (lambda : realalg) (v : 'rV[realalg]_42),
    v != 0
 /\ v *m (map_mx ratr M2_rat) = lambda *: (v *m (map_mx ratr M1_rat))
 /\ (ratr (4%:Q / 105%:Q) : realalg) < lambda.
```

**(II) Polynomial-pencil form (root of `det(M2 − x M1)`).**
```rocq
Definition detpencil : {poly rat} :=
  \det (map_mx polyC M2_rat - 'X *: map_mx polyC M1_rat).

Theorem maynard_S1_detpencil :
  exists lambda : realalg,
    root (map_poly ratr detpencil) lambda
 /\ (ratr (4%:Q / 105%:Q) : realalg) < lambda.
```

**(III) Standard char-poly form.**
```rocq
Definition A_rat : 'M[rat]_42 := invmx M1_rat *m M2_rat.

Theorem maynard_S1_charpoly :
  exists lambda : realalg,
    eigenvalue (map_mx ratr A_rat) lambda
 /\ (ratr (4%:Q / 105%:Q) : realalg) < lambda.
```

`eigenvalue : forall (F : fieldType) (n : nat), 'M_n -> pred F` is the
MathComp predicate (`mxalgebra`); by `eigenvalueP` it is the reflection of
`exists2 v, v *m A = a *: v & v != 0`, and by `eigenvalue_root_char` it is
equal (as booleans) to `root (char_poly A) a`. So form (III) implicitly
bundles both the "Av = λv" and the "root of char poly" readings, and gives us
the cleanest handle to the Sturm side via `char_poly`.

## 2. Recommended target: (III)

Confirming the user's instinct: **pick (III)**. Rationale:

- The FLINT pipeline ships the standard char poly `q = det(xI − A)`,
  i.e. `char_poly A` up to sign conventions (MathComp uses `char_poly A :=
  \det (char_poly_mx A) = \det ('X%:M − A%:M)`, same object). So L2 only
  needs to equate a shipped `list Z` with `char_poly A_rat`, which is
  syntactically the MathComp target. Form (II) would force us to additionally
  unfold a polynomial-matrix determinant; form (I) would force us into
  `mxalgebra`'s kernel/image lemmas for the non-standard pencil and would
  need a generalised-eigenvalue infrastructure that MathComp does not ship.
- `eigenvalue_root_char` and `eigenvalueP` are already in MathComp, giving
  L3 for free.
- `A_rat` is a single `'M[rat]_42`; no auxiliary `{poly rat}`-valued matrix
  in the statement.
- `map_char_poly` (confirmed present) commutes `ratr` with `char_poly`, so
  the Sturm count done in `realalg` matches the char poly of the rational
  matrix.

(II) remains a useful intermediate *lemma* (it is how we ultimately tie in
`det M1` if we ever want it), but it is not the statement of S1.

## 3. Bridge-lemma chain, smallest to biggest

Let `q_rat : {poly rat} := char_poly A_rat`, `q_RA := map_poly ratr q_rat :
{poly realalg}`, `θ := ratr (4%:Q / 105%:Q) : realalg`, `p_int : {poly int}`
the common-denominator-cleared integer char poly shipped from FLINT. Let
`n_sturm : nat` be the value the FLINT chain's verified `V(θ) − V(+∞)`
computation produces in Rocq on a `list Z`-based polynomial representation.

- **L1 — Sturm count = real-root count.** From `changes_itv_mods_cindex` and
  `taq_taq_itv` over `realalg`, plus the fact that `cindexR` of `(p', p)`
  (resp. on `(θ, +∞)`) equals `#{r : realalg | root q_RA r, θ < r}`.
  Statement:
  `n_sturm = size [seq r <- polyrcf.roots q_RA θ B | true]` for some
  `B > all roots of q_RA`, which by `taq_taq_itv` with `q := 1` equals the
  cardinal of real roots of `q_RA` in `(θ, B)`.
  Reduces to: `taq_taq_itv`, `changes_itv_mods_cindex` (both confirmed),
  plus a one-off lemma discharging the non-vanishing side conditions at `θ`
  and at the upper bound. **Effort: medium.** The ugly piece is the
  `all (fun p0 => p0.[a] != 0) (mods …)` sanity clauses, which themselves
  need a `vm_compute`-certified check on the integer-cleared chain.

- **L2 — shipped polynomial equals `char_poly A_rat`.** The only truly
  load-bearing bridge; see section 4 for the chosen strategy.
  Statement: `map_poly intr p_int = (lcm_den p_int) *: char_poly A_rat`
  (or: `char_poly A_rat = (1 / lcm_den) *: map_poly intr p_int`).
  **Effort: medium–hard**, driven entirely by whether we can avoid
  `vm_compute`ing `char_poly A_rat`.

- **L3 — root of char poly = eigenvalue.** `eigenvalue_root_char` gives
  `eigenvalue A a = root (char_poly A) a` as a boolean equality. Combined
  with `map_char_poly` this pushes over `ratr : rat → realalg`.
  Statement:
  `root q_RA λ ↔ eigenvalue (map_mx ratr A_rat) λ`.
  Reduces directly to: `eigenvalue_root_char` + `map_char_poly`.
  **Effort: trivial.**

- **L4 — Maynard bridge.** By definition `M_k = k · λ_max((M2, M1))` with
  `λ_max` the largest generalised eigenvalue. For SPD `M1`, this equals the
  largest eigenvalue of `A = M1⁻¹ M2`. So `λ > 4/105` on the largest such
  eigenvalue is equivalent to `105 · λ > 4`, i.e. `M_{105} > 4`. In the
  Rocq statement of S1 we do **not** need to formalise "largest" — having
  *some* eigenvalue `> 4/105` suffices, because the sup is monotone.
  Statement: `(exists λ, eigenvalue A λ ∧ θ < λ) → M_k > 4`.
  Reduces to: one `Definition` unfold of `M_k`, and the sup-monotonicity
  inequality `λ ∈ S → sup S ≥ λ` (MathComp has this for bounded sets; for
  a finite set it is `\max_`-based). **Effort: easy**, provided we accept
  that `M_k` is *defined* as `k * λ_max` rather than as a sup over a
  function space. If we insist on the function-space definition we need
  Rayleigh-Ritz `k · (vᵀ M2 v)/(vᵀ M1 v) ≤ k · λ_max`, which is a further
  medium lemma but is the same one the witness MVP already carries.

## 4. L2: how to equate a `list Z` with `char_poly A_rat` without computing
`char_poly` on the MathComp side

Given the performance wall (`vm_compute` on `'M[rat]_42` times out, as does
`vm_compute` on `{poly rat}` and `{poly int}`), we **cannot** reduce L2 to a
`reflexivity` against the MathComp char poly. Two routes:

**(A) Shadow implementation in `list (list Z)`.** Write
`char_poly_int : list (list Z) -> Z -> list Z` (Faddeev–Leverrier; for
`A = M1⁻¹ M2` start from `D_A := det M1`-cleared `M2 · adj M1` and track a
second scalar denominator). Prove once-and-for-all
`Lemma char_poly_int_correct : forall M D,
  map_poly intr (Poly (char_poly_int M D)) =
  D%:~R ^+ 42 *: char_poly (rat_of_intmat M D)`
using the abstract spec but *not* `vm_compute` on the abstract side; the
proof is an induction on the Faddeev recurrence matched against
`char_poly_trig` / `mulmx_addl`. Then the FLINT polynomial is literally
`char_poly_int M1M2_int D_int`, and equality to what Rocq rebuilds from
`M1_int, M2_int` is a `vm_compute; reflexivity`.

**(B) Bypass char_poly.** Work directly with `det(xI − A)` as a polynomial
living inside `polyrcf`'s `cindex`/`taq` world, using a custom Rocq
reflection that equates the FLINT-shipped `{poly rat}` with the
matrix-pencil determinant through a `\det`-expansion lemma. This is the
path Cyril Cohen's `qe_rcf_th` uses internally.

**Recommendation: (A).** Rationale:

1. (A) decouples the heavy computation (once-compiled `char_poly_int_correct`)
   from the per-instance proof. The per-instance `vm_compute; reflexivity`
   only needs to run on `list Z`, which we have already measured is fast.
2. (A) lets us reuse `eigenvalue_root_char` unchanged — we land exactly on
   `char_poly A_rat`, which is where L3 wants us.
3. (B) moves all the weight into one custom `cindex`-pencil chain lemma,
   which has **no** counterpart in MathComp and which we would have to
   invent; L2 would become an order of magnitude more painful, and L3 would
   also need to be re-derived without `char_poly_mx`.
4. The `char_poly_int_correct` lemma in (A) is proved *abstractly* (by
   induction on Faddeev, never `vm_compute`ing anything), so the
   "MathComp side is computationally dead" constraint is respected.

## 5. `n ≥ 1` → `exists root` is fine

The `polyrcf.roots` seq is built via a non-effective `projT1` of a
classical existence proof (confirmed: `roots : forall R : rcfType, {poly R}
→ R → R → seq R`, and its construction goes through `sig` in `polyrcf.v`).
That is **exactly what we want** for S1: S1 only claims the *existence* of
an eigenvalue above `4/105`, never its value. Going from `size (roots q_RA
θ B) >= 1` to `∃ r, r \in roots q_RA θ B` is one `lt0n`/`mem_nth` step, and
then `in_rootsP` / `rootsP` (from `polyrcf`) turns membership into
`root q_RA r ∧ θ < r ∧ r < B`. No computation on `realalg` is required; the
whole witness is a classical existence proof, whose *numerical* content is
borne entirely by the integer Sturm chain. This is the right separation of
concerns.

## 6. `> 4` vs `> 4/105` — definitely `4/105`

Maynard defines `M_k := k · sup_{v ≠ 0} (vᵀ M2 v) / (vᵀ M1 v)`. The claim
`M_{105} > 4` therefore reads `105 · λ_max > 4`, i.e. `λ_max > 4/105`, for
`λ_max` the largest generalised eigenvalue of `(M2, M1)` (equivalently, the
largest eigenvalue of `A = M1⁻¹ M2`). The FLINT pipeline already computed
`V(4/105) − V(+∞) = 1` and Arb cross-checked
`k · top = 4.00206976193804713…`, so "threshold 4/105 on the eigenvalue"
is the consistent story. **Anywhere the Rocq theorem writes a literal 4 it
is wrong — it must be `4 / 105`.** The outer statement `M_{105} > 4` only
appears after L4 multiplies through by `k = 105`.

## 7. Final Rocq theorem statement (S1 target)

```rocq
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import realalg.
Import GRing.Theory Num.Theory.
Open Scope ring_scope.

Section MaynardS1.

(* The exact rational Gram matrices from Maynard §7, k = 105, |B| = 42. *)
Variable M1_rat M2_rat : 'M[rat]_42.
Hypothesis M1_unit : M1_rat \in unitmx.

Definition A_rat : 'M[rat]_42 := invmx M1_rat *m M2_rat.

Theorem maynard_eigenvalue_S1 :
  exists lambda : realalg,
    eigenvalue (map_mx (ratr : rat -> realalg) A_rat) lambda
 /\ (ratr (4%:Q / 105%:Q) : realalg) < lambda.

End MaynardS1.
```

Checked identifiers (all via `rocq_query`):
- `eigenvalue : forall (F : fieldType) (n : nat), 'M_n -> pred F`
- `eigenvalueP : reflect (exists2 v : 'rV_n, v *m g = a *: v & v != 0)
  (eigenvalue g a)`
- `eigenvalue_root_char : eigenvalue A a = root (char_poly A) a`
- `char_poly : 'M_n -> {poly R}`
- `char_poly_mx : 'M_n -> 'M[{poly R}]_n`
- `map_char_poly : map_poly f (char_poly A) = char_poly (A ^ f)`
- `map_mx : (aT -> rT) -> 'M_(m,n) -> 'M_(m,n)`
- `invmx : 'M_n -> 'M_n`
- `ratr : rat -> R`
- `realalg : Type` (the canonical `rcfType`)
- `taq_taq_itv`, `changes_itv_mods_cindex` (`qe_rcf_th`)
- `polyrcf.roots : {poly R} -> R -> R -> seq R`

Open side obligations to track as S1 lands: (a) `char_poly_int_correct`
(Faddeev–Leverrier shadow, L2); (b) the `all (… != 0 at a)` side
conditions on `taq_taq_itv` (L1); (c) the L4 definition of `M_k` in Rocq,
reusing the witness MVP's Rayleigh-Ritz lemma to tie `eigenvalue > 4/105`
to `M_{105} > 4`.
