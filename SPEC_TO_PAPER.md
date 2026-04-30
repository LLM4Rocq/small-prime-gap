# SPEC_TO_PAPER.md — Mapping `MaynardSpec.v` to arXiv:1311.4600 §7/§8

**Project:** Rocq formalisation of Maynard's `M_{105} > 4`
(`/home/rocq/prime_gap/`).
**Paper:** James Maynard, *Small gaps between primes*, arXiv:1311.4600.
- v1 (preprint, 2013): the relevant material is §7 — Lemmas 7.1, 7.2, 7.3.
- v3 (Annals 181 (2015) 383–413): the same material is §8 — Lemmas 8.1, 8.2, 8.3.

The two numberings are content-identical (`§7 ≡ §8`, `Lemma 7.x ≡ Lemma 8.x`).
Throughout this document we use the **v3 / Annals** numbering, consistent with
`REPORT.md`. Where the paper formula has a clear v1 line reference we list
both.

This file closes audit finding **M-4** (`audit_mathematician.md`):
`MaynardSpec.v` was previously documented only against the reconstructed
Mathematica notebook `notebook_reconstructed.md`, which is a
re-derivation of Maynard's original `Computations.nb`. The mapping to
the *paper* lived in reviewer heads. This document provides the line-level
citation-style mapping that the audit asked for.

## How to read this document

For each Rocq definition in `theories/S1/MaynardSpec.v` we give:

1. The Rocq source (file + line range, read directly out of the .v file).
2. Maynard's paper formula in the v3/§8 numbering.
3. A symbol-by-symbol mapping `Rocq factor ↔ paper symbol`.
4. A small-`n` (or small-`k`) sanity check, where one is illuminating.

We close with two sections: what is verified *inside* the Rocq kernel
(by `vm_compute` over all 1764 entries of each matrix) and what is left
to the paper.

The reader is assumed to be comfortable with undergraduate linear algebra
and combinatorics. No prior knowledge of the project's internals or of
MathComp is required.

---

## 1. Conventions

### Paper conventions

In §8 Maynard works with smooth symmetric test functions
`F : ℝ_{≥0}^k → ℝ` supported on the simplex `{Σ t_i ≤ 1}` and with the
quadratic forms

```
I_k(F)       = ∫_{Δ_k} F(t)² dt
J_k^{(m)}(F) = ∫_{Δ_{k-1}}  ( ∫_0^{1 - Σ_{i ≠ m} t_i} F(t) dt_m )² dt_{≠ m}
M_k          = sup_F  ( Σ_m J_k^{(m)}(F) ) / I_k(F).
```

By symmetry of `F` in its `k` arguments, all `J_k^{(m)}` are equal, so
`Σ_m J_k^{(m)} = k · J_k^{(1)}`.

Maynard then **restricts** `F` (for tractability — paper p. 23, "for
simplicity") to the linear span of the monomials

```
((1 - P_1)^b · P_2^c)         with  b + 2c ≤ deg_max,    P_1 = Σ t_i,  P_2 = Σ t_i².
```

For `deg_max = 11` this span has dimension 42 (the basis in question; see §8
below for the count). The matrices `M_1`, `M_2` are the Gram matrices of
the inner products `(F, G) ↦ I_k(F·G)` and `(F, G) ↦ J_k^{(1)}(F·G)` on
this 42-dimensional subspace. Lemma 8.2 gives closed forms for their
entries; Lemma 8.3 says

```
M_k = k · λ_max( M_1^{-1} M_2 )         (when this matrix is per-coordinate J_k^{(1)})
```

so any rigorous lower bound on `λ_max` of at least `4/k` would yield
`M_k > 4`.

In the paper, indices `(b_i, c_i)` and `(b_j, c_j)` denote the bidegrees
of the `i`-th and `j`-th basis monomials. The paper writes `k` for the
outer integration dimension; in our formalisation this is `k_param = 105`.

### Rocq conventions

`MaynardSpec.v` uses two parallel implementations of the same closed forms:

- **Part A (rat-level)**: `bnd`, `cff`, `G_2`, `M1_entry`, `alpha`,
  `M2_entry` — readable side-by-side with Maynard's paper, all valued
  in MathComp's `rat`.
- **Part B (Z-level)**: `bndZ`, `cffZ`, `G2Z`, `m1_num_den`, `alphaZ`,
  `m2_num_den` — same closed forms, but each rational result is presented
  as a `(num, den) : Z * Z` pair. Used by `MaynardVerify.v` because
  `vm_compute` on `'M[rat]_42` triggers MathComp's HB canonical-structure
  elaborator and stalls (REPORT.md §4d).

The two are connected by the `M1_spec_rat_eq`/`M2_spec_rat_eq` bridges in
`MaynardSpec.v` (sanity checks, not on the critical path of
`MaynardVerify`).

### The `K = 105` vs `K2 = 104` distinction

The constant of integration changes after the substitution that
"integrates out" `t_1` (Lemma 8.2 / eq. 8.8). Concretely:

- The outer integrand for `M_1` is taken over the `k`-simplex `Δ_k`:
  the Rocq spec uses `K1 := 105` (matches `Witness.k_param`).
- Inside `M_2`, after the eq. 8.8 expansion, the residual integral is
  on the `(k - 1)`-simplex `Δ_{k-1}`: the Rocq spec uses `K2 := 104`
  (= 105 − 1) for the `G_{·,2}` factor that appears at the second layer.

This is **not** a typo or an off-by-one: see audit note **N-4**
(`audit_mathematician.md`) for the algebraic reconciliation
`K2 + b_sum + 2 c_sum = 105 + (b_i + b_j + 2c_i + 2c_j) + 1`, which is
exactly Maynard's M2 denominator.

---

## 2. `MaynardSpec.bnd i n` ↔ Maynard's `Bnd(i, n)`

### Source

`theories/S1/MaynardSpec.v:48–61`:

```rocq
Fixpoint enum_bnd_aux (slots_left remaining : nat) : seq (seq nat) :=
  match slots_left with
  | 0 => [:: [::] ]
  | S m =>
      if (remaining <= m)%N then [::]
      else
        let upper := (remaining - m)%N in
        flatten
          [seq [seq (ai :: tl) | tl <- enum_bnd_aux m (remaining - ai)%N]
             | ai <- iota 1 upper]
  end.

Definition bnd (i n : nat) : seq (seq nat) :=
  if (n == 0)%N then [::] else enum_bnd_aux i (n - 1)%N.
```

### Paper

Maynard, Lemma 8.1 (v1 Lemma 7.1), proof: the inner sum in `G_{n,2}(k)`
is over compositions

```
{ (b_1, …, b_i) ∈ ℕ_{≥1}^i  :  Σ b_j ≤ n − 1 }.
```

(The implicit final part `b_{i+1} = n − Σ b_j` must also be `≥ 1`,
which is why we require `Σ b_j ≤ n − 1` rather than `≤ n`.)

### Mapping

| Rocq | Paper | Note |
|------|-------|------|
| `i` (slots) | length of the composition `(b_1, …, b_i)` | |
| `n` (Rocq `bnd`'s 2nd arg) | the polynomial degree `n` | |
| `remaining = n − 1` | upper bound on `Σ b_j` | "`b_{i+1} ≥ 1`" |
| recursive call `enum_bnd_aux m (remaining - ai)` | fix `b_1 = ai`, recurse on `(b_2, …, b_i)` | |
| guard `remaining ≤ m` ⇒ `[::]` | not enough budget left for `m` parts each `≥ 1` | base prune |
| guard `slots_left = 0` ⇒ `[[::]]` | one empty composition (the `i = 0` case) | base case |

### Sanity check

- `bnd 0 n = [[::]]` for `n ≥ 1` — one empty composition. ✓
- `bnd 1 3` enumerates `(b_1)` with `b_1 ≥ 1`, `b_1 ≤ 2`: outputs
  `[[1]; [2]]`. ✓
- `bnd 2 4` enumerates `(b_1, b_2)`, both `≥ 1`, sum `≤ 3`: outputs
  `[[1;1]; [1;2]; [2;1]]`. ✓

This matches audit note **N-2**.

---

## 3. `MaynardSpec.cff` and `MaynardSpec.G_2` ↔ Maynard's `G_{n,2}(k)`

### Source

`theories/S1/MaynardSpec.v:63–73`:

```rocq
Definition cff (a : seq nat) (n : nat) : rat :=
  factQ n
  * \prod_(x <- a) (factQ (2 * x) / factQ x)
  * (factQ (2 * (n - sumn a)) / factQ (n - sumn a)).

Definition G_2 (n k : nat) : rat :=
  if (n == 0)%N then 1
  else
    k%:R * factQ (2 * n)
      + \sum_(i <- iota 1 (n - 1)%N)
          binQ k i.+1 * \sum_(a <- bnd i n) cff a n.
```

### Paper

Maynard, **Lemma 8.1** (v1 Lemma 7.1). The polynomial `G_{b, j}(x)` is
defined for `b ∈ ℕ`, `j ∈ ℕ_{≥1}`, real `x` (here we instantiate
`j = 2`):

```
G_{b, 2}(x) = b! · Σ_{r=1}^b   C(x, r) · Σ_{ (b_1,…,b_r) ∈ ℕ^r_{≥1},  Σ b_s = b }   Π_s ( (2 b_s)! / b_s! ).
```

Convention: `G_{0, 2}(x) := 1` (empty product / the implicit `b = 0` case).

### Mapping

Rewrite Maynard's outer sum by separating the `r = 1` term, which
collapses to a single composition `b_1 = b = n`:

```
G_{n, 2}(x)
  = n! · ( C(x, 1) · (2n)!/n! )                           — the r=1 term
    + n! · Σ_{r=2}^n  C(x, r) · Σ_{ (b_1,…,b_r) }  Π_s (2 b_s)!/b_s!
  = x · (2n)!
    + Σ_{r=2}^n  C(x, r) · n! · Σ_{ (b_1,…,b_r) }  Π_s (2 b_s)!/b_s!.
```

Reindex `r = i + 1`. Then the `r ≥ 2` outer index becomes `i ∈ {1, …, n−1}`,
and a composition `(b_1, …, b_{i+1})` of length `i + 1` is in bijection
with a composition `(b_1, …, b_i)` of length `i` plus an implicit last
part `b_{i+1} = n − Σ_{s ≤ i} b_s`. The constraint `b_{i+1} ≥ 1` is
exactly `Σ_{s ≤ i} b_s ≤ n − 1` — the set enumerated by `bnd i n`. The
inner product factor

```
n! · Π_{s=1}^{i+1} (2 b_s)! / b_s!
```

is what `cff a n` computes (the last `s = i+1` factor is broken out as
`(2 (n − sumn a))! / (n − sumn a)!`). The `C(x, r) = C(x, i+1)` factor
is `binQ k i.+1`.

| Rocq | Paper | Note |
|------|-------|------|
| `if n = 0 then 1` | `G_{0, 2}(x) := 1` | base case |
| `k%:R * factQ (2 * n)` | the `r = 1` term `x · (2n)!` | `x = k` |
| `iota 1 (n - 1)` for `i` | reindexed `r = i + 1`, `r ∈ {2, …, n}` | |
| `binQ k i.+1` | `C(x, r) = C(x, i+1)` | |
| `bnd i n` | `(b_1, …, b_i)` with `b_s ≥ 1`, `Σ ≤ n − 1` | §2 above |
| `cff a n` | `n! · Π_s (2 b_s)! / b_s!` (over `s = 1, …, i+1`) | implicit last part |

### Sanity checks (audit note **N-1**)

- `G_{0, 2}(k) = 1`.   ✓ (Rocq branch.)
- `G_{1, 2}(k) = k · 2! = 2k`.   Rocq computes `k · 2! + (empty `i` range) = 2k`. ✓
- `G_{2, 2}(k) = 4k² + 20k`.
  Rocq: `k · 4! = 24 k`, plus `i = 1`: `C(k, 2) · cff([1], 2)` where
  `cff([1], 2) = 2! · ((2·1)!/1!) · ((2·1)!/1!) = 2 · 2 · 2 = 8`. So
  `24 k + C(k, 2) · 8 = 24 k + 4 k (k − 1) = 4 k² + 20 k`. ✓

---

## 4. `MaynardSpec.M1_entry` ↔ Maynard's `M_{1, ij}` (Lemma 8.2)

### Source

`theories/S1/MaynardSpec.v:75–81`:

```rocq
Definition K1 : nat := 105.
Definition K2 : nat := 104.

Definition M1_entry (bi ci bj cj : nat) : rat :=
  let b := (bi + bj)%N in
  let c := (ci + cj)%N in
  factQ b / factQ (K1 + b + 2 * c)%N * G_2 c K1.
```

### Paper

Maynard, **Lemma 8.2 (first part)**, paper p. 22 (v1 Lemma 7.2, paper
p. 19): for the basis monomial `((1 − P_1)^b P_2^c)`,

```
M_{1, ij}  =  (b_i + b_j)! · G_{c_i + c_j, 2}(k)  /  (k + b_i + b_j + 2 c_i + 2 c_j)!
```

with the convention `0! = 1`.

### Mapping

| Rocq | Paper |
|------|-------|
| `b := bi + bj` | `b_i + b_j` |
| `c := ci + cj` | `c_i + c_j` |
| `factQ b` | `(b_i + b_j)!` |
| `factQ (K1 + b + 2 * c)` | `(k + b_i + b_j + 2 c_i + 2 c_j)!`, with `K1 = k = 105` |
| `G_2 c K1` | `G_{c_i + c_j, 2}(k)` |

The Rocq formula is the paper formula verbatim modulo arithmetic
rearrangement; see audit note **N-3** for the side-by-side verification.

The corresponding `Z`-level pair is given at
`theories/S1/MaynardSpec.v:185–188`:

```rocq
Definition m1_num_den (bi ci bj cj : nat) : Z * Z :=
  let b := (bi + bj)%nat in
  let c := (ci + cj)%nat in
  (factZ b * G2Z c K1n, factZ (K1n + b + 2 * c)%nat).
```

i.e., `num = b! · G_{c, 2}(k)`, `den = (k + b + 2c)!`. Both are
positive integers, so `num/den = M1_entry` in `ℚ`.

---

## 5. `MaynardSpec.alpha` ↔ Maynard's eq. 8.8 expansion coefficient

This is the substitution that "integrates out" `t_1` in the inner
integral defining `J_k^{(1)}`. It is the heart of the M2 derivation
and is worth describing carefully.

### Source

`theories/S1/MaynardSpec.v:83–85`:

```rocq
Definition alpha (b c cp : nat) : rat :=
  binQ c cp * factQ b * factQ (2 * c - 2 * cp)%N
    / factQ (b + 2 * c - 2 * cp + 1)%N.
```

### Paper

Maynard, **Lemma 8.2, eq. 8.8** (v1 eq. 7.10): one fixes a basis monomial
`F_i = (1 − P_1)^{b_i} P_2^{c_i}` and computes

```
∫_0^{1 − Σ_{j ≠ 1} t_j}   F_i(t)   d t_1
   =   Σ_{c'_1 = 0}^{c_i}   α(b_i, c_i, c'_1)
                          · ( 1 − Σ_{j ≠ 1} t_j )^{ b_i + 2 c_i − 2 c'_1 + 1 }
                          · ( Σ_{j ≠ 1} t_j² )^{ c'_1 }
```

with

```
α(b, c, c')  =  C(c, c') · b! · (2c − 2c')! / (b + 2c − 2c' + 1)!.
```

Algebraically: starting from `(1 − P_1)^b · P_2^c`, write `P_2 =
t_1² + Σ_{j ≠ 1} t_j²`, expand `P_2^c` by the binomial theorem with
index `c'`, then integrate `t_1^{2(c − c')} (1 − Σ_j t_j)^b` from
`t_1 = 0` to `t_1 = 1 − Σ_{j ≠ 1} t_j` using the standard Beta-function
identity

```
∫_0^X t^a (X − t)^b dt = a! · b! · X^{a+b+1} / (a + b + 1)!.
```

The factor `(2c − 2c')!` in the numerator is `a! = (2(c − c'))!`, and
the `b! · X^{a+b+1} / (a + b + 1)!` shape rearranges to the `α` displayed
above (the `b! / (b + 2c − 2c' + 1)!` part), with `X = 1 − Σ_{j ≠ 1} t_j`
producing the first power tail of the eq. 8.8 right-hand side and the
remaining `Σ_{j ≠ 1} t_j²` producing the `( · )^{c'}` factor.

### Mapping

| Rocq | Paper |
|------|-------|
| `binQ c cp` | `C(c, c')` (binomial-theorem expansion of `P_2^c`) |
| `factQ b` | `b!` (numerator from the Beta integral) |
| `factQ (2*c - 2*cp)` | `(2c − 2c')!`, the `a!` of the Beta integral with `a = 2(c − c')` |
| `factQ (b + 2*c - 2*cp + 1)` | `(b + 2c − 2c' + 1)!`, the `(a + b + 1)!` of the Beta integral |

The Z-level twin lives at `theories/S1/MaynardSpec.v:217–219`:

```rocq
Definition alphaZ (b c cp : nat) : Z * Z :=
  (binZ c cp * factZ b * factZ (2 * c - 2 * cp)%nat,
   factZ (b + 2 * c - 2 * cp + 1)%nat).
```

`binZ c cp` is integer-valued (`c ≥ cp`), so the numerator is a positive
integer, and the denominator is a positive factorial.

---

## 6. `MaynardSpec.M2_entry` ↔ Maynard's `M_{2, ij}^{(1)}` (Lemma 8.2)

### Source

`theories/S1/MaynardSpec.v:87–96`:

```rocq
Definition M2_entry (bi ci bj cj : nat) : rat :=
  \sum_(cp1 <- iota 0 ci.+1)
    \sum_(cp2 <- iota 0 cj.+1)
      let bp1 := (bi + 2 * ci - 2 * cp1 + 1)%N in
      let bp2 := (bj + 2 * cj - 2 * cp2 + 1)%N in
      let bsum := (bp1 + bp2)%N in
      let csum := (cp1 + cp2)%N in
      alpha bi ci cp1 * alpha bj cj cp2
        * factQ bsum / factQ (K2 + bsum + 2 * csum)%N
        * G_2 csum K2.
```

### Paper

Maynard, **Lemma 8.2 (second part)**, paper p. 22 (v1 Lemma 7.2,
p. 19): the per-coordinate matrix entry `M_{2, ij}^{(1)}` (i.e. the
integrand from `J_k^{(1)}`, **not** `Σ_m J_k^{(m)}`). After applying the
eq. 8.8 substitution to both `F_i` and `F_j`, one is left with a
double sum over `(c'_1, c'_2) ∈ [0, c_i] × [0, c_j]` of:

```
α(b_i, c_i, c'_1) · α(b_j, c_j, c'_2)
  · ∫_{Δ_{k-1}}  ( 1 − Σ_{j ≠ 1} t_j )^{b'_1 + b'_2}  ( Σ_{j ≠ 1} t_j² )^{c'_1 + c'_2}  d t_{≠1}
```

with `b'_1 = b_i + 2c_i − 2c'_1 + 1`, `b'_2 = b_j + 2c_j − 2c'_2 + 1`.
The remaining integral is exactly Lemma 8.1 / eq. 8.4 evaluated at degree
`(b'_1 + b'_2, c'_1 + c'_2)` over the `(k − 1)`-simplex. So it equals

```
(b'_1 + b'_2)! · G_{c'_1 + c'_2, 2}(k − 1)  /  ( (k − 1) + b'_1 + b'_2 + 2 (c'_1 + c'_2) + 1)!
=  (b_sum)! · G_{c_sum, 2}(k − 1)  /  (104 + b_sum + 2 c_sum)!
```

since `(k − 1) + 1 = k = 105` and our `K2 = k − 1 = 104` on the RHS.

**Caveat on eq. 8.4 (paper p. 409).** Maynard's eq. 8.4 — the
closed-form Beta–Dirichlet integral
`∫_{Δ_n} (1 − Σ t_j)^b (Σ t_j²)^c dt = b! · G_{c,2}(n) / (n + b + 2c + 1)!`
— is stated under the implicit hypothesis `b ≠ 0`. The `b = 0` case
has a different closed form (the volume term `1/n!` vs the formal
substitution `1/(n+1)!`). For our M2 application this is harmless:
the M2 integrand is invoked with `b_sum = b'_1 + b'_2 = b_i + b_j +
2(c_i + c_j) − 2(c'_1 + c'_2) + 2`, and since `c'_1 ≤ c_i`,
`c'_2 ≤ c_j`, we have `b_sum ≥ 2 > 0` for every term in the M2
double sum. So eq. 8.4 is always applied in the `b ≠ 0` regime
in our derivation.

For the M1 integrand the corresponding `b = b_i + b_j` *can* be
zero (when `b_i = b_j = 0`, e.g. the `(0, 0)` × `(0, 0)` basis
entry). The M1 formula in our `M1_entry` treats this case using
the same closed-form expression as for `b ≠ 0`; this is consistent
with Maynard's Lemma 8.2 first part as written, which gives the
M1 entries directly as `b! · G_{c, 2}(k) / (k + b + 2c)!` for all
`b ≥ 0`. In particular Maynard's M1 closed form does not invoke
eq. 8.4's `b = 0` corner case — it is derived independently for
M1, before eq. 8.8's substitution introduces the `+1` in `b'_i`.
So the corner case of eq. 8.4 is not silently assumed in either
M1 or M2.

### Mapping

| Rocq | Paper |
|------|-------|
| outer `\sum_(cp1 <- iota 0 ci.+1) \sum_(cp2 <- iota 0 cj.+1)` | `Σ_{c'_1=0}^{c_i} Σ_{c'_2=0}^{c_j}` |
| `bp1 = bi + 2 ci − 2 cp1 + 1` | `b'_1 = b_i + 2 c_i − 2 c'_1 + 1` |
| `bp2 = bj + 2 cj − 2 cp2 + 1` | `b'_2 = b_j + 2 c_j − 2 c'_2 + 1` |
| `alpha bi ci cp1 * alpha bj cj cp2` | `α(b_i, c_i, c'_1) · α(b_j, c_j, c'_2)` (eq. 8.8) |
| `factQ bsum / factQ (K2 + bsum + 2 csum)` | `(b'_1 + b'_2)! / ((k − 1) + (b'_1 + b'_2) + 2(c'_1 + c'_2) + 1)!` |
| `G_2 csum K2` | `G_{c'_1 + c'_2, 2}(k − 1)` |

This matches Maynard's formula on p. 22 verbatim; see audit note **N-4**
for the explicit reconciliation
`K2 + b_sum + 2 c_sum = 105 + (b_i + b_j + 2 c_i + 2 c_j) + 1`.

### Why the `k` factor lives in the threshold, not the matrix

By symmetry of `F` in its `k` variables, `Σ_m J_k^{(m)}(F) = k · J_k^{(1)}(F)`,
so

```
M_k = sup_F  Σ_m J_k^{(m)}(F) / I_k(F)
    = sup_F  k · J_k^{(1)}(F) / I_k(F)
    = k · λ_max( M_1^{-1} · M_2 )
```

where `M_2` is **per-coordinate** `J_k^{(1)}` (what `M2_entry` computes).
Equivalently, the Cert.v threshold

```
λ_max( M_1^{-1} · M_2 )  >  4 / k  =  4 / 105
```

is what gives `M_k > 4`. The Rocq layer proves the existence of *some*
real eigenvalue of `M_1^{-1} M_2` strictly above `4 / 105`, which is
≤ `λ_max` (max ≥ any). The factor `k = 105` is paid in the threshold
`4 / 105`, *not* in the matrix entries. This is audit note **Mn-1**.

The Z-level twin is `m2_num_den` at `theories/S1/MaynardSpec.v:229–235`,
which folds `qplus`/`qmul` over the same double sum, accumulating a single
`(num, den)` pair per `(i, j)` entry.

---

## 7. The 42-element basis

### Source

`theories/S1/MaynardBasis.v:20–28`:

```rocq
Definition maynard_basis : list (nat * nat) :=
  [ (0, 0); (1, 0); (0, 1); (2, 0); (1, 1); (3, 0)
  ; (0, 2); (2, 1); (4, 0); (1, 2); (3, 1); (5, 0)
  ; (0, 3); (2, 2); (4, 1); (6, 0); (1, 3); (3, 2)
  ; (5, 1); (7, 0); (0, 4); (2, 3); (4, 2); (6, 1)
  ; (8, 0); (1, 4); (3, 3); (5, 2); (7, 1); (9, 0)
  ; (0, 5); (2, 4); (4, 3); (6, 2); (8, 1); (10, 0)
  ; (1, 5); (3, 4); (5, 3); (7, 2); (9, 1); (11, 0)
  ]%nat.

Lemma maynard_basis_size : length maynard_basis = 42.
Lemma maynard_basis_eq_witness : maynard_basis = Witness.basis.
```

### Paper

Maynard, p. 23 (v1 p. 21–22), the "for simplicity" reduction:

> "We restrict our attention to test functions of the form `F = Σ a_{b,c}
> (1 − P_1)^b P_2^c`" with `P_1 = Σ t_i`, `P_2 = Σ t_i²` and `b + 2c ≤
> deg_max`.

For `deg_max = 11`, the set

```
{ (b, c) ∈ ℕ²  :  b + 2c ≤ 11 }
```

has `Σ_{c = 0}^{5} (12 − 2c) = 12 + 10 + 8 + 6 + 4 + 2 = 42` elements.

### Mapping

The Rocq list is exactly this set, ordered by the Mathematica
enumeration used in `python/flint_probe.py` (the `xExponents_mma(5)` /
`yExponents_mma(5)` order). Audit note **N-5** independently re-derives
the set and confirms the listing.

`Witness.basis` (autogenerated from `python/certificate.json`) and
`MaynardBasis.maynard_basis` (hand-readable in the .v file) are pinned
together by `maynard_basis_eq_witness`, a `vm_compute` lemma. So the
basis a reviewer reads in `MaynardBasis.v` is the *same* basis the
shipped matrix entries are indexed by.

### What this restriction is and is not

This is a **lower-bound subspace**. Maynard's full optimisation problem
is over all symmetric `F` with `deg ≤ 11` in 105 variables; restricting
to polynomials in the two power sums `P_1, P_2` is a strict subspace.
The supremum of a Rayleigh quotient over a subspace is `≤` the
unrestricted supremum. So:

```
M_{105}  =  sup over full space  ≥  k · λ_max( M_1^{-1} M_2 )  on this 42-dim subspace.
```

Because we are proving a *lower bound* `M_{105} > 4`, the subspace
restriction goes the right way. This is the "for simplicity" reduction
in Maynard p. 23.

---

## 8. What is verified inside the Rocq kernel

`MaynardVerify.v:99–120` cross-checks every entry of the shipped integer
matrices against `MaynardSpec` via Z-level cross-multiplication:

```rocq
Definition M1_entry_matchZ (i j : nat) : bool :=
  Z.eqb (m1_num i j * D_M1)
        (mat_get M1_int i j * m1_den i j).

Definition all_match_M1Z : bool :=
  List.forallb
    (fun i => List.forallb (fun j => M1_entry_matchZ i j) (List.seq 0 42))
    (List.seq 0 42).

Lemma all_match_M1Z_true : all_match_M1Z = true.
Proof. vm_compute. reflexivity. Qed.
```

(and analogously for `M2`). Both `Lemma`s are `Qed` and close by a
single `vm_compute`. `Print Assumptions` reports "Closed under the
global context" — no axioms, not even Uint63 primitives, are involved
(the proof is pure Z arithmetic).

**Coverage:** `42 × 42 = 1764` entries per matrix, so 3528 per-entry
checks total. The check is the standard rational identity
`a/b = c/d ⟺ a · d = b · c` for positive `b, d`, applied to
`(M_int[i][j], D_M_l)` and `(num_spec[i][j], den_spec[i][j])`.

**Timing** (REPORT.md §3.8): ~90 s for `M1`, ~35 min for `M2`. The
M2 cost dominates because each entry is a sum of up to `(c_i + 1)
× (c_j + 1) ≤ 36` terms, each of which forms a full `G_{·,2}(104)`
expansion — the per-term denominator grows to thousands of digits before
`qplus` collapses it.

---

## 9. What is NOT verified inside Rocq

The audit explicitly lists the gaps; we reproduce them here for
transparency.

### 9.1 Lemma 8.3 (`M_k = k · λ_max(M_1^{-1} M_2)`) — *paper-side only*

The Rocq layer proves "there exists a real algebraic eigenvalue of
`M_1^{-1} M_2` strictly above `4/105`" (`Cert.maynard_eigenvalue_S1`).
Bridging this to `M_{105} > 4` requires:

(a) Lemma 8.3's identity `M_k = k · λ_max(M_1^{-1} M_2)`
    (Lagrange multipliers over a positive-definite Gram matrix), and
(b) the trivial `λ_max ≥ any real eigenvalue`.

Both are taken on the paper side (REPORT.md §1.4, audit note **M-1**).

### 9.2 Reality of the spectrum of `M_1^{-1} M_2`

Inside Rocq we work in `realalg`, the real algebraic closure of `ℚ`,
so any eigenvalue we extract via IVT is automatically real. We do not
formalise the structural claim "the spectrum of `M_1^{-1} M_2` is real
because `M_1` is symmetric PD and `M_2` is symmetric" (Sylvester's law /
generalised eigenvalue problem). The audit is satisfied that this is
correct on the paper side: `M_1`, `M_2` are Gram matrices of `L^2`
inner products on a 42-dimensional subspace of polynomials, hence
symmetric; `M_1` is PD because `aᵀ M_1 a = ∫ F² ≥ 0` with equality only
at `F = 0`. See audit notes **Mn-2**, **Mn-3**.

### 9.3 The Beta-integral derivation `J_k(F)/I_k(F) → closed form`

The closed-form rational formulas in §3–§6 above (Lemma 8.1 / 8.2)
are taken as **definitions** in Rocq. The analytic derivation —
Beta-function identity for `∫_0^X t^a (X − t)^b dt`, integrate `t_1`
out via eq. 8.8, sum over compositions — is the content of Lemma 8.1's
proof in Maynard. We do not reproduce this analytic step inside Rocq.

What Rocq *does* certify is that the resulting closed-form rational
matches the shipped integer matrix `M1_int / D_M1`, `M2_int / D_M2`
entry-for-entry. So if a reviewer accepts Maynard's Lemma 8.1 / 8.2
on paper, the kernel guarantees the matrices `Cert.v` consumes are
exactly the Maynard matrices.

---

## Summary table

| Rocq object | File:lines | Paper (v3 §8) | Audit note |
|-------------|-----------|---------------|------------|
| `enum_bnd_aux`, `bnd` | `MaynardSpec.v:48–61` | Lemma 8.1 inner enumeration | N-2 |
| `cff` | `MaynardSpec.v:63–66` | Lemma 8.1 product `Π (2 b_s)!/b_s!` | N-1 |
| `G_2` | `MaynardSpec.v:68–73` | Lemma 8.1 (`G_{n, 2}(k)`) | N-1 |
| `K1`, `K2` | `MaynardSpec.v:75–76` | `k = 105`, `k − 1 = 104` | §1 above |
| `M1_entry` | `MaynardSpec.v:78–81` | Lemma 8.2 (M1 part) | N-3 |
| `alpha` | `MaynardSpec.v:83–85` | eq. 8.8 (=v1 eq. 7.10) | §5 above |
| `M2_entry` | `MaynardSpec.v:87–96` | Lemma 8.2 (M2 part, per-coord `J_k^{(1)}`) | N-4, Mn-1 |
| `M1_spec_ij`, `M2_spec_ij` | `MaynardSpec.v:98–106` | indexed via 42-basis | — |
| `m1_num_den`, `m2_num_den` | `MaynardSpec.v:185–235` | Z-level twin of M1, M2 | — |
| `maynard_basis` | `MaynardBasis.v:20–28` | p. 23, "for simplicity" | N-5 |
| `all_match_M1Z_true`, `all_match_M2Z_true` | `MaynardVerify.v:116–120` | 1764 cross-checks each | N-6 |

---

*End of SPEC_TO_PAPER.md.*
