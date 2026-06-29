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

`MaynardSpec.v` transcribes Maynard's closed-form expressions for the matrix
entries `M_{1, ij}`, `M_{2, ij}` (Lemma 8.2) in two parallel forms — a
`rat`-valued spec for direct paper comparison, and a `(num, den) : Z * Z`
spec for `vm_compute`-friendly cross-checking against the FLINT-shipped
data. This document gives the line-level mapping from each Rocq definition
back to its paper counterpart.

## How to read this document

For each Rocq definition in `theories/S1/MaynardSpec.v` we give:

1. The Rocq source (file + approximate line range).
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

For `deg_max = 11` this span has dimension 42 (the basis in question; see
§7 below for the count). The matrices `M_1`, `M_2` are the Gram matrices
of the inner products `(F, G) ↦ I_k(F·G)` and `(F, G) ↦ J_k^{(1)}(F·G)` on
this 42-dimensional subspace. Lemma 8.2 gives closed forms for their
entries; Lemma 8.3 says

```
M_k = k · λ_max( M_1^{-1} M_2 )         (when M_2 is per-coordinate J_k^{(1)})
```

so any rigorous lower bound on `λ_max` of at least `4/k` would yield
`M_k > 4`.

In the paper, indices `(b_i, c_i)` and `(b_j, c_j)` denote the bidegrees
of the `i`-th and `j`-th basis monomials. The paper writes `k` for the
outer integration dimension; in our formalisation this is `k_param = 105`.

### Rocq conventions

`MaynardSpec.v` uses two parallel implementations of the same closed forms:

- **Part A (rat-level)**: `compositions`, `cff`, `G_2`, `M1_entry`,
  `alpha`, `M2_entry` — readable side-by-side with Maynard's paper, all
  valued in MathComp's `rat`.
- **Part B (Z-level)**: `compositionsZ`, `cffZ`, `G2Z`, `m1_num_den`,
  `alphaZ`, `m2_num_den` — same closed forms, but each rational result
  is presented as a `(num, den) : Z * Z` pair. Used by `MaynardVerify.v`
  because `vm_compute` on `'M[rat]_42` triggers MathComp's HB
  canonical-structure elaborator and stalls (REPORT.md §4d).

Part A and Part B are structurally isomorphic: every operation in Part A
has a directly corresponding operation in Part B. The kernel-Qed bridge
between them lives in `theories/S1/MaynardSpecBridge.v`:

```rocq
Lemma M1_spec_rat_eq (i j : nat) :
  M1_spec_ij i j = qfrac (m1_num_den_at i j).

Lemma M2_spec_rat_eq (i j : nat) :
  M2_spec_ij i j = qfrac (m2_num_den_at i j).
```

where `qfrac (n, d) := (Z_to_int n)%:~R / (Z_to_int d)%:~R : rat`. Both
lemmas are `Qed` and `Print Assumptions` reports *Closed under the
global context* — no axioms, no `Uint63` primitives. The bridge is layered
through `factZ_to_rat`, `dblratZ_to_rat`, `binZ_to_rat`,
`compositionsZ_eq_compositions`, `G2Z_to_rat`, `qfrac_qmul`, `qfrac_qplus`,
and `alphaZ_to_rat`, each one a small structural induction.

`MaynardSpecBridge.v` is imported by `Cert.v` and used (together with
the Z-level bool match `all_match_M{1,2}Z_true` from `MaynardVerify.v`)
to discharge a *composed* paper-form ↔ FLINT identity in the headline:

```rocq
Lemma M{1,2}_spec_eq_int i j :
  (i < 42)%nat -> (j < 42)%nat ->
  M{1,2}_spec_ij i j = Z2rat (mat_get M{1,2}_int i j) / Z2rat D_M{1,2}.
```

where `Z2rat (z : Z) : rat := (Z_to_int z)%:~R`. The headline theorem
`CertRayleigh.maynard_M105_certified_rayleigh` exposes this composed identity
directly (one conjunct per matrix), not the Z-level bool match and
the rat<->Z bridge as separate conjuncts. The Z-level bool checks
`all_match_M{1,2}Z_true`
and the rat<->Z bridges `M{1,2}_spec_rat_eq` still EXIST as standalone
`Qed`s in `MaynardVerify.v` / `MaynardSpecBridge.v` — they are
individually `Print Assumptions`-able — they just no longer appear as
top-level conjuncts of the headline. Their purpose remains to certify
in the kernel that the rat-level paper-form spec (the documentation-
shaped Part A a reviewer reads against the paper) and the Z-level
computational spec (the Part B `vm_compute` consumes) encode the same
closed forms.

### Two certified routes to `M_{105} > 4`

The project now closes `M_{105} > 4` in **two** axiom-free forms; both are
`Qed` and `Print Assumptions` reports *Closed under the global context*.

- **Route 1 — direct Rayleigh witness.**
  `CertRayleigh.maynard_M105_certified_rayleigh`
  (`theories/S1/CertRayleigh.v`) is the 3-conjunct headline described above:
  the two composed paper-form ↔ FLINT identities plus the strict
  Rayleigh-quotient bound `4 * quad_spec M1_spec_ij < 105 * quad_spec
  M2_spec_ij` at the shipped 42-entry rational witness. It uses **no**
  eigenvalue, **no** characteristic polynomial, and **no** Chinese-remainder
  lift — it is the single-quotient strategy of Maynard's original notebook,
  mechanised in pure-`Z` arithmetic by `vm_compute`.

- **Route 2 — eigenvalue / target form.**
  `MaynardEigen.maynard_M105_certified` (`theories/S1/MaynardEigen.v:372`)
  proves the spectral form that matches Maynard's Lemma 8.3 characterisation
  of `M_k` directly (see "The eigenvalue route" section below). It is built
  *on* Route 1 — `CertRayleigh.rayleigh_lt_main` supplies the strict `> 4`
  input — and additionally formalises an eigenvalue, a characteristic
  polynomial (mod `p`, lifted by deterministic CRT), and the
  positive-definiteness of `M_1`.

Route 1 is therefore both the direct route and the computational core of
Route 2. Neither route uses IVT, a Sturm chain, `realalg`, or native 63-bit
integers.

### The `K = 105` vs `K2 = 104` distinction

The constant of integration changes after the substitution that
"integrates out" `t_1` (Lemma 8.2 / eq. 8.8). Concretely:

- The outer integrand for `M_1` is taken over the `k`-simplex `Δ_k`:
  the Rocq spec uses `K1 := 105` (matches `Witness.k_param`).
- Inside `M_2`, after the eq. 8.8 expansion, the residual integral is
  on the `(k - 1)`-simplex `Δ_{k-1}`: the Rocq spec uses `K2 := 104`
  (= 105 − 1) for the `G_{·,2}` factor that appears at the second layer.

This is **not** a typo or an off-by-one: the algebraic reconciliation is
`K2 + b_sum + 2 c_sum = 105 + (b_i + b_j + 2c_i + 2c_j) + 1`, which is
exactly the M2 denominator written in Maynard's Lemma 8.2.

---

## 2. `MaynardSpec.compositions r n` ↔ Maynard's length-`r` compositions of `n`

### Source

`theories/S1/MaynardSpec.v`, in PART A:

```rocq
Fixpoint compositions_aux (r remaining : nat) : seq (seq nat) :=
  match r with
  | 0 => if (remaining == 0)%N then [:: [::] ] else [::]
  | S r' =>
      flatten
        [seq [seq (a :: tl) | tl <- compositions_aux r' (remaining - a)%N]
           | a <- iota 1 remaining]
  end.

Definition compositions (r n : nat) : seq (seq nat) := compositions_aux r n.
```

### Paper

The inner sum of Maynard's `G_{b, j}(x)` (Lemma 8.1) is indexed by

```
{ (b_1, …, b_r) ∈ ℕ_{≥1}^r  :  Σ b_s = b }.
```

That is, length-`r` compositions of `b` with parts ≥ 1. In our Rocq we use
`r` for the length and `n` for the total to avoid clashing with the basis
indices `(b_i, c_i)`.

### Mapping

| Rocq | Paper | Note |
|------|-------|------|
| `r` (first arg) | length of the composition `(b_1, …, b_r)` | |
| `n` (second arg) | the sum `Σ b_s = b` (= the polynomial degree in `G_{·,2}`) | |
| recursive call `compositions_aux r' (remaining - a)` | fix `b_1 = a`, recurse on `(b_2, …, b_r)` summing to `remaining − a` | |
| base `r = 0`, `remaining = 0` ⇒ `[[::]]` | the empty composition is the unique length-0 composition of 0 | |
| base `r = 0`, `remaining > 0` ⇒ `[::]` | a length-0 composition cannot sum to a positive number | |

### Sanity check

- `compositions 0 0 = [[::]]` — one empty composition.   ✓
- `compositions 0 n = [::]` for `n ≥ 1` — no length-0 composition of `n`.   ✓
- `compositions 1 4 = [[1]; [2]; [3]; [4]]` — but wait, only `[4]` sums
  to 4 with one part ≥ 1, so this should be `[[4]]`. **Verify:** the
  recursion `compositions_aux 1 4` goes `slots = 1`, `remaining = 4`, and
  iterates `a ∈ iota 1 4 = [1; 2; 3; 4]`. For each `a`, recurses on
  `compositions_aux 0 (4 − a)`; the inner result is `[[::]]` only when
  `4 − a = 0`, i.e. `a = 4`. For `a ∈ {1, 2, 3}` the inner result is
  `[::]` and contributes nothing. Net: `compositions 1 4 = [[4]]`.   ✓
- `compositions 2 4` enumerates `(b_1, b_2)`, both `≥ 1`, sum `= 4`:
  outputs `[[1; 3]; [2; 2]; [3; 1]]`.   ✓
- `compositions 3 4` enumerates length-3 compositions of 4: outputs
  `[[1; 1; 2]; [1; 2; 1]; [2; 1; 1]]`.   ✓

The Z-level twin `compositionsZ` in PART B has the same shape, differing
only in stdlib names (`List.flat_map` for `flatten ∘ map`, `List.seq` for
`iota`):

```rocq
Fixpoint compositions_auxZ (r remaining : nat) : list (list nat) :=
  match r with
  | O => if Nat.eqb remaining 0 then [nil] else nil
  | S r' =>
      List.flat_map
        (fun a => List.map (fun tl => a :: tl)
                           (compositions_auxZ r' (remaining - a)%nat))
        (List.seq 1 remaining)
  end.

Definition compositionsZ (r n : nat) : list (list nat) := compositions_auxZ r n.
```

`seq` is a notation for `list` in MathComp, so `compositions = compositionsZ`
as values for every `(r, n)` (modulo lemma `iota = List.seq`).

---

## 3. `MaynardSpec.cff` and `MaynardSpec.G_2` ↔ Maynard's `G_{n, 2}(k)`

### Source

`theories/S1/MaynardSpec.v`, PART A:

```rocq
Definition cff (a : seq nat) : rat :=
  \prod_(x <- a) (factQ (2 * x) / factQ x).

Definition G_2 (n k : nat) : rat :=
  if (n == 0)%N then 1
  else
    factQ n
    * \sum_(r <- iota 1 n) binQ k r * \sum_(a <- compositions r n) cff a.
```

### Paper

Maynard's **Lemma 8.1** (= v1 Lemma 7.1), specialised to `j = 2`:

```
G_{n, 2}(k) = n! · Σ_{r=1}^{n} C(k, r) · Σ_{(b_1,...,b_r) ∈ ℕ^r_{≥1}, Σ b_s = n}  Π_{s=1}^{r} (2 b_s)! / b_s!.
```

The convention `G_{0, 2}(k) := 1` (empty product) handles the `n = 0`
base case.

### Mapping

| Rocq | Paper |
|------|-------|
| `if n = 0 then 1` | `G_{0, 2}(k) := 1` |
| `factQ n` | `n!` (the global prefactor in front of the double sum) |
| `\sum_(r <- iota 1 n)` | `Σ_{r=1}^{n}` |
| `binQ k r` | `C(k, r)` |
| `\sum_(a <- compositions r n)` | `Σ_{(b_1,...,b_r), b_s ≥ 1, Σ = n}` |
| `cff a = \prod_(x <- a) (factQ (2x) / factQ x)` | `Π_{s=1}^{r} (2 b_s)! / b_s!` |

The Rocq formula is Maynard's Lemma 8.1 character-for-character.
`cff a` is the inner product factor; `G_2 n k` collects the `n!`
prefactor, the `r`-sum, the binomial coefficient, and the inner sum.

### Sanity checks

- `G_{0, 2}(k) = 1`.   ✓ (Rocq branch.)
- `G_{1, 2}(k) = 2k`.   The only length-1 composition of 1 is `[1]`,
  with `cff([1]) = 2!/1! = 2`. So `G_{1, 2}(k) = 1! · binom(k, 1) · 2 = 2k`. ✓
- `G_{2, 2}(k) = 4k² + 20k`.
  - Length 1: only composition is `[2]`, `cff([2]) = 4!/2! = 12`.
    Contribution: `binom(k, 1) · 12 = 12k`.
  - Length 2: only composition is `[1; 1]`, `cff([1;1]) = (2!/1!)² = 4`.
    Contribution: `binom(k, 2) · 4 = 2k(k − 1)`.
  - Total: `2! · (12k + 2k(k − 1)) = 2 · (12k + 2k² − 2k) = 4k² + 20k`. ✓

These three sanity values are spot-checked by `vm_compute` smoke tests
against `G_2 n k` for small `n, k`.

### PART B twin

```rocq
Definition cffZ (a : list nat) : Z := prod_dblratZ a.

Definition G2Z (n k : nat) : Z :=
  if Nat.eqb n O then 1
  else
    factZ n
    * List.fold_left Z.add
        (List.map (fun r =>
            binZ k r
            * List.fold_left Z.add
                (List.map cffZ (compositionsZ r n)) 0)
           (List.seq 1 n)) 0.
```

Here `prod_dblratZ a := Π_(x ∈ a) factZ (2 x) / factZ x` is the Z-integer
product; the integer divisions are exact because `factZ x ∣ factZ (2 x)`
for all `x`. Lifting `G2Z` to `rat` gives back `G_2` exactly.

---

## 4. `MaynardSpec.M1_entry` ↔ Maynard's `M_{1, ij}` (Lemma 8.2)

### Source

`theories/S1/MaynardSpec.v`, PART A:

```rocq
Definition K1 : nat := 105.
Definition K2 : nat := 104.

Definition M1_entry (bi ci bj cj : nat) : rat :=
  let b := (bi + bj)%N in
  let c := (ci + cj)%N in
  factQ b / factQ (K1 + b + 2 * c)%N * G_2 c K1.
```

### Paper

Maynard, **Lemma 8.2 (first part)**, paper p. 22 (v1 Lemma 7.2,
paper p. 19): for the basis monomial `((1 − P_1)^b P_2^c)`,

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
rearrangement.

### PART B twin

```rocq
Definition m1_num_den (bi ci bj cj : nat) : Z * Z :=
  let b := (bi + bj)%nat in
  let c := (ci + cj)%nat in
  (factZ b * G2Z c K1n, factZ (K1n + b + 2 * c)%nat).
```

i.e., `num = b! · G_{c, 2}(k)`, `den = (k + b + 2c)!`. Both are positive
integers, so `num/den = M1_entry` in `ℚ`.

---

## 5. `MaynardSpec.alpha` ↔ Maynard's eq. 8.8 expansion coefficient

This is the substitution that "integrates out" `t_1` in the inner
integral defining `J_k^{(1)}`. It is the heart of the M2 derivation
and is worth describing carefully.

### Source

`theories/S1/MaynardSpec.v`, PART A:

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

### PART B twin

```rocq
Definition alphaZ (b c cp : nat) : Z * Z :=
  (binZ c cp * factZ b * factZ (2 * c - 2 * cp)%nat,
   factZ (b + 2 * c - 2 * cp + 1)%nat).
```

`binZ c cp` is integer-valued (when `cp ≤ c`), so the numerator is a
positive integer, and the denominator is a positive factorial.

---

## 6. `MaynardSpec.M2_entry` ↔ Maynard's `M_{2, ij}^{(1)}` (Lemma 8.2)

### Source

`theories/S1/MaynardSpec.v`, PART A:

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

**On the `b = 0` regime of the Beta–Dirichlet integral.** Maynard's
closed form `b! · G_{c,2}(n) / (n + b + 2c)!` (eq. 8.4 / Lemma 8.2)
is correct for all `b ≥ 0` with the standard `0! = 1` convention. The
formula does not require a separate `b = 0` case. Both `M1_entry`
(where `b = b_i + b_j ≥ 0` may be zero, e.g. for the `(0,0) × (0,0)`
entry) and `M2_entry` (where `b_sum = b_i + b_j + 2(c_i + c_j) −
2(c'_1 + c'_2) + 2 ≥ 2 > 0` always) apply it as written. No corner
case is silently assumed.

### Mapping

| Rocq | Paper |
|------|-------|
| outer `\sum_(cp1 <- iota 0 ci.+1) \sum_(cp2 <- iota 0 cj.+1)` | `Σ_{c'_1=0}^{c_i} Σ_{c'_2=0}^{c_j}` |
| `bp1 = bi + 2 ci − 2 cp1 + 1` | `b'_1 = b_i + 2 c_i − 2 c'_1 + 1` |
| `bp2 = bj + 2 cj − 2 cp2 + 1` | `b'_2 = b_j + 2 c_j − 2 c'_2 + 1` |
| `alpha bi ci cp1 * alpha bj cj cp2` | `α(b_i, c_i, c'_1) · α(b_j, c_j, c'_2)` (eq. 8.8) |
| `factQ bsum / factQ (K2 + bsum + 2 csum)` | `(b'_1 + b'_2)! / ((k − 1) + (b'_1 + b'_2) + 2(c'_1 + c'_2) + 1)!` |
| `G_2 csum K2` | `G_{c'_1 + c'_2, 2}(k − 1)` |

This matches Maynard's formula on p. 22 verbatim; the explicit
reconciliation `K2 + b_sum + 2 c_sum = 105 + (b_i + b_j + 2 c_i + 2 c_j) + 1`
follows from `K2 + 1 = 105`.

### Why the `k` factor lives in the threshold, not the matrix

By symmetry of `F` in its `k` variables, `Σ_m J_k^{(m)}(F) = k · J_k^{(1)}(F)`,
so

```
M_k = sup_F  Σ_m J_k^{(m)}(F) / I_k(F)
    = sup_F  k · J_k^{(1)}(F) / I_k(F)
    = k · λ_max( M_1^{-1} · M_2 )
```

where `M_2` is **per-coordinate** `J_k^{(1)}` (what `M2_entry` computes).
Equivalently, the inequality

```
sup_a  a^T M_2 a / a^T M_1 a   >   4 / k   =   4 / 105
```

is what gives `M_k > 4`. The Rocq layer proves the strict Rayleigh-
quotient bound `a^T M_2 a / a^T M_1 a > 4 / 105` at a specific
42-entry rational witness `a = v_witness` (shipped in
`Witness_Rayleigh.v` and consumed by `CertRayleigh.v`); the supremum is at
least the value at any individual `a`. The factor `k = 105` is paid
in the threshold `4 / 105`, *not* in the matrix entries.

### PART B twin

`m2_num_den` in PART B folds `qplus`/`qmul` over the same double sum,
accumulating a single `(num, den)` pair per `(i, j)` entry. The fold uses

```rocq
Definition qplus (p q : Z * Z) : Z * Z :=
  let '(a, b) := p in let '(c, d) := q in (a * d + c * b, b * d).
Definition qmul (p q : Z * Z) : Z * Z :=
  let '(a, b) := p in let '(c, d) := q in (a * c, b * d).
```

so that lifting back to `rat` gives `M2_entry` exactly.

---

## 6½. The eigenvalue route: `M105` ↔ Maynard's `M_k = k · λ_max(M_1^{-1} M_2)`

This section maps the Route 2 objects back to Maynard's Lemma 8.3. Route 1
(§6, "Why the `k` factor lives in the threshold") bounds the Rayleigh
quotient at a single witness; Route 2 instead exhibits an eigenvalue of the
scaled pencil and so certifies the spectral form of `M_{105}` itself.

### Source

`theories/S1/EigenBridge.v`:

```rocq
Definition M1_rat : 'M[rat]_42 := mat_int_to_rat M1_int D_M1 42.
Definition M2_rat : 'M[rat]_42 := mat_int_to_rat M2_int D_M2 42.
Definition A_rat  : 'M[rat]_42 := invmx M1_rat *m M2_rat.       (* M_1^{-1} M_2 *)
Definition M105   : 'M[rat]_42 := 105%:Q *: A_rat.             (* 105 * M_1^{-1} M_2 *)

Definition matches_closed_forms (M : 'M[rat]_42) : Prop :=
  [/\ M = M105,
      (forall i j, (i < 42)%nat -> (j < 42)%nat ->
         M1_spec_ij i j = Z2rat (mat_get M1_int i j) / Z2rat D_M1)
    & (forall i j, (i < 42)%nat -> (j < 42)%nat ->
         M2_spec_ij i j = Z2rat (mat_get M2_int i j) / Z2rat D_M2)].
```

### Paper

Maynard, **Lemma 8.3** (v1 Lemma 7.3): with `M_2` the per-coordinate
`J_k^{(1)}` Gram matrix and `M_1` the `I_k` Gram matrix,

```
M_k = k · λ_max( M_1^{-1} M_2 ),
```

equivalently `λ_max` of the generalized eigenproblem `M_2 v = λ M_1 v`. Hence
`M_{105} = λ_max( 105 · M_1^{-1} M_2 ) = λ_max(M105)`, and any eigenvalue of
`M105` exceeding `4` forces `M_{105} = λ_max(M105) > 4`.

### Mapping

| Rocq | Paper |
|------|-------|
| `A_rat = invmx M1_rat *m M2_rat` | `M_1^{-1} M_2` |
| `M105 = 105 *: A_rat` | `k · M_1^{-1} M_2` with `k = 105`; `λ_max(M105) = M_{105}` |
| `matches_closed_forms M105` | `M105` is built from the closed-form spec matrices `M{1,2}_spec_ij`, which equal the FLINT-shipped `M{1,2}_int / D_M{1,2}` (the §4/§6 identities, reused here as the trust contract) |
| `exists lam, eigenvalue (ratrM M105) lam /\ 4 < lam` | `λ_max(M105) ≥ lam > 4`, i.e. `M_{105} > 4` |

Here `ratrM := map_mx (ratr : rat -> algC)` casts `M105` into the algebraic
complex numbers `C := algC`, where the spectral theorem is available. The
headline theorem is

```rocq
Theorem maynard_M105_certified :
  matches_closed_forms M105 /\
  exists lam : C, eigenvalue (ratrM M105) lam /\ (4 < lam).
```

(`theories/S1/MaynardEigen.v:372`). It exhibits *an* eigenvalue above `4`;
since `M_{105} = λ_max(M105)` dominates every eigenvalue, this is exactly
`M_{105} > 4` in Maynard's eigenvalue form.

### How the eigenvalue is produced (axiom-free)

1. **Rayleigh input.** `CertRayleigh.rayleigh_lt_main` (the strict bound of
   §6) gives `wᵀ Sc w > 0` for `Sc := ratrM(105 *: M2_rat - 4 *: M1_rat)` at
   the cast witness (`MaynardEigen.form_pos`).
2. **Spectral bridge.** `SpectralCrux.herm_crux` — if `A` is Hermitian and
   `wᵀAw > 0` then `A` has a positive eigenvalue — applied via the spectral
   theorem over `algC`. `M1PosDef.M1_rat_factor` supplies a complex
   congruence factor `R` (`Rᵀ* *m R = ratrM M1_rat`) that turns the
   generalized pencil into a standard Hermitian eigenproblem; the positive
   eigenvalue, shifted by `4`, is the eigenvalue `> 4` of `ratrM M105`.
3. **Positive-definiteness of `M_1`.** `M1PosDef` proves `M_1` PD without
   floating point: `M1CharPoly.char_poly_int_M1_eq` certifies
   `char_poly_int M1_int = cp_M1_value` (a sign-alternating coefficient list
   ⟹ all eigenvalues `> 0`) by agreement modulo 200 CRT primes whose product
   exceeds twice the Hadamard-style coefficient bound
   (`Bound.char_poly_int_coeff_bound`) — deterministic, not probabilistic.
   The per-prime mod-`p` characteristic polynomials use the
   Faddeev–LeVerrier / Hessenberg routines `ModularFL.char_poly_modZ` and
   `ModularHess.char_poly_hess` (both `_sound`, fully proven).

All of these are `Qed` and `Print Assumptions` reports *Closed under the
global context* — same `vm_compute`-over-`Z` footprint as Route 1, no
project axioms.

---

## 7. The 42-element basis

### Source

`theories/S1/MaynardBasis.v` defines `maynard_basis : list (nat * nat)` as
an explicit 42-pair list (in Mathematica enumeration order to match
`Witness.basis`), and proves four facts — three set-level pins
(`_size`, `_uniq`, `_spec`) plus a `vm_compute`-Qed match against the
shipped witness ordering:

```rocq
Lemma maynard_basis_size : length maynard_basis = 42.
Lemma maynard_basis_uniq : uniq maynard_basis.
Lemma maynard_basis_spec : forall p,
  (p \in maynard_basis) = (p.1 + 2 * p.2 <= 11)%N.
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

`maynard_basis_spec` + `maynard_basis_uniq` + `maynard_basis_size = 42`
together pin the Rocq basis to *exactly* the multiset
`{(b, c) ∈ ℕ² : b + 2c ≤ 11}`. The literal 42-pair list in `MaynardBasis.v`
is an implementation detail — a reviewer never has to read it. They check
the *predicate* (one line: `b + 2c ≤ 11`) and trust the three Qed lemmas.

The order of `maynard_basis` matches `Witness.basis` (the FLINT-shipped
matrix indexing) by `maynard_basis_eq_witness` (`vm_compute`-Qed). Order
matters because matrix rows/columns and the entries of the witness
vector `v_witness` (in `Witness_Rayleigh.v`) must all align with the same
indexing in `M{1,2}_int`.

### What this restriction is and is not

This is a **lower-bound subspace**. Maynard's full optimisation problem
is over all symmetric `F` with `deg ≤ 11` in 105 variables; restricting
to polynomials in the two power sums `P_1, P_2` is a strict subspace.
The supremum of a Rayleigh quotient over a subspace is `≤` the
unrestricted supremum. So:

```
M_{105}  =  sup over full space  ≥  k · sup_{a in Q^42}  a^T M_2 a / a^T M_1 a  on this 42-dim subspace.
```

Because we are proving a *lower bound* `M_{105} > 4`, the subspace
restriction goes the right way. This is the "for simplicity" reduction
in Maynard p. 23.

---

## 8. What is verified inside the Rocq kernel

`MaynardVerify/Def.v` and `MaynardVerify.v` cross-check every entry of
the shipped integer matrices against `MaynardSpec` via Z-level
cross-multiplication:

```rocq
Definition M1_entry_matchZ (i j : nat) : bool :=
  Z.eqb (BinInt.Z.mul (m1_num i j) D_M1)
        (BinInt.Z.mul (mat_get M1_int i j) (m1_den i j)).

Definition all_match_M1Z : bool :=
  List.forallb
    (fun i => List.forallb (fun j => M1_entry_matchZ i j) (List.seq 0 42))
    (List.seq 0 42).

Lemma all_match_M1Z_true : all_match_M1Z = true.
Proof. vm_compute. reflexivity. Qed.
```

The `M2` analogue is split into six 7-row chunks (one Qed per chunk,
files `MaynardVerify/M2_0.v` … `MaynardVerify/M2_5.v`) so no single
`vm_compute` has to pay the full 42-row cost in one go; the final
assembly in `MaynardVerify.v` glues them via `seq_split_42` and
`M2_check_rows_app`:

```rocq
Lemma all_match_M2Z_true : all_match_M2Z = true.
Proof.
  unfold all_match_M2Z.
  rewrite seq_split_42.
  rewrite !M2_check_rows_app.
  rewrite M2_check_rows_0_6 M2_check_rows_7_13 M2_check_rows_14_20
          M2_check_rows_21_27 M2_check_rows_28_34 M2_check_rows_35_41.
  reflexivity.
Qed.
```

Both `all_match_M{1,2}Z_true` are `Qed`. `Print Assumptions` on each
reports the standard `Uint63` / `PrimInt63` kernel primitives that
`vm_compute` requires (the same footprint as any `vm_compute`-Qed in
the project); no project-specific axioms.

**Coverage:** `42 × 42 = 1764` entries per matrix, so 3528 per-entry
checks total. The check is the standard rational identity
`a/b = c/d ⟺ a · d = b · c` for positive `b, d`, applied to
`(M_int[i][j], D_M_l)` and `(num_spec[i][j], den_spec[i][j])`.

**Timing** (REPORT.md §3.8): ~90 s for `M1`, ~35 min aggregate for the
six `M2` chunks. The M2 cost dominates because each entry is a sum of
up to `(c_i + 1) × (c_j + 1) ≤ 36` terms, each of which forms a full
`G_{·,2}(104)` expansion — the per-term denominator grows to thousands
of digits before `qplus` collapses it.

---

## 9. What is NOT verified inside Rocq

### 9.1 Lemma 8.3 (`M_k = k · sup_F J_k(F)/I_k(F)`) — *paper-side only*

The Rocq layer proves the strict Rayleigh-quotient bound
`4 · a^T M_1 a < 105 · a^T M_2 a` (with `a^T M_1 a > 0`) at the
specific 42-entry rational witness `a = v_witness` in
`Witness_Rayleigh.v`, by `CertRayleigh.rayleigh_witness_holds` (lifted to
rat via `CertRayleigh.rayleigh_lt_main`). Bridging this to `M_{105} > 4`
requires:

(a) Lemma 8.3's identity `M_k = k · sup_F J_k(F)/I_k(F)`
    (Lagrange multipliers over a positive-definite Gram matrix), and
(b) the trivial `sup ≥ value at any individual F`.

The analytic identity itself (integrals `→` Gram matrices) is taken on
the paper side (REPORT.md §1.4 makes the same disclosure).

What the **two routes** formalise of the matrix-level conclusion differs:

- **Route 1** (`maynard_M105_certified_rayleigh`) discharges only (b) at a
  single witness — it formalises **no** eigenvalue, **no** characteristic
  polynomial, and **no** Chinese-remainder lift; the proof is the
  single-quotient strategy of Maynard's original Mathematica notebook,
  mechanised in pure-`Z` arithmetic by `vm_compute`.
- **Route 2** (`maynard_M105_certified`) goes further and formalises the
  spectral half `k · λ_max(M_1^{-1} M_2) > 4` of (a) inside Rocq: it *does*
  build a characteristic polynomial (mod `p`, lifted by deterministic CRT),
  prove `M_1` positive-definite, and exhibit an actual eigenvalue of
  `M105` above `4` (see §6½). The analytic step relating `M_k` to the Gram
  matrices remains paper-side.

Neither route invokes IVT, a Sturm chain, `realalg`, or native 63-bit
integers — those denials hold for the whole development.

### 9.2 Positivity of `M_1` and the supremum / max equivalence

Maynard's Lemma 8.3 is the analytic statement
`M_k = k · sup_F J_k(F)/I_k(F)` for the quadratic forms `J_k`, `I_k`
defined by `M_2`, `M_1` (paper). The strict Rayleigh-quotient bound
at *any* fixed `a` is a lower bound on this supremum so long as
`a^T M_1 a > 0`, which `CertRayleigh.rayleigh_witness_M1_positive`
checks for `a = v_witness`. For **Route 1** the per-witness positivity
is all that is needed — positivity of `M_1` as a whole is not used.
**Route 2**, by contrast, *does* prove `M_1` positive-definite as a whole
(`M1PosDef`, via the CRT-over-`Z` sign-alternating characteristic-polynomial
certificate of §6½): full PD is what makes the spectral square-root factor
`M1_rat_factor` available and turns the generalized pencil into a standard
Hermitian eigenproblem.

### 9.3 The Beta-integral derivation `J_k(F)/I_k(F) → closed form`

The closed-form rational formulas in §3–§6 above (Lemma 8.1 / 8.2)
are taken as **definitions** in Rocq. The analytic derivation —
Beta-function identity for `∫_0^X t^a (X − t)^b dt`, integrate `t_1`
out via eq. 8.8, sum over compositions — is the content of Lemma 8.1's
proof in Maynard. We do not reproduce this analytic step inside Rocq.

What Rocq *does* certify is that the resulting closed-form rational
matches the shipped integer matrix `M1_int / D_M1`, `M2_int / D_M2`
entry-for-entry. So if a reviewer accepts Maynard's Lemma 8.1 / 8.2
on paper, the kernel guarantees the matrices `CertRayleigh.v` consumes
are exactly the Maynard matrices.

---

## Summary table

| Rocq object | File | Paper (v3 §8) |
|-------------|------|---------------|
| `compositions_aux`, `compositions` | `MaynardSpec.v` PART A | Lemma 8.1 inner index set: length-`r` compositions of `n`, parts ≥ 1 |
| `cff` | `MaynardSpec.v` PART A | Lemma 8.1 inner product `Π (2 b_s)!/b_s!` |
| `G_2` | `MaynardSpec.v` PART A | Lemma 8.1 (`G_{n, 2}(k) = n! · Σ_r C(k, r) · Σ_{a ∈ comp(r,n)} cff a`) |
| `K1`, `K2` | `MaynardSpec.v` PART A | `k = 105`, `k − 1 = 104` |
| `M1_entry` | `MaynardSpec.v` PART A | Lemma 8.2 (M1 part) |
| `alpha` | `MaynardSpec.v` PART A | eq. 8.8 (= v1 eq. 7.10) |
| `M2_entry` | `MaynardSpec.v` PART A | Lemma 8.2 (M2 part, per-coord `J_k^{(1)}`) |
| `M1_spec_ij`, `M2_spec_ij` | `MaynardSpec.v` PART A | indexed via 42-basis |
| `compositionsZ`, `cffZ`, `G2Z`, `m1_num_den`, `alphaZ`, `m2_num_den` | `MaynardSpec.v` PART B | Z-level twin of PART A; same closed forms as `(num, den) : Z × Z` pairs |
| `M1_spec_rat_eq`, `M2_spec_rat_eq` | `MaynardSpecBridge.v` | rat-level bridge: `M{1,2}_spec_ij i j = qfrac (m{1,2}_num_den_at i j)`, `Qed`, *Closed under the global context* (standalone, used inside `M{1,2}_spec_eq_int`) |
| `maynard_basis` (and `_size`, `_uniq`, `_spec`, `_eq_witness`) | `MaynardBasis.v` | p. 23, "for simplicity" |
| `all_match_M1Z_true` | `MaynardVerify/Def.v` | 1764 Z-level cross-checks for `M_1`, single `vm_compute. reflexivity.` (standalone, used inside `M1_spec_eq_int`) |
| `all_match_M2Z_true` | `MaynardVerify.v` (+ six chunks `MaynardVerify/M2_0..5.v`) | 1764 Z-level cross-checks for `M_2`, six 7-row chunks reassembled via `seq_split_42` (standalone, used inside `M2_spec_eq_int`) |
| `M1_spec_eq_int`, `M2_spec_eq_int` | `Cert.v` | composed identity `M{1,2}_spec_ij i j = Z2rat (mat_get M{1,2}_int i j) / Z2rat D_M{1,2}` — these are the two rat-level conjuncts of the headline `CertRayleigh.maynard_M105_certified_rayleigh` |
| `maynard_M105_certified_rayleigh` | `CertRayleigh.v` | 3-conjunct headline: `M1_spec` = `M1_int / D_M1`, `M2_spec` = `M2_int / D_M2`, plus the strict Rayleigh-quotient bound `4 * quad_spec M1_spec_ij < 105 * quad_spec M2_spec_ij` at the shipped witness vector |
| `rayleigh_witness_holds` | `CertRayleigh.v` | integer Rayleigh inequality `4 * D_M2 * v_num^T M1_int v_num < 105 * D_M1 * v_num^T M2_int v_num` at the shipped scaled-integer witness, `vm_compute` Qed, *Closed under the global context* |
| `rayleigh_witness_M1_positive` | `CertRayleigh.v` | integer positivity `v_num^T M1_int v_num > 0`, `vm_compute` Qed, *Closed under the global context* |
| `v_witness` | `Witness_Rayleigh.v` | 42-entry rational witness vector as `list (Z * Z)`; autogenerated by `python/build_quad_witness.py`; verified slack `≈ +2.07e-3` |
| `M1_rat`, `M2_rat`, `A_rat`, `M105` | `EigenBridge.v` | `M{1,2}_int / D_M{1,2}` as `'M[rat]_42`; `A_rat = M_1^{-1} M_2`; `M105 = 105 *: A_rat = k · M_1^{-1} M_2` (Lemma 8.3) |
| `matches_closed_forms` | `EigenBridge.v` | trust contract: `M = M105` and the paper-form spec entries equal the FLINT-shipped integer data (reuses `M{1,2}_spec_eq_int`) |
| `maynard_M105_certified` | `MaynardEigen.v:372` | Route 2 headline (eigenvalue / target form): `matches_closed_forms M105 /\ exists lam : algC, eigenvalue (ratrM M105) lam /\ 4 < lam` — Maynard's `M_{105} = λ_max(M105) > 4`, `Qed`, *Closed under the global context* |
| `M1_rat_factor` | `M1PosDef.v` | complex congruence factor `R` with `Rᵀ* *m R = ratrM M1_rat` (`M_1` PD spectral square root) |
| `char_poly_int_M1_eq` | `M1CharPoly.v` | `char_poly_int M1_int = cp_M1_value` (sign-alternating ⟹ `M_1` PD), via CRT over 200 primes |
| `herm_crux` | `SpectralCrux.v` | spectral crux: `A` Hermitian, `0 < wᵀAw` ⟹ `A` has a positive eigenvalue |
