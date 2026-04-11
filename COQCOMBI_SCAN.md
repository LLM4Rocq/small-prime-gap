# CoqCombi Scan Report: Closing `fl_loop_rat_is_char_poly_L2`

## 1. Relevant Lemmas Found

### 1A. Newton's Identities (from `Combi.MPoly.sympoly`)

All four Newton identity lemmas exist and are proved (opaque, Qed):

**`Newton_symh`** (line 1226):
```
forall n R k,  k *: 'h_k = \sum_(i < k) 'h_i * 'p_(k - i)
```
Reads: k times the k-th complete homogeneous symmetric polynomial equals
the sum over i < k of h_i * p_{k-i}.

**`Newton_symh1`** (line 1252):
```
forall n R k,  k *: 'h_k = \sum_(1 <= i < k.+1) 'p_i * 'h_(k - i)
```
Same identity, re-indexed with p on the left and summation from 1 to k.

**`Newton_syme`** (line 1489):
```
forall n R k,  k *: 'e_k = \sum_(i < k) (-1)^(k-i+1) *: 'e_i * 'p_(k-i)
```
Newton's identity for elementary symmetric polynomials (with signs).

**`Newton_syme1`** (line 1467):
```
forall n R k,  k *: 'e_k = \sum_(1 <= i < k.+1) (-1)^(i+1) *: 'p_i * 'e_(k-i)
```
Re-indexed version for elementary symmetric polynomials.

### 1B. Roots-to-Coefficients Bridge (from `mathcomp.multinomials.mpoly`)

**`mroots_coeff`** (mpoly line 4226):
```
forall [R : idomainType] [n : nat] (cs : n.-tuple R) (k : 'I_n.+1),
  (\prod_(c <- cs) ('X - c%:P))`_(n - k) = (-1)^+k * (mesym n R k).@[tnth cs]
```
This connects univariate polynomial coefficients to elementary symmetric
polynomials evaluated at the roots. Key fact:
- `mesym n R k` is the k-th elementary symmetric polynomial (same as `'e_k`'s underlying mpoly)
- `.@[tnth cs]` is `meval` at the tuple of roots
- The product `\prod_(c <- cs) ('X - c%:P)` is exactly what char_poly gives
  (when cs = eigenvalues)

### 1C. Power Sum Definition (from `Combi.MPoly.sympoly`)

**`symp_pol`**:
```
symp_pol n R d = \sum_(i < n) 'X_i ^+ d
```
So `'p_d` evaluated at eigenvalues `(lambda_1, ..., lambda_n)` gives
`\sum_i lambda_i^d = tr(A^d)`.

### 1D. Evaluation Machinery

**`meval_is_lrmorphism`** (from mathcomp-multinomials):
```
forall [n : nat] [R : comNzRingType] (v : 'I_n -> R),
  scalable_for *%R (meval v)
```
`meval v` is a ring morphism (preserves +, *, scalar mult). This means
we can push `meval eigenvalues` through the entirety of Newton's identity.

**`map_sympoly`**: Ring morphism between sympoly over different base rings.
Allows coefficient changes (e.g., int -> rat).

**`sympolyf_eval`**: Projects multivariate polynomials to sympoly by
averaging over permutations. Ring morphism. Has cancel lemma `sympolyf_evalK`.

### 1E. Basis Conversion

**`symh_to_symp_prod_partsum`**: Expresses `'h_n` in the power-sum basis
(requires char 0 field). Exact statement:
```
forall nvar0 [R : fieldType] n, pchar R =i pred0 ->
  'h_n = \sum_(c : intcompn n) (prod_partsum (cnval c))^-1 *: \prod_(i <- cnval c) 'p_i
```

**`coeff_symh_to_symp`**: The transition matrix coefficients between
homogeneous and power-sum bases.

### 1F. Omega Involution

**`omegasf`**: The involution `'h_k <-> 'e_k` on symmetric polynomials.
**`omegasf_prodsymh`**: `omegasf 'h[la] = 'e[la]` (swaps h and e basis).

### 1G. Products

**`prod_syme`**, **`prod_symh`**: Products of elementary/homogeneous symmetric
polynomials indexed by partitions.

## 2. Mapping Newton's Identity to the FL Recurrence

### The FL Recurrence (from CharPolyL2.v)
```
M_k     = A * M_{k-1} + c_{n-k+1} * I_n
c_{n-k} = -(1/k) * tr(A * M_k)
```
Expanding: `k * c_{n-k} = -tr(A * M_k) = -\sum_{i=0}^{k-1} c_{n-i} * tr(A^{k-i})`

### Newton_symh says
```
k *: 'h_k = \sum_(i < k) 'h_i * 'p_(k-i)
```

### The Exact Mapping

The char_poly of an n x n matrix A over a commutative ring is:
```
char_poly A = \prod_(eigenvalue lambda) ('X - lambda%:P)
```
By `mroots_coeff`, its coefficient at degree `n - k` is:
```
(char_poly A)`_(n-k) = (-1)^k * (mesym n R k).@[eigenvalues]
```

The standard convention for char_poly coefficients c_k (low-to-high) is:
```
c_k = (char_poly A)`_k = (-1)^(n-k) * e_{n-k}(eigenvalues)
```

The complete homogeneous symmetric polynomials relate via the omega involution:
```
h_k(eigenvalues) corresponds to (-1)^k * e_k(eigenvalues) (up to signs)
```

**The precise correspondence for FL:**
- `'h_k` evaluated at eigenvalues = `(-1)^k * c_{n-k}` (with appropriate sign convention)
- `'p_k` evaluated at eigenvalues = `tr(A^k)`
- Newton_symh after evaluation gives exactly the FL recurrence (up to signs)

**However**, there is a critical gap: Newton_symh lives in `{sympoly R[n]}`,
the ring of symmetric polynomials in n variables. To use it for matrices,
we need to:
1. Take eigenvalues `lambda_1, ..., lambda_n` of A (requires algebraically closed field)
2. Apply `meval (tnth eigenvalues)` to both sides of Newton_symh
3. Identify `meval eigenvalues 'h_k` with char_poly coefficients (via `mroots_coeff`)
4. Identify `meval eigenvalues 'p_k` with `tr(A^k)` (via `symp_pol` definition)

## 3. Specialization Machinery Assessment

### What Exists
- `meval v` is an lrmorphism, so it distributes over Newton_symh cleanly
- `mroots_coeff` gives `meval eigenvalues (mesym n R k)` = char_poly coefficient
- `symp_pol` = `\sum_i 'X_i^d`, so `meval eigenvalues (symp_pol n R d)` = `\sum_i lambda_i^d`

### What Is Missing
- **No `char_poly_sym` lemma** connecting char_poly to symmetric polynomials directly
- **No `tr_pow_eq_meval_symp` lemma** saying `tr(A^k) = (symp_pol n R k).@[eigenvalues]`
- **No eigenvalue tuple extraction** -- getting from `A : 'M[R]_n` to an n-tuple of
  eigenvalues requires working over an algebraically closed field (or using the splitting
  field of char_poly)
- **`mroots_coeff` requires roots**, i.e., an n-tuple `cs` such that
  `char_poly A = \prod_(c <- cs) ('X - c%:P)`. Over `rat` this does not generally
  hold (char_poly may be irreducible).

### The Algebraic Closure Problem
This is the fundamental obstacle to the "specialize Newton at eigenvalues" route.
Over `rat`, the char_poly need not split into linear factors, so there is no
n-tuple of eigenvalues to evaluate at.

**Workarounds:**
1. **Work over the splitting field**: Lift A to `'M[algC]_n` (or the splitting field),
   factor char_poly, extract roots, apply Newton, then pull back to `rat` by
   universality (the identity is polynomial, so it holds over `rat` if it holds
   over any extension). This requires `algC` infrastructure from mathcomp.
2. **Use the polynomial identity directly**: Newton_symh is an identity in the
   polynomial ring `{sympoly R[n]}`. We don't need eigenvalues at all if we can
   establish the connection between FL and Newton at the polynomial level.
3. **Use the adjugate route** (already outlined in CharPolyL2.v): The
   `mul_mx_adj` identity works over any commutative ring, no eigenvalues needed.

## 4. The Adjugate Route (mul_mx_adj)

### Available in MathComp
**`mul_mx_adj`** (matrix.v line 3620):
```
forall [R : comPzRingType] [n : nat] (A : 'M_n),
  A *m \adj A = (\det A)%:M
```

Applied to `char_poly_mx A`:
```
char_poly_mx A *m \adj (char_poly_mx A) = (char_poly A)%:M
```

### What This Route Needs
1. Express `\adj (char_poly_mx A)` as a polynomial in 'X with matrix coefficients:
   `\adj (char_poly_mx A) = \sum_{k=0}^{n-1} B_k *: 'X^k` where `B_k : 'M[rat]_n`
2. Expand the product `(('X *: 1%:M) - A%:P%:M) * (\sum B_k 'X^k)`
3. Match coefficients of 'X^k on both sides to get the FL recurrence
4. Identify `B_k` with `fl_M_rat` by uniqueness of the recurrence

### CoqCombi Contribution to This Route
CoqCombi does NOT directly help with the adjugate route -- this is purely
MathComp linear algebra over polynomial matrices. However:

- Newton_symh could provide an **alternative proof** that avoids the adjugate
  entirely, if the algebraic closure issue is handled.
- The `mroots_coeff` lemma (from mathcomp-multinomials, not CoqCombi) could
  help bridge the gap.

## 5. Concrete Plan for Closing `fl_loop_rat_is_char_poly_L2`

### Recommended Route: Adjugate (mul_mx_adj) -- No CoqCombi Needed

This is the route already outlined in CharPolyL2.v and is the most direct.
It works over `rat` without needing eigenvalues or algebraic closure.

**Steps:**

**Step A** (~50 lines): Define polynomial matrix coefficient extraction.
```
Definition polymat_coef (n : nat) (M : 'M[{poly rat}]_n) (k : nat) : 'M[rat]_n :=
  \matrix_(i, j) (M i j)`_k.
```

**Step B** (~80 lines): Prove that expanding `char_poly_mx A *m \adj (char_poly_mx A)`
gives a recurrence on `polymat_coef`. Specifically, if we write
`\adj (char_poly_mx A) = \sum_k B_k 'X^k`, then from `mul_mx_adj`:
```
(X*I - A) * (sum_k B_k X^k) = (char_poly A)%:M
```
Matching the coefficient of X^k gives:
- k=0: `-A * B_0 = c_0 * I`  (so `B_0 = -c_0 * A^{-1}*I`, but better: `B_0 = c_0 * I` from constant term)
- 0<k<n: `B_{k-1} - A*B_k = c_k * I`  (i.e., `A*B_k = B_{k-1} - c_k*I`)
- k=n: `B_{n-1} - A*0 = c_n * I = I`  (from leading coefficient, monic)

Rearranging with `M_j = B_{n-1-j}` (the FL indexing):
```
M_0 = B_{n-1} = I  ... wait, need to check index conventions
```

Actually the FL loop says M_0 = 0, c_n = 1. The adjugate coefficients B_k
satisfy: `B_{k-1} - A*B_k = c_k * I` for 1 <= k <= n, with B_{-1} = 0
(convention) and B_{n-1} free. Setting `M_k = B_{n-k}`:
- `M_1 = B_{n-1} = A*B_n + c_n*I` but B_n doesn't exist... 

The exact index mapping needs careful working out. This is the core of the proof.

**Step C** (~60 lines): Extract `c_k = -tr(A * M_k) / k` from the trace of the
recurrence. Taking trace of both sides of the matrix equation gives:
```
tr(B_{k-1}) - tr(A*B_k) = c_k * n
```
Combined with `\sum_k c_k = 0` (trace of char_poly_mx) this gives the FL formula.

**Step D** (~30 lines): Conclude by showing the recurrence has a unique solution,
so `fl_loop_rat` must produce the char_poly coefficients.

**Estimated total: 200-300 lines of new Rocq code, 1-2 weeks of work.**

### Alternative Route: Newton via Algebraic Closure -- CoqCombi Helps

**Steps:**

**Step A** (~30 lines): Lift `A : 'M[rat]_n` to `A' : 'M[algC]_n` via the
embedding `rat -> algC`.

**Step B** (~40 lines): Factor `char_poly A'` over `algC` into linear factors:
`char_poly A' = \prod_i ('X - lambda_i%:P)`. This requires finding an n-tuple
of eigenvalues. MathComp's `closed_field_poly_normal` gives this.

**Step C** (~20 lines): Apply `mroots_coeff` to get:
`(char_poly A')`_(n-k) = (-1)^k * (mesym n algC k).@[tnth lambdas]`

**Step D** (~30 lines): Apply `meval (tnth lambdas)` to Newton_symh (from CoqCombi):
```
k * (mesym n algC k).@[tnth lambdas] = 
  \sum_(i < k) (mesym n algC i).@[tnth lambdas] * (symp_pol n algC (k-i)).@[tnth lambdas]
```
Wait -- Newton_symh uses `'h_k` (complete homogeneous), not `'e_k` (elementary).
We need Newton_syme instead (or use the omega involution).

Actually, **Newton_syme** is the right one:
```
k *: 'e_k = \sum_(i < k) (-1)^(k-i+1) *: 'e_i * 'p_(k-i)
```
After meval at eigenvalues and using mroots_coeff, this becomes:
```
k * c_{n-k}/(-1)^k = \sum_i c_{n-i}/(-1)^i * tr(A^{k-i}) * (-1)^{k-i+1}
```
which simplifies to the FL recurrence.

**Step E** (~40 lines): Show the identity over `algC` implies the identity over `rat`
(by injectivity of `rat -> algC` on polynomials, or by working with the universal
identity).

**Step F** (~30 lines): Connect to `fl_loop_rat` by showing the FL recurrence has a
unique solution.

**Estimated total: 200-300 lines, but requires `algC` and `closed_field_poly_normal`
infrastructure. Similar difficulty to the adjugate route.**

### Hybrid Route (Recommended): Newton at the Polynomial Level

The cleanest approach avoids eigenvalues entirely by working in the polynomial ring:

1. `char_poly A = \sum_k c_k * 'X^k` with `c_n = 1`.
2. Taking `d/dX log(char_poly A)` and using the formal identity
   `(d/dX char_poly) / char_poly = \sum_k k*c_k*X^{k-1} / char_poly`
   gives Newton's recurrence purely at the polynomial level.
3. Alternatively, differentiate `char_poly A` and use Cayley-Hamilton.

But this requires formal power series or polynomial division machinery
that MathComp may not have ready-made.

## 6. Summary and Recommendation

### CoqCombi Provides:
| Lemma | Location | Usefulness |
|-------|----------|------------|
| `Newton_symh` | sympoly.v:1226 | HIGH -- Newton's identity for 'h basis |
| `Newton_syme` | sympoly.v:1489 | HIGH -- Newton's identity for 'e basis (with signs) |
| `Newton_symh1` | sympoly.v:1252 | MEDIUM -- re-indexed Newton for 'h |
| `Newton_syme1` | sympoly.v:1467 | MEDIUM -- re-indexed Newton for 'e |
| `symh_to_symp_prod_partsum` | sympoly.v | MEDIUM -- basis change h->p |
| `omegasf`/`omegasf_prodsymh` | sympoly.v | LOW -- omega involution |
| `map_sympoly` | sympoly.v | LOW -- coefficient ring change |
| `prod_syme`/`prod_symh` | sympoly.v | LOW -- partition products |

### mathcomp-multinomials Provides:
| Lemma | Location | Usefulness |
|-------|----------|------------|
| `mroots_coeff` | mpoly.v:4226 | CRITICAL -- roots <-> coefficients |
| `meval_is_lrmorphism` | mpoly.v | CRITICAL -- meval is ring morphism |
| `mevalE` | mpoly.v | HIGH -- explicit meval formula |

### MathComp Provides:
| Lemma | Location | Usefulness |
|-------|----------|------------|
| `mul_mx_adj` | matrix.v:3620 | CRITICAL -- adjugate identity |
| `char_poly` machinery | matrix.v | CRITICAL -- char_poly definition |

### Bottom Line

**The adjugate route (`mul_mx_adj`) remains the most practical path** for closing
`fl_loop_rat_is_char_poly_L2`. It works directly over `rat`, requires no
algebraic closure, and the proof structure is already outlined in CharPolyL2.v.

**CoqCombi's Newton identities (`Newton_symh`/`Newton_syme`) provide a viable
alternative route**, but require either:
(a) lifting to an algebraically closed field to get eigenvalues, or
(b) working with the polynomial-level Newton identity (needs more infrastructure).

Both routes are estimated at **200-300 lines of new code and 1-2 weeks of work**,
a significant improvement over the original 3-6 week estimate. The Newton route
via CoqCombi could be **slightly shorter** if the `algC` lifting is straightforward,
since Newton_symh/Newton_syme give the recurrence directly (no need to manually
extract it from the adjugate product).

### Third Route: Cayley-Hamilton + Trace

MathComp provides `Cayley_Hamilton`:
```
forall [R : comNzRingType] [n' : nat] (A : 'M_n'.+1),
  horner_mx A (char_poly A) = 0
```
This says `\sum_{k=0}^{n} c_k * A^k = 0` (as a matrix equation). Multiplying
both sides by `A^j` and taking traces:
```
\sum_{k=0}^{n} c_k * tr(A^{k+j}) = 0   for all j >= 0
```
Setting j=0,1,...,n-1 gives a system that recovers the FL recurrence. This
route avoids both eigenvalues and the adjugate, working purely with traces.

**Advantage**: Very short proof if `horner_mx` expansion lemmas exist.
**Disadvantage**: Gives `\sum c_k * tr(A^{k+j}) = 0` but needs re-indexing
to match FL exactly, and the base cases (j=0 gives the trace formula but
not the FL step-by-step recurrence). Also requires showing the recurrence
has a unique solution.

**Estimated**: 150-250 lines if the `horner_mx` expansion is smooth.

### Key Bridge Lemmas Needed (Any Route)

1. **`tr_pow_meval_symp`**: `tr(A^k) = (symp_pol n R k).@[eigenvalues]` -- needed for
   Newton route only.
2. **`polymat_coef_mul`**: Coefficient extraction for polynomial matrix products --
   needed for adjugate route only.
3. **`fl_recurrence_unique`**: The FL recurrence has a unique solution (all routes).
4. **`char_poly_coeff_sign`**: `(char_poly A)`_k = (-1)^(n-k) * e_{n-k}(eigenvalues)`
   -- follows from `mroots_coeff` + factorization over `algC`.
5. **`horner_mx_trace`**: `tr(horner_mx A p) = \sum_k p`_k * tr(A^k)` -- needed for
   Cayley-Hamilton route.

### Prioritized Recommendation

1. **First try**: Cayley-Hamilton route (simplest, ~150-250 lines, no CoqCombi needed)
2. **If stuck**: Adjugate route via `mul_mx_adj` (~200-300 lines, no CoqCombi needed)
3. **Alternative**: Newton via CoqCombi + algC (~200-300 lines, uses Newton_syme)

All three routes are **1-2 weeks**, a major improvement over the original 3-6 week estimate.
