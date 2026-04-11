# JACOBI_SCAN: MathComp / CoqCombi / multinomials scan for `adj_coef_jacobi` sub-admits

**Date**: 2026-04-09
**Environment**: Rocq 9.0.1, MathComp 2.5.0, mathcomp-real-closed 2.0.3, mathcomp-multinomials 2.4.0, CoqCombi (Combi logical path), mathcomp-algebra-tactics 1.2.7
**File under analysis**: `theories/S1/CharPolyL2.v`, lines 593-674

---

## Summary

**Jacobi's formula is NOT proved anywhere in the MathComp ecosystem.** None of the three sub-admits can be closed by a single existing lemma. Each requires a multi-line proof using available building blocks.

---

## The three sub-admits

### 1. `Hcoef_eq` (line 607-617): Coefficient recurrence from `mul_mx_adj`

**Goal**: For `P = char_poly_mx B` and `Q k = map_mx (coefp k) (\adj P)`:
```
Q k - B *m Q k.+1 = cp`_k.+1 *: 1%:M
```

**Status**: No direct lemma exists. Must be proved by hand.

**Available building blocks**:
- `mul_mx_adj : A *m \adj A = (\det A)%:M` -- the core identity
- `char_poly_mx = fun A => 'X%:M - (A ^ polyC)` -- structure of P
- `coef_deriv`, `derivM`, `derivD`, `derivN` -- polynomial coefficient manipulation
- `expand_det_row / expand_det_col` -- cofactor expansion of determinant

**Proof strategy**: Apply `mul_mx_adj` to `P`, extract entry `(i,j)`, expand `P_{il} = delta_{il}*'X - B_{il}%:P`, then match coefficient `k+1` on both sides. The LHS becomes `(adj P)_{ij}`\_k - sum\_l B\_{il} * `(adj P)_{lj}`\_{k+1} which is `(Q k - B *m Q (k+1))_{ij}`. The RHS is `(det P)_{k+1} * delta_{ij} = cp_{k+1} * delta_{ij}`. This is a ~20-line calculation using `mxE`, `big_split`, coefficient extraction, etc.

### 2. `HQn` off-diagonal (line 619-631): `coefp n (cofactor(P, j, i)) = 0` when `i != j`

**Goal**: For `i != j`, show `coefp n (cofactor (char_poly_mx B) j i) = 0`.

**Status**: No `size_cofactor` or `degree_cofactor` lemma exists in MathComp.

**Available building blocks**:
- `expand_cofactor` -- expresses cofactor as a sum over permutations s with s(j) = i, of products over k != j of `P_{k, s(k)}`
- `size_prod : (forall i, P i -> F i != 0) -> size (\prod_(i | P i) F i) = (\sum_(i | P i) size (F i)).+1 - #|P|` -- polynomial degree of products
- `char_poly_mx` entries: diagonal entries `P_{k,k} = 'X - B_{k,k}%:P` have `size = 2`; off-diagonal `P_{k,l} = -(B_{k,l})%:P` (for k != l) have `size <= 1`

**Proof strategy**: When `i != j`, every permutation s with `s(j) = i` must send some `k != j` to `s(k) != k` (since `s(j) = i != j`, so s is not the identity on the remaining indices), meaning each product `\prod_(k | j != k) P_{k, s(k)}` contains at most `n-1` linear factors (at least one factor is a constant). By `size_prod`, the polynomial degree of each summand is at most `n-1`, so `coefp n = 0`. This requires a combinatorial argument about permutations, roughly 15-25 lines.

### 3. `jacobi` (line 654-658): Jacobi's formula for polynomial matrices

**Goal**:
```
deriv (\det P) = \sum_(k : 'I_n.+1) \det (row' k (col' k P))
```
where `P = char_poly_mx B : 'M[{poly rat}]_(n.+1)`.

**Status**: **NOT in MathComp, NOT in CoqCombi, NOT in multinomials.** Web search confirms no Coq formalization exists in any publicly known library.

**Available building blocks**:
- `determinant` is defined via `\sum_(s : 'S_n) (-1)^s * \prod_i A_{i,s(i)}`
- `derivM : (p * q)^`() = p^`() * q + p * q^`()` -- Leibniz product rule for polynomials
- `deriv_exp : (p ^+ n)^`() = p^`() * p ^+ n.-1 *+ n` -- derivative of power
- `derivD`, `derivN`, `derivZ`, `derivC`, `derivX` -- linearity of deriv
- `expand_det_row`, `expand_det_col` -- cofactor expansion
- `row'_col'_char_poly_mx : row' i (col' i (char_poly_mx M)) = char_poly_mx (row' i (col' i M))` -- **critical**: minors of char_poly_mx are char_poly_mx of minors

**Proof strategy**: The determinant is `\sum_s sign(s) * \prod_i P_{i, s(i)}`. Differentiate using linearity of `deriv` over sums and the product rule (Leibniz rule for n factors). This gives `\sum_s sign(s) * \sum_k P_{k,s(k)}^`() * \prod_(i != k) P_{i,s(i)}`. For `char_poly_mx`, the derivative `P_{k,s(k)}^`()` is 1 when `s(k) = k` (diagonal) and 0 when `s(k) != k` (off-diagonal constant). So only the identity-on-k terms survive, giving `\sum_k \sum_(s | s(k) = k) sign(s) * \prod_(i != k) P_{i,s(i)} = \sum_k det(row' k (col' k P))`.

**This is the hardest admit.** A general Jacobi's formula would be ~50-80 lines. However, the *specialized* version for `char_poly_mx` is simpler because the derivative kills off-diagonal entries, reducing to ~30-40 lines.

**Key insight for simplification**: Instead of proving general Jacobi, prove the specialized identity directly:
1. Write `det P = \sum_s sign(s) * \prod_i P_{i,s(i)}`
2. Use `derivM` inductively (via big product derivative lemma) to get `\sum_s sign(s) * \sum_k (deriv P_{k,s(k)}) * \prod_(i!=k) P_{i,s(i)}`
3. For `char_poly_mx`: `deriv (P k (s k))` = 1 if `s k = k`, else 0 (since off-diag entries are constants)
4. Reindex to get `\sum_k det(row' k (col' k P))`

The missing piece is a "derivative of a big product" lemma, which MathComp does NOT have. One would need:
```
deriv (\prod_(i in S) f i) = \sum_(j in S) deriv (f j) * \prod_(i in S | i != j) f i
```
This must be proved by induction on `|S|` using `derivM`.

---

## Key lemmas found in MathComp

| Lemma | Location | Relevance |
|-------|----------|-----------|
| `mul_mx_adj` | matrix.v | `A *m \adj A = (\det A)%:M` -- core for Hcoef_eq |
| `mul_adj_mx` | matrix.v | `\adj A *m A = (\det A)%:M` |
| `expand_det_row` | matrix.v | cofactor expansion |
| `expand_cofactor` | matrix.v | explicit sum over permutations |
| `cofactor_tr` | matrix.v | transpose of cofactor |
| `cofactor_map_mx` | matrix.v | cofactor commutes with ring morphisms |
| `row'_col'_char_poly_mx` | mxpoly.v | **critical**: minors of char_poly_mx = char_poly_mx of minors |
| `size_char_poly` | mxpoly.v | `size (char_poly A) = n.+1` |
| `char_poly_monic` | mxpoly.v | char_poly is monic |
| `Cayley_Hamilton` | mxpoly.v | `horner_mx A (char_poly A) = 0` |
| `size_prod` | poly.v | degree of product of polynomials |
| `derivM` | poly.v | product rule for polynomial derivative |
| `deriv_exp` | poly.v | derivative of power |
| `coef_deriv` | poly.v | `(p^`())_i = p_{i+1} *+ i.+1` |

## Lemmas NOT found anywhere

| Needed | Status |
|--------|--------|
| `deriv (\det M) = ...` (Jacobi's formula) | **Not in any library** |
| `size (cofactor M i j) <= ...` (degree bound on cofactors) | **Not in any library** |
| `deriv (\prod_(i<n) f i) = \sum_j ...` (derivative of big product) | **Not in any library** |
| `coefp k (cofactor (char_poly_mx B) j i)` for any explicit k | **Not in any library** |
| `map_mx coefp` interaction with adjugate/cofactor | **Not in any library** |

---

## Recommendation

**None of the three admits can be closed with a 1-liner.** All require substantive proofs:

1. **Hcoef_eq** (~20 lines): Straightforward coefficient extraction from `mul_mx_adj`. Use `matrixP`, expand entries, manipulate polynomial coefficients.

2. **HQn off-diagonal** (~20 lines): Degree bound argument using `expand_cofactor` + `size_prod` + case analysis on permutations of `char_poly_mx`.

3. **jacobi** (~40 lines): Most work. Prove specialized Jacobi for `char_poly_mx` by:
   - First prove a "derivative of big product" helper lemma (~15 lines)
   - Then specialize to `char_poly_mx` entries where `deriv` kills constants (~25 lines)
   - Reindex the surviving terms as `\sum_k det(row' k (col' k P))` using `expand_cofactor`

**Total estimated effort**: ~80 lines of new proof code across the three admits.
