# Remaining Admits Plan -- Maynard M_{105} > 4

**Date**: 2026-04-09
**Environment**: Rocq 9.0.1, MathComp 2.5.0, mathcomp-real-closed, mathcomp-algebra-tactics
**Total remaining admits**: 9

---

## Table of Contents

1. [Dependency Map and Critical Path](#1-dependency-map-and-critical-path)
2. [Per-Admit Detailed Plans](#2-per-admit-detailed-plans)
3. [External Library Survey](#3-external-library-survey)
4. [Effort Summary](#4-effort-summary)

---

## 1. Dependency Map and Critical Path

### Headline theorem dependency chain

```
maynard_eigenvalue_S1 (Cert.v, Qed)
  |-- sturm_count_correct (L1, Qed -- delegates to maynard_L1_concrete)
  |     |-- maynard_L1_concrete (CertL1.v, Qed)
  |           |-- prs_chain_sturm_correct (CertL1.v, ADMITTED)         [#4]
  |                 |-- prs_chain_variation_diff_eq (CertL1.v, ADMITTED) [#5]
  |                 |-- cauchy_bound_le_of_chain (CertL1.v, ADMITTED)    [#6]
  |
  |-- charpoly_int_eq_charpoly (L2, Cert.v, ADMITTED)                  [#1]
  |     |-- char_poly_int_correct (CharPoly.v, ADMITTED)               [#2]
  |           |-- Z_rem_of_intr_eq (CharPolyL2.v, ADMITTED)            [#3]
  |           |-- fl_invariant_L2 (CharPolyL2.v, Qed modulo #3)
  |           |-- fl_loop_rat_is_char_poly_L2 (CharPolyL2.v, Qed)
  |
  |-- eigenvalue_of_root_realalg (L3, Cert.v, Qed)
  |-- A_rat_unitmx (Cert.v, Qed -- uses vm_compute + bridge)
        |-- det_rat_nonzero_M1 (UnitmxCheck.v, ADMITTED)               [#8]
        |-- det_rat_nonzero_M2 (UnitmxCheck.v, ADMITTED)               [#9]
              |-- det_int_laplace_eq_det_int (IntMatProof.v, ADMITTED)  [#7]
```

### Critical path for the headline L2

**Minimal set to close L2**: Admits #1, #2, #3.

- **#3 (Z_rem_of_intr_eq)** is the leaf: once closed, `fl_combined` in CharPolyL2.v becomes fully Qed, making `fl_invariant_L2` and `fl_divisibility_L2` unconditionally Qed.
- **#2 (char_poly_int_correct)** is assembly: it chains `fl_invariant_L2` (needs #3) + `fl_loop_rat_is_char_poly_L2` (already Qed). This is the most straightforward assembly.
- **#1 (charpoly_int_eq_charpoly)** bridges the FLINT-shipped `charpoly_int` (from Witness.v) to MathComp's `char_poly A_rat`. This requires either (a) proving `char_poly_int_correct` for the concrete Maynard matrix and then equating `charpoly_int` with `char_poly_int(A_int)` via `char_poly_int_agrees_with_flint` (CRT-verified, Qed), or (b) a direct route through `charpoly_int` being a known polynomial whose roots are verified.

**Critical path for L1**: Admits #4, #5, #6. These are independent of L2.

**Outside headline**: Admits #7, #8, #9 feed `A_rat_unitmx`. However, `A_rat_unitmx` is already Qed in Cert.v via the modular determinant check + `A_rat_unitmx_from_check`. Admits #8/#9 are the leaves of that chain. They do NOT block the headline `maynard_eigenvalue_S1` because the proof of `A_rat_unitmx` already compiles (it uses `det_rat_nonzero_M1/M2` which are admitted but their results are consumed). Wait -- re-checking: `A_rat_unitmx` in Cert.v IS Qed and calls `A_rat_unitmx_from_check` which calls `det_rat_nonzero_M1/M2`. So #8/#9 DO propagate to the headline's assumption set. They must be closed for a clean `Print Assumptions maynard_eigenvalue_S1`.

### Priority order

1. **#3** (Z_rem_of_intr_eq) -- leaf, ~20 lines, unblocks #2
2. **#2** (char_poly_int_correct) -- assembly, ~80 lines, unblocks #1
3. **#1** (charpoly_int_eq_charpoly) -- bridge, ~60 lines
4. **#5** (prs_chain_variation_diff_eq) -- hard math, ~200 lines
5. **#4** (prs_chain_sturm_correct) -- depends on #5 + #6, ~50 lines
6. **#6** (cauchy_bound_le_of_chain) -- BigZ bridge, ~100 lines
7. **#8, #9** (det_rat_nonzero_M1/M2) -- modular bridge, ~120 lines each
8. **#7** (det_int_laplace_eq_det_int) -- Bareiss = Laplace, ~300 lines

---

## 2. Per-Admit Detailed Plans

---

### Admit #1: `charpoly_int_eq_charpoly` (Cert.v)

**Statement**:
```coq
charpoly_as_poly_realalg = map_poly ratr (char_poly A_rat)
```
where `charpoly_as_poly_realalg = map_poly ratr (pol_to_polyrat charpoly_int)` and `A_rat = invmx(M1_rat) *m M2_rat`.

**Challenge**: `charpoly_int` is a pre-shipped polynomial from FLINT (in Witness.v), NOT computed by `char_poly_int`. The connection goes through:
1. `char_poly_int_agrees_with_flint` (Qed in CharPolyAgree.v): CRT verification that `char_poly_int(A_int) = charpoly_int` modulo 10 primes whose product exceeds 2^300.
2. `char_poly_int_correct` (#2): `pol_to_polyrat(char_poly_int M) = char_poly(mat_int_to_rat M 1 n)`.
3. Matrix algebra: `char_poly(A_rat) = char_poly(invmx(M1_rat) *m M2_rat)`.

**Proof outline** (pseudocode):
```
1. Establish charpoly_int = char_poly_int A_int_product
   (where A_int_product is the integer-cleared product matrix)
   via CRT lifting from char_poly_int_agrees_with_flint.
2. Apply char_poly_int_correct to get:
   pol_to_polyrat(charpoly_int) = char_poly(mat_int_to_rat A_int_product 1 42)
3. Show mat_int_to_rat A_int_product 1 42 = D *: A_rat for appropriate D,
   so char_poly(mat_int_to_rat ...) relates to char_poly(A_rat) via
   char_poly_scalemx or direct coefficient scaling.
4. Lift both sides through map_poly ratr (which is a ring morphism).
```

**Alternative (simpler) route**: If the CRT bridge is too complex, prove directly that the shipped `charpoly_int` coefficients, when evaluated at rat and lifted to realalg, give the same polynomial as `char_poly A_rat` by:
- Using `char_poly_int_correct` for `A_int` with D=1.
- Relating `char_poly(M1^{-1} M2)` to `char_poly_int(M1^{-1} M2)_int` via the denominator-clearing identity.

**Key MathComp lemmas**:
- `map_char_poly : map_poly f (char_poly A) = char_poly (map_mx f A)` (in `mxalgebra.v`)
- `char_poly_monic : char_poly A \is monic` (in `matrix.v`)
- `map_poly_comp : map_poly f (map_poly g p) = map_poly (f \o g) p`
- `size_char_poly : size (char_poly A) = n.+1`

**Estimated lines**: 60-80
**Risk**: Medium. The CRT integer-lifting bridge (going from "equal mod 10 primes" to "equal over Z") requires a formal CRT argument or a bound argument. The bound argument is viable because the char_poly coefficients are bounded by Hadamard's bound, and the CRT modulus exceeds that bound.
**External library**: CoqEAL's refinement framework could help with the CRT bridge.

---

### Admit #2: `char_poly_int_correct` (CharPoly.v)

**Statement**:
```coq
pol_to_polyrat (char_poly_int M) = char_poly (mat_int_to_rat M 1 n)
```

**Current state**: All dependencies are now Qed or nearly Qed:
- `fl_loop_rat_is_char_poly_L2` -- **Qed** (CharPolyL2.v line 958)
- `fl_invariant_L2` -- **Qed modulo #3** (CharPolyL2.v line 1353, depends on `Z_rem_of_intr_eq`)
- `fl_divisibility_L2` -- **Qed modulo #3** (CharPolyL2.v line 1363)
- Step 1 bridge lemmas (CharPolyHelpers.v) -- all **Qed**

**Proof outline**:
```
1. Unfold char_poly_int to fl_loop n 1 M (meye n) (mzero n) 1 [] ++ [1].
2. Show fl_loop produces the coefficient list [c_0; ...; c_{n-1}]
   where c_k = fl_c_int_k M (n-k), by a straightforward list induction
   on fl_loop matching fl_state.
3. Apply fl_invariant_L2 to lift each c_k to rat:
   (Z_to_int c_k)%:~R = fl_c_rat A k
4. Apply fl_loop_rat_is_char_poly_L2:
   Poly(rcons [fl_c_rat A n; ...; fl_c_rat A 1] 1) = char_poly A
5. Show pol_to_polyrat distributes over the list:
   pol_to_polyrat (cs ++ [1]) = Poly (map Z_to_int_rat cs ++ [1])
6. Close by polynomial extensionality (polyP/coefP).
```

**Key MathComp lemmas**:
- `polyP : (forall i, p`_i = q`_i) -> p = q`
- `coef_Poly : (Poly s)`_i = nth 0 s i`
- `Poly_cat, map_cat` (Stdlib list lemmas + Poly properties)

**Estimated lines**: 60-80
**Risk**: Easy-medium. This is assembly work. The main subtlety is index bookkeeping between `fl_loop` (which iterates forward accumulating in reverse) and `fl_c_int_k` (which is defined via `fl_state`). A helper lemma `fl_loop_eq_fl_state` relating the two is needed (~20 lines of list induction).
**External library**: None needed.

---

### Admit #3: `Z_rem_of_intr_eq` (CharPolyL2.v)

**Statement**:
```coq
Lemma Z_rem_of_intr_eq (a : Z) (k : nat) (z : int) :
  (0 < k)%N ->
  ((Z_to_int a)%:~R : rat) = (- ((k%:R : rat) * (z%:~R : rat))) ->
  Z.rem a (Z.of_nat k) = Z0.
```

**Current state**: The proof is started (CharPolyL2.v line 1229-1240). The hypothesis gives `Z_to_int a = -(Posz k * z)` as int (already derived via `intr_injective_rat`). Then `Z.rem_divide` is applied but the divisibility witness is not provided.

**Proof outline**:
```
1. From Heq, derive: Z_to_int a = -(Posz k * z) as int.
   (Already done in the file via intr_injective_rat.)
2. Apply Z_to_int_inj (from IntMatProof.v or prove locally) to get:
   a = -(Z.of_nat k * int_to_Z z) over Z.
   This requires an inverse function int_to_Z : int -> Z and the
   roundtrip Z_to_int_inv: int_to_Z (Z_to_int a) = a.
3. Z.rem a (Z.of_nat k) = Z.rem (-(Z.of_nat k * q)) (Z.of_nat k)
   = 0 by Z.rem_opp_l and Z.rem_mul.
```

The key missing piece is the `int_to_Z` inverse and the identity `int_to_Z(-(Posz k * z)) = -(Z.of_nat k * int_to_Z z)`. This is straightforward case analysis on the sign of z.

**Key lemmas**:
- `Z.rem_divide : d <> 0 -> Z.rem a d = 0 <-> (d | a)` (Stdlib)
- `Z.rem_opp_l : Z.rem (-a) b = -(Z.rem a b)` (Stdlib)
- `Z.rem_mul : b <> 0 -> Z.rem (a * b) b = 0` (Stdlib)
- `Z_to_int_inj` (IntMatProof.v, Qed)

**Estimated lines**: 20-30
**Risk**: Easy. Pure plumbing between Z and int representations.
**External library**: None needed.

---

### Admit #4: `prs_chain_sturm_correct` (CertL1.v)

**Statement**:
```coq
sturm_count_above WitnessChain.sturm_chain 4 105
= size (List.filter (fun r => threshold_ralg 4 105 < r)
          (rootsR (pol_to_polyralg charpoly_int))).
```

**Depends on**: #5 (prs_chain_variation_diff_eq), #6 (cauchy_bound_le_of_chain).

**Proof outline**:
```
1. Rewrite LHS (sturm_count_above) as:
   changes_horner(shipped_chain, 4/105) - changes_pinfty(shipped_chain)
   using variation_at_rat_morph and variation_at_pinf_morph (Bridge.v, Qed).

2. Apply prs_chain_variation_diff_eq (#5) to replace with:
   changes_horner(mods_chain, 4/105) - changes_pinfty(mods_chain)

3. The mods chain's variation difference equals the root count by
   the Sturm theorem. Specifically, use:
   - taq_taq_itv (qe_rcf_th): connects taq on roots in (a,b) to
     changes_itv_mods when mods-chain entries don't vanish at a,b.
   - Take a = 4/105, b = cauchy_bound(P).
   - Use cauchy_bound_le_of_chain (#6) for the side conditions.
   - Use ge_cauchy_bound to show no roots >= cauchy_bound.

4. The root count in (a, cauchy_bound) = root count in (a, +inf)
   since all roots lie below cauchy_bound (by root_cauchy_boundP).

5. Equate with size(filter ...) on rootsR.
```

**Key MathComp lemmas**:
- `taq_taq_itv : a < b -> all ... (mods p (p^` * q)) -> ... -> taq (roots p a b) q = taq_itv a b p q` (qe_rcf_th)
- `rootsR : {poly R} -> seq R` (realalg)
- `ge_cauchy_bound : p != 0 -> {in [cauchy_bound p, +oo[, forall x, ~~ root p x}` (polyrcf)
- `root_cauchy_boundP` (polyrcf)
- `changes_horner, changes_pinfty` (qe_rcf_th)

**Estimated lines**: 50-70
**Risk**: Medium. Depends on #5 and #6 being closed. The Sturm theorem wiring itself is well-supported by MathComp-real-closed.
**External library**: None -- MathComp-real-closed has everything needed.

---

### Admit #5: `prs_chain_variation_diff_eq` (CertL1.v)

**Statement**:
```coq
(changes_horner lc a - changes_pinfty lc)
= (changes_horner mc a - changes_pinfty mc)
```
where `lc = map pol_to_polyralg WitnessChain.sturm_chain` (shipped PRS chain) and `mc = mods P P'` (abstract Euclidean chain).

**This is the hardest remaining admit.**

**Mathematical content**: Two PRS chains for the same polynomial pair have the same sign-variation difference V(a) - V(+inf). The shipped chain and the mods chain differ entry-by-entry by nonzero (but possibly negative) scalar factors. Individual `changes` values can differ when scalars are negative, but the DIFFERENCE is invariant.

**Proof strategy** (two viable routes):

**Route A (direct induction on mods)**: ~200 lines
```
1. By induction on the mods recursion, show that each shipped chain
   entry q_i is a nonzero scalar multiple alpha_i of the corresponding
   mods chain entry m_i:
     pol_to_polyralg (shipped_chain[i]) = alpha_i *: mods_chain[i]
   This uses Bridge.next_mod_scaled_morph (Qed) at each step,
   composed with CRTCheck verification of the shipped chain's PRS
   recurrence.

2. Show that changes_horner and changes_pinfty on scaled chains
   satisfy:
     changes(alpha_i * p_i, alpha_{i+1} * p_{i+1})
     = changes(sgn(alpha_i) * p_i, sgn(alpha_{i+1}) * p_{i+1})
   since scaling by a nonzero constant preserves or flips sign.

3. When consecutive scalars have the same sign: changes is preserved.
   When consecutive scalars have opposite signs: changes flips
   (0 <-> 1), but this happens at BOTH a and +inf, so the
   DIFFERENCE is preserved.

4. Formally: define parity(i) = sgn(alpha_i). Show:
   changes(parity * chain1, a) - changes(parity * chain1, inf)
   = changes(chain2, a) - changes(chain2, inf)
   by a telescoping argument on the parity flips.
```

**Route B (via cindexR/crossR)**: ~250 lines
```
1. Use changes_mods_cindex: changes_mods p q = cindexR q p.
2. Show cindexR is invariant under scaling of the PRS chain entries.
3. Apply changes_mods_rec to decompose both chains.
```

**Key MathComp lemmas**:
- `changes : seq R -> nat` (qe_rcf_th) -- sign variation count
- `changes_horner : seq {poly R} -> R -> nat` (qe_rcf_th)
- `changes_pinfty : seq {poly R} -> nat` (qe_rcf_th)
- `neq0_mods_rec : p != 0 -> mods p q = p :: mods q (next_mod p q)` (qe_rcf_th)
- `changes_mods_rec : changes_mods p q = crossR(p*q) + changes_mods q (next_mod p q)` (qe_rcf_th)
- `next_mod : {poly R} -> {poly R} -> {poly R}` (qe_rcf_th)

**Estimated lines**: 200-250
**Risk**: Hard. This is the most mathematically non-trivial admit. The scalar-factor sign-tracking argument requires careful bookkeeping. No existing MathComp lemma directly gives "changes_horner is invariant under entrywise nonzero scaling (in the difference sense)."
**External library**: math-comp/cad might have relevant PRS chain theory, but inspection suggests it focuses on CAD, not PRS chain equivalence.

---

### Admit #6: `cauchy_bound_le_of_chain` (CertL1.v)

**Statement**:
```coq
forall q, In q WitnessChain.sturm_chain ->
  cauchy_bound (pol_to_polyralg q) <= cauchy_bound (pol_to_polyralg charpoly_int)
```

**Current state**: `CauchyCheck.all_chain_cb_le` (Qed via vm_compute) verifies the inequality at the BigZ level. The bridge to realalg is pending.

**Cauchy bound definition** (from polyrcf):
```
cauchy_bound p = 1 + |lead_coef p|^{-1} * sum_i |p`_i|
```

**Proof outline**:
```
1. Define a BigZ-to-realalg bridge for the Cauchy bound:
   cb_bigZ(p) = sum_abs(p) / |lc(p)|  (BigZ level)
   cauchy_bound(lift p) = 1 + |lead_coef(lift p)|^{-1} * sum |coef_i|

2. Show cb_bigZ and cauchy_bound agree after lifting:
   cauchy_bound(pol_to_polyralg p) = 1 + (lift of cb_bigZ numerator/denom)
   This requires showing:
   a) lead_coef(pol_to_polyralg p) = ratr(Z_to_int(plead p))
   b) sum_i |coef_i| lifts correctly
   c) The BigZ comparison cb_le q p implies the realalg comparison.

3. The key bridge:
   BigZ.leb (sum_abs q * |lc p|) (sum_abs p * |lc q|)
   implies
   sum_abs_ralg(q) / |lc_ralg(q)| <= sum_abs_ralg(p) / |lc_ralg(p)|
   which gives cauchy_bound(q) <= cauchy_bound(p).

4. The BigZ comparison is verified by all_chain_cb_le (vm_compute).
```

**Key MathComp lemmas**:
- `cauchy_bound = fun p => 1 + |lead_coef p|^{-1} * \sum_(i < size p) |p`_i|` (polyrcf)
- `ler_wpM2l : 0 <= c -> a <= b -> c * a <= c * b` (ssrnum)
- `normr_ge0, invr_ge0` (ssrnum)
- `coef_map_id0 : (map_poly f p)`_i = f (p`_i)` (poly)

**Estimated lines**: 80-120
**Risk**: Medium. The BigZ-to-realalg bridge is tedious but conceptually clear. The main work is showing the coefficient-level operations (sum of absolute values, leading coefficient) agree between BigZ and realalg representations.
**External library**: None needed.

---

### Admit #7: `det_int_laplace_eq_det_int` (IntMatProof.v)

**Statement**:
```coq
mat_dim M = n ->
Forall (fun row => length row = n) M ->
bareiss_no_swap (mat_dim M) 1 M ->
det_int_laplace M = det_int M
```

**Current state**: Base cases n=0 and n=1 are Qed. The n >= 2 case requires the Bareiss fraction-free elimination identity.

**Proof outline**:
```
1. The Bareiss algorithm maintains the invariant:
   After processing column j with pivot p_{j-1}, the (i,k)-entry of
   the remaining submatrix equals det(M[{0..j,i}, {0..j,k}]) / p_{j-1}.
   (Sylvester-Bareiss identity.)

2. At step j, the Bareiss loop eliminates row 0 and produces:
   bareiss_step prev row rest
   where each entry of the result is (row[0]*rest[i][k] - rest[i][0]*row[k]) / prev.

3. Under bareiss_no_swap (all pivots nonzero), the final single entry
   equals det(M) (up to division by the accumulated pivot product).

4. Meanwhile, det_int_laplace expands along the first row at each step,
   producing the same Laplace expansion that the Bareiss loop computes
   (they agree on the cofactors because the Bareiss step is equivalent
   to Gaussian elimination on the minor).

5. Prove by strong induction on n, using the Sylvester-Bareiss identity
   to relate bareiss_step output to minors.
```

**Key MathComp lemmas**: None directly (this is a list-level proof about our custom `det_int` and `det_int_laplace`).

**Key Stdlib lemmas**:
- `Z.div_mul`, `Z.mul_comm`, `Z.mul_assoc` (ZArith)

**Estimated lines**: 250-350
**Risk**: Hard. The Bareiss correctness proof is a classic but non-trivial formalization. The `bareiss_no_swap` condition simplifies things (no permutation tracking), but the fraction-free division identity still requires careful induction.
**External library**: CoqEAL (https://github.com/rocq-community/coqeal) has a formalized Bareiss algorithm with correctness proof (`bareiss.v` in the theory directory). If compatible with Rocq 9.0.1 / MathComp 2.5.0, this could be reused directly or adapted. However, CoqEAL works with MathComp matrices, not list-of-lists, so a refinement bridge would be needed.

---

### Admit #8: `det_rat_nonzero_M1` (UnitmxCheck.v)

**Statement**:
```coq
forallb (fun p => check_det_nonzero p M1_int) crt_primes_local = true ->
\det (mat_int_to_rat M1_int 1 42) != 0
```

**Proof outline**:
```
1. From the hypothesis: for each of 10 CRT primes p_i,
   det_mod p_i M1_int != 0 (i.e., det(M1_int) != 0 mod p_i).

2. det_mod uses char_poly_mod to compute the constant term of
   char_poly(M1_int) mod p_i. The constant term of char_poly is
   (-1)^n * det(M1_int). So det(M1_int) != 0 mod p_i.

3. By CRT: if det(M1_int) != 0 mod p_i for all i, and the product
   of the p_i exceeds 2 * |det(M1_int)|, then det(M1_int) != 0 over Z.

4. The product of the 10 primes is > 2^300. By Hadamard's bound,
   |det(M1_int)| <= prod_i ||row_i|| <= (42 * max_entry^2)^{21},
   which is far below 2^300 for the concrete M1_int entries.

5. Alternatively, skip the Hadamard bound and use a direct BigZ
   computation: compute det(M1_int) via BigZ Bareiss, check != 0.
   This is simpler but slower (the 42x42 BigZ determinant might be
   expensive but feasible with vm_compute).

6. Lift Z-nonzero to rat-nonzero:
   Z_to_int(det_int M1_int) != 0 (as int)
   => (Z_to_int(det_int M1_int))%:~R != 0 (as rat)  [by intr_eq0]
   Then use det_int_correct (from IntMatProof.v, Qed modulo #7):
   (Z_to_int(det_int M1_int))%:~R = \det(mat_int_to_rat M1_int 1 42)
```

**Alternative (self-contained) route**: Bypass det_int entirely.
```
1. Compute det(M1_int) mod each prime via char_poly_mod (already done).
2. Use a formal CRT reconstruction to get det(M1_int) mod (prod primes).
3. Show det(M1_int) mod (prod primes) != 0.
4. Since |det(M1_int)| < prod_primes / 2, det(M1_int) != 0 over Z.
5. Bridge to rat via Z_to_int and intr_eq0.
```

**Key MathComp lemmas**:
- `intr_eq0 : (n%:~R == 0 :> F) = (n == 0)` for char-0 fields
- `det_int_correct` (IntMatProof.v, Qed modulo #7)

**Estimated lines**: 100-150
**Risk**: Medium. The CRT integer lifting is conceptually simple but requires formal Hadamard bound or direct BigZ computation. The `bareiss_no_swap` condition for `det_int_laplace_eq_det_int` must be verified for M1_int (it holds because M1_int is SPD, so all leading principal minors are positive).
**External library**: Bignums (already imported for BigZ).

---

### Admit #9: `det_rat_nonzero_M2` (UnitmxCheck.v)

Identical structure to #8, for M2_int instead of M1_int.

**Statement, outline, lemmas, risk**: Same as #8.
**Estimated lines**: Same as #8 (100-150), or factored into a shared lemma ~20 additional lines.

---

## 3. External Library Survey

### MathComp ecosystem repositories scanned

| Repository | Relevant content | Useful for admits |
|---|---|---|
| **math-comp/real-closed** | `mods`, `changes_horner`, `changes_pinfty`, `taq_taq_itv`, `cauchy_bound`, `rootsR`, `next_mod` -- full Sturm theorem infrastructure | #4, #5, #6 |
| **math-comp/math-comp** (core) | `char_poly`, `map_char_poly`, `expand_det_row`, `Cayley_Hamilton`, `mul_mx_adj`, `cofactor`, `det_mx00/11`, `polyP`, `coef_Poly` | #1, #2, #7 |
| **math-comp/analysis** | Normed spaces, measure theory. NOT directly relevant. | -- |
| **math-comp/cad** | Cylindrical Algebraic Decomposition. May have PRS chain theory. | Possibly #5 |
| **math-comp/Abel** | Galois theory, Abel-Ruffini. NOT relevant. | -- |
| **math-comp/multinomials** | Multivariate polynomials. NOT relevant. | -- |
| **math-comp/Coq-Combi** | Combinatorics. NOT relevant. | -- |
| **rocq-community/coqeal** | Bareiss algorithm formalization, refinement framework (MathComp matrices <-> list-of-lists). `bareiss.v` has formal correctness. | #7, #8, #9 |
| **Bignums** | BigZ, BigN. Already used for CauchyCheck. | #6, #8, #9 |
| **Stdlib ZArith** | `Z.rem`, `Z.div`, `Z.rem_divide`, `Z.rem_mul`. | #3 |

### Key findings

1. **MathComp-real-closed has everything for L1** (#4, #5, #6). The `qe_rcf_th.v` file provides `mods`, `changes_horner`, `changes_pinfty`, `taq_taq_itv`, and the full Sturm theorem. No external library is needed for the Sturm wiring.

2. **No existing formalization of "PRS chain variation invariance"** was found. The `changes` function in `qe_rcf_th.v` does not come with a lemma saying "scaling entries by nonzero constants preserves the variation difference." This must be proved from scratch for #5.

3. **CoqEAL's Bareiss** could shortcut #7 if the library is compatible. The refinement framework bridges MathComp matrices to list-of-lists, which is exactly our setup. However, the `bareiss_no_swap` condition is project-specific and may not match CoqEAL's formulation.

4. **No Newton's identities or Faddeev-LeVerrier lemma** exists in any MathComp library. The project's `fl_loop_rat_is_char_poly_L2` (already Qed) fills this gap via the `mul_mx_adj` / adjugate coefficient approach.

---

## 4. Effort Summary

| # | Admit | File | Lines | Risk | Blocks | On critical path? |
|---|-------|------|-------|------|--------|-------------------|
| 3 | `Z_rem_of_intr_eq` | CharPolyL2.v | ~25 | Easy | #2 | Yes (L2) |
| 2 | `char_poly_int_correct` | CharPoly.v | ~80 | Easy-Med | #1 | Yes (L2) |
| 1 | `charpoly_int_eq_charpoly` | Cert.v | ~70 | Medium | headline | Yes (L2) |
| 6 | `cauchy_bound_le_of_chain` | CertL1.v | ~100 | Medium | #4 | Yes (L1) |
| 5 | `prs_chain_variation_diff_eq` | CertL1.v | ~220 | Hard | #4 | Yes (L1) |
| 4 | `prs_chain_sturm_correct` | CertL1.v | ~60 | Medium | headline | Yes (L1) |
| 8 | `det_rat_nonzero_M1` | UnitmxCheck.v | ~120 | Medium | headline | Yes (clean) |
| 9 | `det_rat_nonzero_M2` | UnitmxCheck.v | ~120 | Medium | headline | Yes (clean) |
| 7 | `det_int_laplace_eq_det_int` | IntMatProof.v | ~300 | Hard | #8, #9 | Indirect |

**Total estimated new proof lines**: ~1100

### Recommended execution order (parallelizable)

**Phase 1** (can be done in parallel, unblocks everything):
- Close **#3** (Z_rem_of_intr_eq) -- 1 day, 1 person
- Start **#5** (prs_chain_variation_diff_eq) -- 3-5 days, 1 person

**Phase 2** (after #3):
- Close **#2** (char_poly_int_correct) -- 1-2 days
- Close **#6** (cauchy_bound_le_of_chain) -- 2 days (parallel with #2)

**Phase 3** (after #2):
- Close **#1** (charpoly_int_eq_charpoly) -- 1-2 days

**Phase 4** (after #5 + #6):
- Close **#4** (prs_chain_sturm_correct) -- 1 day

**Phase 5** (independent, for clean assumptions):
- Close **#7** (det_int_laplace_eq_det_int) or adopt CoqEAL route -- 3-5 days
- Close **#8, #9** (det_rat_nonzero_M1/M2) -- 2 days after #7

**Fastest path to headline with 0 admits**: Phases 1-4 = ~7-10 days with 2 people working in parallel on L1 and L2 tracks. Phase 5 adds ~5 more days for the determinant chain.
