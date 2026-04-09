# Reconstruction of `Computations.nb` (Maynard, *Small gaps between primes*, arXiv:1311.4600v3)

Source file: `/tmp/Computations.nb` (a Mathematica 8 notebook). The `.nb` file
is a plain-text expression tree wrapping the actual input inside
`Cell[BoxData[ RowBox[{ ... }] ]`. This document is the result of flattening
that tree back into pure Mathematica source, plus a mathematical explanation
of every function.

The notebook computes a lower bound on the generalized-eigenvalue ratio
`M_k = sup_f k * J_k(f) / I_k(f)`
where `I_k(f) = \int_{R_k} f(t_1,...,t_k)^2 dt` and
`J_k(f) = \int_{R_{k-1}} ( \int_0^{1-sum t_i} f dt_1 )^2 dt_2...dt_k`,
with `R_k = { t in [0,1]^k : sum t_i < 1 }` the standard unit simplex, and
`f` restricted to symmetric functions of the form
`f(t) = F(1 - sum t_i, sum t_i^2)`
where `F(x,y)` is a polynomial of bidegree `deg_x F + 2 deg_y F <= d`.

For the main paper this gives Proposition 4.3: `M_{105} > 4`, from which
Maynard deduces the existence of bounded gaps with `H = 600`.

--------------------------------------------------------------------------
## 1. Reconstructed Mathematica source (verbatim, flattened)

```mathematica
Clear[A,k,x,y,Bnd,Cff,Poly,Polys,PrmeCalc,ConstCalc]

(* Bnd: Given a list of symbolic variables {a_1,...,a_m} and an integer tot,
   return the Mathematica iterator ranges {a_i, 1, upper_i} that enumerate
   all integer tuples with each a_i >= 1 and sum(a_i) <= tot-1. *)
Bnd[lst_, tot_] := Module[{i1, i2, i3, i4, i5},
  Table[
    {lst[[i1]], 1,
     tot - 1 - Sum[lst[[i2]], {i2, 1, i1 - 1}] - (Length[lst] - i1)},
    {i1, 1, Length[lst]}]
  ];

(* Cff: Given a tuple lst={a_1,...,a_m} and an integer tot,
   return  (prod_{i=1}^m (2 a_i)! / a_i!)  *  tot!  *  (2 a_{m+1})! / a_{m+1}!
   where a_{m+1} = tot - sum a_i.  This is the summand in the formula for
   G_{tot,2}(k) below. *)
Cff[lst_, tot_] := Module[{i1, i2, i3},
   Product[Factorial[2*lst[[i1]]]/Factorial[lst[[i1]]],
           {i1, 1, Length[lst]}]
 * Factorial[tot]
 * Factorial[2*tot - 2*Sum[lst[[i2]], {i2, 1, Length[lst]}]]
 / Factorial[tot - Sum[lst[[i3]], {i3, 1, Length[lst]}]]
  ];

(* Poly: Returns the polynomial
     G_{n,2}(k)  :=  \int_{R_k} ( sum t_i^2 )^n  *  k!/(k + 2n)!  * (something)
   expanded as a polynomial in the symbolic variable k.
   Built via the binomial / partition expansion:
     G_{n,2}(k)  =  k*(2n)!    [i=1 term, one variable]
                  + sum_{i=2}^{n-1} C(k,i+1) * sum_{Bnd(a_1..a_i,n)} Cff(...,n)
*)
Poly[n_, k_] := Module[
  {A = {a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,
        a17,a18,a19,a20,a21,a22,a23,a24,a25,a26,a27,a28,a29,a30,
        a31,a32,a33,a34,a35,a36,a37,a38,a39,a40},
   X = k*Factorial[2*n], i, Lst},
  If[n == 0,
     X = 1,
     For[i = 1, i <= n - 1, i++,
         Lst = Take[A, i];
         X = X + Binomial[k, i + 1]
               * Apply[Sum, Join[{Cff[Lst, n]}, Bnd[Lst, n]]];
        ];
     Expand[X]
    ]
  ];

(* Precompute the polynomials G_{0,2},...,G_{11,2} as an indexed list. *)
Polys[k_] = Table[Poly[n, k], {n, 0, 11}];

(* ConstCalc: Given a polynomial Expr in two formal variables x, y and an
   integer k, square Expr, decompose into monomials x^b y^c, and integrate
   monomial by monomial using the closed-form Lemma 7.1 of the paper.
   The convention is  x := 1 - sum_{i=1}^k t_i    y := sum_{i=1}^k t_i^2.
   The integral \int_{R_k} x^b y^c dt is a rational number equal to
       (b! / (k+b+2c)!)  *  G_{c,2}(k)
   and ConstCalc returns the sum of these contributions. *)
ConstCalc[Expr_, k_] := Module[
  {Sum = 0, IntExpr = Expand[Expr^2], xdeg, ydeg, b, c, tmp, Coeff},
  xdeg = Exponent[IntExpr, x];
  For[b = 0, b <= xdeg, b++,
    tmp  = Coefficient[IntExpr, x, b];
    ydeg = Exponent[tmp, y];
    For[c = 0, c <= ydeg, c++,
      Coeff = Coefficient[tmp, y, c];
      Sum = Sum + Coeff * Factorial[b] / Factorial[k + b + 2*c]
                        * Polys[k][[c + 1]];
    ];
  ];
  Sum
];

(* PrmeCalc: Computes J_k.  Given f(t_1,...,t_k) = F(1 - sum t_i, sum t_i^2),
   first integrates over t_1 to obtain
       g(t_2,...,t_k) = \int_0^{1 - sum_{i>=2} t_i} F(1-sum, sum sq) dt_1,
   using the closed form (equation 7.8 of the paper):
       \int_0^{1-sum'} (1-sum' - t_1)^b ((sum')^{2} + t_1^2)^c dt_1
           = sum_{cp=0..c} C(c,cp) b!(2c-2cp)!/(b+2c-2cp+1)!
                           (1-sum')^{b+2c-2cp+1} (sum')^{2 cp}
   written in terms of new formal variables x' := 1-sum_{i>=2} t_i,
   y' := sum_{i>=2} t_i^2.  Then passes the result to ConstCalc with k-1. *)
PrmeCalc[Expr_, k_] := Module[
  {NewExpr = 0, FirstExpr = Expand[Expr], n1, n2, b, c, cp, tmp, Coeff},
  n1 = Exponent[Expr, x];
  For[b = 0, b <= n1, b++,
    tmp = Coefficient[FirstExpr, x, b];
    n2  = Exponent[tmp, y];
    For[c = 0, c <= n2, c++,
      Coeff = Coefficient[tmp, y, c];
      NewExpr = NewExpr + Coeff *
        Sum[x^(b + 2 c - 2 cp + 1) * y^(cp)
            * Binomial[c, cp] * Factorial[b] * Factorial[2 c - 2 cp]
            / Factorial[b + 2 c - 2 cp + 1],
            {cp, 0, c}];
    ];
  ];
  ConstCalc[NewExpr, k - 1]
];

(* yExponents, xExponents, p: build the generic polynomial
     F(x, y) = sum_i  A_i  *  x^{X[i]} * y^{Y[i]}
   whose monomials are all (b, c) with 0 <= b, 0 <= c, b + 2 c <= 2 n + 1.
   Enumerated in a specific order so that A_i are the unknown coefficients. *)
yExponents[n_] := Module[{S = {}, i, tmp},
  For[i = 0, i <= n, i++,
    tmp = Append[Reverse[Range[i]], 0];
    S = Join[S, tmp, tmp];
  ];
  S];
xExponents[n_] := Module[{S = {}, i, tmp},
  For[i = 1, i <= n + 1, i++,
    tmp = 2*Range[i];
    S = Join[S, tmp - 2, tmp - 1];
  ];
  S];
p[n_] := Module[{X = xExponents[n], Y = yExponents[n], i, A},
  A = Table[ToExpression["A" <> ToString[i]], {i, Length[X]}];
  Return[Sum[A[[i]] * x^X[[i]] * y^Y[[i]], {i, Length[X]}]]
];

(* --------- ACTUAL COMPUTATION FOR k = 105, d = 2 n + 1 = 11 ---------- *)
k    = 105;
poly = p[5];                                (* 42 monomials, b + 2c <= 11 *)
vars = DeleteCases[DeleteCases[Variables[poly], x], y];  (* {A1,...,A42} *)

(* Build the 42x42 symmetric rational Gram matrices.
   M1 is the Gram matrix of < , >_I  where <f,g>_I = \int_{R_k} f g dt,
   M2 is the Gram matrix of < , >_J  where
      <f,g>_J = \int_{R_{k-1}} (\int_0^{1-sum'} f dt_1)(\int_0^{1-sum'} g dt_1) dt'.
   CoefficientArrays[...,Symmetric->True][[3]] extracts the degree-2 part of
   the quadratic form in the A_i as a symmetric matrix. *)
M1 = CoefficientArrays[ConstCalc[poly, k], vars, Symmetric -> True][[3]];
M2 = CoefficientArrays[PrmeCalc[poly, k], vars, Symmetric -> True][[3]];

M3 = Inverse[M1] . M2;

(* Numerically compute the top eigenvector of M1^{-1} M2 at 150 decimal digits,
   then snap each component to a close rational (tol 10^{-40}).  This is a
   certificate-style trick: the eigenvalue itself is then recomputed exactly
   as the Rayleigh quotient  k * v^T M2 v / v^T M1 v  using only rational
   arithmetic, so the final printed number is a true *lower bound* for M_k. *)
RatVec = Rationalize[Eigenvectors[N[M3, 150], 1][[1]], 10^(-40)];
Ratio  = k * (RatVec . M2 . RatVec) / (RatVec . M1 . RatVec);
N[Ratio, 20]
```

Output cell (the only printed result):

```
4.00206976193804713686805879340335542151`20.
```

--------------------------------------------------------------------------
## 2. Mathematical meaning of each routine

| Routine | Input | Output | Maths |
|---|---|---|---|
| `Bnd[lst,tot]` | symbolic vars, int `tot` | list of Mathematica iterator ranges | Enumerates tuples `(a_1,...,a_m)` with `a_i>=1`, `sum a_i <= tot-1` |
| `Cff[lst,tot]` | tuple, `tot` | rational number | The Dirichlet-weight summand `tot! * prod (2a_i)!/a_i! * (2 a_{m+1})!/a_{m+1}!` with `a_{m+1}=tot-sum a_i`. |
| `Poly[n,k]` | int `n`, symbol `k` | polynomial in `k` | Builds `G_{n,2}(k)`, the polynomial in `k` equal to `(k+2n)!/k! * \int_{R_k} (sum t_i^2)^n dt`. Expanded as `sum_i C(k,i+1) * (partition sum)`. |
| `Polys[k]` | symbol `k` | length-12 list | Caches `G_{0,2}..G_{11,2}` as polynomials in `k`. |
| `ConstCalc[F,k]` | polynomial `F(x,y)`, int `k` | rational number (or polynomial in the `A_i`) | `\int_{R_k} F^2 dt`, computed by the monomial closed form `(b!/(k+b+2c)!) * G_{c,2}(k)`. This is the `I_k` integral. |
| `PrmeCalc[F,k]` | polynomial `F(x,y)`, int `k` | rational / polynomial in `A_i` | `\int_{R_{k-1}} (\int_0^{1-sum'} F dt_1)^2 dt'`. First uses eq. 7.8 to integrate `t_1` analytically (produces a new polynomial in `x',y'`), then calls `ConstCalc` at level `k-1`. This is the `J_k` integral. |
| `xExponents, yExponents, p[n]` | int `n` | symbolic polynomial with undetermined `A_i` | Creates the generic ansatz `F(x,y) = sum A_i x^{b_i} y^{c_i}` over the index set `{ (b,c) : b+2c <= 2n+1 }`. |

The identity underlying `Poly` is the classical
`\int_{R_k} (sum t_i^2)^n dt = (something)/(k+2n)!`
obtained by expanding the `n`-th power by the multinomial theorem and
integrating each monomial over the simplex with the Dirichlet formula
`\int_{R_k} prod t_i^{a_i} dt = prod a_i! / (k + sum a_i)!`.

--------------------------------------------------------------------------
## 3. Dimensions actually used for the λ > 4 claim

* `n = 5` (passed as `p[5]`)
* Polynomial degree cutoff `d = 2 n + 1 = 11` (i.e. all `x^b y^c` with `b + 2 c <= 11`)
* Number of monomials = **42** (enumerated once; no duplicates)
* Matrix sizes: `M1`, `M2`, `M3` are all **42 × 42**
* Simplex parameter: `k = 105`
* Precomputed polynomial table: `Polys[k]` has 12 entries, `G_{0,2}` through `G_{11,2}`

(The 40-element symbol vector `{a1,...,a40}` inside `Poly` is just scratch
storage for the partition enumeration; it is unrelated to the matrix size.)

--------------------------------------------------------------------------
## 4. Final reported number

The single output cell of the notebook reads:

```
4.00206976193804713686805879340335542151`20.
```

i.e. `λ ≈ 4.00206976193804713686805879340335542151`. This is displayed via
`N[Ratio, 20]`, so 20 significant digits are requested (Mathematica often
prints a few extra). The underlying rational `Ratio` is exact.

Since `λ > 4`, and 4 is the threshold in Maynard's Proposition 4.3, this
certifies `M_{105} > 4` and hence the bounded-gap conclusion.

--------------------------------------------------------------------------
## 5. Exact-vs-floating-point audit

This is the subtlest part of the notebook and is the key to making it
reproducible in Rocq / FLINT.

**Matrix assembly: fully exact.**
`Bnd`, `Cff`, `Poly`, `Polys`, `ConstCalc`, `PrmeCalc` use only `Factorial`,
`Binomial`, `Sum`, `Expand`, `Coefficient` on integer/rational inputs. No `N[]`
is introduced. The polynomials `G_{n,2}(k)` are exact polynomials in `k` with
integer coefficients; at `k = 105` they evaluate to exact integers / exact
rationals. Therefore `M1` and `M2` are **exact rational 42×42 matrices**, and
every entry is of the form `P(k)/(k + b + 2c)!` for explicit integer `P`.

**Eigenproblem: floating point, but only as a heuristic.**
The line
```
RatVec = Rationalize[Eigenvectors[N[M3, 150], 1][[1]], 10^(-40)];
```
does three things:
1. `N[M3, 150]`: coerce `M3 = Inverse[M1].M2` to arbitrary-precision floats
   with 150 decimal digits of precision.
2. `Eigenvectors[..., 1]`: numerically compute the top eigenvector of this
   (non-symmetric, but similar to a symmetric positive operator) matrix at
   150-digit precision.
3. `Rationalize[..., 10^{-40}]`: round each component to a rational with
   denominator small enough that the error is below `10^{-40}`.

This step is **not trusted**. Its only purpose is to produce a good rational
test vector `v ∈ Q^{42}`.

**Rayleigh quotient: fully exact.**
```
Ratio = k * (RatVec . M2 . RatVec) / (RatVec . M1 . RatVec)
```
Both numerator and denominator are computed as exact rationals from the exact
matrices `M1, M2` and the exact rational vector `RatVec`, so `Ratio` is an
exact rational number in `Q`. The quantity `k * v^T M2 v / v^T M1 v` is by
construction a **lower bound** for the top generalized eigenvalue of the
pencil `(M2, M1)` (Rayleigh–Ritz), regardless of how `v` was obtained.
Hence the certificate is valid even though Mathematica's numerical
eigenvector routine is a black box.

Only the very last line `N[Ratio, 20]` uses floating-point, and only for
*display*; the underlying exact rational can be printed with larger precision
and the inequality `Ratio > 4` can be decided by exact integer comparison
`num(Ratio - 4) > 0`.

**Implications for the re-implementation:**

* In Rocq (using `bignums` / interval arithmetic), the entire assembly of
  `M1, M2` can be done in `Q`. The test vector `v` can be hard-coded as a
  rational vector (exported from Mathematica or recomputed via a certified
  power iteration). The final inequality `k * v^T M2 v > 4 * v^T M1 v` is a
  single comparison of integers (after clearing denominators).
* In C / Python with FLINT, use `fmpq_mat` for `M1`, `M2`, compute the
  numerator and denominator of `v^T M_i v` with `fmpq_mat_mul`, and compare.
  No floating-point needed anywhere on the verification path. The only place
  where an eigensolver is useful is in *finding* the vector `v`; that can be
  done with Arb (`arb_mat_approx_eig_qr`) at 150+ digits, then snapped to
  rationals.

--------------------------------------------------------------------------
## 6. Suggested reference points in the paper

* Lemma 7.1 — the `\int_{R_k} x^b y^c dt` closed form used inside `ConstCalc`.
* Equation 7.8 — the 1D anti-derivative used inside `PrmeCalc`.
* §8, Proposition 4.3 — the `M_{105} > 4` claim.
* `G_{n,2}(k)` is defined around Lemma 7.1; the recursion `Poly[n,k]`
  reproduces it term by term.

--------------------------------------------------------------------------
## 7. Files produced / used

* Input : `/tmp/Computations.nb`
* Flatten script: `/tmp/flatten_nb.py`
* Flattened source (raw, with `\[IndentingNewLine]` etc): `/tmp/flattened.txt`
* Flattened source (cleaned): `/tmp/flattened_clean.txt`
* This document: `/home/rocq/prime_gap/notebook_reconstructed.md`
