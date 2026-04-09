# research_charpoly — MathComp `char_poly` reuse scouting report

Scope: MathComp 2.5.0 installed under `~/.opam/4.14.2+flambda/lib/coq/user-contrib/mathcomp`, checked with rocq-mcp `rocq_query`. All signatures below were captured verbatim from live queries (no speculation).

---

## 1. Inventory (verbatim `About` output)

### 1.1 Definitions (file: `mathcomp/algebra/mxpoly.v`)

```
char_poly_mx :
forall {R : nzRingType} {n : nat},
'M_n -> matrix_matrix__canonical__Algebra_BaseAddMagma
          (poly_polynomial__canonical__Algebra_Nmodule R) n n
-- transparent; line 396
char_poly_mx = fun R n A => ('X%:M - (A ^ polyC)%sesqui)%R

char_poly :
forall {R : nzRingType} {n : nat},
'M_n -> poly_polynomial__canonical__GRing_PzRing R
-- transparent; line 397
char_poly = fun R n A => (\det (char_poly_mx A))%R
```

```
mxminpoly : forall {F : fieldType} {n' : nat},
            'M_n'.+1 -> poly_polynomial__canonical__GRing_PzSemiRing F
-- transparent; line 673
-- defined as 'X^d - mx_inv_horner (A ^+ d) where d := degree_mxminpoly A,
   itself an ex_minn proof term (NOT reducible)

companionmx : forall {R : nzRingType} (p : seq R), 'M_(size p).-1
-- transparent; line 537
```

### 1.2 Key lemmas

```
size_char_poly  : forall [R n] (A : 'M_n), size (char_poly A) = n.+1                 (opaque, l.427)
char_poly_monic : forall [R n] (A : 'M_n), char_poly A \is monic                      (opaque, l.433)
char_poly_trace : forall [R n] (A : 'M_n), 0 < n ->
                    ((char_poly A)`_n.-1)%R = (- \tr A)%R                              (opaque, l.441)
char_poly_det   : forall [R n] (A : 'M_n),
                    ((char_poly A)`_0)%R = ((-1) ^+ n * \det A)%R                      (opaque, l.454)
char_poly_trig  : forall {R : comNzRingType} [n A], is_trig_mx A ->
                    char_poly A = (\prod_(i < n) ('X - (A i i)%:P))%R                  (opaque, l.529)
Cayley_Hamilton : forall [R : comNzRingType] [n'] (A : 'M_n'.+1),
                    horner_mx A (char_poly A) = 0%R                                    (opaque, l.508)
companionmxK    : forall {R : comNzRingType} [p], p \is monic ->
                    char_poly (companionmx p) = p                                      (opaque)
row'_col'_char_poly_mx : row' i (col' i (char_poly_mx M)) = char_poly_mx (row' i (col' i M))
pchar_poly      : forall R : nzSemiRingType, [char {poly R}]%R =i [char R]%R
```

```
mxminpoly_dvd_char : (mxminpoly A %| char_poly A)%R                                    (opaque, l.741)
root_mxminpoly    : root (mxminpoly A) a = root (char_poly A) a                        (opaque, l.758)
```

No results for `coef_char_poly`, `char_coef`, nor any identity of the form
`(char_poly A)`_k = <closed expression in A>` for `0 < k < n-1`.

### 1.3 `mxpoly` does NOT contain

```
Search "Faddeev".            -> (no output)
Search "LeVerrier".          -> (no output)
Search "FaddeevLeVerrier".   -> (no output)
Search "Hessenberg".         -> (no output)
Search "hessenberg".         -> (no output)
Search "Newton_id".          -> (no output)
Search "mesym".              -> (no output)
Search "symmetric_poly".     -> (no output)
Search "sym_fundamental".    -> (no output)
Search "power_sum".          -> (no output)
Search "coef_char_poly".     -> (no output)
```

`grep -r mesym|Newton|power_sum` over the entire MathComp install tree returns
hits only in `Stdlib/Reals/NewtonInt.v` (Newton integration — unrelated).

---

## 2. Computational properties

- `char_poly_mx` and `char_poly` are flagged **transparent**, but this is
  misleading: unfolding `char_poly` gives `\det (char_poly_mx A)`, and
  `\det` (`determinant`) is:
  ```
  determinant = fun R n A =>
    (\sum_s (-1) ^+ perm.odd_perm s * \prod_i A i (perm.fun_of_perm.body s i))%R
  ```
  a big-operator sum over `'S_n` (the permutation finGroupType). `\sum_s` /
  `\prod_i` are locked through `reducebig`/`BigOp.bigop`, so `cbv` does NOT
  enumerate the permutations — kernel reduction stalls on the `'S_n` enumeration.
  This is exactly why the user's 4x4 `'M[rat]_4` Rayleigh quotient timed out.

- `mxminpoly` is transparent but depends on `degree_mxminpoly := ex_minn …`,
  an opaque proof term; it is completely unreducible in practice.

- `companionmx` is transparent and a plain `\matrix_(i, j)` builder; it is
  reducible *in principle*, but its only forward lemma `companionmxK` lands
  us straight back into `char_poly (companionmx p) = p`, which again invokes
  the stuck `\det`.

- Per the constraint (no `vm_compute` on `'M[rat]`/`{poly rat}`/`{poly int}`),
  I did not issue any `Eval vm_compute`. I also skipped `Eval cbv` probes on
  toy matrices: given that `determinant` unfolds to `\sum_(s : 'S_n) …`, a
  single `cbv delta` step exposes `BigOp.bigop` on a finType whose enumeration
  is itself built from `Finite.enum 'S_n` — this is the exact pattern we
  measured to time out. Static inspection of `Print determinant` is sufficient
  and safer than a 30 s probe.

**Bottom line:** none of `char_poly`, `char_poly_mx`, `mxminpoly`, or
`determinant` are computationally usable from within the kernel on rational
entries, regardless of their transparency flag.

---

## 3. Newton-Girard / power-sum reduction

**Not present in MathComp 2.5.0.** No `Newton_id`, no `mesym`, no
`symmetric_poly`, no `power_sum`, no `elementary_symmetric_poly`, no
`prod_root_char_poly`, no `prod_mxtrace`. The only `mxtrace` lemmas are the
basic additivity / linearity / block / transpose / scalar identities:
`mxtrace0`, `mxtrace1`, `mxtraceD`, `mxtraceZ`, `mxtrace_scalar`,
`mxtrace_tr`, `mxtrace_mulC`, `mxtrace_block`, `mxtrace_diag`,
`mxtrace_mxdiag`, `mxtrace_mxblock`, and the additive/linear instances.

There is **no lemma connecting `\tr (A ^+ k)` to `(char_poly A)`_k`** in
MathComp's `mxpoly.v`, `matrix.v`, or `mxalgebra.v`. A Newton-Girard bridge
would have to be proved by us.

## 4. Faddeev-LeVerrier

**Not present anywhere in the installed MathComp / real_closed / analysis
trees.** `Search "Faddeev"`, `Search "LeVerrier"`, `Search "FaddeevLeVerrier"`
all returned empty. `grep -r Faddeev ~/.opam/.../mathcomp` returns nothing.

## 5. `map_poly_char_poly` and `eigenvalue_root_char`

Both present and exactly as hoped:

```
map_char_poly :
forall [aR rR : nzRingType] (f : {rmorphism aR -> rR}) [n] (A : 'M_n),
  map_poly (rR:=rR) f (char_poly A) = char_poly (A ^ f)%sesqui
-- mxpoly.v l.815, opaque

map_char_poly_mx :
forall [aR rR : nzRingType] (f : {rmorphism aR -> rR}) [n] (A : 'M_n),
  (char_poly_mx A ^ map_poly (rR:=rR) f)%sesqui = char_poly_mx (A ^ f)%sesqui
-- mxpoly.v l.809, opaque

eigenvalue_root_char :
forall [F : fieldType] [n] (A : 'M_n) (a : F),
  eigenvalue (F:=F) A a = root (char_poly A) a
-- mxpoly.v l.516, opaque
```

Note the lemma is named `map_char_poly`, not `map_poly_char_poly`. The
`map_poly` side is applied to the polynomial; the `^f`/sesqui side applies
`f` entrywise to the matrix.

---

## 6. Recommendation

**Hand-roll our own `char_poly_int : list (list Z) -> list Z` via Faddeev-
LeVerrier, and bridge it to `char_poly` through `map_char_poly`.** There is
no shortcut in MathComp: (a) no Faddeev-LeVerrier, (b) no Newton-Girard /
`mesym` infrastructure, (c) no `coef_char_poly`-at-k identity, (d) `char_poly`
itself is unreducible on `rat`/`int`. The only lemmas we can actually *use*
from MathComp are the *specification* lemmas: `size_char_poly`,
`char_poly_monic`, `char_poly_trace`, `char_poly_det`, `companionmxK`, and
crucially `map_char_poly` (to lift a `Z` shadow through `intr : int -> rat`
via `map_poly intr`), plus `eigenvalue_root_char` to turn the eigenvalue bound
into a `root (char_poly A)` statement on the rational/real side.

Concrete bridge plan (names to use verbatim):

1. Define `char_poly_int : seq (seq int) -> seq int` computationally (we
   implement Faddeev-LeVerrier over `int`, no division — for an integer
   matrix the intermediate `M_k` and `c_k` are integers).
2. Prove `char_poly_int_correct : forall (A : 'M[int]_n),
     Poly (char_poly_int (to_list A)) = char_poly A`.
   This is proved by induction on `n` using the Faddeev recurrence, where
   the invariant side only mentions `char_poly A`, `\tr`, and matrix products
   — no `\det` needs to unfold. `char_poly_trace` and `char_poly_det` pin
   the top / bottom coefficients; intermediate coefficients are characterized
   through `Cayley_Hamilton` + the Faddeev invariant.
3. Lift to `'M[rat]_n` via `map_char_poly (intr : {rmorphism int -> rat})`:
   `char_poly (map_mx intr A) = map_poly intr (char_poly A)
                              = map_poly intr (Poly (char_poly_int _))`.
4. Connect eigenvalues via `eigenvalue_root_char`.

This keeps the "fast list of `Z`" computation entirely outside the kernel's
`\det` machinery while retaining a clean MathComp-facing specification.

---

## Appendix: queries run
`About char_poly`, `About char_poly_mx`, `Print char_poly`, `Print char_poly_mx`,
`Print determinant`, `About determinant`, `About size_char_poly`,
`About char_poly_monic`, `About char_poly_trace`, `About char_poly_det`,
`About char_poly_trig`, `About Cayley_Hamilton`, `About map_char_poly`,
`About map_char_poly_mx`, `About eigenvalue_root_char`, `About mxminpoly`,
`About mxminpoly_dvd_char`, `About root_mxminpoly`, `About companionmx`,
`Search "char_poly"`, `Search "Faddeev"`, `Search "LeVerrier"`,
`Search "FaddeevLeVerrier"`, `Search "Hessenberg"`, `Search "hessenberg"`,
`Search "Newton"`, `Search "mxtrace"`, `Search "elementary_symmetric"`,
`Search "prod_root_char"`, `Search (char_poly _ = _)`,
`Search (char_poly (_ * _))`, `Search "coef_char_poly"`,
`Search "mesym"`, `Search "Newton_id"`, `Search "sym_fundamental"`,
`Search "power_sum"`, `Search "det"`, `Search "determinant"`.
Reference file inspected directly: `~/.opam/4.14.2+flambda/lib/coq/user-contrib/mathcomp/algebra/mxpoly.v`.
