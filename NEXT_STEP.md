# Closing the remaining admits — Opacity Strategy

**Expert insight (translated from French):**
> "Stop trying to compute expressions with casts going into `rat`. There are
> proofs in these expressions and reduction gets lost in irrelevant subterms.
> These casts must be **opaque** and pushed as far **outside** as possible,
> until we can compute below only with representations suited for that."

## Root cause analysis

`mat_int_to_rat`, `pol_to_polyrat`, `Z_to_int`, and especially MathComp's
`intr` (int → rat coercion via `%:~R`) are all **transparent**. When the
kernel encounters expressions like `map_mx (intr : int -> rat) A_int` on
the concrete 42×42 matrix `A_int`, it tries to normalize each rat entry,
which involves:
1. Reducing `intr` applications (transparent in MathComp)
2. Normalizing `Z_to_int` (transparent in CharPoly.v)
3. Field axiom resolution on `(_)%:~R / (_)%:~R` divisions

At dimension 42, this is exponential.

## Strategy: Opaque + Push Outside

### Step 1: Make rat casts opaque locally

In CharPoly.v and CertL2.v:
```coq
Local Strategy 100 [intr Z_to_int mat_int_to_rat pol_to_polyrat].
```
Or use `Opaque` after the proof of equational properties.

### Step 2: Restructure mat_A_eq_Arat to push casts outside

Current:
```coq
Lemma mat_A_eq_Arat : mat_int_to_rat A_int D_A 42 = A_rat.
```

The proof rewrites *inside* `'M[rat]_42` (each entry is a division). Better:
prove a generic lemma about `mat_int_to_rat M D` that doesn't unfold to
divisions, and apply it once:
```coq
Lemma mat_int_to_rat_eq_invD_scale_int (M : mat) (D : Z) (n : nat) :
  D <> 0%Z ->
  mat_int_to_rat M D n =
  (Z_to_int D)%:~R^-1 *: mat_int_to_rat M 1 n.
```
This lemma is proved ONCE (generically), then applied to specific A_int.
The key: the `intr` cast on `D` stays at the OUTSIDE as `^-1 *: ...`,
not inside each entry.

### Step 3: Restructure charpoly_int_Dq_scaled

Push the `(Z_to_int D_q)%:~R` scalar OUTSIDE all polynomial operations.
Use `char_poly_scale` (already Qed in CharPolyScale.v) to extract the
scalar as a single multiplication, not as a per-coefficient cast.

### Step 4: For charpoly_coeff_bound

The Qed hangs because `change charpoly_Z_A with (char_poly_int A_int)`
forces conversion that triggers `fl_c_rat_is_int` reduction (which
internally uses MathComp's `map_char_poly` on the rat-lifted matrix).

Fix: avoid `change` entirely. Use only the generic structural lemmas
`char_poly_int_nth_lt` and `char_poly_int_nth_leading` (already proved).
Make `fl_all_divisible_from_L2` more opaque — wrap it in a Qed lemma
specialized to A_int that hides the rat manipulations.

### Step 5: For per_prime_agreement

Same `Transparent/unfold/Opaque` pattern triggers slow conversion.
Use a similar opacity strategy.

## Implementation order

1. Add opacity declarations in CharPoly.v (local Strategy 100 for intr)
2. Refactor `mat_A_eq_Arat` to use the generic outside-cast lemma
3. Refactor `charpoly_int_Dq_scaled` similarly
4. Refactor `charpoly_coeff_bound` to avoid `change` on charpoly_Z_A
5. Test each compile incrementally

## Goal

Close all 6 admits (3 in CRTLift.v, 2 in CertL2.v, 1 in Cert.v) on this
machine. Resource budget: <30 min compile time per proof, <16 GB RAM.
