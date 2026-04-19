# Closing the remaining admits — Opacity Strategy (in progress)

**Status: 6 of 9 CRTLift admits closed. 3 admits + 2 CertL2 admits + 1 Cert admit remain.**

## Expert insight

> Stop trying to compute expressions with casts going into `rat`. There are
> proofs in these expressions and reduction gets lost in irrelevant subterms.
> These casts must be **opaque** and pushed as far **outside** as possible,
> until we can compute below only with representations suited for that.

## Investigation findings

The core issue is that several MathComp/CharPoly definitions are transparent:

- `intr` (int → rat coercion via `%:~R`): MathComp standard, transparent
- `Z_to_int`: declared `Opaque` in CertL2.v line 92, but too late
- `mat_int_to_rat`: transparent everywhere
- `pol_to_polyrat`: transparent everywhere
- `fl_bound_aux` (a Fixpoint): transparent — when applied to `42`, kernel
  unfolds 42 times during conversion, creating exponential-sized terms
  on symbolic `B = max_abs_entry A_int`
- `char_poly_int A_int`: when unfolded, the kernel reduces the FL loop
  on the concrete 42×42 matrix

## Existing well-structured proof in git

Commit `ad3b1ca` has the FULL proof for `mat_A_eq_Arat` that already
follows the expert advice (push casts outside via `mat_int_to_rat_scale_inv'`
+ `invmxZ` + `mulKVmx`). It was tested before and takes 50-90 min on
16 GB RAM — too slow for current hardware.

## Attempted strategy (incomplete)

1. Add `Local Strategy 1000 [intr Z_to_int]` before slow proofs
2. Add `Opaque fl_bound_aux fl_coeff_bound` before `charpoly_coeff_bound`
3. Add bridge lemma `charpoly_Z_A_eq` to avoid `change` triggering kernel reduction
4. Use existing proof structure from commit ad3b1ca for `mat_A_eq_Arat`

**Problem**: Each compile attempt takes 30-60+ minutes due to the
existing vm_compute steps (10+ min) plus the `per_prime_agreement` Qed
(~35 min on this machine). Iterating on opacity strategies is impractical
without faster compile times.

## Path forward

To close the remaining admits, the practical approach is:
1. Get a machine with ≥ 16 GB RAM and `native_compute` enabled
2. For the 2 CertL2 admits: uncomment the proofs from commit `ad3b1ca`
   (fix the 2 bugs: wrong arg count for `mat_int_to_rat_scale_inv'`,
   wrong lemma name `char_poly_scale_coef` → `char_poly_scale`)
3. For the 3 CRTLift admits:
   - `per_prime_shipped_eq`: replace with `Proof. native_compute. reflexivity. Qed.`
   - `per_prime_matrix_agreement`: same with `Transparent` first
   - `charpoly_coeff_bound`: needs the opacity strategy to work

## Resources budget

On a 60 GB / 16-core machine with native_compute:
- vm_compute steps: ~5 min total (with native_compute much faster)
- per_prime_agreement Qed: ~5 min (without rat reduction triggers)
- 5 CertL2 admits: ~50-90 min total

**Total estimated**: 1-2 hours on suitable hardware.
