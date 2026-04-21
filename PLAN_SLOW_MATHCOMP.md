# Plan: Close the 2 remaining CertL2.v admits without massive compute

## Executive summary

Three independent reviews (mathematician, MathComp/Rocq expert, devil's advocate)
converged on the same answer: **the commented "complete" proofs in CertL2.v are
NOT complete** — they reference a non-existent lemma `char_poly_scale_coef`
(actual name: `char_poly_scale` in `CharPolyScale.v:49`). They were never
compiled. Throwing more RAM at them produces a type error at minute 0, not a
Qed.

The right fix is structural, not computational:

1. **Drop `mat_A_eq_Arat`.** It is only referenced from inside the *commented*
   body of `charpoly_int_Dq_scaled`. The headline `maynard_eigenvalue_S1`
   (Cert.v) does NOT depend on it. Verified by transitive use search.

2. **Reprove `charpoly_int_Dq_scaled` per-coefficient.** Use `apply/polyP => k`
   then `char_poly_scale` (the real name) at the poly level. Replace `A_rat`
   with `(Z_to_int D_A)%:~R^-1 *: mat_int_to_rat A_int 1 42` (a one-line
   pointwise consequence of `mat_int_to_rat_scale_inv'`, NOT the heavy
   `mat_A_eq_Arat`). All matrix arithmetic happens at generic `n` inside
   `char_poly_scale`; the kernel only specializes to 42 at Qed.

3. **Belt-and-suspenders performance hints**: `Set Keyed Unification.` and
   `Strategy opaque [mat_int_to_rat A_rat char_poly char_poly_mx map_mx invmx]`
   at file top. These mirror the `CRTLift.v` Strategy-opaque pattern that
   closed the previous admits in milliseconds.

Estimated total work: **~30-50 lines of Rocq, one compile cycle (~5-10 min)**.
No native_compute. No 90-minute waits. No 16 GB RAM.

## What the existing infrastructure gives us

All Z-level facts are Qed (post the previous CRTLift work):
- `scaling_Z_from_check` (CharPolyAgree.v:979): per-coefficient
  `charpoly_int[k] * D_A^(42-k) = D_q * charpoly_of_A_int[k]`. Pure Z.
- `char_poly_int_correct` (CharPoly.v:1936):
  `pol_to_polyrat (char_poly_int A_int) = char_poly (mat_int_to_rat A_int 1 42)`.
- `fl_eq_flint` (CRTLift.v): `charpoly_Z_A = charpoly_of_A_int` at Z level.
- `char_poly_scale` (CharPolyScale.v:49): generic-n
  `(char_poly (c *: M))_k = c^(n-k) * (char_poly M)_k`.
- `mat_int_to_rat_scale_inv'` (CertL2.v:116):
  `mat_int_to_rat M D n = (Z_to_int D)%:~R^-1 *: mat_int_to_rat M 1 n`. Pointwise, fast.
- `mat_identity_rat` (CertL2.v:217): the matrix identity over rats. Already Qed.

## Step-by-step plan

### Step 1: Verify `mat_A_eq_Arat` is not needed (defensive)

```bash
# In Cert.v, charpoly_int_Dq_scaled is used. mat_A_eq_Arat is not.
grep -rn "mat_A_eq_Arat" theories/S1/
```
Expect to see references only inside CertL2.v comments and the admit itself.
If clean, delete the lemma + commented body. If there's a stray external use,
fix that caller first (likely zero work, but check).

### Step 2: Rewrite `charpoly_int_Dq_scaled` per-coefficient

Replace the current admit with a coefficient-wise proof:

```coq
Lemma charpoly_int_Dq_scaled :
  pol_to_polyrat charpoly_int = (Z_to_int D_q)%:~R *: char_poly A_rat.
Proof.
  have HDA : D_A <> Z0 by discriminate.
  have HDA_unit : (Z_to_int D_A)%:~R \is a @GRing.unit rat
    by exact: Z_to_int_unit'.
  have HDA_ne : (Z_to_int D_A)%:~R != (0 : rat)
    by rewrite intr_eq0; exact: Z_to_int_neq0'.

  (* Key bridge: A_1 = D_A *: A_rat, expressed without mat_A_eq_Arat.
     Both sides are matrices; we never reason about them as a whole.
     Instead, char_poly_scale operates per-coefficient at generic n. *)
  set A_1 := mat_int_to_rat A_int 1 42.
  have HA1_scale : A_1 = (Z_to_int D_A)%:~R *: A_rat.
  { (* This is the ONLY matrix-level step.
       Using mat_int_to_rat_scale_inv' on the A_rat side. *)
    rewrite /A_rat.
    (* Try one of:
       (a) apply/matrixP => i j; rewrite !mxE; field
       (b) the original chain rewrites scalerA mulVr ... if Strategy opaque tames it
       Decide empirically; keep whichever fits in 5 min. *)
    admit. }

  apply/polyP => k.
  rewrite coefZ.
  case: (leqP k 42) => Hk; last first.
  { (* k > 42: both coefficients are 0 *)
    rewrite nth_default; last by rewrite size_ship; apply/leP.
    rewrite mul0r nth_default //.
    rewrite size_scale; last exact HDA_ne.
    rewrite size_char_poly. by apply/leP. }

  (* k <= 42: use scaling_Z + char_poly_scale *)
  have Hcoef : (Z_to_int (List.nth k charpoly_int Z0))%:~R *
               (Z_to_int D_A)%:~R ^+ (42 - k) =
               (Z_to_int D_q)%:~R *
               (Z_to_int (List.nth k charpoly_of_A_int Z0))%:~R :> rat.
  { rewrite -intrM -Z_to_int_mul -[in RHS]intrM -Z_to_int_mul.
    apply/eqP. rewrite (eqr_int rat). apply/eqP.
    rewrite Z_to_int_Zpow_rat. (* if needed *)
    exact: scaling_Z. }

  (* Rewrite (char_poly A_rat)_k via char_poly_scale and HA1_scale *)
  have Hcpa1 : (char_poly A_1)`_k =
               (Z_to_int D_A)%:~R ^+ (42 - k) * (char_poly A_rat)`_k.
  { rewrite HA1_scale. exact: char_poly_scale. }

  (* Rewrite (pol_to_polyrat charpoly_int)_k via char_poly_int_correct + scaling *)
  ...
Admitted. (* Sketch — fill in and Qed. *)
```

The detailed gluing should land in 20-30 lines. The point is: **no `invmx`,
no `scalerA`, no `mulVr`, no `mulKVmx`, no `invmxZ`, no `invrM`** — the slow
matrix-algebra rewrites that the original commented proof attempted.

### Step 3: Add performance hints (insurance)

At top of CertL2.v, after MathComp imports:

```coq
Set Keyed Unification.
Strategy opaque [mat_int_to_rat A_rat char_poly char_poly_mx map_mx invmx].
```

These prevent the kernel from descending into 42x42 matrix bodies during
unification, mirroring the CRTLift.v fix. Cheap insurance.

### Step 4: Test with `Time` profiling

For each remaining `rewrite` that is suspected slow, wrap with `time "label"`:
```coq
time "scalerA-step" rewrite scalerA.
```
Log shows per-step timing. Anything over 10 sec is rejected and refactored
per Step 2's per-coefficient pattern.

### Step 5: Verify the headline

```bash
rocq compile -Q theories/S1 PrimeGapS1 theories/S1/Cert.v
# Then:
echo 'From PrimeGapS1 Require Import Cert.
Print Assumptions maynard_eigenvalue_S1.' > /tmp/check.v
rocq compile -Q theories/S1 PrimeGapS1 /tmp/check.v
```
Expect ONLY PrimInt63 axioms — no `charpoly_int_Dq_scaled`, no `mat_A_eq_Arat`.

## Risk assessment

| Risk | Likelihood | Mitigation |
|------|-----------|------------|
| `char_poly_scale` signature doesn't fit Step 2's gluing | Medium | Read its actual statement; adjust the helper rewrites |
| Even per-coefficient proof has slow rewrite at fixed 42 | Low | All operations are at `rat` (not matrix); rat ops are fast |
| `mat_int_to_rat_scale_inv'` rewrite of `A_rat` is itself slow | Medium | Use `apply/matrixP => i j; rewrite !mxE; field` instead — pointwise rat arithmetic |
| `Z_to_int_Zpow_rat` doesn't apply directly | Low | Already exists at CertL2.v:108; signature matches |
| Hidden caller of `mat_A_eq_Arat` | Very low | One grep verifies, takes 5 sec |
| Slow `Qed` due to elaboration of `'M[rat]_42` even after pointwise reasoning | Medium | Strategy opaque on `A_rat` and `char_poly` |

## Implementation order

1. (5 min) Grep `mat_A_eq_Arat` uses; if clean, delete it + commented body.
2. (5 min) Add Strategy opaque + Set Keyed Unification hints at file top.
3. (15-30 min) Write the per-coefficient proof of `charpoly_int_Dq_scaled`.
4. (5 min) Compile CertL2.v; iterate if needed.
5. (5 min) Verify Cert.v compiles and `Print Assumptions` is clean.

Total: ~1 hour active work, plus compile time.

## Success criteria

- `CertL2.v` compiles in under 2 min.
- 0 admits in CertL2.v.
- `Print Assumptions maynard_eigenvalue_S1` shows ONLY PrimInt63 kernel
  axioms (no project-specific admits or axioms).
