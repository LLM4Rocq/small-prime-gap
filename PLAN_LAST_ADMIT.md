# Plan: Close `charpoly_int_Dq_scaled` — the last project admit

## Status: RESOLVED — admit closed, 0 project assumptions in critical path.

## Background

- Single remaining admit: `CertL2.charpoly_int_Dq_scaled` at
  `/home/rocq/prime_gap/theories/S1/CertL2.v:373`.
- Headline `maynard_eigenvalue_S1` (Cert.v) depends on it.
- Prior attempts to use `apply: char_poly_scale` at concrete dim 42 hung
  >2 min in what I suspected was kernel reduction — but wasn't.

## Findings from the research team

### Devil's advocate
- The admit body in the file is literally `Proof. Admitted.` — no proof checked in.
- `mat_A_scale_eq_Arat` IS already Qed at concrete dim 42 (via generic-n
  helper `abstract_mat_scale`). So dim 42 is not a universal blocker.
- Recommendation: test `char_poly_scale` at n=42 in an isolated scratch
  file BEFORE conceding.

### Mathematician
- Proposed `charpoly_scaled_poly_eq` helper at generic `n` parameterized
  over abstract matrices + scalars. Qed at abstract n → opaque proof term
  → specialization at n=42 is instant.
- Signature provided; uses existing building blocks (mat_A_scale_eq_Arat,
  char_poly_int_correct, fl_eq_flint, scaling_Z, pol_to_polyrat_coef).

### MathComp investigator (the decisive one)
- **Diagnosis**: the hang is NOT kernel reduction. It's MathComp's HB
  canonical-structure elaborator walking the algebraic-instance graph
  on the concrete `'M[rat]_42` type, triggered by tactic-level
  unification (`apply:`, `exact:`, `rewrite`).
- `Strategy opaque [...]` has no effect (wrong layer).
- `@char_poly_scale [the fieldType of rat] 42 ...` still hangs.
- `Set Keyed Unification.` has no effect.

## Winning technique

Two complementary moves, both required:

1. **Term-mode plugging instead of tactic-mode** for any call whose
   statement mentions `(char_poly A_rat)` or similar concrete-dim-42
   MathComp expressions. Example:
   ```coq
   (* Instead of: apply: char_poly_scale; [exact HDA_ne | exact Hk]. *)
   (* Write: *)
   := char_poly_scale_rat42 HDA_ne Hk
   ```
   Term-mode bypasses the elaborator's canonical-structure walk.

2. **Auxiliary lemmas pre-specialised to `(rat, 42)`**, each with
   `Proof. exact: <generic>. Qed.`:
   ```coq
   Lemma char_poly_scale_rat42 (c : rat) (M : 'M[rat]_42) (k : nat) :
     c != 0 -> (k <= 42)%N ->
     (char_poly (c *: M))`_k = c ^+ (42 - k) * (char_poly M)`_k.
   Proof. exact: char_poly_scale. Qed.
   ```
   Inside the aux lemma the context is tiny; HB resolution runs in ms.

3. **Abstract `(char_poly A_rat)`_k as a fresh rat variable** before the
   final algebraic manipulation:
   ```coq
   pose c := (char_poly A_rat)`_k.
   change (char_poly A_rat)`_k with c in *.
   (* now all subsequent tactics see pure rat terms *)
   ```

4. **Explicit `eq_trans` / `f_equal`** wherever a `rewrite` would
   re-expose `A_rat` to the elaborator.

## Compile time

- Before: hung >2 min → timeout kill.
- After: `CertL2.v` compiles in ~11 sec.

## Takeaways

- Not every MathComp slowness is a kernel reduction issue. Distinguish
  kernel conversion (fix with `Strategy opaque`) from HB canonical
  structure elaboration (fix with term-mode + pre-specialised aux).
- Testing a suspect call in isolation (5-line scratch file) is always
  worth doing before conceding an admit.
- The "hang" story from PLAN_SLOW_MATHCOMP.md was correct that the
  symptom was real but wrong about the cause.
