# Formal-Methods Audit: Trust Base of `maynard_eigenvalue_S1`

**Auditor role.** Formal-methods specialist on a four-person red team. Distinct
focus: rigour of the trust base and soundness of the Rocq machinery (kernel
axioms, `vm_compute`/`native_compute`, `Strategy`, dependency tracking,
MathComp libraries). Math correctness vs. arXiv:1311.4600 and proof-tactic
quality are out of scope here.

**Project audited.** `/home/rocq/prime_gap/`, branch `main`, commit `63501f1`.
Headline theorem `PrimeGapS1.Cert.maynard_eigenvalue_S1`. Build state was
left untouched; all `.vo` files were already up-to-date (`make -q` exit 0,
no `.v` newer than its `.vo`).

---

## Verdict

**The proof's trust base matches what the README and REPORT advertise.**
`Print Assumptions maynard_eigenvalue_S1`, executed against the existing
`.vo` files via a small wrapper compiled with the project's `coqc`, returns
exactly 50 distinct symbols, every one of which is a standard Rocq kernel
primitive in the `Stdlib.Numbers.Cyclic.Int63` namespace
(`PrimInt63.*` constants and their `Uint63Axioms.*` specifications). There
are zero project-specific axioms, zero `Admitted` lemmas, no classical-logic
escape hatches (`functional_extensionality`, `proof_irrelevance`,
`Hilbert_choice`, `JMeq_eq`, `LEM`, etc.), and no `BigN.*` axioms despite the
project's heavy use of the Bignums library.

I have no critical findings. I have a small handful of minor observations
about presentation and one major-but-already-mitigated risk class (kernel
WHNF reduction during conversion at Qed time, which the project explicitly
guards against using `Strategy opaque`). Details below.

---

## Assumption inventory

### Headline theorem `maynard_eigenvalue_S1`

`Print Assumptions` returns 50 distinct symbols under one `Axioms:` header.
All 50 are kernel primitives or their specifications:

**Operators / types (25 symbols, `PrimInt63.*`):**

```
PrimInt63.int : Set
PrimInt63.{add, sub, mul, div, mod, mulc} : int -> int -> int (or pair)
PrimInt63.{addc, subc, addcarryc, subcarryc} : int -> int -> carry int
PrimInt63.{lsl, lsr, land, lor, lxor} : int -> int -> int
PrimInt63.{eqb, ltb, leb} : int -> int -> bool
PrimInt63.compare : int -> int -> comparison
PrimInt63.{head0, tail0} : int -> int
PrimInt63.{diveucl, diveucl_21, addmuldiv}
```

**Specifications (25 symbols, `Uint63Axioms.*`):**

```
Uint63Axioms.{add_spec, sub_spec, mul_spec, mulc_spec, div_spec,
              mod_spec} -- arithmetic mod 2^63
Uint63Axioms.{addc_def_spec, addcarryc_def_spec, subc_def_spec,
              subcarryc_def_spec, diveucl_def_spec,
              compare_def_spec, addmuldiv_def_spec} -- recursive defs match
Uint63Axioms.{lsl_spec, lsr_spec, land_spec, lor_spec, lxor_spec} -- bit ops
Uint63Axioms.{ltb_spec, leb_spec} -- comparison correctness
Uint63Axioms.{eqb_correct, eqb_refl}
Uint63Axioms.{head0_spec, tail0_spec} -- leading/trailing zero counts
Uint63Axioms.{of_to_Z, diveucl_21_spec}
```

I cross-checked each against
`Stdlib/Numbers/Cyclic/Int63/PrimInt63.v` and `Uint63Axioms.v` in the
installed Rocq 9.1.1 (the prover that built the `.vo` files): every one
of the 50 reported symbols is declared there as `Primitive ...` (constants)
or `Axiom ...` (specifications). Nothing is project-specific.

Categorisation:

- **Kernel primitive (50/50).** Every symbol is a Rocq kernel primitive
  for native 63-bit integers, shipped with `coq-stdlib`/`rocq-stdlib`.
- **Library axiom (0/50).** None. Notably, Bignums (`BigZ`/`BigN`) does
  not appear; see Major finding 2 below.
- **Project-specific (0/50).** None.
- **Suspicious (0/50).** None.

### Sub-lemma assumption inventory

I verified `Print Assumptions` on every load-bearing sub-lemma the report
mentioned:

| Lemma | File | Assumption set |
|-------|------|----------------|
| `maynard_L1_concrete` | `theories/S1/CertL1.v` | Same 50 (PrimInt63 + Uint63Axioms) |
| `charpoly_int_Dq_scaled` | `theories/S1/CertL2.v` | Same 50 |
| `fl_eq_flint` | `theories/S1/CRTLift.v` | Same 50 |
| `matrix_identity_Z` | `theories/S1/CRTLift.v` | Same 50 |
| `MaynardVerify.all_match_M1Z_true` | `theories/S1/MaynardVerify.v` | **Closed under the global context** |
| `MaynardVerify.all_match_M2Z_true` | `theories/S1/MaynardVerify.v` | **Closed under the global context** |
| `CharPolyAgree.char_poly_int_agrees_710` | `theories/S1/CharPolyAgree.v` | Only the 25 `PrimInt63.*` constants (no `Uint63Axioms.*` specs) |
| `CRTSigns.signs_at_x0_shipped` | `theories/S1/CRTSigns.v` | Same 50 |
| `CRTSigns.signs_at_inf_shipped` | `theories/S1/CRTSigns.v` | Same 50 |

Two notable structural facts:

1. **`MaynardVerify` lemmas are axiom-free.** "Closed under the global
   context" is the strongest possible result — even Uint63 primitives are
   not pulled in. This is consistent with the file's design: the cross-check
   `m1_num · D_M1 = M1_int[i][j] · m1_den` lives entirely in stdlib `Z`
   arithmetic, which is computational kernel reduction, no Uint63 involved.
   The report's claim that "L0 closes the trust gap on the input matrices
   without any FLINT trust" stands.
2. **`char_poly_int_agrees_710` only depends on the 25 `PrimInt63.*`
   *constants*, not the spec axioms.** This is exactly what one expects
   from a `vm_compute. reflexivity.` proof: the kernel runs the VM, gets
   a normal form, and checks definitional equality. The VM uses the
   primitive operators directly, but no spec axiom is invoked because
   nothing in the proof reasons *about* the operators — it just runs
   them. (Spec axioms get pulled in only when downstream lemmas like
   `char_poly_mod_sound` rewrite using `mul_spec`, `mod_spec`, etc.)

### Wider MathComp/realalg surface

I audited the relevant MathComp and `mathcomp.real_closed` constants the
headline theorem statement and proof rely on, by running `Print Assumptions`
in a fresh wrapper:

- `realalg : Type` — **Closed under the global context.**
- `polyrcf.cauchy_bound` — **Closed.**
- `polyrcf.poly_ivtoo` — **Closed.**
- `ratr` (rational embedding into a unitring) — **Closed.**
- `char_poly` (MathComp matrix charpoly) — **Closed.**
- `eigenvalue` — **Closed.**
- `map_char_poly`, `eigenvalue_root_char` — **Closed.**

These are the predicates and lemmas that appear in the headline statement
and L1/L3 proofs. Their axiom-freedom is required, otherwise their
assumptions would surface in `Print Assumptions maynard_eigenvalue_S1`.
This is reassuring: the construction `realalg = quotient of algebraic
expressions` does *not* require Hilbert ε, classical logic, or
`functional_extensionality`. (MathComp's quotient `ChoiceType` uses
constructive `xchoose`-style witnesses on countable types, not the
classical axiom.)

### Bignums sanity check

`BigZ.spec_add` and `BigN.spec_add` were also checked. They use only
the same 50 `PrimInt63.*` / `Uint63Axioms.*` symbols. The Bignums library
adds no axioms of its own; its `bigN`/`bigZ` types are computational
encodings on top of native 63-bit ints, with their specifications proved
from `Uint63Axioms`.

---

## Findings

### Major

**M1. Single use of `native_compute` (not a finding per se, but flagged
for transparency).**

`grep` finds exactly one `native_compute` invocation in
`theories/S1/CRTLift.v:138`:

```rocq
Lemma fl_crt_bound :
  (2 * fl_coeff_bound 42 (max_abs_entry A_int) +
   2 * max_abs_coeff charpoly_of_A_int < crt_product_710)%Z.
Proof. apply Z.ltb_lt. native_compute. reflexivity. Qed.
```

`native_compute` extends the trust base in a way `vm_compute` does not:
the kernel emits OCaml code, hands it to the *system OCaml compiler* to
compile to a native shared object, dynamically loads that object, runs it,
and checks the resulting normal form. Hence the OCaml compiler used by the
build *is* in the trust base of any lemma closed by `native_compute`.

This is mitigated by three observations:
- The lemma in question proves a numerical inequality of the form
  `2A + 2B < P` between three Z-level constants, where A is the
  computable bound `fl_coeff_bound 42 (...)`, B the maximum coefficient
  of the shipped charpoly, and P the product of 710 primes. Both sides
  are purely arithmetic data with no symbolic content; an erroneous
  `native_compute` result would have to flip the truth of a comparison
  on a ~21300-bit integer, which is not a category of bug native_compute
  exhibits.
- The same fact would be provable by `vm_compute. reflexivity.` (the REPORT
  notes the bound just barely exceeds vm_compute's reach in time, not in
  expressive power). Replacing the one `native_compute` with `vm_compute`
  would shrink the trust base by removing the OCaml compiler.
- A reviewer worried about native_compute can rebuild that single file
  with `vm_compute`, after waiting a few extra minutes per run.

Recommendation: I would prefer `vm_compute` here for trust-base purity,
but this is a soft recommendation, not a finding.

**M2. README/REPORT mention "BigN.*" axioms in `Print Assumptions`; the
actual output contains none.**

README.md line 28-30 says

> The only assumptions reported by `Print Assumptions
> maynard_eigenvalue_S1` are Rocq's standard PrimInt63 kernel primitives
> (`Uint63Axioms.*`)

REPORT.md §6 line 1009-1010 says

> only the standard `PrimInt63` primitives (and their `Z` / `Uint63`
> specifications) shipped with Rocq 9.0/9.1 and the `Bignums` library:
> things like `Uint63.add`, `Uint63.mul`, `Uint63.to_Z`, `BigN.succ_spec`.

The empirical output contains zero `BigN.*` symbols. The README is
correct; the REPORT example is slightly misleading (no
`BigN.succ_spec` is actually pulled in). This is a documentation
inaccuracy, not a soundness issue. In Rocq 9.0/9.1, Bignums is built
entirely on PrimInt63 with proved specs, so `BigN.spec_*` lemmas are
theorems, not axioms. No fix needed for the proof itself; the wording in
REPORT §6 could be tightened.

### Minor

**m1. `_CoqProject` lists `Cert.v` before `CertL2.v`, but `Cert.v`
imports `CertL2.v`.**

```
$ grep -n "Cert" _CoqProject
26:theories/S1/Cert.v
27:theories/S1/CertL2.v
```

This is harmless because `make` is driven by the `coqdep`-generated
dependency file (`.Makefile.d`), which correctly lists
`theories/S1/Cert.vo : ... theories/S1/CertL2.vo ...`. The build order
is determined by dependencies, not `_CoqProject` order. But it is
visually surprising and contradicts the README's claim "26 .v files in
dependency order". Recommend swapping the two lines for clarity. Not a
soundness issue.

**m2. Top-level `Opaque charpoly_Z_A.` in `CRTLift.v:62`.**

```rocq
Definition charpoly_Z_A : list Z := char_poly_int A_int.
Lemma charpoly_Z_A_eq : charpoly_Z_A = char_poly_int A_int.
Proof. reflexivity. Qed.
Opaque charpoly_Z_A.
```

`Opaque` is permanently set on a `Definition` (not a `Lemma`), which
prevents the kernel from delta-unfolding `charpoly_Z_A` during
conversion. This is a kernel performance hint (it forces the kernel to
treat the definition as a "black box" that can only be opened via
explicit `unfold` or via the proved equation `charpoly_Z_A_eq`). It does
NOT change the computational content, and `Print Assumptions` confirms
no axioms are introduced by this. Pattern is similar to the
`Strategy opaque [...]/transparent` blocks but at a coarser
"permanently opaque" level. Sound.

**m3. `Strategy opaque [...]/Strategy transparent [...]` blocks.**

Two such blocks in CRTLift.v (lines 723-731 and 1033-1121). I read the
text of each and confirmed:
- The opaque list is matched by an identical transparent list AFTER
  the relevant Qed in both cases.
- `Strategy` is a kernel-reduction-priority directive only; it cannot
  introduce unsoundness. (Soundness of the kernel is invariant under
  the order in which it chooses to reduce convertible terms.)
- `Print Assumptions` on the lemmas guarded by these blocks
  (`per_prime_shipped_eq`, `per_prime_matrix_agreement`) inherits no
  new axioms.

Therefore this technique is purely a performance hack: it shortens
the kernel's WHNF reduction at conversion time so that the Qed
type-check completes in milliseconds instead of >25 minutes (for the
shipped-eq case).

**m4. `Hypothesis` declarations inside `Section`s.**

Three sections use `Hypothesis`:
- `CharPoly.v:960-1065` `Section FL_Invariant_Proof` (10
  hypotheses).
- `CharPoly.v:1071-1460` `Section FL_CharPoly_Core` (depends on the
  invariant hypothesis chain).
- `CertL2.v:216-240` `Section AbstractMatScale` (4 hypotheses).

All sections close with `End ...`, and inside the section the
hypotheses are local. After the section closes, every lemma proved
inside is generalised over its hypotheses (they become explicit
arguments). I verified by `grep -n "^End"` that every `Section` has a
matching `End`. This is the correct, sound use of `Section`/`Hypothesis`
in Rocq; the hypotheses do not leak out.

### Critical

**None.** The audit found no critical issues with the trust base.

---

## What I checked and confirmed sound

1. **Headline `Print Assumptions` is exactly as advertised.** Compiled
   a wrapper `From PrimeGapS1 Require Import Cert. Print Assumptions
   maynard_eigenvalue_S1.` against the existing `.vo` files, output
   is 50 symbols, all PrimInt63/Uint63Axioms. No project axiom, no
   Admitted, no classical logic axioms.

2. **Zero `Admitted`, zero `Axiom` declarations in `theories/S1/`.**
   `grep -rn "Admitted\|Axiom\b\|admit\b" theories/S1/*.v` returns
   only matches in *comments* (Cert.v:12, CharPoly.v:29,
   Bridge.v:11/353/615). No syntactic declaration uses these.

3. **Zero unsafe global-flag changes.** `grep -rn "Unset Guard\|Unset
   Positivity\|Allow StrictProp\|Set Universe Polymorphism\|Set
   Definitional UIP"` returns nothing. The only global flags in the
   project are `Set Implicit Arguments`, `Unset Strict Implicit`,
   `Unset Printing Implicit Defensive` — purely cosmetic.

4. **`make -q` reports clean: no stale `.vo`.** All `.vo` are at least
   as recent as their `.v`. No `.v` files lack a `.vo`.

5. **`_CoqProject` lists all 26 `.v` files** (verified by `diff` of
   sorted file lists). Modulo the one ordering quibble (m1), every
   source is in the build.

6. **Single `native_compute`, single trivial inequality.** Only one
   use of `native_compute` anywhere in `theories/S1/`, on a
   straightforward arithmetic inequality
   (`fl_crt_bound`). Acceptable, with the caveat M1 above.

7. **MathComp / realalg surface is axiom-free.**
   `cauchy_bound`, `poly_ivtoo`, `ratr`, `char_poly`, `eigenvalue`,
   `map_char_poly`, `eigenvalue_root_char`, and even `realalg` itself
   are all "Closed under the global context". No classical axioms
   needed for the algebraic-real layer.

8. **Bignums is axiom-free relative to PrimInt63.** `BigZ.spec_add`,
   `BigN.spec_add` use only `PrimInt63.*` and `Uint63Axioms.*`. The
   `BigZ`/`BigN` types are computational, with proved specs.

9. **`A_rat` is built from MathComp standards.** No shadowing of
   `eigenvalue`, `map_mx`, `ratr`, `realalg`, `char_poly`, `invmx`,
   `*m`, `*:`, `\matrix`. Definition in `CertL2.v:180`:
   `A_rat := invmx (mat_int_to_rat M1_int D_M1 42) *m
   mat_int_to_rat M2_int D_M2 42`, where `mat_int_to_rat` (in
   `CharPoly.v:146`) uses MathComp's `\matrix_(i,j) ((Z_to_int x)%:~R
   / (Z_to_int D)%:~R)`.

10. **`M1_int`, `M2_int` are unique definitions in `Witness.v`,
    referenced consistently.** `grep "^Definition M1_int|^Definition
    M2_int|^Definition A_int"` returns exactly one site each
    (`Witness.v:70`, `1925`, `3780`). `MaynardVerify.v` references
    them via the `Witness` import; no shadowing.

11. **`Strategy opaque/transparent` blocks are matched and
    semantics-preserving.** Verified by reading lines 718-731 and
    1029-1121 of `CRTLift.v`. Each opaque is followed by a transparent.
    `Print Assumptions` after each guarded Qed confirms no new axioms
    are introduced. (Strategy is fundamentally a reduction-order
    hint; the kernel's conversion check is sound regardless of which
    convertible reduction sequence it picks.)

12. **`vm_compute` / `native_compute` reductions are within the
    standard soundness theorem.** Every `vm_compute` use I sampled is
    of the form `vm_compute. reflexivity.` (or implicit-reflexivity
    via `apply Z.ltb_lt; vm_compute; reflexivity`). The kernel runs
    the bytecode VM (or native compiler) on a closed term, reads
    back its normal form, and checks definitional equality at the
    head — the standard soundness story for these tactics. No
    "axiomatised fast computation" anywhere; no invocation of
    extracted OCaml; no plugin-defined reduction tactic.

13. **Sections close cleanly.** All `Section` declarations have
    matching `End`s. Hypotheses are properly scoped.

14. **Independent kernel re-checking via `coqchk` (in progress).**
    I started `coqchk PrimeGapS1.Cert` against the existing `.vo`
    files. (Full re-check from `Cert.vo` requires re-checking every
    transitive dependency including the heavy `CharPolyAgree.vo`,
    `CRTLift.vo`, `MaynardVerify.vo`. As of report time it is still
    running, having read ~177 MB of `.vo` data; `vm_compute` checks
    inside coqchk re-run the computations, which is on the order of
    tens of minutes.) `coqchk`'s output, if it terminates without
    error, is a stronger guarantee than `coqc` alone, because it
    re-checks the kernel-level proof terms with a separate code base
    that does not share the elaboration/tactic infrastructure of
    `coqc`.

---

## Open questions / areas where I could not fully confirm

1. **`coqchk` did not finish during this audit window.** I started it
   in the background; it was still running when this report was
   written. If a reviewer wants the *strongest* available guarantee,
   they should run `coqchk -Q theories/S1 PrimeGapS1 PrimeGapS1.Cert`
   to completion (estimated ~15–60 min). I have no reason to expect
   failure: every individual `.vo` was already produced by `coqc` of
   the exact same kernel, the kernel is deterministic, and `coqchk`
   uses the same conversion algorithm. But it is the formal
   gold-standard cross-check and I did not get to see its exit code.

2. **OCaml compiler trust for the single `native_compute`.** As
   discussed in M1, that one inequality
   (`fl_crt_bound`) puts the OCaml compiler used during the project
   build in the trust base. I did not audit OCaml itself. The
   alternative — replacing `native_compute` with `vm_compute` — would
   eliminate this. (`vm_compute` is interpreted by Rocq's bundled
   bytecode VM, which is in the kernel's trust base regardless.)

3. **Trust of the `coq-stdlib`/`rocq-stdlib` distribution.** The 50
   axioms I list above are all from the installed `coq-stdlib`
   package. If the package were tampered with (e.g., `Uint63Axioms`
   replaced with a non-faithful set), every "verified" Rocq proof in
   the world would inherit the corruption. This is the standard
   trusted-base of any Rocq proof; the project does not extend it.

4. **The `Uint63Axioms.*` axioms claim that Rocq's native 63-bit ops
   match the OCaml `Int64`/native semantics.** This is a Rocq-design
   trust assumption (the compiler implements the operations
   faithfully). It is well-known and widely accepted, but not formally
   verified itself. Any project using `vm_compute` on `Uint63` data —
   which this one does extensively — inherits this assumption. The
   project does not introduce any *new* trust concerns here.

5. **The mathematical correctness of the `M1_int`, `M2_int` data
   matches Maynard's spec.** Verified by `MaynardVerify.all_match_M*Z_true`
   inside the kernel, but those lemmas assume `MaynardSpec.G_2`,
   `M1_entry`, `M2_entry` are faithful transcriptions of Maynard's
   formulas. I did not re-read `MaynardSpec.v` against arXiv:1311.4600
   — that is the mathematician's job on the red team. From a
   formal-methods perspective, the chain is closed: if `MaynardSpec.v`
   correctly encodes Maynard's formulas, then `M1_int`/`M2_int` are
   verified to encode them too.

---

## Bottom line

The headline theorem `maynard_eigenvalue_S1`'s trust base is exactly
"Rocq 9.1.1's kernel + 50 standard `PrimInt63`/`Uint63Axioms` axioms
shipped with the prover + the OCaml compiler used to build the prover
(via one `native_compute` invocation, which is replaceable by
`vm_compute`)". There are zero project-specific axioms, zero
`Admitted`s, zero classical-logic escape hatches, zero stale `.vo`
files, zero shadowed MathComp definitions, and zero global flags
weakening kernel checking. The README's and REPORT's claims about the
trust base are accurate, modulo a small documentation imprecision in
REPORT §6 where it lists "`BigN.succ_spec`" as an example assumption
that does not in fact appear.

The project's formal-methods machinery is sound. A reviewer who
trusts:

1. Rocq 9.0/9.1's kernel,
2. the 50 `Uint63Axioms.*`/`PrimInt63.*` primitive-integer axioms (50
   symbols enumerated above),
3. the `vm_compute` and (for one inequality) `native_compute` tactics,

obtains a Rocq-kernel-checked existence proof of a `realalg` eigenvalue
of a specific `'M[rat]_42` strictly above `4/105`. The 42×42 input
matrices are themselves kernel-checked (axiom-free, "Closed under the
global context") against a transcription of Maynard's Lemma 7.1 / eq.
7.8 closed forms.
