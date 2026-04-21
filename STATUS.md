# Project status

**22 Rocq files. Headline proof is COMPLETE.**

- 0 `Admitted` anywhere in `theories/S1/`.
- 0 project-specific axioms visible to
  `Print Assumptions maynard_eigenvalue_S1`.
- The only assumptions reported are standard PrimInt63 kernel
  primitives (Uint63Axioms), which are built into Rocq.

## Headline theorem

```rocq
Theorem maynard_eigenvalue_S1 :
  exists lambda : realalg,
    eigenvalue (map_mx (ratr : rat -> realalg) A_rat) lambda
    /\ (ratr (4%:Q / 105%:Q) : realalg) < lambda.
```

`Qed` in `theories/S1/Cert.v`.

## Proof assembly

| Layer | File | Content |
|---|---|---|
| L1 | `CertL1.v` | IVT root existence via Sturm count |
| L2 | `CertL2.v` | Root transfer via `charpoly_int_Dq_scaled` |
| L3 | `Cert.v` | Root of char poly implies eigenvalue |
| L4 | `Cert.v` | Maynard bound `4/105 < lambda` |

## Verification infrastructure

- **CRT lift (`CRTLift.v`)**: `fl_eq_flint` and `matrix_identity_Z`
  lift the 710-prime modular agreement (machine-checked by `vm_compute`)
  to equality over Z, using the coefficient bound derived from the
  Faddeev-LeVerrier recurrence on a matrix with bounded entries.
- **FL modular soundness (`CRTBridge.v`)**: bridges the concrete
  `char_poly_int` implementation to MathComp's `char_poly` through the
  FL recurrence identified in `CharPoly.v`.
- **Sturm chain CRT check (`CRTCheck.v`)**: the 42-step PRS chain is
  cross-checked by reducing modulo 10 primes and verifying the
  identity `lc(B)^d * A = Q*B + beta*C` in `Uint63`. (The final
  CRT-to-Z conversion of this chain is not on the critical path of
  `maynard_eigenvalue_S1`; the headline proof uses the charpoly
  lift in `CRTLift.v` instead.)

## Build

```bash
coq_makefile -f _CoqProject -o Makefile
make -j     # ~20-25 min with parallelism, ~44 min sequential
```

## Verifying assumptions

```bash
coqtop -Q theories/S1 PrimeGapS1 \
  -l theories/S1/Cert.v -batch \
  -e 'Print Assumptions maynard_eigenvalue_S1.'
```

Expected output: only entries of the form `Uint63Axioms.*` and
`PrimInt63.*` (Rocq's built-in primitive integer specification).
