"""
Build the Rayleigh-quotient witness vector v in Q^42 for Maynard's M_{105} > 4.

Pipeline:
  1. Load M1, M2 in Q^{42 x 42} from python/m1m2.pkl (cached by flint_probe).
  2. Build A = M1^{-1} M2 in arb_mat / acb_mat at 1024-bit precision and
     extract the top right eigenvector via acb_mat.eig(right=True).  This
     is only a *heuristic*; verification is exact rational.
  3. Rotate the complex eigenvector so the largest-magnitude entry is real
     positive (the top eigenvalue is real, so the eigenvector is real up
     to a global complex phase), and divide so that entry is exactly 1.
  4. Read the exact rational midpoint of each component via arb.mid().fmpq()
     — arb midpoints are exact dyadic rationals at the working precision.
  5. Snap each component to a small-denominator rational via Mathematica-
     style absolute tolerance:  find smallest q with |v_i - p/q| <= tol,
     using ascending tol = 10^-2, 10^-3, ... until the exact Rayleigh
     quotient inequality
        105 * v^T M2 v  >  4 * v^T M1 v        and    v^T M1 v > 0
     both hold over Q.
  6. Emit Rocq source theories/S1/Witness_Quad.v with the 42 (num, den)
     pairs in MaynardBasis.maynard_basis order.

Why does max_den end up around 10^14, not 10^6?
  The eigenvector entries span ~14 decimal orders of magnitude (1e-14 to 1),
  reflecting the ill-conditioning of M1.  Components below 1e-14 are
  numerically meaningful for the inner product because the corresponding
  M_k entries are large (~1e29) and amplify them.  Truncating those small
  entries to 0 destroys the inequality.  Therefore the practical lower
  bound on the denominator is roughly the magnitude span of the eigenvector,
  i.e. ~1e14.

Run with:   .venv/bin/python python/build_quad_witness.py
"""
from __future__ import annotations
import math, pickle, sys, time
from fractions import Fraction
from math import gcd
from pathlib import Path

from flint import acb_mat, arb_mat, arb, acb, fmpq, ctx

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
CACHE = HERE / "m1m2.pkl"
OUT = ROOT / "theories" / "S1" / "Witness_Quad.v"

assert CACHE.exists(), f"missing {CACHE} — run python/flint_probe.py first"

with open(CACHE, "rb") as f:
    M1_rat, M2_rat = pickle.load(f)

DIM = len(M1_rat)
assert DIM == 42, DIM
print(f"Loaded M1, M2 ({DIM} x {DIM}) from {CACHE}", flush=True)

# ----------------------------------------------------------------------
# 1. High-precision top eigenvector of A = M1^{-1} M2.
# ----------------------------------------------------------------------
PREC = 1024
ctx.prec = PREC

print(f"Building arb_mat A = M1^{{-1}} M2 at {PREC}-bit precision …", flush=True)
t0 = time.time()
M1arb = arb_mat([[arb(fmpq(M1_rat[i][j].numerator, M1_rat[i][j].denominator))
                  for j in range(DIM)] for i in range(DIM)])
M2arb = arb_mat([[arb(fmpq(M2_rat[i][j].numerator, M2_rat[i][j].denominator))
                  for j in range(DIM)] for i in range(DIM)])
A_acb = acb_mat(M1arb.inv() * M2arb)
print(f"  done in {time.time() - t0:.2f}s", flush=True)

print("Computing eigenvalues + right eigenvectors of A …", flush=True)
t0 = time.time()
E, R = A_acb.eig(right=True, algorithm="rump")
print(f"  done in {time.time() - t0:.2f}s; got {len(E)} eigenvalues", flush=True)

imax = max(range(len(E)), key=lambda i: float(E[i].real.mid()))
top_eig = E[imax]
print(f"  top eigenvalue  ≈ {float(top_eig.real.mid()):.16f}")
print(f"  105 * top_eig   ≈ {105 * float(top_eig.real.mid()):.16f}  (target ≈ 4.00207)")
assert 3.99 < 105 * float(top_eig.real.mid()) < 4.05

v_acb = [R[i, imax] for i in range(DIM)]

# Rotate to align the largest-magnitude entry to the positive real axis,
# and rescale so that entry is exactly 1.
def cmag(c):
    rm = float(c.real.mid()); im = float(c.imag.mid())
    return (rm * rm + im * im) ** 0.5

ipiv = max(range(DIM), key=lambda i: cmag(v_acb[i]))
piv = v_acb[ipiv]
print(f"Pivot index {ipiv}, |value| ≈ {cmag(piv):.6e}", flush=True)
piv_conj = acb(piv.real, -piv.imag)
piv_abs2 = piv.real * piv.real + piv.imag * piv.imag
mult = piv_conj / acb(piv_abs2, arb(0))
v_scaled = [v_acb[i] * mult for i in range(DIM)]
max_imag = max(abs(float(c.imag.mid())) for c in v_scaled)
max_real = max(abs(float(c.real.mid())) for c in v_scaled)
print(f"After phase alignment: max |Im| = {max_imag:.3e},  max |Re| = {max_real:.3e}", flush=True)
assert max_imag < 1e-30 * max(1.0, max_real)

# arb.mid() is an exact dyadic rational; fmpq() gives it exactly.
print("Extracting exact rational midpoints …", flush=True)
v_exact_q = []
for c in v_scaled:
    f = c.real.mid().fmpq()
    v_exact_q.append(Fraction(int(f.p), int(f.q)))

# ----------------------------------------------------------------------
# 2. Reality check at full numerical precision.
# ----------------------------------------------------------------------
def rayleigh(vec_q):
    """Return (v^T M2 v,  v^T M1 v)  as Fractions."""
    s2 = Fraction(0)
    s1 = Fraction(0)
    for i in range(DIM):
        vi = vec_q[i]
        if vi == 0:
            continue
        row1 = M1_rat[i]
        row2 = M2_rat[i]
        for j in range(DIM):
            vj = vec_q[j]
            if vj == 0:
                continue
            prod = vi * vj
            s1 += prod * row1[j]
            s2 += prod * row2[j]
    return s2, s1

print("Verifying Rayleigh quotient at full numerical precision …", flush=True)
t0 = time.time()
s2_hp, s1_hp = rayleigh(v_exact_q)
ratio_hp = Fraction(105 * s2_hp, s1_hp)
print(f"  done in {time.time() - t0:.2f}s", flush=True)
print(f"  105 * v^T M2 v / v^T M1 v ≈ {float(ratio_hp):.12f}  (target ≈ 4.00207)", flush=True)
assert s1_hp > 0
assert 4.0 < float(ratio_hp) < 4.01

# ----------------------------------------------------------------------
# 3. Snap to small-denominator rationals.
#
# Strategy: Mathematica-style absolute-tolerance Rationalize.  For each
# component v_i, find smallest q s.t. |v_i - p/q| <= tol with an optimal p
# (the best p is the closest convergent / semi-convergent of v_i with
# denominator <= q).  Walk the continued fraction; first convergent whose
# distance from v_i is below tol gives the answer.
# ----------------------------------------------------------------------
def rationalize_abs(x: Fraction, tol: Fraction) -> Fraction:
    """Smallest-denominator p/q (q >= 1) such that |x - p/q| <= tol.

    Returns 0 if |x| <= tol.  Uses the continued-fraction convergents of x;
    by the standard CF theory, the first convergent satisfying the error
    bound is optimal in the smallest-denominator sense (modulo semi-
    convergents, which we don't need for our use case).
    """
    if abs(x) <= tol:
        return Fraction(0)
    sign = 1 if x > 0 else -1
    x = abs(x)
    # h_{-2}=0, h_{-1}=1;  k_{-2}=1, k_{-1}=0  (standard CF recurrence).
    h_pp, h_p = 0, 1
    k_pp, k_p = 1, 0
    y = x
    for _ in range(500):
        a = math.floor(y)
        h_curr = a * h_p + h_pp
        k_curr = a * k_p + k_pp
        if k_curr > 0 and abs(x - Fraction(h_curr, k_curr)) <= tol:
            return Fraction(sign * h_curr, k_curr)
        h_pp, h_p = h_p, h_curr
        k_pp, k_p = k_p, k_curr
        frac = y - a
        if frac == 0:
            return Fraction(sign * h_curr, k_curr) if k_curr > 0 else Fraction(0)
        y = Fraction(1) / frac
    # Shouldn't reach here for our input; fall back to last computed.
    return Fraction(sign * h_p, k_p) if k_p > 0 else Fraction(0)

print()
print("Per-component absolute-tolerance rationalisation:")
witness = None
report = None
for tol_exp in range(2, 24):
    tol = Fraction(1, 10 ** tol_exp)
    t0 = time.time()
    vec_q = [rationalize_abs(x, tol) for x in v_exact_q]
    s2, s1 = rayleigh(vec_q)
    elapsed = time.time() - t0
    if s1 <= 0:
        print(f"  tol=10^-{tol_exp:>2}: s1 <= 0  ({elapsed:.2f}s)")
        continue
    slack = Fraction(105 * s2 - 4 * s1) / Fraction(s1)
    md = max((x.denominator for x in vec_q if x != 0), default=1)
    nnz = sum(1 for x in vec_q if x != 0)
    ok = (105 * s2) > (4 * s1)
    mark = "PASS" if ok else "fail"
    print(f"  tol=10^-{tol_exp:>2}  nnz={nnz:>2}  max_den={md:>16}  "
          f"ratio={float(105*s2/s1):.8f}  slack={float(slack):+.4e}  {mark}  "
          f"({elapsed:.2f}s)")
    if ok and witness is None:
        witness = vec_q
        report = {"tol_exp": tol_exp, "max_den": md, "nnz": nnz,
                  "s1": s1, "s2": s2, "slack": slack}
        # Keep going one or two more steps in case smaller tol gives smaller md
        # (rare but possible due to convergent jumps); however since tol shrinks
        # monotonically, max_den only grows, so we can stop.
        break

assert witness is not None, "no PASS encountered; tighten denom_limits"

# ----------------------------------------------------------------------
# 4. Summary.
# ----------------------------------------------------------------------
print()
print("=" * 64)
print("Witness vector found.")
print(f"  rationalize tol         = 10^-{report['tol_exp']}")
print(f"  non-zero entries        = {report['nnz']} / {DIM}")
print(f"  max v_i.denominator     = {report['max_den']}  "
      f"(~{math.log10(report['max_den']):.1f} decimal digits, "
      f"{report['max_den'].bit_length()} bits)")
print(f"  v^T M1 v > 0            : verified")
print(f"  105 * v^T M2 v > 4 v^T M1 v : verified")
print(f"  slack = (105 s2 - 4 s1) / s1 ≈ {float(report['slack']):.6e}")
print(f"  (Mathematica notebook reports ratio − 4 ≈ 2.0698 × 10⁻³.)")
print("=" * 64)

# ----------------------------------------------------------------------
# 5. Emit Rocq source.
# ----------------------------------------------------------------------
def z_lit(n: int) -> str:
    n = int(n)
    if n >= 0:
        return f"{n}%Z"
    return f"(-{-n})%Z"

pairs_lines = []
for i, x in enumerate(witness):
    p, q = x.numerator, x.denominator
    assert gcd(abs(p), q) == 1
    assert q > 0
    suffix = " ;" if i + 1 < DIM else ""
    pairs_lines.append(f"  ({z_lit(p)}, {z_lit(q)}){suffix}")
pairs_block = "\n".join(pairs_lines)
slack_float = float(report["slack"])

src = f"""(* ============================================================== *)
(* AUTOGENERATED by python/build_quad_witness.py — do not edit.   *)
(* Maynard `M_{{105}} > 4` Rayleigh-quotient witness vector.        *)
(*                                                                  *)
(* The pair (M1_int, M2_int) is shipped by theories/S1/Witness.v.   *)
(* This file ships a rational vector v in Q^42 such that             *)
(*    105 * v^T M2 v  >  4 * v^T M1 v       and   v^T M1 v > 0,      *)
(* both inequalities verifiable by a single exact integer compare.   *)
(*                                                                  *)
(* Provenance:                                                      *)
(*   - top right eigenvector of M1^{{-1}} M2 from acb_mat.eig at     *)
(*     {PREC}-bit precision, phase-aligned (largest entry positive real)*)
(*   - Mathematica-style absolute-tolerance Rationalize with         *)
(*     tol = 10^-{report['tol_exp']} (continued-fraction convergents).         *)
(*                                                                  *)
(* Verification statistics (all exact over Q):                      *)
(*   non-zero entries          = {report['nnz']} / 42                          *)
(*   max v_i.denominator       = {report['max_den']}            *)
(*                              (~{math.log10(report['max_den']):.1f} dec digits, {report['max_den'].bit_length()} bits)              *)
(*   v^T M1 v > 0              : verified                            *)
(*   slack  = (105*v^T M2 v - 4*v^T M1 v) / v^T M1 v                *)
(*          ≈ {slack_float:+.6e}                                          *)
(*                                                                  *)
(* The 42 entries are listed in the same row/column order as the    *)
(* MaynardBasis.maynard_basis enumeration (pinned by                 *)
(* maynard_basis_eq_witness in Witness.v).                           *)
(*                                                                  *)
(* Note: the eigenvector spans ~14 decimal orders of magnitude       *)
(* (smallest non-zero |v_i| ≈ 1e-14 vs. largest ≈ 1), which lower-    *)
(* bounds the denominator size.  This matches the ill-conditioning   *)
(* of M1; truncating small components destroys the inequality.       *)
(* ============================================================== *)

From Stdlib Require Import ZArith List.
Import ListNotations.
Open Scope Z_scope.

(* v_witness[i] = (num_i, den_i), with gcd(|num_i|, den_i) = 1 and den_i > 0. *)
Definition v_witness : list (Z * Z) :=
  [
{pairs_block}
  ].
"""

OUT.parent.mkdir(parents=True, exist_ok=True)
OUT.write_text(src)
print(f"Wrote {OUT}  ({OUT.stat().st_size:,} bytes)", flush=True)
print(f"Entries: {len(witness)}", flush=True)
