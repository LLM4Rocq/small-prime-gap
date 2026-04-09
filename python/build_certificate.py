"""
Build the full Maynard λ>4 certificate that the Rocq side will consume.

Pipeline:
  1. Load (or rebuild) M1, M2 ∈ Q^{42×42} from the notebook formulas.
  2. Sanity-check a handful of entries against closed-form Beta integrals.
  3. Clear denominators: emit M1_int, M2_int : list[list[int]] and a single
     scalar D such that M1[i][j] = M1_int[i][j] / D, same for M2.
  4. Form A = M1^{-1} M2 in fmpq_mat, compute q(x) = char_poly(A).
  5. Clear denominators of q to get Q : Z[x] of degree 42.
  6. Compute the Brown-Traub subresultant PRS chain of (Q, Q'), with
     a per-step audit (delta_i, psi_i, beta_i) so the Rocq side can
     verify each step exactly.
  7. Compute sign vectors at x0 = 4/105 and at +infinity, and the
     variation counts V(x0), V(+inf), and assert
     V(x0) − V(+inf) ≥ 1.
  8. Cross-check the eigenvalue with arb_mat at 256-bit precision.
  9. Write everything to certificate.json.
 10. Also dump the heavy chain to certificate_chain.json so the small
     metadata file is greppable.

The emitter is *deterministic*: re-running on the same machine produces
byte-identical output (up to JSON key order, which we lock).

Run with:   python python/build_certificate.py
"""
from __future__ import annotations
import json, math, os, pickle, sys, time
from fractions import Fraction
from functools import reduce
from math import lcm
from pathlib import Path

# Brown-Traub PRS coefficients hit ~100 kbit ⇒ ~30 000 decimal digits.
sys.set_int_max_str_digits(1_000_000)

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

# We import the matrix builders from the existing flint_probe.py.  Doing so
# triggers its module-level code, which is fine the first time but slow on
# re-runs (90 s for prime_gram).  We use the cached pickle when present.
CACHE = ROOT / "m1m2.pkl"

if not CACHE.exists():
    print("[1/10] Building M1, M2 (no cache, ~90 s)…", flush=True)
    # Importing flint_probe.py runs prime_gram automatically and writes the cache.
    import flint_probe as _  # noqa: F401
else:
    print("[1/10] Loading cached M1, M2…", flush=True)

with open(CACHE, "rb") as f:
    M1_rat, M2_rat = pickle.load(f)
DIM = len(M1_rat)
assert DIM == 42, DIM
assert all(len(row) == DIM for row in M1_rat) and all(len(row) == DIM for row in M2_rat)

# ----------------------------------------------------------------------
# 2. Hand-checked sanity tests (closed-form Beta integrals).
# ----------------------------------------------------------------------
print("[2/10] Sanity-checking against closed-form integrals…", flush=True)

# Mathematica xExponents/yExponents for n=5, basis ordering pinned in flint_probe.
# We re-derive locally to avoid re-importing flint_probe.
def _xExponents(n):
    S = []
    for i in range(1, n + 2):
        tmp = [2 * j for j in range(1, i + 1)]
        S.extend([t - 2 for t in tmp])
        S.extend([t - 1 for t in tmp])
    return S

def _yExponents(n):
    S = []
    for i in range(0, n + 1):
        tmp = list(reversed(range(1, i + 1))) + [0]
        S.extend(tmp)
        S.extend(tmp)
    return S

K = 105
N5 = 5
Xexp = _xExponents(N5)
Yexp = _yExponents(N5)
BASIS = list(zip(Xexp, Yexp))
assert len(BASIS) == DIM
assert BASIS[0] == (0, 0)
assert BASIS[1] == (1, 0)
assert BASIS[2] == (0, 1)

# M1[i,j] = ∫_{Δ_K} x^{b_i+b_j} y^{c_i+c_j} dt
# closed-form: (b!/(K+b+2c)!) * G_{c,2}(K), with b = b_i+b_j, c = c_i+c_j.
def G_n_2(n: int, k: int) -> Fraction:
    """G_{n,2}(k), Maynard's closed-form polynomial in k, evaluated at k."""
    if n == 0:
        return Fraction(1)
    out = Fraction(k) * math.factorial(2 * n)
    for i in range(1, n):
        # sum over compositions a_1+…+a_i ≤ n-1, a_j ≥ 1.
        def _enum(prefix, idx, remaining):
            if idx == i:
                yield tuple(prefix)
                return
            slots = i - idx
            upper = remaining - (slots - 1)
            for a in range(1, upper + 1):
                prefix.append(a)
                yield from _enum(prefix, idx + 1, remaining - a)
                prefix.pop()
        inner = Fraction(0)
        for tup in _enum([], 0, n - 1):
            s = sum(tup)
            cff = math.factorial(n)
            for a in tup:
                cff *= math.factorial(2 * a) // math.factorial(a)
            cff *= math.factorial(2 * (n - s)) // math.factorial(n - s)
            inner += Fraction(cff)
        bcoef = Fraction(1)
        for j in range(i + 1):
            bcoef *= Fraction(k - j, j + 1)
        out += bcoef * inner
    return out

# Spot checks of M1.
checks = [
    ((0, 0), Fraction(1, math.factorial(105))),                         # F=1
    ((0, 1), Fraction(1, math.factorial(106))),                         # F·F = x
    ((0, 2), Fraction(G_n_2(1, 105), math.factorial(107))),             # F·F = y, G_{1,2}=2k=210
    ((1, 1), Fraction(math.factorial(2), math.factorial(107))),         # F·F = x^2
]
for (i, j), expected in checks:
    actual = M1_rat[i][j]
    assert actual == expected, f"M1[{i}][{j}] mismatch: {actual} != {expected}"
print(f"  ✓ {len(checks)} M1 entries match closed-form integrals")

# Spot check M2[0][0]: F=1, J_K(1) = ∫_{Δ_{K-1}} (1-Σ' t)^2 dt' = 2/(K+1)!
assert M2_rat[0][0] == Fraction(2, math.factorial(106)), \
    f"M2[0][0]: {M2_rat[0][0]} != 2/106!"
print("  ✓ M2[0][0] = 2/106! matches closed form")

# Symmetry.
for i in range(DIM):
    for j in range(i + 1, DIM):
        assert M1_rat[i][j] == M1_rat[j][i], (i, j)
        assert M2_rat[i][j] == M2_rat[j][i], (i, j)
print("  ✓ M1 and M2 symmetric")

# ----------------------------------------------------------------------
# 3. Integer-clear M1, M2.
# ----------------------------------------------------------------------
print("[3/10] Integer-clearing M1, M2…", flush=True)

def common_denom(M):
    return reduce(lcm, (x.denominator for row in M for x in row), 1)

def clear(M, D):
    return [[(x.numerator * (D // x.denominator)) for x in row] for row in M]

D_M1 = common_denom(M1_rat)
D_M2 = common_denom(M2_rat)
M1_int = clear(M1_rat, D_M1)
M2_int = clear(M2_rat, D_M2)
print(f"  D_M1 bit-length = {D_M1.bit_length()}")
print(f"  D_M2 bit-length = {D_M2.bit_length()}")
max_M1 = max(abs(x).bit_length() for row in M1_int for x in row)
max_M2 = max(abs(x).bit_length() for row in M2_int for x in row)
print(f"  M1_int max entry bits = {max_M1}")
print(f"  M2_int max entry bits = {max_M2}")

# ----------------------------------------------------------------------
# 4. Char poly via fmpq_mat.charpoly().
# ----------------------------------------------------------------------
print("[4/10] Computing A = M1^{-1} M2 and q(x) = char_poly(A)…", flush=True)
from flint import fmpq, fmpz, fmpq_mat, fmpq_poly, fmpz_poly, arb_mat, ctx as flint_ctx

def to_fmpq_mat(G):
    return fmpq_mat(DIM, DIM, [fmpq(x.numerator, x.denominator)
                               for row in G for x in row])

M1f = to_fmpq_mat(M1_rat)
M2f = to_fmpq_mat(M2_rat)
A = M1f.inv() * M2f
q = A.charpoly()  # fmpq_poly
assert q.degree() == DIM

# 5. Clear denominators of q to get Q ∈ Z[x].
print("[5/10] Clearing denominators of q(x)…", flush=True)
coefs = [q[i] for i in range(q.degree() + 1)]  # low to high
nums = [int(fmpq(c).p) for c in coefs]
dens = [int(fmpq(c).q) for c in coefs]
D_q = reduce(lcm, dens, 1)
Q_low_to_high = [nums[i] * (D_q // dens[i]) for i in range(len(coefs))]
Q_high_to_low = list(reversed(Q_low_to_high))
max_Q = max(abs(c).bit_length() for c in Q_low_to_high)
print(f"  D_q bit-length = {D_q.bit_length()}")
print(f"  Q max coef bit-length = {max_Q}")

Q_poly = fmpz_poly(Q_low_to_high)
Qprime_poly = Q_poly.derivative()
Qprime_low_to_high = [int(Qprime_poly[i]) for i in range(Qprime_poly.degree() + 1)]

# ----------------------------------------------------------------------
# 6. Brown-Traub subresultant PRS, with audit trail.
# ----------------------------------------------------------------------
print("[6/10] Brown-Traub subresultant PRS with audit…", flush=True)

def prem_int(A_p, B_p):
    """Pseudo-remainder of A by B as Python lists (low-to-high).
    Returns R such that lc(B)^(deg A - deg B + 1) * A = Q*B + R, deg R < deg B.
    Standard Knuth pseudo-division algorithm; stays in Z when inputs are in Z.
    """
    A_p = list(A_p)
    B_p = list(B_p)
    while A_p and A_p[-1] == 0:
        A_p.pop()
    while B_p and B_p[-1] == 0:
        B_p.pop()
    if not B_p:
        raise ZeroDivisionError
    m = len(A_p) - 1
    n = len(B_p) - 1
    if m < n:
        return A_p
    d = m - n + 1
    lcB = B_p[-1]
    A_p = [c * (lcB ** d) for c in A_p]
    while len(A_p) - 1 >= n:
        lcA = A_p[-1]
        if lcA == 0:
            A_p.pop()
            continue
        q_term, rem = divmod(lcA, lcB)
        assert rem == 0, "pseudo-div leading not exact (bug in d)"
        shift = (len(A_p) - 1) - n
        for i, bc in enumerate(B_p):
            A_p[shift + i] -= q_term * bc
        # Strip trailing zeros that may have appeared.
        while A_p and A_p[-1] == 0:
            A_p.pop()
    return A_p

def deg_of(p):
    p = list(p)
    while p and p[-1] == 0:
        p.pop()
    return len(p) - 1

def lc_of(p):
    p = list(p)
    while p and p[-1] == 0:
        p.pop()
    return p[-1] if p else 0

def divexact_list(p, c):
    out = []
    for x in p:
        q, r = divmod(x, c)
        assert r == 0, f"divexact not exact: {x}/{c}"
        out.append(q)
    return out

def subres_prs_audited(F0_p, F1_p):
    """Brown-Traub subresultant PRS.

    Returns (chain, betas) where:
      chain = [F_0, F_1, F_2, ..., F_n] (a list of polynomials, lowest deg last),
      betas = [β_1, β_2, ..., β_{n-1}]   (one β per step i ≥ 1),
    such that for every i ≥ 1:  prem(F_{i-1}, F_i) = β_i · F_{i+1} (exact).
    Length invariant:  len(betas) = len(chain) − 2.
    """
    chain = [list(F0_p), list(F1_p)]
    betas = []
    d_prev = deg_of(chain[0]) - deg_of(chain[1])
    psi = -1
    beta = (-1) ** (d_prev + 1)        # β_1
    step = 1
    while deg_of(chain[-1]) > 0:
        Fi_1 = chain[-2]
        Fi   = chain[-1]
        R = prem_int(Fi_1, Fi)
        Fnext = divexact_list(R, beta)  # this divisor is the current β = β_step
        chain.append(Fnext)
        betas.append(beta)              # record β_step
        # Update ψ and β for the *next* iteration (will become β_{step+1}).
        d = deg_of(Fi) - deg_of(Fnext)
        lc_Fi = lc_of(Fi)
        if d_prev == 0:
            psi_new = psi
        elif d_prev == 1:
            psi_new = -lc_Fi
        else:
            num   = (-lc_Fi) ** d_prev
            denom = psi ** (d_prev - 1)
            q2, rem2 = divmod(num, denom)
            assert rem2 == 0, f"ψ update not exact at step {step}"
            psi_new = q2
        psi = psi_new
        beta = -lc_Fi * (psi ** d)
        d_prev = d
        step += 1
        if step > 100:
            raise RuntimeError("runaway PRS")
    return chain, betas

t0 = time.time()
chain, betas = subres_prs_audited(Q_low_to_high, Qprime_low_to_high)
print(f"  Brown-Traub done in {time.time() - t0:.2f} s; chain length = {len(chain)}")
assert len(betas) == len(chain) - 2

# Self-check: ∀ i ≥ 1, prem(chain[i-1], chain[i]) == betas[i-1] * chain[i+1].
print("[6b/10] Verifying every PRS step in pure Python…", flush=True)
def pad(p, n):
    return list(p) + [0] * (n - len(p))
for i in range(1, len(chain) - 1):
    R     = prem_int(chain[i - 1], chain[i])
    beta_i = betas[i - 1]
    expected = [c * beta_i for c in chain[i + 1]]
    n = max(len(R), len(expected))
    assert pad(R, n) == pad(expected, n), \
        f"PRS audit FAILED at step {i}"
print(f"  ✓ all {len(chain) - 2} PRS steps verified")

# ----------------------------------------------------------------------
# 7. Sign vectors at 4/105 and at +∞.
# ----------------------------------------------------------------------
print("[7/10] Computing sign vectors at 4/105 and +∞…", flush=True)
# Eval poly p (low-to-high coefs, in Z) at the rational a/b: returns sign of p(a/b),
# computed exactly via b^deg * p(a/b) = sum c_i * a^i * b^(deg-i)  ∈ Z.
def sign_at_rational(p_int, a_num, a_den):
    p = list(p_int)
    while p and p[-1] == 0:
        p.pop()
    if not p:
        return 0
    deg = len(p) - 1
    val = 0
    for i, c in enumerate(p):
        val += c * (a_num ** i) * (a_den ** (deg - i))
    if val == 0:
        return 0
    return 1 if val > 0 else -1

def sign_at_inf(p_int):
    p = list(p_int)
    while p and p[-1] == 0:
        p.pop()
    if not p:
        return 0
    return 1 if p[-1] > 0 else -1

THRESH_NUM, THRESH_DEN = 4, 105
signs_at_x0 = [sign_at_rational(p, THRESH_NUM, THRESH_DEN) for p in chain]
signs_at_inf = [sign_at_inf(p) for p in chain]

def variation(signs):
    v = 0
    last = 0
    for s in signs:
        if s == 0:
            continue
        if last != 0 and s != last:
            v += 1
        last = s
    return v

V_x0 = variation(signs_at_x0)
V_inf = variation(signs_at_inf)
print(f"  V(4/105) = {V_x0}")
print(f"  V(+inf)  = {V_inf}")
print(f"  V(4/105) − V(+inf) = {V_x0 - V_inf}  (must be ≥ 1)")
assert V_x0 - V_inf >= 1, "Sturm count failed: no real eigenvalue > 4/105 detected"

# ----------------------------------------------------------------------
# 8. Cross-check with Arb at 256-bit.
# ----------------------------------------------------------------------
print("[8/10] Arb 256-bit eigenvalue cross-check…", flush=True)
flint_ctx.prec = 256
Ar = arb_mat(A)
eigs = Ar.eig(algorithm="approx")
real_parts = sorted((float(complex(e).real) for e in eigs), reverse=True)
top = real_parts[0]
k_top = K * top
print(f"  top real eig of A = {top}")
print(f"  k · top = {k_top}  (Maynard reports 4.00206976193804713…)")
assert abs(k_top - 4.00206976193804713) < 1e-12, "Arb cross-check failed"

# ----------------------------------------------------------------------
# 9. Emit certificate.json (small) and certificate_chain.json (heavy).
# ----------------------------------------------------------------------
print("[9/10] Writing certificate files…", flush=True)
out_meta = {
    "schema_version": 1,
    "dim": DIM,
    "k": K,
    "deg_max": 11,
    "basis": [list(b) for b in BASIS],
    "D_M1": str(D_M1),
    "D_M2": str(D_M2),
    "M1_int": [[str(x) for x in row] for row in M1_int],
    "M2_int": [[str(x) for x in row] for row in M2_int],
    "charpoly": {
        "common_den": str(D_q),
        "deg": q.degree(),
        "coefs_low_to_high": [str(c) for c in Q_low_to_high],
        "max_coef_bits": max_Q,
    },
    "threshold_x0": {"num": THRESH_NUM, "den": THRESH_DEN},
    "signs_at_x0": signs_at_x0,
    "signs_at_inf": signs_at_inf,
    "V_x0": V_x0,
    "V_inf": V_inf,
    "roots_in_x0_inf": V_x0 - V_inf,
    "arb_top_eig": repr(top),
    "arb_k_times_top": repr(k_top),
    "chain_summary": [
        {"i": i, "deg": deg_of(p),
         "max_coef_bits": max((abs(c).bit_length() for c in p), default=0)}
        for i, p in enumerate(chain)
    ],
}

out_chain = {
    "schema_version": 1,
    "dim": DIM,
    "chain_len": len(chain),
    "sturm_chain": [
        {"i": i, "deg": deg_of(p), "coefs_low_to_high": [str(c) for c in p]}
        for i, p in enumerate(chain)
    ],
    "betas": [str(b) for b in betas],  # one per step i ≥ 1; len = chain_len - 2
}

CERT = ROOT / "certificate.json"
CERT_CHAIN = ROOT / "certificate_chain.json"
with open(CERT, "w") as f:
    json.dump(out_meta, f, indent=2, sort_keys=False)
with open(CERT_CHAIN, "w") as f:
    json.dump(out_chain, f, sort_keys=False)
print(f"  wrote {CERT}  ({CERT.stat().st_size:,} bytes)")
print(f"  wrote {CERT_CHAIN}  ({CERT_CHAIN.stat().st_size:,} bytes)")

# ----------------------------------------------------------------------
# 10. Final summary.
# ----------------------------------------------------------------------
print("[10/10] Done.", flush=True)
print()
print("=" * 60)
print(f"  dim                  = {DIM}")
print(f"  k                    = {K}")
print(f"  charpoly degree      = {q.degree()}")
print(f"  charpoly max bits    = {max_Q}")
print(f"  D_M1 bits            = {D_M1.bit_length()}")
print(f"  D_M2 bits            = {D_M2.bit_length()}")
print(f"  D_q bits             = {D_q.bit_length()}")
print(f"  Brown-Traub steps    = {len(chain) - 1}")
print(f"  terminal coef bits   = {max(abs(c).bit_length() for c in chain[-1])}")
print(f"  V(4/105) − V(+inf)   = {V_x0 - V_inf}")
print(f"  Arb k·top eig        = {k_top}")
print("=" * 60)
print("Certificate is consistent.  M_{105} > 4 verified by FLINT.")
