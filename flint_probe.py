"""
Probe script: builds M1, M2 (the 42x42 rational Gram matrices from Maynard's
notebook_reconstructed.md), then runs FLINT to compute the characteristic
polynomial of A = M1^-1 M2, a Sturm chain, and sign-variation counts at
x = 4 and x = +infty.
"""
import time, json, math, sys
from fractions import Fraction
from flint import fmpq, fmpz, fmpq_mat, fmpz_mat, fmpq_poly, fmpz_poly, arb_mat, arb, ctx

# ------------------------------------------------------------------
# 1. Re-implementation of the Mathematica helpers.
# ------------------------------------------------------------------

def factorial(n): return math.factorial(n)

def Cff_rat(lst, tot):
    """Cff from notebook: (prod_i (2 a_i)!/a_i!) * tot! * (2(tot-sum))!/(tot-sum)!"""
    p = Fraction(1)
    for a in lst:
        p *= Fraction(factorial(2*a), factorial(a))
    s = sum(lst)
    p *= factorial(tot)
    p *= Fraction(factorial(2*(tot - s)), factorial(tot - s))
    return p

def enumerate_bounds(length, tot):
    """Enumerate tuples (a_1,...,a_length) of positive ints with sum <= tot-1
       (matching Bnd/Sum in Mathematica)."""
    out = []
    def rec(prefix, idx, remaining):
        # remaining = tot - 1 - sum_{j<idx} a_j ; we need a_idx in [1, remaining - (length - idx)]
        if idx == length:
            out.append(tuple(prefix))
            return
        slots_left = length - idx      # including current
        upper = remaining - (slots_left - 1)
        if upper < 1:
            return
        for ai in range(1, upper + 1):
            prefix.append(ai)
            rec(prefix, idx + 1, remaining - ai)
            prefix.pop()
    rec([], 0, tot - 1)
    return out

def Poly_at_k(n, k):
    """G_{n,2}(k) at integer k, returning Fraction."""
    if n == 0:
        return Fraction(1)
    X = Fraction(k) * factorial(2*n)
    for i in range(1, n):  # i = 1..n-1
        inner = Fraction(0)
        for lst in enumerate_bounds(i, n):
            inner += Cff_rat(list(lst), n)
        # Binomial(k, i+1)
        b = Fraction(1)
        for j in range(i+1):
            b *= Fraction(k - j, j + 1)
        X += b * inner
    return X

K = 105
Polys = [Poly_at_k(n, K) for n in range(12)]  # G_{0,2}..G_{11,2} as rationals

# Build the xExponents, yExponents, p[n=5] monomials: list of (b, c) with b+2c <= 11
# mimicking the Mathematica enumeration order.
def xExponents(n):
    S = []
    for i in range(1, n+2):  # i=1..n+1
        tmp = [2*j for j in range(1, i+1)]
        S.extend([t-2 for t in tmp])
        S.extend([t-1 for t in tmp])
        # Above gives interleaving; actual MMA code: Join[S, tmp-2, tmp-1]
    return S

def xExponents_mma(n):
    # exact MMA transcription: for i in 1..n+1, tmp=2*Range[i]; S = Join[S, tmp-2, tmp-1]
    S = []
    for i in range(1, n+2):
        tmp = [2*j for j in range(1, i+1)]
        S.extend([t-2 for t in tmp])
        S.extend([t-1 for t in tmp])
    return S

def yExponents_mma(n):
    # for i in 0..n, tmp = Append[Reverse[Range[i]], 0]; S = Join[S, tmp, tmp]
    S = []
    for i in range(0, n+1):
        tmp = list(reversed(range(1, i+1))) + [0]
        S.extend(tmp)
        S.extend(tmp)
    return S

N5 = 5
Xexp = xExponents_mma(N5)
Yexp = yExponents_mma(N5)
assert len(Xexp) == len(Yexp)
M = len(Xexp)
print(f"# monomials (should be 42): {M}", flush=True)
assert M == 42, f"expected 42 got {M}"

# ConstCalc: for polynomial F(x,y) = sum_i A_i * x^{Xexp[i]} * y^{Yexp[i]},
# we want the matrix Q1 such that F^T Q1 F = \int_R_k F^2 dt.
# For monomial pair (x^{b1} y^{c1}, x^{b2} y^{c2}):
#   product is x^{b1+b2} y^{c1+c2},
#   integral is (b! / (k+b+2c)!) * G_{c,2}(k)  where b=b1+b2, c=c1+c2.
# Note: matrix entry (i,j) = (coefficient of A_i A_j in F^2)/2 contribution, etc.
# We build the SYMMETRIC gram matrix directly:
#   M1[i,j] = integral_{R_k} (x^{b_i} y^{c_i}) * (x^{b_j} y^{c_j}) dt.

def const_gram():
    G = [[Fraction(0)]*M for _ in range(M)]
    for i in range(M):
        for j in range(M):
            b = Xexp[i] + Xexp[j]
            c = Yexp[i] + Yexp[j]
            val = Fraction(factorial(b), factorial(K + b + 2*c)) * Polys[c]
            G[i][j] = val
    return G

# PrmeCalc: first applies eq 7.8 in t_1:
#   \int_0^{1-sum'} (1-sum'-t_1)^b ( (sum')^2 + t_1^2 )^c dt_1
#   = sum_{cp=0..c} C(c,cp) b! (2c-2cp)! / (b+2c-2cp+1)! (1-sum')^{b+2c-2cp+1} (sum')^{2 cp}.
# Wait: careful -- in MMA it's y^cp (not (sum')^{2 cp}). The substitution x -> 1-sum', y -> (sum')^2 so y^cp has y=sum_{i>=2} t_i^2, and the 1D integral of t_1 introduces (sum')^{2 cp}. But in the reconstructed code the new polynomial written is in terms of new formal variables x' := 1-sum_{i>=2} t_i, y' := sum_{i>=2} t_i^2 (treated same as x,y). But the prime formula uses (sum')^{2 cp} = (1-x')^{2 cp}, not y'^cp. Let me re-read...
# Actually the MMA code writes y^cp in the 1D integral formula -- which only works if y represents (sum t_i)^2 (single squared), not sum t_i^2. Hmm.
# Re-reading the reconstructed comment: y := sum t_i^2 originally. The 1D integral wrt t_1 yields (sum_{i>=2} t_i)^{2 cp}, not y^{cp}. But MMA code writes y^cp. This might be an error in the reconstruction comment, OR y might actually mean something else.
# Since we're doing a numerical *probe* (to get coefficient sizes), it's acceptable to just use what the MMA code literally does. Any error here would produce a matrix that still has the right *structure* (42x42 rational), so coefficient-size estimates and pipeline design remain valid.
# IMPORTANT NOTE: If the spectrum doesn't match ~4.002 we log it, but proceed.

def binom(n, k):
    return Fraction(math.comb(n, k))

def prime_gram():
    # First transform each monomial x^b y^c into a polynomial in x, y using eq 7.8.
    # Result: each original monomial (b,c) -> list of (b', c', coef) where
    #   b' = b + 2c - 2 cp + 1, c' = cp, coef = C(c,cp) b!(2c-2cp)!/(b+2c-2cp+1)!.
    transformed = []
    for b, c in zip(Xexp, Yexp):
        terms = []
        for cp in range(c + 1):
            bp = b + 2*c - 2*cp + 1
            co = binom(c, cp) * Fraction(factorial(b) * factorial(2*c - 2*cp), factorial(b + 2*c - 2*cp + 1))
            terms.append((bp, cp, co))
        transformed.append(terms)

    # Now the new ansatz is sum_i A_i * P_i(x, y) where P_i = sum_cp co * x^bp y^cp.
    # ConstCalc at level k-1 for F^2 = sum_{i,j} A_i A_j P_i P_j.
    # Gram entry (i,j) = integral of P_i * P_j = sum_{cp1,cp2} co1 co2 * monomial_integral(bp1+bp2, cp1+cp2)
    # with the (k-1)-level formula.
    Kp = K - 1
    Polys_p = [Poly_at_k(n, Kp) for n in range(24)]  # need up to c=22
    def mon_int(b, c):
        return Fraction(factorial(b), factorial(Kp + b + 2*c)) * Polys_p[c]
    G = [[Fraction(0)]*M for _ in range(M)]
    for i in range(M):
        for j in range(M):
            s = Fraction(0)
            for (b1, c1, co1) in transformed[i]:
                for (b2, c2, co2) in transformed[j]:
                    s += co1 * co2 * mon_int(b1 + b2, c1 + c2)
            G[i][j] = s
    return G

import pickle, os
CACHE = "/home/rocq/prime_gap/m1m2.pkl"
if os.path.exists(CACHE):
    with open(CACHE, "rb") as f:
        M1_rat, M2_rat = pickle.load(f)
    print("loaded cached M1, M2", flush=True)
else:
    print("Building M1 (ConstCalc gram) ...", flush=True)
    t0 = time.time()
    M1_rat = const_gram()
    print(f"  done in {time.time()-t0:.2f}s", flush=True)

    print("Building M2 (PrmeCalc gram) ...", flush=True)
    t0 = time.time()
    M2_rat = prime_gram()
    print(f"  done in {time.time()-t0:.2f}s", flush=True)
    with open(CACHE, "wb") as f:
        pickle.dump((M1_rat, M2_rat), f)

# Sanity: M1, M2 symmetric?
for i in range(M):
    for j in range(i+1, M):
        assert M1_rat[i][j] == M1_rat[j][i], (i,j)
        assert M2_rat[i][j] == M2_rat[j][i], (i,j)
print("symmetry OK", flush=True)

# Convert to fmpq_mat.
def to_fmpq_mat(G):
    return fmpq_mat(M, M, [fmpq(x.numerator, x.denominator) for row in G for x in row])

M1f = to_fmpq_mat(M1_rat)
M2f = to_fmpq_mat(M2_rat)

# Quick Rayleigh sanity using a random integer vector -- we just want to see the
# *top* eigenvalue is in the right ballpark (~4) without trusting floats.
# Skip for now, do charpoly directly.

print("Computing A = M1^{-1} M2 ...", flush=True)
t0 = time.time()
A = M1f.inv() * M2f
print(f"  done in {time.time()-t0:.2f}s", flush=True)

print("Computing charpoly q(x) of A ...", flush=True)
t0 = time.time()
q = A.charpoly()   # fmpq_poly
print(f"  done in {time.time()-t0:.2f}s; degree = {q.degree()}", flush=True)

# Clear denominators: q = (1/D) * Q where Q in Z[x].
coefs = [q[i] for i in range(q.degree() + 1)]
nums = [fmpq(c).p for c in coefs]
dens = [fmpq(c).q for c in coefs]
from math import lcm
common_den = 1
for d in dens:
    common_den = lcm(common_den, int(d))
Q_int = [int(c * common_den) for c in coefs]  # fmpq supports *int via fmpq math... careful
# redo safely:
Q_int = [(int(nums[i]) * (common_den // int(dens[i]))) for i in range(len(coefs))]

max_bits = max((abs(c).bit_length() for c in Q_int), default=0)
print(f"q(x) common denominator bits: {common_den.bit_length()}", flush=True)
print(f"q(x) integer coefs max bits:  {max_bits}", flush=True)
print(f"q(x) integer coefs bit sizes: {[abs(c).bit_length() for c in Q_int]}", flush=True)

# Save for the next stage -- compute Sturm chain on fmpz_poly Q (scaled q).
# Build Q as fmpz_poly
Q = fmpz_poly(Q_int)   # coefs low->high

# Also make q' as fmpz_poly (derivative of Q; since multiplying q by common_den doesn't change roots)
Qd = Q.derivative()

# Check gcd(Q, Q')
print("gcd(Q, Q') ...", flush=True)
t0 = time.time()
g = Q.gcd(Qd)
print(f"  deg gcd = {g.degree()}  (should be 0 for simple spectrum) ; {time.time()-t0:.2f}s", flush=True)

if g.degree() != 0:
    print("!!! gcd has positive degree, multiple roots present", flush=True)

# Naive Sturm chain via fmpq_poly (rational division)
# qrat_0 = q (as fmpq_poly for rem), qrat_1 = q' (also fmpq_poly)
def to_fmpq_poly(fmpz_p):
    return fmpq_poly([fmpq(fmpz_p[i], 1) for i in range(fmpz_p.degree() + 1)])

q0 = to_fmpq_poly(Q)
q1 = to_fmpq_poly(Qd)

chain = [q0, q1]
print("Building Sturm chain (naive fmpq_poly rem) ...", flush=True)
t0 = time.time()
while chain[-1].degree() > 0:
    a, b = chain[-2], chain[-1]
    # remainder of a divided by b
    rem = a % b
    if rem == fmpq_poly([0]):
        print("  zero remainder -> repeated roots", flush=True)
        break
    nxt = -rem
    chain.append(nxt)
print(f"  chain length = {len(chain)}; {time.time()-t0:.2f}s", flush=True)

# Report bit sizes of each polynomial in the chain
def poly_bit_stats(p):
    # p is fmpq_poly
    bits_num = 0
    bits_den = 0
    deg = p.degree()
    cs = [p[i] for i in range(deg + 1)]
    from math import lcm
    d = 1
    for c in cs:
        d = lcm(d, int(fmpq(c).q))
    nums = [int(fmpq(c).p) * (d // int(fmpq(c).q)) for c in cs]
    mb = max((abs(n).bit_length() for n in nums), default=0)
    return deg, mb, d.bit_length()

print("chain stats (i, deg, max int-coef bits after clearing per-poly den, den bits)", flush=True)
for i, p in enumerate(chain):
    deg, mb, db = poly_bit_stats(p)
    print(f"  [{i}] deg={deg} max_coef_bits={mb} den_bits={db}", flush=True)

# The claim M_k > 4 where M_k = k * top_eig(A). So the generalized eigenvalue
# itself clears 4/k = 4/105. We therefore need the Sturm count at threshold
# x0 = 4/105, not 4.
def sign_at(p, x):
    # p is fmpq_poly, x is fmpq
    val = p(x)
    if val == 0:
        return 0
    return 1 if int(fmpq(val).p) > 0 else -1

def sign_inf(p):
    deg = p.degree()
    lc = p[deg]
    if lc == 0:
        return 0
    return 1 if int(fmpq(lc).p) > 0 else -1

X0 = fmpq(4, 105)
s_x0 = [sign_at(p, X0) for p in chain]
sinf = [sign_inf(p)    for p in chain]

def variation(signs):
    v = 0
    last = 0
    for s in signs:
        if s == 0: continue
        if last != 0 and s != last:
            v += 1
        last = s
    return v

V_x0 = variation(s_x0)
Vinf = variation(sinf)
print(f"signs at 4/105:  {s_x0}", flush=True)
print(f"signs at +inf:   {sinf}", flush=True)
print(f"V(4/105) = {V_x0}   V(+inf) = {Vinf}   roots in (4/105, +inf) = {V_x0 - Vinf}", flush=True)

# Also sanity-check: top eigenvalue via arb.
import flint as _fl
_fl.ctx.prec = 256
Ar = arb_mat(A)
try:
    eigs = Ar.eig(algorithm="approx")
    reals = [complex(e).real for e in eigs]
    reals.sort(reverse=True)
    print(f"top 3 real parts of eigs of A: {reals[:3]}", flush=True)
    print(f"  so k*top = 105*{reals[0]} = {105*reals[0]}", flush=True)
except Exception as e:
    print(f"arb eig failed: {e}", flush=True)

# Cross-check with arb_mat.eig (if available)
try:
    from flint import arb_mat, arb
    Ar = arb_mat(A)
    # Get eigenvalues as a list of complex intervals
    eigs = Ar.eig(algorithm="approx")  # may not be this API
    print("arb_mat eig sample:", eigs[:5], flush=True)
except Exception as e:
    print(f"arb_mat eig not attempted: {e}", flush=True)

# Emit a skeleton JSON certificate
out = {
    "dim": M,
    "charpoly_q": {
        "common_den": str(common_den),
        "coefs_high_to_low": [str(c) for c in reversed(Q_int)],
        "max_coef_bits": max_bits,
    },
    "sturm_chain_len": len(chain),
    "threshold_x0": "4/105",
    "V_x0": V_x0,
    "V_inf": Vinf,
    "roots_in_x0_inf": V_x0 - Vinf,
    "signs_at_x0": s_x0,
    "signs_at_inf": sinf,
}

# --- Probe the subresultant PRS availability in python-flint on fmpz_poly ---
try:
    attrs = [a for a in dir(fmpz_poly) if 'resul' in a.lower() or 'pseudo' in a.lower() or 'prs' in a.lower()]
    print(f"fmpz_poly subresultant-related attrs: {attrs}", flush=True)
except Exception as e:
    print(f"subresultant probe failed: {e}", flush=True)

try:
    r = Q.resultant(Qd)
    print(f"Q.resultant(Q'): bits = {int(r).bit_length()}", flush=True)
except Exception as e:
    print(f"resultant failed: {e}", flush=True)
with open("/home/rocq/prime_gap/flint_probe.json", "w") as f:
    json.dump(out, f, indent=2)
print("wrote /home/rocq/prime_gap/flint_probe.json", flush=True)
