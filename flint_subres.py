"""
Manual subresultant PRS on Q = q * common_denom (integer polynomial of
degree 42). Goal: bound the bit-size of the Sturm chain when computed
with the Brown-Traub subresultant scheme. python-flint 0.8.0 doesn't
expose a direct subresultant PRS; we roll one.

Algorithm (Brown-Traub / Collins, following Knuth vol. 2, 4.6.1):
  f_0 := P, f_1 := Q           (Q = f_0', for Sturm)
  For i >= 1:
    delta_i = deg f_{i-1} - deg f_i
    psi_1 = -1
    For i >= 2: psi_i = (-lc(f_{i-1}))^{delta_{i-1}} * psi_{i-1}^{1 - delta_{i-1}}
    beta_i = -lc(f_{i-1}) * psi_i^{delta_i}        (i=1: beta_1 = (-1)^{delta_1+1})
    f_{i+1} = prem(f_{i-1}, f_i) / beta_i
  (prem is the polynomial pseudo-remainder.)

  The invariant is that all f_i live in Z[x] with bits growing at most
  *polynomially* in the input coefficient bits (classical bound: each
  coefficient is bounded by ~d * (bit_input) ~ 42 * 1354 = ~57000 bits,
  but in practice much smaller).

We track sign changes rather than sign(b_i) corrections. For the Sturm
sequence we negate at each step if beta_i > 0 (to keep signs consistent
with the "minus remainder" convention). Track parity.
"""
import os, pickle, time, json, math
from flint import fmpz_poly, fmpz

with open("/home/rocq/prime_gap/flint_probe.json") as f:
    probe = json.load(f)

# Reconstruct Q (integer polynomial) from probe
common_den = int(probe["charpoly_q"]["common_den"])
coefs_high_to_low = [int(c) for c in probe["charpoly_q"]["coefs_high_to_low"]]
coefs_low_to_high = list(reversed(coefs_high_to_low))
Q = fmpz_poly(coefs_low_to_high)
print(f"Q degree = {Q.degree()}, max coef bits = {max(abs(c).bit_length() for c in coefs_low_to_high)}")

def prem(A, B):
    """Pseudo-remainder: (lc(B))^{deg A - deg B + 1} * A mod B, stays in Z[x]."""
    if B.degree() < 0:
        raise ZeroDivisionError
    m = A.degree()
    n = B.degree()
    if m < n:
        return A
    d = m - n + 1
    lcB = B[n]
    # Multiply A by lcB^d then do normal polynomial division modulo B, but
    # pseudo-division algorithm: keep reducing leading term.
    A = A * (lcB ** d)
    # Now remainder in Z
    R = fmpz_poly(list(A))  # copy
    while R.degree() >= n:
        # R_lead / B_lead is integer because we pre-multiplied enough.
        lcR = R[R.degree()]
        shift = R.degree() - n
        # subtract (lcR / lcB) * B * x^shift  -- exact since lcB divides lcR
        # Actually classical pseudo-div subtracts (lcR * B - contribution*lcB stuff)
        # Safer: use explicit division of R by B via coefficient loop.
        # We use the basic "long division" form: q = lcR / lcB (integer), then
        # R = R - q * B * x^shift
        q, rem = divmod(int(lcR), int(lcB))
        # if rem != 0, pre-multiplier was insufficient; the initial A * lcB^d
        # is the standard fix -- it gives enough headroom.
        if rem != 0:
            # This shouldn't happen if d was chosen correctly
            raise AssertionError(f"pseudo-div leading doesn't divide: {lcR}/{lcB}")
        term_coefs = [0]*shift + list(B)
        term = fmpz_poly([q * c for c in term_coefs])
        R = R - term
    return R

# Sanity: test prem on small example
P1 = fmpz_poly([1,2,3,4])  # 4x^3 + 3x^2 + 2x + 1
P2 = fmpz_poly([5,6,7])    # 7x^2 + 6x + 5
R = prem(P1, P2)
print(f"sanity prem test: deg = {R.degree()}, coefs = {list(R)}")

# Brown-Traub subresultant PRS
def subres_prs(F0, F1):
    chain = [F0, F1]
    if F1.degree() < 0:
        return chain
    delta_prev = F0.degree() - F1.degree()
    psi = fmpz(-1)
    # beta_1 = (-1)^{delta_1 + 1}
    beta = (-1) ** (delta_prev + 1)
    i = 1
    while chain[-1].degree() > 0:
        Fi_1 = chain[-2]
        Fi   = chain[-1]
        R = prem(Fi_1, Fi)
        if R.degree() < 0:
            break
        # divide R by beta
        coef = list(R)
        q, rem = divmod(int(coef[0]) if coef else 0, int(beta))
        # do exact integer division across all coefs
        new_coefs = []
        for c in coef:
            q, rem = divmod(int(c), int(beta))
            assert rem == 0, f"beta={beta} does not divide coef {c}"
            new_coefs.append(q)
        F_next = fmpz_poly(new_coefs)
        chain.append(F_next)
        # Update psi, beta for next step
        delta = Fi.degree() - F_next.degree()
        lc_Fi = Fi[Fi.degree()]
        # psi_{i+1} = (-lc(Fi))^{delta_prev} * psi^{1-delta_prev}
        # careful: when 1-delta_prev < 0, psi must divide numerator. classical identity.
        num = fmpz((-int(lc_Fi)) ** delta_prev)
        if delta_prev == 0:
            psi_new = psi  # 1 - 0 = 1
        else:
            # psi^{1 - delta_prev} where 1 - delta_prev <= 0
            # so divide num by psi^{delta_prev - 1}
            denom = fmpz(int(psi)) ** (delta_prev - 1)
            q2, rem2 = divmod(int(num), int(denom))
            assert rem2 == 0, f"psi update: {num}/{denom} not exact"
            psi_new = fmpz(q2)
        psi = psi_new
        # beta_{i+1} = -lc(Fi) * psi_{i+1}^{delta}
        beta = fmpz(-int(lc_Fi)) * (fmpz(int(psi)) ** delta)
        beta = int(beta)
        delta_prev = delta
        i += 1
        if i > 100:
            raise RuntimeError("runaway chain")
    return chain

print("Running Brown-Traub subresultant PRS ...")
t0 = time.time()
try:
    Qp = Q.derivative()
    chain = subres_prs(Q, Qp)
    print(f"  done in {time.time()-t0:.2f}s; len = {len(chain)}")
    for i, f in enumerate(chain):
        cs = list(f)
        mb = max((abs(c).bit_length() for c in cs), default=0)
        print(f"  [{i}] deg={f.degree()} max_coef_bits={mb}")
except Exception as e:
    import traceback; traceback.print_exc()
    print(f"FAILED: {e}")
