#!/usr/bin/env python3
"""Generate CRT primes for PRS verification and emit theories/S1/CRTPrimes.v.

Reads certificate_chain.json, computes the maximum coefficient magnitude across
all PRS verification steps, determines how many ~30-bit primes are needed so
their product exceeds 2*max_coeff, generates those primes, and writes a Rocq
file containing the prime list and the degree-drop (d) values.
"""

import json
import math
import os
import sys

# Large integer string conversion limit
sys.set_int_max_str_digits(100000)

# ---------------------------------------------------------------------------
# 1. Load data
# ---------------------------------------------------------------------------
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
ROOT_DIR = os.path.dirname(SCRIPT_DIR)
CERT_PATH = os.path.join(ROOT_DIR, "certificate_chain.json")

with open(CERT_PATH) as f:
    cert = json.load(f)

chain_len = cert["chain_len"]  # 43 entries (indices 0..42)
sturm = cert["sturm_chain"]   # list of {i, deg, coefs_low_to_high}
betas = cert["betas"]         # list of scalar strings (length chain_len - 2)
quotients = cert["prs_quotients"]  # list of {i, deg, coefs_low_to_high}

# Parse chain polynomials: chain[i] as list of Python ints (low-to-high)
chains = {}
for entry in sturm:
    idx = entry["i"]
    chains[idx] = [int(c) for c in entry["coefs_low_to_high"]]

# Parse betas (scalars)
beta_vals = [int(b) for b in betas]

# Parse quotients: quot[i] for step i (i starting at 1)
quots = {}
for entry in quotients:
    idx = entry["i"]
    quots[idx] = [int(c) for c in entry["coefs_low_to_high"]]

# ---------------------------------------------------------------------------
# Helper: polynomial arithmetic on coefficient lists (low-to-high)
# ---------------------------------------------------------------------------

def poly_mul(a, b):
    """Multiply two polynomials (list of int coefficients, low-to-high)."""
    if not a or not b:
        return []
    result = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        if ai == 0:
            continue
        for j, bj in enumerate(b):
            result[i + j] += ai * bj
    return result


def poly_add(a, b):
    """Add two polynomials."""
    result = [0] * max(len(a), len(b))
    for i, v in enumerate(a):
        result[i] += v
    for i, v in enumerate(b):
        result[i] += v
    return result


def poly_sub(a, b):
    """Subtract: a - b."""
    result = [0] * max(len(a), len(b))
    for i, v in enumerate(a):
        result[i] += v
    for i, v in enumerate(b):
        result[i] -= v
    return result


def poly_scale(a, s):
    """Multiply polynomial by scalar."""
    return [c * s for c in a]


def max_abs_coeff(p):
    """Return the maximum absolute value among coefficients."""
    if not p:
        return 0
    return max(abs(c) for c in p)


# ---------------------------------------------------------------------------
# 2. Compute max coefficient across all PRS verification steps
# ---------------------------------------------------------------------------
# For step i (1-indexed, i in 1..chain_len-2):
#   LHS = lc(chain_i)^d * chain_{i-1}
#   RHS = Q_i * chain_i + beta_i * chain_{i+1}
# where d = deg(chain_{i-1}) - deg(chain_i) + 1
#
# The verification checks LHS == RHS.  The max coefficient of either side
# (they should be equal) is what we need to bound for CRT correctness.

print("Computing max coefficient across PRS verification steps...")

global_max = 0
d_values = []  # d_i for each step i = 1 .. chain_len-2

for step in range(1, chain_len - 1):
    c_prev = chains[step - 1]  # chain_{i-1}
    c_curr = chains[step]      # chain_i
    c_next = chains[step + 1]  # chain_{i+1}

    deg_prev = len(c_prev) - 1
    deg_curr = len(c_curr) - 1
    d = deg_prev - deg_curr + 1
    d_values.append(d)

    lc_curr = c_curr[-1]  # leading coefficient of chain_i

    # LHS = lc(chain_i)^d * chain_{i-1}
    lc_pow = lc_curr ** d
    lhs = poly_scale(c_prev, lc_pow)

    # RHS = Q_i * chain_i + beta_i * chain_{i+1}
    #   beta index: betas are indexed 0..chain_len-3, beta_vals[step-1] for step i
    q_i = quots[step]
    beta_i = beta_vals[step - 1]

    rhs_part1 = poly_mul(q_i, c_curr)
    rhs_part2 = poly_scale(c_next, beta_i)
    rhs = poly_add(rhs_part1, rhs_part2)

    # Sanity check: LHS and RHS should be equal
    diff = poly_sub(lhs, rhs)
    diff_max = max_abs_coeff(diff)
    if diff_max != 0:
        print(f"  WARNING: step {step} has nonzero LHS-RHS difference (max={diff_max})")

    step_max = max(max_abs_coeff(lhs), max_abs_coeff(rhs))
    if step_max > global_max:
        global_max = step_max

    if step <= 3 or step >= chain_len - 3:
        bits = global_max.bit_length()
        print(f"  step {step}: d={d}, step_max bits={step_max.bit_length()}, running global_max bits={bits}")

print(f"\nGlobal max coefficient magnitude M = (bit length: {global_max.bit_length()})")

# ---------------------------------------------------------------------------
# 3. Determine number of primes needed
# ---------------------------------------------------------------------------
# Need product of primes > 2*M.  Using primes near 2^30, each contributes ~30
# bits to the product.

M = global_max
two_M = 2 * M
bits_needed = two_M.bit_length()
PRIME_BITS = 30  # each prime ~ 2^30, contributing ~30 bits to product
num_primes = math.ceil(bits_needed / PRIME_BITS)

print(f"2M bit length: {bits_needed}")
print(f"Number of primes needed (ceil({bits_needed}/30)): {num_primes}")

# Add a small safety margin
num_primes += 2
print(f"With safety margin: {num_primes} primes")

# ---------------------------------------------------------------------------
# 4. Generate primes in [2^30, 2^31)
# ---------------------------------------------------------------------------
# Simple approach: use sympy if available, otherwise manual isprime

def is_prime(n):
    """Miller-Rabin primality test for correctness on small numbers."""
    if n < 2:
        return False
    if n < 4:
        return True
    if n % 2 == 0 or n % 3 == 0:
        return False
    # Deterministic Miller-Rabin for n < 2^31 using witnesses {2, 3, 5, 7}
    d_val = n - 1
    r = 0
    while d_val % 2 == 0:
        d_val //= 2
        r += 1
    for a in [2, 3, 5, 7]:
        if a >= n:
            continue
        x = pow(a, d_val, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(r - 1):
            x = pow(x, 2, n)
            if x == n - 1:
                break
        else:
            return False
    return True


print(f"\nGenerating {num_primes} primes starting from 2^30 = {1 << 30}...")

primes = []
candidate = (1 << 30) + 1  # Start just above 2^30
while len(primes) < num_primes:
    if is_prime(candidate):
        primes.append(candidate)
    candidate += 2  # skip evens

print(f"Generated {len(primes)} primes")
print(f"First prime: {primes[0]}, last prime: {primes[-1]}")
print(f"All primes < 2^31? {all(p < (1 << 31) for p in primes)}")

# Verify product > 2M
log2_product = sum(math.log2(p) for p in primes)
print(f"log2(product of primes) = {log2_product:.1f}")
print(f"log2(2M) = {math.log2(two_M):.1f}")
assert log2_product > math.log2(two_M), "Product of primes is not large enough!"

# ---------------------------------------------------------------------------
# 5. Emit theories/S1/CRTPrimes.v
# ---------------------------------------------------------------------------
COQ_PATH = os.path.join(ROOT_DIR, "theories", "S1", "CRTPrimes.v")
os.makedirs(os.path.dirname(COQ_PATH), exist_ok=True)

lines = []
lines.append("(* Autogenerated by python/generate_primes.py -- DO NOT EDIT *)")
lines.append("")
lines.append("From Stdlib Require Import List.")
lines.append("From Stdlib Require Import Uint63.")
lines.append("Import ListNotations.")
lines.append("")
lines.append(f"(* Max coefficient bit-size across PRS verification: {global_max.bit_length()} bits *)")
lines.append(f"(* Number of CRT primes: {len(primes)} *)")
lines.append(f"(* Each prime is in [2^30, 2^31), so a*b mod p fits in 62 < 63 bits *)")
lines.append("")

# Emit prime list
lines.append("Definition crt_primes : list int :=")
prime_strs = [f"  {p}%uint63" for p in primes]
lines.append("  [ " + prime_strs[0].strip())
for ps in prime_strs[1:]:
    lines.append("  ; " + ps.strip())
lines.append("  ].")
lines.append("")

# Emit d values
lines.append(f"(* d_i = deg(chain_{{i-1}}) - deg(chain_i) + 1 for step i = 1..{chain_len-2} *)")
lines.append("Definition prs_d_values : list int :=")
d_strs = [f"  {d}%uint63" for d in d_values]
lines.append("  [ " + d_strs[0].strip())
for ds in d_strs[1:]:
    lines.append("  ; " + ds.strip())
lines.append("  ].")
lines.append("")

content = "\n".join(lines)

with open(COQ_PATH, "w") as f:
    f.write(content)

file_size = os.path.getsize(COQ_PATH)
print(f"\nWrote {COQ_PATH}")
print(f"File size: {file_size} bytes ({file_size/1024:.1f} KB)")

# ---------------------------------------------------------------------------
# 6. Report
# ---------------------------------------------------------------------------
print("\n" + "=" * 60)
print("REPORT")
print("=" * 60)
print(f"Max coefficient bit-size: {global_max.bit_length()} bits")
print(f"Number of CRT primes:     {len(primes)}")
print(f"Prime range:              [{primes[0]}, {primes[-1]}]")
print(f"log2(prime product):      {log2_product:.1f}")
print(f"log2(2M):                 {math.log2(two_M):.1f}")
print(f"d values (per step):      {d_values}")
print(f"CRTPrimes.v file size:    {file_size} bytes")
print("=" * 60)
