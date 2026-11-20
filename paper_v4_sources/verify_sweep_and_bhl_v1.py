#!/usr/bin/env python3
"""Independent exact verification script for:
1. Bringmann-Hikami-Lovejoy (2010) +/-2 trefoil Dehn-surgery signed-boundary benchmark
2. 2D flat-torus Dirac operator chiral pairing & exact vanishing of eta_N(D_{T^2})
3. Alexander polynomials & unit-circle wall loci for 3_1, 4_1, 5_2, and 8_19 = T(3,4)
   + exact Levine-Tristram signature for T(3,4) and T(2,3)
4. 1D circle Dirac spectral-flow smooth-drift counterexample to Delta eta = 2 SF
5. T^2 lattice counts vs S^2 shell sum 2 * sum_{l=0}^{n-1} (2l+1) = 2 n^2
"""
import math
from fractions import Fraction
import numpy as np

print("=== 1. BHL (2010) +/-2 Trefoil Surgery Exact Integer q-Series Check ===")
N = 128

def poly_mul_trunc(a, b, max_deg):
    out = [0] * (max_deg + 1)
    for i, ai in enumerate(a):
        if ai == 0:
            continue
        lim = min(len(b), max_deg + 1 - i)
        for j in range(lim):
            if b[j]:
                out[i + j] += ai * b[j]
    return out

# Compute (-q; q)_k up to degree N
poch = [[1] + [0] * N]
for k in range(1, 2 * N + 2):
    # multiply by (1 + q^k)
    prev = poch[-1]
    nxt = prev[:]
    if k <= N:
        for d in range(N - k + 1):
            nxt[d + k] += prev[d]
    poch.append(nxt)

# phi0(q) = sum_{n>=0} q^n (-q; q)_{2n+1}
phi0 = [0] * (N + 1)
M_ser = [0] * (N + 1)
for n in range(N + 1):
    p = poch[2 * n + 1]
    for d in range(N - n + 1):
        phi0[d + n] += p[d]
    if 2 * n <= N:
        for d in range(N - 2 * n + 1):
            M_ser[d + 2 * n] += p[d]

# psi(q) = sum_{n>=1} q^{n^2} / (q; q^2)_n up to degree M2 = 2*N + 2
M2 = 2 * N + 2
psi = [0] * (M2 + 1)
inv_prod = [0] * (M2 + 1)
inv_prod[0] = 1
for n in range(1, int(math.isqrt(M2)) + 2):
    step = 2 * n - 1
    # divide by (1 - q^step)
    for d in range(step, M2 + 1):
        inv_prod[d] += inv_prod[d - step]
    n2 = n * n
    if n2 <= M2:
        for d in range(M2 - n2 + 1):
            psi[d + n2] += inv_prod[d]

# Check Thm 1.1 Eq (1.5): 2 q^2 phi0(q^2) = psi(q) + psi(-q)
thm11_ok = True
for k in range(M2 + 1):
    rhs = psi[k] + ((-1) ** k) * psi[k]
    lhs = 2 * phi0[(k - 2) // 2] if (k >= 2 and k % 2 == 0) else 0
    if lhs != rhs:
        thm11_ok = False
        print(f"  Thm 1.1 MISMATCH at q^{k}: lhs={lhs}, rhs={rhs}")
        break

# Check Thm 1.2 Eq (1.7): 2 + 2 q^2 M(q) = (-q)_infty + sum_{n>=0} q^{n(3n+1)/2} (1 - q^{2n+1})
neg_q_inf = poch[N]
false_theta = [0] * (N + 1)
n = 0
while True:
    e1 = n * (3 * n + 1) // 2
    if e1 > N:
        break
    false_theta[e1] += 1
    e2 = e1 + 2 * n + 1
    if e2 <= N:
        false_theta[e2] -= 1
    n += 1

thm12_ok = True
for k in range(N + 1):
    lhs = (2 if k == 0 else 0) + (2 * M_ser[k - 2] if k >= 2 else 0)
    rhs = neg_q_inf[k] + false_theta[k]
    if lhs != rhs:
        thm12_ok = False
        print(f"  Thm 1.2 MISMATCH at q^{k}: lhs={lhs}, rhs={rhs}")
        break

diff = [phi0[k] - M_ser[k] for k in range(N + 1)]
print(f"  Thm 1.1 (Eq 1.5) exact through q^{M2} (phi0 through q^{N}): {thm11_ok}")
print(f"  Thm 1.2 (Eq 1.7) exact through q^{N}: {thm12_ok}")
print(f"  phi0[0..10]       = {phi0[:11]}")
print(f"  M[0..10]          = {M_ser[:11]}")
print(f"  (phi0 - M)[0..10] = {diff[:11]}")
print(f"  All (phi0 - M)[k] > 0 for 1 <= k <= {N}: {all(diff[k] > 0 for k in range(1, N + 1))}")
print(f"  psi[0..12]        = {psi[:13]}")

print("\n=== 2. 2D Flat-Torus Dirac Operator Chiral Vanishing Check ===")
sigma3 = np.array([[1.0, 0.0], [0.0, -1.0]], dtype=complex)
rng = np.random.default_rng(42)
max_anticomm = 0.0
max_eta_abs = 0.0
for trial in range(10):
    alpha, beta = rng.uniform(0, 1, 2)
    tau_re, tau_im = rng.uniform(-0.5, 0.5), rng.uniform(0.5, 2.0)
    eta_sum = 0.0
    for m in range(-20, 21):
        for n in range(-20, 21):
            u = 2 * math.pi * (m + alpha)
            v = 2 * math.pi * ((n + beta) - tau_re * (m + alpha)) / tau_im
            H = np.array([[0.0, u - 1j * v], [u + 1j * v, 0.0]], dtype=complex)
            err = np.linalg.norm(sigma3 @ H @ sigma3 + H)
            max_anticomm = max(max_anticomm, err)
            evals = np.linalg.eigvalsh(H)
            for lam in evals:
                if abs(lam) > 1e-12:
                    eta_sum += math.copysign(1.0, lam) * (abs(lam) ** (-0.5))
    max_eta_abs = max(max_eta_abs, abs(eta_sum))
print(f"  max ||sigma_3 H sigma_3 + H|| = {max_anticomm:.3e}")
print(f"  max |eta_N(D_{{T^2}}, s=0.5)| over 10 random (alpha,beta,tau), N=20 = {max_eta_abs:.3e}")

print("\n=== 3. Exact Alexander Wall Loci & Levine-Tristram Signatures (3_1, 4_1, 5_2, 8_19=T(3,4)) ===")
# Check algebraic identity for 8_19 = T(3,4):
# Delta_{3,4}(e^{i theta}) = 2 cos(3t) - 2 cos(2t) + 1 = (2 cos t - 1)(4 cos^2 t - 3)
thetas = np.linspace(0, 2 * math.pi, 1000)
lhs_819 = 2 * np.cos(3 * thetas) - 2 * np.cos(2 * thetas) + 1
rhs_819 = (2 * np.cos(thetas) - 1) * (4 * np.cos(thetas) ** 2 - 3)
print(f"  max |Delta_{{8_19}}(e^{{it}}) - (2cos t - 1)(4cos^2 t - 3)| = {np.max(np.abs(lhs_819 - rhs_819)):.3e}")

# Exact Levine-Tristram signature for torus knot T(p,q) via Litherland (1979) Prop 1:
# For omega = e^{2 pi i alpha} (0 < alpha < 1, not a root of Delta),
# sigma_{T(p,q)}(omega) = #{(i,j): 1<=i<=p-1, 1<=j<=q-1, alpha < i/p + j/q < 1+alpha}
#                       - #{(i,j): 1<=i<=p-1, 1<=j<=q-1, i/p + j/q < alpha or i/p + j/q > 1+alpha}
# Wait: check sign convention! For positive trefoil T(2,3) at alpha=1/2:
# pairs (i,j) in {1}x{1,2}: i/2 + j/3 in {5/6, 7/6}.
# Let's check exact Litherland formula: sigma_{T(p,q)}(e^{2pi i alpha}) = #_{out} - #_{in} (with convention sigma(right-handed trefoil) = -2).
def lt_sig_torus(p, q, alpha):
    # Litherland (1979): for 0 < alpha < 1, jump at i/p + j/q (mod 1)
    # Count pairs (i,j), 1<=i<p, 1<=j<q:
    # if alpha < i/p + j/q < alpha + 1: contributes -1; else +1 (so right-handed T(2,3) has sigma(-1) = -2)
    sig = 0
    for i in range(1, p):
        for j in range(1, q):
            s = Fraction(i, p) + Fraction(j, q)
            if alpha < s < alpha + 1:
                sig -= 1
            elif s < alpha or s > alpha + 1:
                sig += 1
    return sig

for name, p, q, pts in [
    ("T(2,3)=3_1", 2, 3, [Fraction(1, 12), Fraction(1, 4), Fraction(1, 2), Fraction(3, 4), Fraction(11, 12)]),
    ("T(3,4)=8_19", 3, 4, [Fraction(1, 24), Fraction(1, 8), Fraction(1, 4), Fraction(11, 24), Fraction(1, 2)]),
]:
    vals = [(str(a), lt_sig_torus(p, q, a)) for a in pts]
    print(f"  {name} Levine-Tristram sigma(e^{{2pi i alpha}}): {vals}")

# Check 5_2: Delta_{5_2}(e^{it}) = 4 cos t - 3 -> walls at cos t = 3/4
print(f"  5_2 wall angle alpha = arccos(3/4)/(2 pi) = {math.acos(0.75)/(2*math.pi):.10f}")
# Check 4_1: Delta_{4_1}(e^{it}) = 3 - 2 cos t >= 1 -> zero walls
print(f"  4_1 min Delta(e^{{it}}) = {np.min(3 - 2 * np.cos(thetas)):.1f} (no walls, amphicheiral => sigma === 0)")

print("\n=== 4. 1D Circle Smooth-Drift Counterexample ===")
def eta_s1(a):
    frac = a - math.floor(a)
    assert frac != 0
    return 1.0 - 2.0 * frac

a0, a1 = 0.25, 0.75
print(f"  No zero-crossing interval [0.25, 0.75]: eta(0.25)={eta_s1(a0)}, eta(0.75)={eta_s1(a1)}, Delta eta={eta_s1(a1)-eta_s1(a0)} != 0, d eta/da = -2")
b0, b1 = 0.25, 1.25
sf = math.floor(b1) - math.floor(b0)
print(f"  Full loop [0.25, 1.25]: SF={sf}, eta(1.25)-eta(0.25)={eta_s1(b1)-eta_s1(b0)} != 2*SF={2*sf}")
print(f"  Exact odometer identity: 0.5*(eta(b1)-eta(b0)) + (b1-b0) = {0.5*(eta_s1(b1)-eta_s1(b0)) + (b1-b0)} == SF = {sf}")

print("\n=== 5. Shell Capacity 2n^2 Check ===")
for k in range(1, 6):
    s2_sum = sum(2 * (2 * l + 1) for l in range(k))
    t2_box = (2 * k + 1) ** 2
    t2_l1 = 4 * k
    print(f"  k={k}: S^2 shell sum = {s2_sum} (2k^2={2*k*k}), T^2 box = {t2_box}, T^2 L1-ring = {t2_l1}")
