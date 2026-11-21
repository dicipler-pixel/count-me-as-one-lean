# SCRIPT: CMAO-FINAL-CHECKS-01
"""Independent re-run of every exact-arithmetic and floating-point claim of
Count Me as One with the Dirac Anchor Recovered that is not a Lean theorem, or that
the paper states over a longer range than Lean does.

Why each section proves what it claims:
A  Exact roots over Q(sqrt5) in sympy: a ratio equal to phi^10 symbolically is equal, not close.
B  phi_0 and M are expanded as exact integer power series from their defining sums; a
   coefficient comparison over a range is a proof over that range and nothing more.
C  Eq. (1.5) and Eq. (1.7) are compared coefficient by coefficient in exact integers.
D  The T(3,4) Alexander polynomial is checked against the torus-knot formula as a
   polynomial identity; its unit-circle zeros are found exactly from the factorisation.
E  Litherland's count is computed in exact rationals at the stated points.
F  SnapPy is floating point; it can confirm the classical values, never prove them.
G  The flat-torus block symmetry is checked on finite truncations: a nonzero residual
   or a nonzero eta would refute it; zeros are consistent with the proof by blocks.
H  The square-versus-disc cutoff constant is compared to the exact value 8 asinh 1 - 2 pi.
I  Shell counts, Moser fibre orders, orbifold Euler characteristics: exact integers.
"""
from fractions import Fraction as Fr
import math, random

def ok(name, cond, detail=""):
    print(("PASS " if cond else "FAIL ") + name + ("  " + detail if detail else ""))
    assert cond, name

# ---------------- A. Ramanujan Challenge Q1 ratio ----------------
import sympy as sp
lam = sp.symbols('lam')
r = sp.solve(lam**2 + sp.Rational(297, 2)*lam - sp.Rational(729, 4), lam)
r = sorted(r, key=lambda e: float(e))
phi = (1 + sp.sqrt(5))/2
ok("A1 roots are (-297 +- 135 sqrt5)/4", set(sp.simplify(x) for x in r) == {(-297 - 135*sp.sqrt(5))/4, (-297 + 135*sp.sqrt(5))/4})
ratio = sp.nsimplify(sp.simplify(abs(r[0]/r[1])))
ok("A2 |lam_d/lam_s| = (123+55 sqrt5)/2 = phi^10", sp.simplify(ratio - (123 + 55*sp.sqrt(5))/2) == 0 and sp.simplify(sp.expand(phi**10) - (123 + 55*sp.sqrt(5))/2) == 0)
ok("A3 phi^10 + phi^-10 = 123", sp.simplify(phi**10 + phi**-10 - 123) == 0)

# ---------------- B. phi_0 and M as exact series ----------------
N = 260
def mul(a, b):
    c = [0]*(N+1)
    for i, x in enumerate(a):
        if x:
            for j in range(N+1-i):
                if b[j]: c[i+j] += x*b[j]
    return c
def onepow(k, s=1):           # 1 + s q^k
    p = [0]*(N+1); p[0] = 1
    if k <= N: p[k] += s
    return p
def negpoch(m):               # (-q;q)_m = prod_{j=1..m} (1+q^j)
    p = [0]*(N+1); p[0] = 1
    for j in range(1, m+1): p = mul(p, onepow(j))
    return p
def shift(p, k):
    out = [0]*(N+1)
    for i in range(N+1-k): out[i+k] = p[i]
    return out
phi0 = [0]*(N+1); M = [0]*(N+1)
n = 0
while n <= N:
    t = negpoch(2*n+1)
    phi0 = [x+y for x, y in zip(phi0, shift(t, n))]
    if 2*n <= N: M = [x+y for x, y in zip(M, shift(t, 2*n))]
    n += 1
d = [x-y for x, y in zip(phi0, M)]
ok("B1 [q^1] phi0 = 2, [q^1] M = 1", phi0[1] == 2 and M[1] == 1)
ok("B2 phi0 - M through q^16", d[:17] == [0,1,1,2,3,3,5,7,8,11,15,18,23,28,35,43,53], str(d[:17]))
ok("B3 phi0 - M positive for 1 <= k <= 128", all(d[k] > 0 for k in range(1, 129)))
# summand q^n(1-q^n)(-q)_{2n+1} has a negative coefficient (n = 1)
s1 = mul(shift(negpoch(3), 1), [1 if i == 0 else (-1 if i == 1 else 0) for i in range(N+1)])
ok("B4 summands are not coefficientwise positive", min(s1) < 0, "n=1 min coeff %d" % min(s1))

# ---------------- C. Eq (1.5) and Eq (1.7) ----------------
def inv_series(p):            # 1/p for p[0] = 1
    q = [0]*(N+1); q[0] = 1
    for k in range(1, N+1): q[k] = -sum(p[i]*q[k-i] for i in range(1, k+1))
    return q
psi = [0]*(N+1); m = 1
while m*m <= N:
    den = [1] + [0]*N
    for j in range(1, m+1): den = mul(den, onepow(2*j-1, -1))     # (q;q^2)_m
    psi = [x+y for x, y in zip(psi, shift(inv_series(den), m*m))]
    m += 1
lhs = [0]*(N+1)
for k in range(N+1):
    if 2*k+2 <= N: lhs[2*k+2] = 2*phi0[k]
rhs = [psi[i] + ((-1)**i)*psi[i] for i in range(N+1)]
ok("C1 Eq (1.5) 2q^2 phi0(q^2) = psi(q)+psi(-q) through q^258", lhs[:259] == rhs[:259])
negInf = negpoch(N)
false = [0]*(N+1); n = 0
while n*(3*n+1)//2 <= N:
    e = n*(3*n+1)//2; false[e] += 1
    if e + 2*n+1 <= N: false[e+2*n+1] -= 1
    n += 1
lhs7 = [0]*(N+1); lhs7[0] = 2
for k in range(N-1): lhs7[k+2] += 2*M[k]
rhs7 = [x+y for x, y in zip(negInf, false)]
ok("C2 Eq (1.7) 2+2q^2 M(q) = (-q)_inf + false theta through q^128", lhs7[:129] == rhs7[:129])

# ---------------- D. T(3,4) ----------------
t = sp.symbols('t')
P = t**6 - t**5 + t**3 - t + 1
ok("D1 P (t^3-1)(t^4-1) = (t^12-1)(t-1)", sp.expand(P*(t**3-1)*(t**4-1) - (t**12-1)*(t-1)) == 0)
ok("D2 P = (t^2-t+1)(t^4-t^2+1)", sp.expand(P - (t**2-t+1)*(t**4-t**2+1)) == 0)
walls = sorted(set(sp.nsimplify(sp.arg(z)/(2*sp.pi) % 1) for z in sp.solve(P, t)))
ok("D3 walls at 1/12,1/6,5/12,7/12,5/6,11/12", walls == [sp.Rational(k, 12) for k in (1, 2, 5, 7, 10, 11)], str(walls))

# ---------------- E. Litherland ----------------
def lt(p, q, a):
    s = 0
    for i in range(1, p):
        for j in range(1, q):
            x = Fr(i, p) + Fr(j, q)
            s += -1 if a < x < a + 1 else 1
    return s
ok("E1 T(2,3) at 1/12,1/4,1/2,3/4,11/12", [lt(2,3,Fr(*v)) for v in [(1,12),(1,4),(1,2),(3,4),(11,12)]] == [0,-2,-2,-2,0])
ok("E2 T(3,4) at 1/24,1/8,1/4,11/24,1/2", [lt(3,4,Fr(*v)) for v in [(1,24),(1,8),(1,4),(11,24),(1,2)]] == [0,-2,-4,-6,-6])

# ---------------- F. SnapPy and mpmath ----------------
import mpmath as mp, snappy
mp.mp.dps = 30
Vtet = 3*mp.clsin(2, 2*mp.pi/3)/2 # Lobachevsky Lambda(pi/3) = Cl_2(2pi/3)/2 ; V_tet = 3 Lambda(pi/3)
ok("F1 V_tet and 2 V_tet", abs(Vtet - mp.mpf('1.014941606409653625')) < mp.mpf('1e-17'), "2V = %s" % mp.nstr(2*Vtet, 20))
K = snappy.Manifold('4_1')
ok("F2 SnapPy vol(4_1)", abs(float(K.volume()) - 2.0298832128) < 1e-9, str(K.volume()))
sh = [complex(x) for x in K.tetrahedra_shapes('rect')]
ok("F3 shapes e^{i pi/3}", all(abs(z - complex(0.5, 3**.5/2)) < 1e-9 for z in sh))
cs = complex(K.cusp_info()[0]['shape'])
ok("F4 cusp shape 2 sqrt3 i", abs(cs - 2j*3**.5) < 1e-8, str(cs))
ok("F5 CS(4_1) ~ 0", abs(float(K.chern_simons())) < 1e-12, str(K.chern_simons()))
for nm in ['3_1', '8_19']:
    X = snappy.Manifold(nm)
    ok("F6 %s not hyperbolic (volume 0)" % nm, abs(float(X.volume())) < 1e-9)
for s in (2, -2):
    X = snappy.Manifold('3_1'); X.dehn_fill((s, 1))
    ok("F7 H1 of (%+d)-surgery on 3_1 is Z/2" % s, str(X.homology()) == 'Z/2')

# ---------------- G. flat torus truncations ----------------
random.seed(7)
import numpy as np
s1m = np.array([[0,1],[1,0]],complex); s2m = np.array([[0,-1j],[1j,0]]); s3m = np.diag([1,-1]).astype(complex)
worst = 0; etas = []
for _ in range(10):
    al, be, tau = random.random(), random.random(), 0.5 + random.random()
    for m in range(-20, 21):
        for n in range(-20, 21):
            H = (m+al)*s1m + tau*(n+be)*s2m
            worst = max(worst, np.abs(s3m@H@s3m + H).max())
            ev = np.linalg.eigvalsh(H); etas.append(int((ev > 0).sum() - (ev < 0).sum()))
ok("G1 sigma3 H sigma3 + H = 0 on every block", worst == 0)
ok("G2 eta of every block = 0", set(etas) == {0})

# ---------------- H. cutoff constant ----------------
Nn = 400; al, be = .3, .7
xs = np.arange(-Nn, Nn+1)
X, Y = np.meshgrid(xs+al, xs+be); R = np.hypot(X, Y)
sq = (1/R).sum(); disc = (1/R[R <= Nn]).sum()
c = 8*math.asinh(1) - 2*math.pi
ok("H1 (square - disc)/N -> 8 asinh 1 - 2 pi", abs((sq - disc)/Nn - c) < 2e-2, "%.4f vs %.4f" % ((sq-disc)/Nn, c))

# ---------------- I. integers ----------------
ok("I1 sphere shells sum 2(2l+1) = 2n^2", all(sum(2*(2*l+1) for l in range(n)) == 2*n*n for n in range(60)))
ok("I2 torus box (2k+1)^2 and L1 ring 4k", all(sum(1 for a in range(-k,k+1) for b in range(-k,k+1)) == (2*k+1)**2 and sum(1 for a in range(-k,k+1) for b in range(-k,k+1) if abs(a)+abs(b)==k) == 4*k for k in range(1,30)))
ok("I3 Moser fibres |6-2| = 4, |6+2| = 8", abs(6-2) == 4 and abs(6+2) == 8)
ok("I4 orbifold Euler 1/12 and -1/24", 2 - sum(1-Fr(1,a) for a in (2,3,4)) == Fr(1,12) and 2 - sum(1-Fr(1,a) for a in (2,3,8)) == Fr(-1,24))
print("ALL CHECKS PASS")
