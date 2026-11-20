#!/usr/bin/env python3
"""D28 extra checks (Ink Between the Stars, 2026-11-20 CT).
Exact checks use sympy / fractions. Floating-point and SnapPy checks are MODEL grade.
Run: /tmp/snapenv/bin/python d28_checks_v1.py   (needs sympy, mpmath; snappy optional)
"""
from fractions import Fraction as F
import sympy as sp

print("=== A. Ramanujan Challenge Q1 (Problem 2.1) companion roots: ratio = phi^10 ===")
s5 = sp.sqrt(5)
lam_s = (-297 + 135*s5)/4
lam_d = (-297 - 135*s5)/4
lam = sp.symbols('lam')
cp = sp.expand((lam - lam_s)*(lam - lam_d))
print("  (lam-ls)(lam-ld) =", cp, "; equals lam^2+(297/2)lam-729/4:",
      sp.simplify(cp - (lam**2 + sp.Rational(297,2)*lam - sp.Rational(729,4))) == 0)
ratio = sp.radsimp(sp.Abs(lam_d)/lam_s)
phi = (1 + s5)/2
print("  |ld|/ls =", ratio, "; equals (123+55 sqrt5)/2:", sp.simplify(ratio - (123+55*s5)/2) == 0,
      "; equals phi^10:", sp.simplify(sp.expand(phi**10) - ratio) == 0)
print("  phi^10 + phi^-10 =", sp.nsimplify(sp.simplify(sp.expand(phi**10 + phi**-10))))
print("  log10(phi^10) =", sp.N(sp.log(ratio, 10), 12))

print("\n=== B. DT-T33 vs CMaO: L = -M^-6  <=>  L*M^6 = -1 (M != 0) ===")
L, M = sp.symbols('L M', nonzero=True)
print("  solve(L*M**6 + 1, L) =", sp.solve(sp.Eq(L*M**6, -1), L))

print("\n=== C. +/-2 surgery on the trefoil: Seifert invariants and base-orbifold Euler characteristic ===")
# Moser (1971): p/q surgery on the right-handed torus knot T(r,s) has exceptional fibres r, s, |r s q - p|.
for p in (2, -2):
    third = abs(2*3*1 - p)
    chi = 2 - sum(1 - F(1, a) for a in (2, 3, third))
    geom = "spherical (finite pi_1)" if chi > 0 else ("Euclidean/Nil" if chi == 0 else "SL2~ (infinite pi_1)")
    print(f"  right-handed T(2,3), slope {p:+d}: fibres (2,3,{third}), chi_orb = {chi}, {geom}; H_1 = Z/{abs(p)}")
print("  mirror: S^3_p(mK) = -S^3_{-p}(K), so for the LEFT-handed trefoil +2 gives (2,3,8) and -2 gives (2,3,4) (BHL labelling).")
print("  unknot control: S^3_{+-2}(U) = L(2,1) = RP^3; L(p,q) = -L(p,q) iff q^2 = -1 mod p:", (1*1 + 1) % 2 == 0)

print("\n=== D. 8_19 = T(3,4): Alexander polynomial and unit-circle walls (exact) ===")
t, c = sp.symbols('t c')
D34 = sp.cancel((t**12 - 1)*(t - 1)/((t**3 - 1)*(t**4 - 1)))
print("  Delta_{T(3,4)}(t) =", sp.expand(D34))
x = sp.symbols('x', real=True)
lhs = 2*sp.cos(3*x) - 2*sp.cos(2*x) + 1
rhs = (2*sp.cos(x) - 1)*(4*sp.cos(x)**2 - 3)
print("  2cos3x - 2cos2x + 1 - (2cos x - 1)(4cos^2 x - 3) == 0:", sp.simplify(sp.expand_trig(lhs - rhs)) == 0)
print("  t^-3 Delta(t) at t=e^{ix} equals lhs:", sp.simplify(sp.expand((sp.exp(-3*sp.I*x)*D34.subs(t, sp.exp(sp.I*x))).rewrite(sp.cos)) - lhs) == 0)
print("  wall angles alpha = x/2pi in [0,1): ", sorted({F(1,6),F(5,6),F(1,12),F(11,12),F(5,12),F(7,12)}))

print("\n=== E. Levine-Tristram signature of T(2,3) on the whole circle (Litherland count, exact rationals) ===")
def lt(p, q, a):
    s = 0
    for i in range(1, p):
        for j in range(1, q):
            v = F(i, p) + F(j, q)
            if a < v < a + 1: s -= 1
            elif v < a or v > a + 1: s += 1
    return s
grid = [F(k, 240) for k in range(1, 240) if F(k,240) not in (F(1,6), F(5,6))]
win = {a for a in grid if lt(2, 3, a) == -2}
print("  sigma_{T(2,3)}(e^{2 pi i a}) = -2 exactly for a in (1/6,5/6) and 0 elsewhere on grid 1/240:",
      all((lt(2,3,a) == -2) == (F(1,6) < a < F(5,6)) for a in grid) and all(lt(2,3,a) in (0,-2) for a in grid))
print("  wall at a=1/6 is e^{i pi/3}, root of z^2-z+1 (regular tetrahedron shape):",
      sp.simplify(sp.expand_complex(sp.exp(sp.I*sp.pi/3)**2 - sp.exp(sp.I*sp.pi/3) + 1)) == 0)
print("  DT-T38 window: rho on alpha in (1/12,5/12) with character e^{4 pi i alpha} <=> 2alpha in (1/6,5/6): consistent")

print("\n=== F. Figure-eight anchor (MODEL: floating point) ===")
import mpmath as mp
mp.mp.dps = 30
lob = lambda th: -mp.quad(lambda u: mp.log(abs(2*mp.sin(u))), [0, th])
vtet = 3*lob(mp.pi/3)
print("  V_tet = 3 Lobachevsky(pi/3) =", mp.nstr(vtet, 20), "; 2 V_tet =", mp.nstr(2*vtet, 20))
try:
    import snappy
    Mf = snappy.Manifold('4_1')
    print("  SnapPy", snappy.__version__, "4_1: vol", Mf.volume(), "|", Mf.solution_type(), "| cusp shape", Mf.cusp_info('shape'),
          "| CS", Mf.chern_simons(), "| shapes", Mf.tetrahedra_shapes('rect'))
    for k in ('3_1', '8_19'):
        N = snappy.Manifold(k)
        print(f"  SnapPy {k}: vol {N.volume()} | {N.solution_type()} (torus knot; not hyperbolic)")
    for sl in ((2,1), (-2,1)):
        T = snappy.Manifold('3_1'); T.dehn_fill(sl)
        E = snappy.Manifold('4_1'); E.dehn_fill(sl)
        print(f"  SnapPy filling {sl}: H_1(3_1({sl})) = {T.homology()}, H_1(4_1({sl})) = {E.homology()}")
except Exception as e:
    print("  SnapPy not run:", e)

print("\n=== G. Raw difference ruler phi0 - M: closed form of each term ===")
q = sp.symbols('q')
for n in range(1, 4):
    term = q**n*(1 - q**n)*sp.prod([(1 + q**j) for j in range(1, 2*n + 2)])
    alt = q**n*(1 - q**(4*n))*sp.prod([(1 + q**j) for j in range(1, 2*n + 2) if j not in (n, 2*n)])
    print(f"  n={n}: q^n(1-q^n)(-q)_(2n+1) == q^n(1-q^(4n)) prod_(j != n,2n)(1+q^j):", sp.expand(term - alt) == 0,
          "; has negative coeff:", any(cf < 0 for cf in sp.Poly(sp.expand(term), q).coeffs()))
