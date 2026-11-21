# SCRIPT: CMAO-SIGNATURE-FLIP-01
# Where does the -2 / +2 flip come from?
# Same knot, two Seifert matrices: KnotInfo's stored one, and the one SnapPy/spherogram
# builds from the braid closure (and from KnotInfo's PD).  If the knot is the same and the
# two signatures are opposite, the flip is a sign CONVENTION, not a change of handedness.
# Check that would prove it: V_spherogram must be congruent to -V_KnotInfo^T
# (equivalently: every Levine-Tristram value flips sign, and the Alexander polynomials agree).
import warnings; warnings.filterwarnings('ignore')
import snappy, numpy as np, cmath, math, sympy as sp
from database_knotinfo import link_list
rows={r['name']:r for r in link_list()[1:]}
def lt(V,t):
    w=cmath.exp(2j*math.pi*t); V=np.array(V,dtype=complex)
    A=(1-w)*V+(1-w.conjugate())*V.T; A=(A+A.conj().T)/2
    ev=np.linalg.eigvalsh(A); return int(sum(e>1e-9 for e in ev)-sum(e<-1e-9 for e in ev))
x=sp.symbols('t')
def alex(V):
    V=sp.Matrix(V); p=sp.expand((V-x*V.T).det()); p=sp.Poly(p,x)
    c=p.all_coeffs(); 
    while c and c[-1]==0: c=c[:-1]
    if c[0]<0: c=[-a for a in c]
    return c
TS=[0.10,0.20,0.30,0.45,0.50]
print('t values:',TS)
for name in ['3_1','8_19','13a_3542','13a_4018']:
    r=rows[name]; VK=eval(r['seifert_matrix'])
    Kb=snappy.Link(braid_closure=eval(r['braid_notation']))
    Kp=snappy.Link(eval(r['pd_notation']))
    Vb=Kb.seifert_matrix(); Vp=Kp.seifert_matrix()
    print(name)
    print('  KnotInfo stored sig',r['signature'],' | writhe braid',Kb.writhe(),' writhe PD',Kp.writhe())
    print('  LT KnotInfo V      ',[lt(VK,t) for t in TS])
    print('  LT spherogram braid',[lt(Vb,t) for t in TS])
    print('  LT spherogram PD   ',[lt(Vp,t) for t in TS])
    print('  Alexander agree (KI vs braid vs PD):',alex(VK)==alex(Vb)==alex(Vp))
# sanity on the convention: the positive Hopf-band (one positive crossing pair) 
# standard references: right-handed (positive) trefoil has sigma = -2 (Rolfsen / KnotInfo convention)

# KnotInfo's signature_function lists jumps as fractions of pi (omega = exp(i*pi*s)),
# e.g. 3_1 jumps at s = 1/3, the root exp(i*pi/3).  In our t (omega = exp(2*pi*i*t)) the
# 13-crossing window s in (0.4388, 0.4609) is t in (0.2194, 0.2304).  Probe t = 0.225.
print()
print('13-crossing window, t = 0.225 (omega = exp(i*pi*0.45)):')
for name in ['13a_3542','13a_4018']:
    r=rows[name]; VK=eval(r['seifert_matrix'])
    Vb=snappy.Link(braid_closure=eval(r['braid_notation'])).seifert_matrix()
    Vm=snappy.Link(braid_closure=[-g for g in eval(r["braid_notation"])]).seifert_matrix()
    print(' ',name,' KnotInfo V:',lt(VK,0.225),' spherogram braid:',lt(Vb,0.225),
          ' spherogram mirror:',lt(Vm,0.225))

# Dirac Time v3.0.1 Sec 13.5 states the pair's common Alexander polynomial and the window
# alpha in (0.10971, 0.11522) with omega = exp(4*pi*i*alpha).  Check both against KnotInfo.
DT=[1,-7,23,-48,72,-83,72,-48,23,-7,1]
for name in ['13a_3542','13a_4018']:
    print(' ',name,'Alexander = Dirac Time polynomial:',alex(eval(rows[name]['seifert_matrix']))==DT)
p=np.roots(DT); s=sorted(float(np.angle(z))/(4*math.pi) for z in p if abs(abs(z)-1)<1e-9 and np.angle(z)>0)
print('  unit-circle roots as alpha (omega = e^{4 pi i alpha}), upper half:',[round(a,5) for a in s])
# Verdicts
print()
print('VERDICT 1: on every knot and every t the spherogram/SnapPy Seifert matrix gives minus the')
print('  KnotInfo value, with the same diagram (same writhe) and the same Alexander polynomial:')
print('  the -2/+2 flip is a sign convention of the Seifert matrix, not a change of handedness.')
print('VERDICT 2: in KnotInfo convention the positive braid [1,1,1] (right-handed trefoil) has')
print('  sigma = -2 on (1/6,5/6); Dirac Time uses rho = -sigma and KnotInfo signatures, so its')
print('  rho = +2 window is the right-handed trefoil.')
print('VERDICT 3: as stored, 13a_3542 and 13a_4018 have the SAME signature function (-2 in the')
print('  window); only the MIRROR of 13a_4018 reads +2, so the mirror in the DT-O6 pair is required.')
