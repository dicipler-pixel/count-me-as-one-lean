"""SCRIPT: COUNT-ME-AS-ONE-CHECKS-01
Recomputes every number the film and mixer put on screen, independently of the renderer, and writes math_checks.json."""
import numpy as np, json, cmath
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]; PHI=(1+5**.5)/2; out={}
w=cmath.exp(1j*cmath.pi/3); out['edge_at_regular']=abs((w*(w-1))**2-1)
out['regular_half']=abs(w*(w-1)+1)
out['cycle_fixed_regular']=abs(w*(1-w)-1); out['golden_cycle']=PHI*(1-PHI)
H31=np.array([[0,1],[-1,1]]);H41=np.array([[2,1],[1,1]]);V31=np.array([[-1,1],[0,-1]]);V41=np.array([[1,-1],[0,-1]])
out['h31_from_seifert']=(np.round(np.linalg.inv(V31)@V31.T).astype(int)==H31).all().item()
out['h41_from_seifert']=(np.round(np.linalg.inv(V41)@V41.T).astype(int)==H41).all().item()
out['h31_order6']=(np.linalg.matrix_power(H31,6)==np.eye(2)).all().item(); out['h31_cubed_minus_I']=(np.linalg.matrix_power(H31,3)==-np.eye(2)).all().item()
def lad(T,k):
 a,b=2,T
 for _ in range(k):a,b=b,T*b-a
 return a
out['ladder_T1']=[lad(1,k) for k in range(7)];out['ladder_T3']=[lad(3,k) for k in range(7)];out['ladder_T6']=[lad(6,k) for k in range(4)]
out['tr_h41_5']=int(np.trace(np.linalg.matrix_power(H41,5)));out['phi10_plus_inv']=PHI**10+PHI**-10
out['psi_T3_deg']=np.degrees(np.arccos(2/3));out['gd_inv_psi_T3']=np.log(1.5+np.sqrt(1.25));out['log_phi2']=np.log(PHI**2)
x=np.array([(3-5**.5)/2,(3+5**.5)/2]);a=x**2;b=-1+x+2*x**2+x**3-x**4;out['golden_ramification_b_plus_2a']=np.abs(b+2*a).max()
xc=np.exp(2j*np.pi/3);a=xc**2;b=-1+xc+2*xc**2+xc**3-xc**4;out['cube_root_ramification_b_minus_2a']=abs(b-2*a)
P=np.array([[-1,-1],[2,1]]);out['amphichiral_certificate']=(P.T@V41@P==-V41.T).all().item();out['det_P']=int(round(np.linalg.det(P)))
out['saddle_unit']=abs((2**.5-1)**4+(2**.5+1)**4-34)
ok=all([out['edge_at_regular']<1e-12,out['regular_half']<1e-12,out['cycle_fixed_regular']<1e-12,abs(out['golden_cycle']+1)<1e-12,out['h31_from_seifert'],out['h41_from_seifert'],out['h31_order6'],out['h31_cubed_minus_I'],
 out['ladder_T1']==[2,1,-1,-2,-1,1,2],out['ladder_T3']==[2,3,7,18,47,123,322],out['ladder_T6']==[2,6,34,198],out['tr_h41_5']==123,abs(out['phi10_plus_inv']-123)<1e-9,
 abs(out['gd_inv_psi_T3']-out['log_phi2'])<1e-12,out['golden_ramification_b_plus_2a']<1e-9,out['cube_root_ramification_b_minus_2a']<1e-9,out['amphichiral_certificate'],out['det_P']==1,out['saddle_unit']<1e-9])
out['all_pass']=bool(ok); json.dump(out,open(ROOT/'math_checks.json','w'),indent=1,default=float); print('all_pass',ok)
