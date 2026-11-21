"""SCRIPT: COUNT-ME-AS-ONE-MODEL-01
Animated 3D model (core glTF 2.0, GLB) of the eight film chapters. Each chapter is one node holding
computed point geometry; it is shown (scale 1) only during its chapter of the 82-second timeline and
turns slowly. Geometry only: the film's glow, bloom and text are renderer treatments, not in the GLB.
Requires numpy and pygltflib."""
from pathlib import Path
import numpy as np, json
from pygltflib import GLTF2,Scene,Node,Mesh,Primitive,Attributes,Buffer,BufferView,Accessor,Animation,AnimationChannel,AnimationChannelTarget,AnimationSampler
ROOT=Path(__file__).resolve().parents[1]; R=np.random.default_rng(4141)
GOLD=np.array([1.0,.60,.12]);BLUE=np.array([.06,.52,1.0]);ROSE=np.array([1.0,.30,.42]);WHITE=np.array([.85,.92,1.0])
PHI=(1+5**.5)/2
CH=[(0,9),(9,20),(20,31),(31,42),(42,54),(54,64),(64,74),(74,82)]
def trefoil(t):return np.c_[np.sin(t)+2*np.sin(2*t),-np.sin(3*t),np.cos(t)-2*np.cos(2*t)]/3.2
def fig8(t):return np.c_[(2+np.cos(2*t))*np.cos(3*t),np.sin(4*t),(2+np.cos(2*t))*np.sin(3*t)]/3.0
def tube(curve,n,r):
 t=R.uniform(0,2*np.pi,n);c=curve(t);d=curve(t+1e-3)-curve(t-1e-3);d/=np.linalg.norm(d,axis=1)[:,None]
 a=np.cross(d,[0,1.0,0]);a/=np.linalg.norm(a,axis=1)[:,None]+1e-9;b=np.cross(d,a);th=R.uniform(0,2*np.pi,n);rr=r*np.sqrt(R.uniform(.2,1,n))
 return c+rr[:,None]*(np.cos(th)[:,None]*a+np.sin(th)[:,None]*b),t
def seg(a,b,n):s=R.uniform(0,1,(n,1));return a+(b-a)*s
def tet(c,size):
 V=np.array([[1,1,1],[1,-1,-1],[-1,1,-1],[-1,-1,1]],float)*size/1.732+c;return np.vstack([seg(V[i],V[j],700) for i in range(4) for j in range(i+1,4)])
def col(n,c):return np.tile(c,(n,1))
groups=[]
p,t=tube(fig8,12000,.05);c=np.where((np.sin(t*3)>0)[:,None],GOLD,BLUE);a=tet(np.array([-.55,0,0]),.62);b=tet(np.array([.55,0,0]),.62)
groups.append((np.vstack([p,a,b]),np.vstack([c,col(len(a),GOLD),col(len(b),BLUE)])))
pts=[];cs=[]
for r in [np.exp(1j*np.pi/3),np.exp(-1j*np.pi/3)]:
 tr=np.exp(1j*np.angle(r)*(1+np.linspace(0,1,800)));pts.append(np.c_[tr.real,0*tr.real,-tr.imag]);cs.append(col(800,GOLD))
for r in [PHI,-1/PHI]:
 s=np.linspace(0,1,800);m=abs(r)**(1+s);w=m*np.exp(1j*np.pi*s)*(-1) if r<0 else m+0j;pts.append(np.c_[w.real,0*s,-w.imag]);cs.append(col(800,BLUE))
a=np.linspace(0,2*np.pi,1200);pts.append(np.c_[np.cos(a),0*a,np.sin(a)]);cs.append(col(1200,GOLD*.5))
groups.append((np.vstack(pts),np.vstack(cs)))
p,_=tube(trefoil,12000,.05);p[:,1]+=.35;Q=np.array([[2,-1],[-1,2]]);x0=np.array([.62,0]);qv=x0@Q@x0
ang=np.linspace(0,2*np.pi,1200);d=np.c_[np.cos(ang),np.sin(ang)];r=np.sqrt(qv/np.einsum('ni,ij,nj->n',d,Q,d));e=np.c_[r*d[:,0],np.full(1200,-1.25),r*d[:,1]]
groups.append((np.vstack([p,e]),np.vstack([col(len(p),ROSE),col(1200,GOLD)])))
uv=R.uniform(0,1,(20000,2));th=2*np.pi*uv[:,0];ph=2*np.pi*uv[:,1];P=np.c_[(1.15+.45*np.cos(ph))*np.cos(th),.45*np.sin(ph),(1.15+.45*np.cos(ph))*np.sin(th)]
w=uv[:,:1];groups.append((P,GOLD*(1-w)+BLUE*w))
Ts=np.linspace(0,6,3000);pts=[];cs=[]
for sg in (1,-1):
 L=(Ts+sg*np.sqrt((Ts*Ts-4).astype(complex)))/2;X=np.where(Ts>2,np.log(np.abs(L.real))*.9+1,L.real);Z=np.where(Ts>2,0,L.imag);pts.append(np.c_[X,(Ts-3)*.38,-Z]);cs.append(np.where((Ts<2)[:,None],GOLD,BLUE))
groups.append((np.vstack(pts),np.vstack(cs)))
X=np.linspace(.03,4.2,6000);aa=X**2;bb=-1+X+2*X**2+X**3-X**4;D=bb*bb-4*aa*aa;pts=[]
for sg in (1,-1):
 L=np.where(D>=0,(-bb+sg*np.sqrt(np.clip(D,0,None)))/(2*aa),np.nan);ok=np.isfinite(L)&(np.abs(L)<7.5);pts.append(np.c_[X[ok]-1.6,L[ok]*.28,0*X[ok]])
pp=np.vstack(pts);groups.append((pp,col(len(pp),WHITE)))
xy=R.uniform(-1,1,(12000,2));pts=[];cs=[]
for S,cx,cc in [(np.array([[2,-1],[-1,-2]]),-1.45,None),(np.array([[-2,1],[1,-2]]),1.45,ROSE)]:
 q=np.einsum('ni,ij,nj->n',xy,S,xy);pts.append(np.c_[xy[:,0]*.75+cx,q*.13,xy[:,1]*.75]);cs.append(np.where((q>0)[:,None],GOLD,BLUE) if cc is None else col(len(q),cc))
groups.append((np.vstack(pts),np.vstack(cs)))
p,t=tube(fig8,15000,.05);groups.append((p,np.where((np.sin(t*3)>0)[:,None],GOLD,BLUE)))
blob=bytearray();views=[];accs=[];meshes=[];nodes=[]
def add(arr,target=None,typ='VEC3',minmax=False):
 global blob
 arr=np.ascontiguousarray(arr,dtype=np.float32);off=len(blob);blob+=arr.tobytes()
 while len(blob)%4:blob+=b'\0'
 views.append(BufferView(buffer=0,byteOffset=off,byteLength=arr.nbytes,target=target))
 kw=dict(min=arr.min(axis=0).tolist() if arr.ndim>1 else [float(arr.min())],max=arr.max(axis=0).tolist() if arr.ndim>1 else [float(arr.max())]) if minmax else {}
 accs.append(Accessor(bufferView=len(views)-1,componentType=5126,count=len(arr),type=typ,**kw));return len(accs)-1
for i,(P,Cc) in enumerate(groups):
 pa=add(P,34962,'VEC3',True);ca=add(np.clip(Cc,0,1),34962,'VEC3')
 meshes.append(Mesh(name=f'chapter_{i+1}',primitives=[Primitive(attributes=Attributes(POSITION=pa,COLOR_0=ca),mode=0)]))
 nodes.append(Node(name=f'chapter_{i+1}',mesh=i,scale=[0,0,0]))
anim=Animation(name='timeline_82s',channels=[],samplers=[])
for i,(a,b) in enumerate(CH):
 tt=np.array([0,a,b,82] if a>0 else [0,b,82],np.float32);sc=np.array(([[0,0,0],[1,1,1],[0,0,0],[0,0,0]] if a>0 else [[1,1,1],[0,0,0],[0,0,0]]),np.float32)
 it=add(tt,None,'SCALAR',True);ov=add(sc,None,'VEC3')
 anim.samplers.append(AnimationSampler(input=it,output=ov,interpolation='STEP'));anim.channels.append(AnimationChannel(sampler=len(anim.samplers)-1,target=AnimationChannelTarget(node=i,path='scale')))
 k=np.linspace(a,b,9).astype(np.float32);q=np.array([[0,np.sin(.5*.25*(x-a)),0,np.cos(.5*.25*(x-a))] for x in k],np.float32)
 it2=add(k,None,'SCALAR',True);ov2=add(q,None,'VEC4')
 anim.samplers.append(AnimationSampler(input=it2,output=ov2,interpolation='LINEAR'));anim.channels.append(AnimationChannel(sampler=len(anim.samplers)-1,target=AnimationChannelTarget(node=i,path='rotation')))
g=GLTF2(scene=0,scenes=[Scene(nodes=list(range(len(nodes))))],nodes=nodes,meshes=meshes,accessors=accs,bufferViews=views,buffers=[Buffer(byteLength=len(blob))],animations=[anim])
g.set_binary_blob(bytes(blob));out=ROOT/'Count_Me_as_One_Moving_3D_Model.glb';g.save(str(out))
json.dump({'file':out.name,'chapters':len(nodes),'points_per_chapter':[len(P) for P,_ in groups],'animation_seconds':82,'bytes':out.stat().st_size},open(ROOT/'model_checks.json','w'),indent=1)
print(out,out.stat().st_size)
