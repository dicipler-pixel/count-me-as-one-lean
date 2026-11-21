"""SCRIPT: COUNT-ME-AS-ONE-FILM-01
Deterministic 3D film for "Count Me as One" (figure-eight anchors). Built in the manner of
Monopole v5: luminous point samples, bloom, chapter titles, composited equations.
Every moving object is computed from the mathematics it depicts (no generated imagery).
Point samples are rendering samples only, never a density of anything physical.
Run --preview or --render.
"""
from pathlib import Path
import math,time,json,subprocess,io,argparse
import numpy as np
from PIL import Image,ImageDraw,ImageFont
import moderngl
ROOT=Path(__file__).resolve().parents[1]
FPS=24;DURATION=82
GOLD=np.array([1.0,.60,.12]);BLUE=np.array([.06,.52,1.0]);ROSE=np.array([1.0,.30,.42]);WHITE=np.array([.80,.90,1.0])
PHI=(1+5**.5)/2
CH=[(0,9,'TWO STONES. ONE SPACE.','Two regular ideal tetrahedra close every edge of the figure-eight complement.','THURSTON\'S GLUING EQUATION'),
 (9,20,'TWO BRANCHES. ONE SQUARE.','On z = w the edge equation factors; squaring carries each branch on.','THE SYMMETRIC SLICE'),
 (20,31,'SIX TURNS AND HOME.','The trefoil\'s monodromy obeys the regular-tetrahedron polynomial.','THE CHIRAL KNOT\'S TURN'),
 (31,42,'THE THROWN BRANCH STRETCHES.','The golden branch squared is the figure-eight monodromy, the cat map.','THE KEPT DIFFERENCE'),
 (42,54,'ONE LADDER. ONE EDGE.','Below trace 2 the rails circle; above it they stretch; at 2 they merge.','THE TRACE LADDER'),
 (54,64,'THE BRANCHES ARE BRANCH POINTS.','Used as a meridian eigenvalue, each shape ramifies the A-polynomial.','THE A-POLYNOMIAL OF 4₁'),
 (64,74,'ONE HAND, AND ITS MIRROR.','The figure-eight meets its mirror; the trefoil never can.','CHIRALITY ON THE SEIFERT FORM'),
 (74,82,'COUNT ME AS ONE.','Every link in this film is a checked theorem.','FIGURE-EIGHT ANCHORS / LEAN')]
EQ=[r'$z(z-1)\,w(w-1)=1,\qquad z=w=e^{i\pi/3}$',
    r'$z^2(z-1)^2-1=(z^2-z+1)(z^2-z-1)$',
    r'$h_{3_1}^2=h_{3_1}-I,\qquad h_{3_1}^6=I$',
    r'$z^2-z-1=0\ \Rightarrow\ (z^2)^2-3z^2+1=0,\qquad h_{4_1}=\left[\begin{smallmatrix}2&1\\1&1\end{smallmatrix}\right]$'.replace(r'\left[\begin{smallmatrix}2&1\\1&1\end{smallmatrix}\right]','[[2,1],[1,1]]'),
    r'$t_{k+1}=T\,t_k-t_{k-1},\qquad \lambda_\pm=\frac{T\pm\sqrt{T^2-4}}{2}$',
    r'$b+2a=-(x+1)^2(x^2-3x+1),\quad b-2a=-(x-1)^2(x^2+x+1)$',
    r'$P^{T}V_{4_1}P=-V_{4_1}^{T},\qquad x^{T}(V_{3_1}+V_{3_1}^{T})x<0$',
    r'$z^2-z+1\ \ \mathrm{and}\ \ z^2-z-1$']
VERT='''#version 330
in vec3 p; in vec3 c; in float seed;
uniform mat4 vp;uniform float pointscale;uniform float time;
out vec3 col;out float alpha;
void main(){
 float breathe=1.+.04*sin(time*.6+seed*6.28318);
 col=c*(.45+.75*seed)*breathe; alpha=.30+.55*seed;
 gl_Position=vp*vec4(p,1.); gl_PointSize=pointscale*(1.5+1.6*seed);
}'''
FRAG='''#version 330
in vec3 col;in float alpha;out vec4 frag;
void main(){float r=length(gl_PointCoord-.5)*2.;if(r>1.)discard;
 float k=exp(-r*r*5.0)*(1.-smoothstep(.65,1.,r));frag=vec4(col*k,alpha*k);}'''
LINEV='''#version 330
in vec3 p;in vec3 color;uniform mat4 vp;out vec3 col;
void main(){gl_Position=vp*vec4(p,1.);col=color;}'''
LINEF='''#version 330
in vec3 col;out vec4 frag;void main(){frag=vec4(col,1.);}'''
QUADV='''#version 330
in vec2 p;out vec2 uv;void main(){uv=p*.5+.5;gl_Position=vec4(p,0.,1.);}'''
BLUR='''#version 330
uniform sampler2D image;uniform vec2 direction;in vec2 uv;out vec4 frag;
void main(){vec3 c=vec3(0.);for(int i=-4;i<=4;i++){float w=exp(-float(i*i)/6.);c+=texture(image,uv+direction*float(i)).rgb*w/4.328;}frag=vec4(c,1.);}'''
POST='''#version 330
uniform sampler2D image;uniform sampler2D bloom;in vec2 uv;out vec4 frag;
void main(){vec3 c=texture(image,uv).rgb+texture(bloom,uv).rgb*1.15;c=vec3(1.)-exp(-c*1.15);c=pow(c,vec3(.455));frag=vec4(c,1.);}'''
def ease(x):x=np.clip(x,0,1);return x*x*(3-2*x)
def unit(v):v=np.array(v,dtype=float);return v/max(np.linalg.norm(v),1e-12)
def lookat(eye,target):
 f=unit(target-eye);s=unit(np.cross(f,[0,0,1]));u=np.cross(s,f);m=np.eye(4);m[:3,:3]=[s,u,-f];m[:3,3]=-m[:3,:3]@eye;return m
def ortho(w,h,scale=1.65):
 m=np.eye(4);m[0,0]=1/scale;m[1,1]=1/(scale*h/w);m[2,2]=-2/40;return m
RNG=np.random.default_rng(4141)
# ---------- geometry (all computed) ----------
def trefoil(t):return np.c_[np.sin(t)+2*np.sin(2*t),np.cos(t)-2*np.cos(2*t),-np.sin(3*t)]/3.2
def fig8(t):return np.c_[(2+np.cos(2*t))*np.cos(3*t),(2+np.cos(2*t))*np.sin(3*t),np.sin(4*t)]/3.0
def tube(curve,n,r,mirror=False):
 t=RNG.uniform(0,2*np.pi,n);c=curve(t);d=(curve(t+1e-3)-curve(t-1e-3));d/=np.linalg.norm(d,axis=1)[:,None]
 a=np.cross(d,[0,0,1.0]);a/=np.linalg.norm(a,axis=1)[:,None]+1e-9;b=np.cross(d,a)
 th=RNG.uniform(0,2*np.pi,n);rr=r*np.sqrt(RNG.uniform(.2,1,n))
 p=c+rr[:,None]*(np.cos(th)[:,None]*a+np.sin(th)[:,None]*b)
 if mirror:p[:,2]*=-1
 return p,t
def seg_points(a,b,n):s=RNG.uniform(0,1,n)[:,None];return a+(b-a)*s+RNG.normal(0,.006,(n,3))
def tetra(center,size,rot):
 V=np.array([[1,1,1],[1,-1,-1],[-1,1,-1],[-1,-1,1]],float)*size/1.732
 R=rotz(rot)@rotx(rot*.7);V=V@R.T+center;pts=[]
 for i in range(4):
  for j in range(i+1,4):pts.append(seg_points(V[i],V[j],900))
 return np.vstack(pts),V
def rotz(a):c,s=np.cos(a),np.sin(a);return np.array([[c,-s,0],[s,c,0],[0,0,1]])
def rotx(a):c,s=np.cos(a),np.sin(a);return np.array([[1,0,0],[0,c,-s],[0,s,c]])
def roty(a):c,s=np.cos(a),np.sin(a);return np.array([[c,0,s],[0,1,0],[-s,0,c]])
H31=np.array([[0,1],[-1,1]],float);H41=np.array([[2,1],[1,1]],float)
EV41,EVEC41=np.linalg.eigh(H41)
def h41_pow(s):return EVEC41@np.diag(EV41**s)@EVEC41.T   # h41 is symmetric positive definite, so h^s is exact
def lad(T,k):
 a,b=2,T
 for _ in range(k):a,b=b,T*b-a
 return a
class Renderer:
 def __init__(self,w=1080,h=1350):
  self.w=w;self.h=h;self.c=moderngl.create_standalone_context(backend='egl');c=self.c;self.g=moderngl
  self.p=c.program(vertex_shader=VERT,fragment_shader=FRAG);self.pb=c.buffer(reserve=48*300000);self.pvao=c.vertex_array(self.p,[(self.pb,'3f 3f f','p','c','seed')])
  self.line=c.program(vertex_shader=LINEV,fragment_shader=LINEF);self.lb=c.buffer(reserve=4000000);self.lvao=c.vertex_array(self.line,[(self.lb,'3f 3f','p','color')])
  self.scene=c.texture((w,h),4,dtype='f2');self.fbo=c.framebuffer(self.scene)
  self.small=[c.texture((w//4,h//4),4,dtype='f2') for _ in range(2)];self.sfb=[c.framebuffer(t) for t in self.small]
  self.out=c.simple_framebuffer((w,h),components=3)
  q=c.buffer(np.array([[-1,-1],[1,-1],[-1,1],[-1,1],[1,-1],[1,1]],'f4').tobytes())
  self.blur=c.program(vertex_shader=QUADV,fragment_shader=BLUR);self.bvao=c.vertex_array(self.blur,[(q,'2f','p')]);self.blur['image']=0
  self.post=c.program(vertex_shader=QUADV,fragment_shader=POST);self.post['image']=0;self.post['bloom']=1;self.qvao=c.vertex_array(self.post,[(q,'2f','p')])
  self.fonts={};self.s=w/1080;self.eq=[];self.clean=False
  self.fontfile=str(ROOT/'source/fonts/DejaVuSans.ttf');self.boldfile=str(ROOT/'source/fonts/DejaVuSans-Bold.ttf')
  from matplotlib.mathtext import math_to_image
  from matplotlib.font_manager import FontProperties
  for e in EQ:
   b=io.BytesIO();math_to_image(e,b,prop=FontProperties(size=22),dpi=160,color='black',format='png');b.seek(0)
   ink=Image.open(b).convert('L');im=Image.new('RGBA',ink.size,(232,240,248,0));im.putalpha(Image.eval(ink,lambda x:255-x));self.eq.append(im)
  self.build_static()
 def build_static(self):
  self.f8,self.f8t=tube(fig8,40000,.05);self.f8m,_=tube(fig8,40000,.05,mirror=True)
  self.tr,self.trt=tube(trefoil,36000,.05)
  self.seeds={k:RNG.uniform(0,1,300000).astype('f4') for k in ['a']}
  # torus samples in (u,v) coordinates for the cat-map flow
  self.tuv=RNG.uniform(0,1,(60000,2))
  # quadratic-form surfaces
  g=RNG.uniform(-1,1,(50000,2));self.qxy=g
 def font(self,size,bold=False):
  key=(size,bold)
  if key not in self.fonts:self.fonts[key]=ImageFont.truetype(self.boldfile if bold else self.fontfile,max(1,round(size*self.s)))
  return self.fonts[key]
 def text(self,im,xy,txt,size=24,color='#dbeaf1',bold=False,anchor=None):ImageDraw.Draw(im).text(tuple(round(v*self.s) for v in xy),txt,font=self.font(size,bold),fill=color,anchor=anchor)
 def pts(self,P,C,t):
  n=len(P);seed=self.seeds['a'][:n]
  if C.ndim==1:C=np.tile(C,(n,1))
  arr=np.c_[P,C,seed].astype('f4');self.pb.write(arr.tobytes());self.p['time']=t;self.p['pointscale']=1.0*self.s;self.pvao.render(self.g.POINTS,vertices=n)
 def lines(self,arr,color):
  x=np.array(arr,float);v=np.repeat(x,2,axis=0)[1:-1];v=np.c_[v,np.tile(color,(len(v),1))].astype('f4');self.lb.write(v.tobytes());self.lvao.render(self.g.LINES,vertices=len(v))
 def bead(self,pos,color,t,r=.035,n=900):
  p=pos+RNG.normal(0,r,(n,3));self.pts(p,color*1.8,t)
 def project(self,v):
  q=self.vp@np.r_[v,1.];q=q[:3]/q[3];return ((q[0]+1)/2*self.w/self.s,(1-q[1])/2*self.h/self.s)
 def camera(self,t,eye_dist=8,elev=2.6,yaw0=0.,spin=.06,scale=1.65,target=(0,0,0)):
  yaw=yaw0+spin*t;eye=np.array([eye_dist*np.sin(yaw),-eye_dist*np.cos(yaw),elev]);self.vp=ortho(self.w,self.h,scale)@lookat(eye,np.array(target,float))
  self.p['vp'].write(self.vp.T.astype('f4').tobytes());self.line['vp'].write(self.vp.T.astype('f4').tobytes())
 def frame(self,t):
  k=next((i for i,x in enumerate(CH) if x[0]<=t<x[1]),len(CH)-1);a,b,_,_,_=CH[k];u=(t-a)/(b-a)
  c=self.c;g=self.g;self.fbo.use();c.viewport=(0,0,self.w,self.h);c.clear(0,0,0,1);c.enable(g.BLEND|g.PROGRAM_POINT_SIZE);c.blend_func=(g.SRC_ALPHA,g.ONE)
  self.info={}
  getattr(self,f's{k}')(t,u)
  c.disable(g.BLEND);self.scene.use(0);self.sfb[0].use();c.viewport=(0,0,self.w//4,self.h//4);self.blur['direction']=(4/self.w,0);self.bvao.render()
  self.small[0].use(0);self.sfb[1].use();self.blur['direction']=(0,4/self.h);self.bvao.render()
  self.out.use();c.viewport=(0,0,self.w,self.h);self.scene.use(0);self.small[1].use(1);self.qvao.render()
  im=Image.frombytes('RGB',(self.w,self.h),self.out.read(components=3,alignment=1)).transpose(Image.Transpose.FLIP_TOP_BOTTOM)
  self.annotate(im,t,k,u)
  if self.clean:return im
  if t>DURATION-.65:im=Image.blend(Image.new('RGB',im.size),im,float(ease((DURATION-t)/.65)))
  if t<.5:im=Image.blend(Image.new('RGB',im.size),im,float(ease(t/.5)))
  return im
 # ---- scenes ----
 def s0(self,t,u):
  self.camera(t,spin=.09,scale=1.55)
  R=rotz(.25*t);P=self.f8@R.T
  col=np.where((np.sin(self.f8t*3)>0)[:,None],GOLD,BLUE)*.9
  self.pts(P*1.05,col,t)
  gap=1.6*(1-ease(u*1.6))+0.0
  for sgn,cl in [(-1,GOLD),(1,BLUE)]:
   pts,V=tetra(np.array([sgn*(.55+gap),0,-.05]),.62,.3*t*sgn);self.pts(pts,cl*1.3,t)
  self.info['glued']=u>.62
 def s1(self,t,u):
  self.camera(t,elev=4.2,spin=.04,scale=1.6,target=(.6,0,0))
  # complex plane as a faint dotted disc, tilted (z drawn in the x-y plane)
  P=np.c_[RNG.uniform(-1.9,3.4,9000),RNG.uniform(-1.6,1.6,9000),np.zeros(9000)];self.pts(P,np.array([.10,.13,.18]),t)
  a=np.linspace(0,2*np.pi,361);self.lines(np.c_[np.cos(a),np.sin(a),0*a],GOLD*.45);self.lines([[-1.9,0,0],[3.4,0,0]],BLUE*.45)
  s=ease((u-.18)/.6)
  w=np.exp(1j*np.pi/3)
  for r in [w,np.conj(w)]:
   self.bead([r.real,r.imag,0],GOLD,t)
   ang=np.angle(r)*(1+s);z=np.exp(1j*ang);self.bead([z.real,z.imag,0.0],GOLD*.9,t,r=.03)
   tr=np.exp(1j*np.angle(r)*(1+np.linspace(0,s,60)));self.lines(np.c_[tr.real,tr.imag,0*tr.real+.002],GOLD*.8)
  for r in [PHI,-1/PHI]:
   self.bead([r,0,0],BLUE,t);m=abs(r)**(1+s);self.bead([m,0,0.0],BLUE*.9,t,r=.03)
   ar=np.linspace(abs(r) if r>0 else -abs(r),m,60);hh=.25*np.sin(np.linspace(0,np.pi,60))*(1 if r>0 else -1)
   self.lines(np.c_[np.linspace(r,m,60),0*ar,hh*abs(m-r)],BLUE*.8)
  self.info['s']=s
 def s2(self,t,u):
  self.camera(t,spin=.08,scale=1.75,target=(0,0,-.35))
  R=rotz(.3*t);self.pts(self.tr@R.T*1.0+[0,0,.35],ROSE*.95,t)
  # monodromy orbit drawn on the invariant ellipse in a plane under the knot
  k=int(np.floor(u*7))%7;Q=np.array([[2,-1],[-1,2]],float)
  aa=np.linspace(0,2*np.pi,241);E=[];x0=np.array([.62,0.0])
  qv=x0@Q@x0
  for th in aa:
   d=np.array([np.cos(th),np.sin(th)]);r=np.sqrt(qv/(d@Q@d));E.append([r*d[0],r*d[1],-1.25])
  self.lines(E,GOLD*.5)
  orbit=[x0];
  for _ in range(6):orbit.append(H31@orbit[-1])
  for i,q in enumerate(orbit[:6]):self.bead([q[0],q[1],-1.25],GOLD*(1.4 if i==k%6 else .5),t,r=.028,n=500)
  self.info['k']=k;self.info['rung']=lad(1,k);self.info['orbit']=orbit
 def s3(self,t,u):
  self.camera(t,elev=3.4,spin=.05,scale=1.7)
  s=3.0*ease(u)
  UV=(self.tuv@h41_pow(s).T)%1.0
  Rm,rm=1.15,.45;th=2*np.pi*UV[:,0];ph=2*np.pi*UV[:,1]
  P=np.c_[(Rm+rm*np.cos(ph))*np.cos(th),(Rm+rm*np.cos(ph))*np.sin(th),rm*np.sin(ph)]
  w=self.tuv[:,0][:,None];C=GOLD*(1-w)+BLUE*w
  self.pts(P,C*.9,t)
  self.info['s']=s;self.info['trace']=round(lad(3,int(np.floor(s+1e-9)))) if s>=1 else 2
 def s4(self,t,u):
  self.camera(t,elev=3.0,spin=.05,scale=1.8,target=(.6,0,0))
  Ts=np.linspace(0,6,500);zs=(Ts-3)*.38
  for sgn in (1,-1):
   L=(Ts+sgn*np.sqrt((Ts*Ts-4).astype(complex)))/2;X=np.where(Ts>2,np.log(np.abs(L.real))*.9+1,L.real);Y=np.where(Ts>2,0,L.imag)
   # rails: below 2 on the unit circle (x = Re, y = Im); above 2 on the real line in log scale shifted to 1
   col=np.where((Ts<2)[:,None],GOLD,BLUE)
   P=np.c_[X,Y,zs];self.pts(np.repeat(P,30,axis=0)+RNG.normal(0,.012,(len(P)*30,3)),np.repeat(col,30,axis=0)*.7,t)
  T=6*ease(u);z=(T-3)*.38
  for sgn in (1,-1):
   l=(T+sgn*np.sqrt(complex(T*T-4)))/2;x=np.log(abs(l.real))*.9+1 if T>2 else l.real;y=0 if T>2 else l.imag
   self.bead([x,y,z],GOLD if T<2 else BLUE,t,r=.04)
  self.lines([[ -1.2,-1.2,(2-3)*.38],[2.6,-1.2,(2-3)*.38],[2.6,1.2,(2-3)*.38],[-1.2,1.2,(2-3)*.38],[-1.2,-1.2,(2-3)*.38]],WHITE*.35)
  self.info['T']=T
 def s5(self,t,u):
  self.camera(t,elev=.9,spin=.012,yaw0=-.18,scale=2.25,target=(.35,0,.35))
  X=np.linspace(.03,4.2,6000);a=X**2;b=-1+X+2*X**2+X**3-X**4;D=b*b-4*a*a
  for sgn in (1,-1):
   L=np.where(D>=0,(-b+sgn*np.sqrt(np.clip(D,0,None)))/(2*a),np.nan);ok=np.isfinite(L)&(np.abs(L)<7.5)
   P=np.c_[X[ok]-1.6,0*X[ok],L[ok]*.28];self.pts(np.repeat(P,8,axis=0)+RNG.normal(0,.008,(ok.sum()*8,3)),WHITE*.55,t)
  for Lv,cl in [(1,BLUE),(-1,GOLD)]:self.lines([[-1.6,0,Lv*.28],[2.6,0,Lv*.28]],cl*.5)
  rise=ease(u*1.4)
  for xr in [(3-5**.5)/2,(3+5**.5)/2]:self.bead([xr-1.6,0,.28],BLUE,t,r=.035*rise+.001)
  self.bead([1-1.6,0,-.28],WHITE,t,r=.03)
  # complex x-plane below, with the cube-root ramification points
  ang=np.linspace(0,2*np.pi,241);cx0,cz0=1.35,1.7
  self.lines(np.c_[np.cos(ang)*.55+cx0,np.sin(ang)*.55,cz0+0*ang],GOLD*.35)
  for r in [np.exp(2j*np.pi/3),np.exp(-2j*np.pi/3)]:self.bead([r.real*.55+cx0,r.imag*.55,cz0],GOLD,t,r=.03*rise+.001)
 def s6(self,t,u):
  self.camera(t,elev=3.0,spin=.03,scale=2.0)
  xy=self.qxy*1.0
  for S,cx,cl in [(np.array([[2,-1],[-1,-2]]),-1.45,None),(np.array([[-2,1],[1,-2]]),1.45,ROSE)]:
   q=np.einsum('ni,ij,nj->n',xy,S,xy);P=np.c_[xy[:,0]*.75+cx,xy[:,1]*.75,q*.13]
   C=np.where((q>0)[:,None],GOLD,BLUE)*.75 if cl is None else np.tile(cl*.75,(len(q),1))
   self.pts(P,C,t)
  # the mirror certificate acts on the figure-eight form: animate x -> P x on a ring of lattice points
  P41=np.array([[-1,-1],[2,1]],float);s=ease(u)
  ring=np.array([[1,0],[0,1],[-1,0],[0,-1],[1,1],[-1,-1]],float)
  for p0 in ring:
   p1=P41@p0;pp=(1-s)*p0+s*p1;pp=pp/ max(1,np.abs(pp).max())
   self.bead([pp[0]*.75-1.45,pp[1]*.75,.75],WHITE,t,r=.022,n=300)
 def s7(self,t,u):
  self.camera(t,spin=.1,scale=1.6,target=(0,0,.25))
  R=rotz(.25*t);col=np.where((np.sin(self.f8t*3)>0)[:,None],GOLD,BLUE)*.85
  self.pts(self.f8@R.T*.95+[0,0,.55],col,t)
 def annotate(self,im,t,k,u):
  a,b,title,sub,tag=CH[k]
  if self.clean:
   self.text(im,(540,46),tag,21,'#8fbfd6',True,'mm')
  else:
   self.text(im,(540,46),tag,21,'#8fbfd6',True,'mm')
  if self.clean: rows=[]
  else: rows=[title] if len(title)<=30 else [title[:title.rfind(' ',0,30)],title[title.rfind(' ',0,30)+1:]]
  for j,row in enumerate(rows):self.text(im,(540,105+j*47),row,37,'#f1f5f8',True,'mm')
  if not self.clean:
   sy=193 if len(rows)>1 else 164
   self.text(im,(540,sy),sub,20.5,'#a5b6c2',False,'mm')
   self.text(im,(540,236),'COMPUTED 3D GEOMETRY  /  CHECKED IN LEAN',15,'#657c89',False,'mm')
  e=self.eq[k].copy();e.thumbnail((round(990*self.s),round(64*self.s)));im.paste(e,((self.w-e.width)//2,round(1100*self.s)),e)
  I=self.info
  if k==0:
   self.text(im,(540,1012),'Gold and blue: the two tetrahedra.  Glow: rendering only.',20,'#b3c9d3',False,'mm')
   self.text(im,(540,1192),'Each tetrahedron contributes −1;  (−1)(−1) = 1 closes the edge.',22,'#e3edf2',False,'mm')
  if k==1:
   self.text(im,(150,320),'GOLD  z² − z + 1',20,'#f6c56a',True);self.text(im,(150,348),'e^{±iπ/3} → e^{±2iπ/3}',19,'#f1dcae')
   self.text(im,(650,320),'BLUE  z² − z − 1',20,'#7fbaff',True);self.text(im,(650,348),'φ, −1/φ → φ², φ⁻²',19,'#c9defa')
   self.text(im,(540,1012),'Bright beads: the shapes.  Moving beads: z^(1+s), s = %.2f'%I['s'],20,'#b3c9d3',False,'mm')
   self.text(im,(540,1192),'Only the gold branch is fixed by z ↦ 1/(1 − z).',22,'#e3edf2',False,'mm')
  if k==2:
   self.text(im,(540,1012),'Rose: the trefoil.  Gold ring: the orbit of h = [[0,1],[−1,1]].',20,'#b3c9d3',False,'mm')
   self.text(im,(150,330),'TURN',19,'#f6c56a',True);self.text(im,(150,360),f"{I['k']}",34,'#ffe7b8',True)
   self.text(im,(810,330),'RUNG',19,'#f6c56a',True);self.text(im,(810,360),f"{I['rung']:+d}",34,'#ffe7b8',True)
   self.text(im,(540,1192),'Rungs 2, 1, −1, −2, −1, 1, 2: home on the seventh.',22,'#e3edf2',False,'mm')
  if k==3:
   self.text(im,(540,1012),'Torus points moved by h^s, h = [[2,1],[1,1]] (exact power).  s = %.2f'%I['s'],19.5,'#b3c9d3',False,'mm')
   self.text(im,(150,330),'TRACE OF h^n',19,'#7fbaff',True);seq=[2,3,7,18]
   n=int(np.floor(I['s']+1e-9));self.text(im,(150,362),'  '.join(str(lad(3,j)) for j in range(n+1)),28,'#d4e7ff',True)
   self.text(im,(540,1192),'Five turns give 123 = φ¹⁰ + φ⁻¹⁰.  It never comes home.',22,'#e3edf2',False,'mm')
  if k==4:
   T=I['T'];self.text(im,(150,330),'TRACE T',19,'#e8eef3',True);self.text(im,(150,362),f'{T:.2f}',34,'#ffffff',True)
   reg='BAND · rails on the circle' if T<1.99 else ('EDGE · rails merged' if T<2.05 else 'GAP · rails on the line (log scale)')
   self.text(im,(540,1012),reg,21,'#f6c56a' if T<1.99 else ('#ffffff' if T<2.05 else '#7fbaff'),True,'mm')
   self.text(im,(540,1192),'Trefoil T = 1 · figure-eight T = 3 · Apéry and Catalan reach 34.',21,'#e3edf2',False,'mm')
  if k==5:
   self.text(im,(540,1012),'White: real points of A(L, M) = 0 over x = M².  Gold ring: complex x-plane.',19.5,'#b3c9d3',False,'mm')
   xa,ya=self.project(np.array([(3+5**.5)/2-1.6,0,.28]));xb,yb=self.project(np.array([1.35,0,1.7]));xn,yn=self.project(np.array([-.6,0,-.28]))
   self.text(im,(xa,ya-48),'L = +1:  x² − 3x + 1',19,'#7fbaff',True,'mm');self.text(im,(xa,ya-24),'golden branch squared',17,'#c9defa',False,'mm')
   self.text(im,(xb,yb-62),'complex x:  x² + x + 1',19,'#f6c56a',True,'mm');self.text(im,(xb,yb-38),'L = −1, regular branch squared',17,'#f1dcae',False,'mm')
   self.text(im,(xn,yn+34),'node  x = 1, L = −1',17,'#e6edf2',False,'mm')
   self.text(im,(540,1192),'A palindromic in L: the amphichiral involution L ↦ 1/L.',22,'#e3edf2',False,'mm')
  if k==6:
   x1,y1=self.project(np.array([-1.45,0,-.55]));x2,y2=self.project(np.array([1.45,0,-.55]))
   self.text(im,(x1,min(y1+60,975)),'FIGURE-EIGHT  signature 0',20,'#f6c56a',True,'mm');self.text(im,(x2,min(y2+60,975)),'TREFOIL  signature −2',20,'#ff8fa0',True,'mm')
   self.text(im,(540,1012),'Heights: x·(V + Vᵀ)x.  White beads: lattice points moved by P.',19.5,'#b3c9d3',False,'mm')
   self.text(im,(540,1192),'A saddle can be turned into its mirror; a bowl cannot.',22,'#e3edf2',False,'mm')
  if k==7:
   self.text(im,(540,770),'80',76,'#d8f0fa',True,'mm');self.text(im,(540,832),'CHECKED THEOREMS',21,'#adcfdd',True,'mm')
   self.text(im,(540,900),'11 FALSE CONTROLS REJECTED  ·  82 RELATION EDGES',21,'#f0bf86',True,'mm')
   self.text(im,(540,945),'Lean 4.34.1  ·  independent kernel replay  ·  standard axioms only',18.5,'#d7e8ef',False,'mm')
   self.text(im,(540,1192),'In the knotted-cord records, the figure-eight knot is the digit one.',21,'#e3edf2',False,'mm')
  if not self.clean:self.text(im,(540,1302),'Jeromie Beasley · Claude (Anthropic)',18,'#829ca9',False,'mm')
def render(args):
 rr=Renderer(args.width,args.height)
 if args.preview:
  rr.clean=args.clean
  for t in args.times:rr.frame(t).save(ROOT/('stills' if args.clean else 'qa')/f'scene_{t:05.1f}.png')
  return
 out=ROOT/'Count_Me_as_One_The_Moving_Knot.mp4';log=open(ROOT/'encode.log','w')
 cmd=['ffmpeg','-y','-f','rawvideo','-pix_fmt','rgb24','-s',f'{args.width}x{args.height}','-r',str(FPS),'-i','pipe:0','-an','-c:v','libx264','-preset','veryfast','-crf','18','-pix_fmt','yuv420p','-movflags','+faststart',str(out)]
 proc=subprocess.Popen(cmd,stdin=subprocess.PIPE,stderr=log);start=time.time()
 N=round(args.seconds*FPS)
 for i in range(N):
  im=rr.frame(i/FPS);proc.stdin.write(im.tobytes())
  if i%96==0:print(f'Frame {i}/{N}; elapsed {time.time()-start:.1f}s',flush=True)
 proc.stdin.close();assert proc.wait()==0;log.close();print(out,flush=True)
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--preview',action='store_true');ap.add_argument('--clean',action='store_true');ap.add_argument('--render',action='store_true')
 ap.add_argument('--width',type=int,default=1080);ap.add_argument('--height',type=int,default=1350);ap.add_argument('--seconds',type=float,default=DURATION)
 ap.add_argument('--times',type=float,nargs='*',default=[5,15,25.5,38,44,50,59,69,78]);render(ap.parse_args())
