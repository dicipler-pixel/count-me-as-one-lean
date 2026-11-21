/* SCRIPT: COUNT-ME-AS-ONE-MIXER-V51-01
   Count Me as One, with the Dirac Anchor Recovered — mixer (Jeromie Beasley). Built for this paper on the shared 3D parts (mixer3d_parts_v1).
   One feed operator, one live eye per result, in film order. Every readout is computed live from the
   mathematics it reports; grades match the paper. The mixer explores the results; it does not test them. */
(function(){
"use strict";
const M = window.Mixer3D, T = M.T;
const GOLD=[1.0,0.62,0.16], BLUE=[0.10,0.52,1.0], ROSE=[1.0,0.33,0.46], WHITE=[0.85,0.92,1.0], DIM=[0.25,0.32,0.40];
const PHI=(1+Math.sqrt(5))/2;
const V3=(x,y,z)=>new T.Vector3(x,y,z);
/* complex arithmetic */
const C=(re,im)=>({re,im}), cadd=(a,b)=>C(a.re+b.re,a.im+b.im), csub=(a,b)=>C(a.re-b.re,a.im-b.im),
  cmul=(a,b)=>C(a.re*b.re-a.im*b.im,a.re*b.im+a.im*b.re), cabs=a=>Math.hypot(a.re,a.im),
  cexp=t=>C(Math.cos(t),Math.sin(t)), fmtc=(a,d=4)=>`${a.re.toFixed(d)} ${a.im<0?'−':'+'} ${Math.abs(a.im).toFixed(d)}i`;
const f=(x,d=4)=>(x<0?'−':'')+Math.abs(x).toFixed(d);
function lad(Tv,k){ let a=2,b=Tv; for(let i=0;i<k;i++){ const c=Tv*b-a; a=b; b=c; } return a; }
function mm(A,B){ return [[A[0][0]*B[0][0]+A[0][1]*B[1][0],A[0][0]*B[0][1]+A[0][1]*B[1][1]],[A[1][0]*B[0][0]+A[1][1]*B[1][0],A[1][0]*B[0][1]+A[1][1]*B[1][1]]]; }
const H31=[[0,1],[-1,1]], H41=[[2,1],[1,1]];
function mpow(A,n){ let R=[[1,0],[0,1]]; for(let i=0;i<n;i++) R=mm(R,A); return R; }
/* exact real power of the symmetric positive h41: eigenvalues phi^2, phi^-2 */
const ev1=PHI*PHI, ev2=1/(PHI*PHI);
const u1=(()=>{ const v=[1,ev1-2]; const n=Math.hypot(v[0],v[1]); return [v[0]/n,v[1]/n]; })(), u2=[-u1[1],u1[0]];
function h41pow(s){ const a=Math.pow(ev1,s), b=Math.pow(ev2,s);
  return [[a*u1[0]*u1[0]+b*u2[0]*u2[0], a*u1[0]*u1[1]+b*u2[0]*u2[1]],[a*u1[1]*u1[0]+b*u2[1]*u2[0], a*u1[1]*u1[1]+b*u2[1]*u2[1]]]; }
function knotPoints(curve, n, r, colfn){ const p=M.points(n,0.055); const rnd=mulberry(7);
  for(let i=0;i<n;i++){ const t=rnd()*Math.PI*2; const c=curve(t), d=curve(t+1e-3).sub(curve(t-1e-3)).normalize();
    let a=new T.Vector3().crossVectors(d,V3(0,1,0)); if(a.length()<1e-3) a=V3(1,0,0); a.normalize(); const b=new T.Vector3().crossVectors(d,a);
    const th=rnd()*Math.PI*2, rr=r*Math.sqrt(0.2+0.8*rnd()); const P=c.clone().addScaledVector(a,rr*Math.cos(th)).addScaledVector(b,rr*Math.sin(th));
    M.setPt(p,i,P,colfn(t)); } M.flush(p); return p; }
function mulberry(a){ return function(){ a|=0; a=a+0x6D2B79F5|0; let t=Math.imul(a^a>>>15,1|a); t=t+Math.imul(t^t>>>7,61|t)^t; return ((t^t>>>14)>>>0)/4294967296; }; }
const fig8=t=>V3((2+Math.cos(2*t))*Math.cos(3*t)/2.2,Math.sin(4*t)/2.2,(2+Math.cos(2*t))*Math.sin(3*t)/2.2);
const trefoil=t=>V3((Math.sin(t)+2*Math.sin(2*t))/2.4,-Math.sin(3*t)/2.4,(Math.cos(t)-2*Math.cos(2*t))/2.4);
function segs(pairs,color,op){ const g=new T.BufferGeometry().setFromPoints(pairs.flat()); return new T.LineSegments(g,new T.LineBasicMaterial({color,transparent:true,opacity:op==null?0.9:op})); }
function circle(r,y,color,op,cx=0,cz=0){ const pts=[]; for(let i=0;i<=200;i++){ const a=i/200*Math.PI*2; pts.push(V3(cx+r*Math.cos(a),y,cz+r*Math.sin(a))); } return M.line(pts,color,op); }
function bead(color,r){ return M.orb(r||0.07,new T.Color(color[0],color[1],color[2])); }
function lbl(g,txt,col,x,y,z,sc){ const s=M.label(txt,col,sc||0.26); s.position.set(x,y,z); g.add(s); return s; }

/* ---------------- feed operator ---------------- */
const feed={ params:[
  {id:'theta',label:'Shape angle θ (degrees), z = w = e^(iθ)',min:1,max:179,step:1,value:40},
  {id:'s',label:'Squaring path s (shape z → z^(1+s))',min:0,max:1,step:0.01,value:0},
  {id:'cre',label:'Riley parameter c, real part',min:-1,max:2,step:0.005,value:0.2},
  {id:'cim',label:'Riley parameter c, imaginary part',min:-1.5,max:1.5,step:0.005,value:0.5},
  {id:'n',label:'Figure-eight monodromy power s in h^s',min:0,max:3,step:0.01,value:0},
  {id:'T',label:'Trace T of the ladder',min:0,max:6.5,step:0.01,value:1},
  {id:'x',label:'x = M² on the real axis',min:0.05,max:4.1,step:0.005,value:0.6},
  {id:'alpha',label:'Twist α on the unit circle, z = e^(2πiα)',min:0,max:1,step:0.0005,value:0.12},
  {id:'beta',label:'Second twist β (flat torus)',min:0,max:1,step:0.005,value:0.3},
  {id:'a0',label:'Odometer start a₀',min:0.05,max:3,step:0.01,value:0.25},
  {id:'a1',label:'Odometer end a₁',min:0.05,max:3,step:0.01,value:1.25},
  {id:'K',label:'Power k of q',min:1,max:128,step:1,value:17},
  {id:'knot',label:'Knot: 0 unknot · 1 figure-eight · 2 trefoil',min:0,max:2,step:1,value:2},
  {id:'slope',label:'Surgery slope: −2 or +2',min:-2,max:2,step:4,value:2},
  {id:'hand',label:'Trefoil hand: 0 right · 1 left',min:0,max:1,step:1,value:1},
  {id:'B',label:'Repair row B1–B12',min:1,max:12,step:1,value:7}],
  build(P){
    const th=P.theta*Math.PI/180, z=cexp(th), zz1=cmul(z,csub(z,C(1,0))), prod=cmul(zz1,zz1);
    const c=C(P.cre,P.cim), p=cadd(csub(cmul(c,c),c),C(1,0));
    const Tv=P.T, disc=Tv*Tv-4;
    const a=P.x*P.x, b=-1+P.x+2*P.x*P.x+P.x**3-P.x**4;
    return {th,z,zz1,prod,gap:cabs(csub(prod,C(1,0))),c,p,s:P.s,n:P.n,T:Tv,disc,x:P.x,a,b,alpha:P.alpha,beta:P.beta,a0:P.a0,a1:P.a1,K:P.K,knot:P.knot,slope:P.slope,hand:P.hand,B:P.B};
  }};

/* ---------------- eyes ---------------- */
const eyes=[];
/* 1. gluing */
eyes.push({id:'gluing',section:'§2 Thurston\'s gluing equation',grade:'[T] Gluing.regular_half, eis_edge',title:'Two stones, one space',
  eq:'z(z−1)·w(w−1) = 1\nz = w = e^(iπ/3): each factor z(z−1) = −1',
  text:'The figure-eight complement is glued from two ideal tetrahedra. On the slice z = w = e^(iθ) the gap between the two tetrahedra is drawn as |z(z−1)w(w−1) − 1|; it closes exactly at θ = 60°, the regular tetrahedron.',
  uses:['theta'],view:[0.7,0.35,7.0,0.2],
  make(g){ this.knot=knotPoints(fig8,7000,0.06,t=>Math.sin(3*t)>0?GOLD.map(v=>v*0.55):BLUE.map(v=>v*0.55)); g.add(this.knot);
    const Vt=[[1,1,1],[1,-1,-1],[-1,1,-1],[-1,-1,1]].map(v=>V3(v[0],v[1],v[2]).multiplyScalar(0.55));
    this.tets=[]; for(const [col,sg] of [[0xf2a12e,-1],[0x2f8dff,1]]){ const pairs=[]; for(let i=0;i<4;i++) for(let j=i+1;j<4;j++) pairs.push([Vt[i],Vt[j]]);
      const L=segs(pairs,col,0.95); L.userData.sg=sg; g.add(L); this.tets.push(L); } },
  enter(S){ this.change(S); }, change(S){ this.S=S; },
  step(dt,S,t){ const gap=Math.min(1.6,S.gap); this.tets.forEach((L,i)=>{ L.position.set(L.userData.sg*(0.62+gap*0.8),0,0); L.rotation.set(0.4*t*L.userData.sg,0.3*t,0); });
    this.knot.rotation.y=0.15*t;
    return [['z = e^(iθ)',fmtc(S.z)],['z(z−1)',fmtc(S.zz1)],['z(z−1)·w(w−1)',fmtc(S.prod)],['gap |product − 1|',S.gap.toFixed(6)],['regular (θ = 60°)?',S.gap<1e-9?'yes, the edge closes':'no']]; }});
/* 2. branches */
eyes.push({id:'branches',section:'§2 The symmetric slice',grade:'[T] Gluing.edge_symmetric_factor, golden_cycle',title:'Two branches, one square',
  eq:'z²(z−1)² − 1 = (z² − z + 1)(z² − z − 1)\nz(1−z) = 1 ⇔ z² − z + 1 = 0; golden: z(1−z) = −1',
  text:'The complex z-plane lies flat. Gold: the regular roots e^(±iπ/3) on the unit circle. Blue: φ and −1/φ on the real line. Move s to carry each root along z^(1+s) to its square: gold to the cube roots e^(±2iπ/3), blue to φ² and φ⁻².',
  uses:['s'],view:[0.0,1.05,6.4,0.0],
  make(g){ g.add(M.grid(6,24,0x1f2a38,0.55)); g.add(circle(1,0.001,0xf2c14e,0.45)); g.add(M.line([V3(-2.4,0.001,0),V3(3.2,0.001,0)],0x2f8dff,0.45));
    this.fixed=[]; this.mov=[]; this.tr=[];
    const roots=[[cexp(Math.PI/3),GOLD,'g'],[cexp(-Math.PI/3),GOLD,'g'],[C(PHI,0),BLUE,'b'],[C(-1/PHI,0),BLUE,'b']];
    roots.forEach(([r,col,k])=>{ const o=bead(col,0.08); o.position.set(r.re,0.02,-r.im); g.add(o); const m=bead(col.map(v=>v*0.8),0.055); g.add(m); const tr=M.trail(160,0.07); g.add(tr); this.mov.push({r,col,k,m,tr}); });
    lbl(g,'z² − z + 1','#f6c56a',0.2,0.25,-1.2); lbl(g,'z² − z − 1','#7fbaff',2.2,0.25,0.35); },
  enter(S){ this.mov.forEach(o=>M.clearTrail(o.tr)); this.change(S); }, change(S){ this.S=S; },
  step(dt,S,t){ const s=S.s; const rows=[];
    this.mov.forEach(o=>{ let w; if(o.k==='g'){ const a=Math.atan2(o.r.im,o.r.re)*(1+s); w=cexp(a); } else { const m=Math.pow(Math.abs(o.r.re),1+s); w=o.r.re>0?C(m,0):C(-m*Math.cos(Math.PI*s),-m*Math.sin(Math.PI*s)); }
      o.m.position.set(w.re,0.03,-w.im); M.pushTrail(o.tr,o.m.position,o.col); });
    const g=cexp(Math.PI/3*(1+s)), b=Math.pow(PHI,1+s);
    return [['s',s.toFixed(2)],['gold root moved',fmtc(g,4)],['blue root moved',b.toFixed(5)],['at s = 1, gold','e^(2iπ/3): x² + x + 1 = 0'],['at s = 1, blue','φ² = '+(PHI*PHI).toFixed(5)+': x² − 3x + 1 = 0']]; }});
/* 3. Riley */
eyes.push({id:'riley',section:'§3.1 Riley\'s representation',grade:'[T] Riley.relation_defect, riley_iff_shape',title:'The relation defect',
  eq:'WA − BW = [[0, p], [−c·p, 0]],  p = c² − c + 1\nrelation holds ⇔ c² − c + 1 = 0',
  text:'Height is log(1 + |p|) over the complex c-plane, p = c² − c + 1, the single entry that measures how far the knot-group relation fails. Its two zeros are e^(±iπ/3), the regular-tetrahedron shape. Move c to read the defect matrix.',
  uses:['cre','cim'],view:[0.3,1.05,7.4,0.0],
  make(g){ const N=70,Mm=70,sx=1.6,sz=1.6; this.surf=M.surface(N,Mm,sx,sz); this.surf.position.set(0.5,0,0); g.add(this.surf);
    const H=[],Cc=[]; for(let a=0;a<N;a++){ H.push([]);Cc.push([]); for(let b=0;b<Mm;b++){ const cr=0.5-sx+2*sx*a/(N-1), ci=sz-2*sz*b/(Mm-1); const q=cabs(cadd(csub(cmul(C(cr,ci),C(cr,ci)),C(cr,ci)),C(1,0)));
      const h=Math.log(1+q)*0.9; H[a].push(h); const k=Math.min(1,h/2.2); Cc[a].push([GOLD[0]*(1-k)+BLUE[0]*k,GOLD[1]*(1-k)+BLUE[1]*k,GOLD[2]*(1-k)+BLUE[2]*k].map(v=>v*0.75)); } }
    M.setSurface(this.surf,H,Cc); this.b=bead(WHITE,0.07); g.add(this.b);
    [Math.PI/3,-Math.PI/3].forEach(a=>{ const o=bead(GOLD,0.06); o.position.set(Math.cos(a),0.05,-Math.sin(a)); g.add(o); }); },
  enter(S){ this.change(S); }, change(S){ this.S=S; },
  step(dt,S){ const h=Math.log(1+cabs(S.p))*0.9; this.b.position.set(S.c.re,h+0.06,-S.c.im); const cp=cmul(S.c,S.p);
    return [['c',fmtc(S.c,3)],['p = c² − c + 1',fmtc(S.p)],['defect (1,2) entry',fmtc(S.p,3)],['defect (2,1) entry',fmtc(C(-cp.re,-cp.im),3)],['relation holds?',cabs(S.p)<2e-3?'yes, at the regular shape':'no']]; }});
/* 4. trefoil */
eyes.push({id:'trefoil',section:'§3.2 The trefoil\'s monodromy',grade:'[T] Monodromy.h31_charpoly, h31_order6  ·  [R] Corollary 7',title:'Six turns and home',
  eq:'h = V⁻¹Vᵀ = [[0,1],[−1,1]]\nh² = h − I,  h³ = −I,  h⁶ = I',
  text:'The trefoil (rose) and, beneath it, the orbit of a point under its monodromy on the invariant ellipse. Its characteristic polynomial is z² − z + 1, the regular-tetrahedron and Riley polynomial. Ladder rungs tr hᵏ run 2, 1, −1, −2, −1, 1, 2.',
  uses:[],view:[0.6,0.5,7.6,-0.3],
  make(g){ this.k=knotPoints(trefoil,7000,0.06,()=>ROSE.map(v=>v*0.6)); this.k.position.y=0.55; g.add(this.k);
    const Q=[[2,-1],[-1,2]], x0=[0.85,0]; const qv=2*x0[0]*x0[0]; const pts=[]; for(let i=0;i<=200;i++){ const a=i/200*2*Math.PI, d=[Math.cos(a),Math.sin(a)]; const r=Math.sqrt(qv/(Q[0][0]*d[0]*d[0]+2*Q[0][1]*d[0]*d[1]+Q[1][1]*d[1]*d[1])); pts.push(V3(r*d[0],-1.25,-r*d[1])); }
    g.add(M.line(pts,0xf2c14e,0.5)); this.orbit=[x0]; for(let i=0;i<6;i++){ const q=this.orbit[i]; this.orbit.push([H31[0][0]*q[0]+H31[0][1]*q[1],H31[1][0]*q[0]+H31[1][1]*q[1]]); }
    this.beads=this.orbit.slice(0,6).map(q=>{ const o=bead(GOLD,0.055); o.position.set(q[0],-1.25,-q[1]); g.add(o); return o; }); this.cur=bead(WHITE,0.08); g.add(this.cur); },
  enter(){}, change(){},
  step(dt,S,t){ this.k.rotation.y=0.25*t; const k=Math.floor(t/1.1)%7, q=this.orbit[k%6]; this.cur.position.set(q[0],-1.25,-q[1]); const Hk=mpow(H31,k);
    return [['turn k',String(k)],['hᵏ',`[[${Hk[0][0]},${Hk[0][1]}],[${Hk[1][0]},${Hk[1][1]}]]`],['rung tr hᵏ',String(lad(1,k))],['h³',(()=>{const A=mpow(H31,3);return `[[${A[0][0]},${A[0][1]}],[${A[1][0]},${A[1][1]}]] = −I`;})()],['order','6']]; }});
/* 5. cat map */
eyes.push({id:'catmap',section:'§4 The golden branch squared',grade:'[T] Monodromy.h41_cat, Ladder.golden_squared, h41_trace5',title:'The thrown branch stretches',
  eq:'z² − z − 1 = 0 ⇒ (z²)² − 3z² + 1 = 0\nh = [[2,1],[1,1]],  tr h⁵ = 123 = φ¹⁰ + φ⁻¹⁰',
  text:'Points on the torus are moved by the exact real power hˢ of the figure-eight monodromy (h is symmetric with eigenvalues φ² and φ⁻²). Area is kept (det = 1) while one direction stretches by φ²ˢ and the other shrinks: it never comes home.',
  uses:['n'],view:[0.5,0.75,7.2,0.0],
  make(g){ const N=9000; this.N=N; this.p=M.points(N,0.05); g.add(this.p); const r=mulberry(11); this.uv=[]; for(let i=0;i<N;i++) this.uv.push([r(),r()]); },
  enter(S){ this.change(S); }, change(S){ this.S=S; this.draw(S.n); },
  draw(s){ const A=h41pow(s), R=1.35, r=0.55; for(let i=0;i<this.N;i++){ const [u,v]=this.uv[i]; let U=(A[0][0]*u+A[0][1]*v)%1, W=(A[1][0]*u+A[1][1]*v)%1; if(U<0)U+=1; if(W<0)W+=1;
      const th=2*Math.PI*U, ph=2*Math.PI*W; const P=V3((R+r*Math.cos(ph))*Math.cos(th),r*Math.sin(ph),(R+r*Math.cos(ph))*Math.sin(th));
      const k=u; M.setPt(this.p,i,P,[GOLD[0]*(1-k)+BLUE[0]*k,GOLD[1]*(1-k)+BLUE[1]*k,GOLD[2]*(1-k)+BLUE[2]*k].map(x=>x*0.7)); } M.flush(this.p); },
  step(dt,S){ const n=Math.floor(S.n+1e-9); const A=h41pow(S.n); const det=A[0][0]*A[1][1]-A[0][1]*A[1][0];
    return [['power s',S.n.toFixed(2)],['stretch φ^(2s)',Math.pow(PHI,2*S.n).toFixed(5)],['det hˢ (area)',det.toFixed(10)],['traces tr hᵏ, k ≤ ⌊s⌋',Array.from({length:n+1},(_,k)=>lad(3,k)).join(', ')],['tr h⁵','123']]; }});
/* 6. ladder */
eyes.push({id:'ladder',section:'§5 One trace ladder',grade:'[T] Ladder.ladder_law, band_edge_merge, trefoil_ladder, fig8_ladder, sqrt2_ladder',title:'One ladder, one edge',
  eq:'x + y = T, xy = 1 ⇒ xᵏ + yᵏ = t_k,  t_{k+1} = T t_k − t_{k−1}\nT = 2 sec ψ,  log λ₊ = gd⁻¹(ψ)',
  text:'Height is the trace T. Below T = 2 the two rails λ± lie on the unit circle (gold) and the ladder rotates; at T = 2 they merge (the white ring); above it they lie on the real line (blue, logarithmic scale) and the ladder stretches. Trefoil T = 1, figure-eight T = 3, Apéry and Catalan reach 34 from T = 6.',
  uses:['T'],view:[0.8,0.25,8.0,0.2],
  make(g){ const n=900; this.rail=M.points(n*2,0.05); g.add(this.rail); let i=0;
    for(let j=0;j<n;j++){ const Tv=6.5*j/(n-1); for(const sg of [1,-1]){ let X,Z; if(Tv<2){ X=Tv/2; Z=sg*Math.sqrt(1-Tv*Tv/4); } else { const l=(Tv+sg*Math.sqrt(Tv*Tv-4))/2; X=1+0.9*Math.log(l); Z=0; }
      M.setPt(this.rail,i++,V3(X,this.y(Tv),-Z),(Tv<2?GOLD:BLUE).map(v=>v*0.55)); } } M.flush(this.rail);
    g.add(circle(0.45,this.y(2),0xffffff,0.6,1,0)); this.b1=bead(GOLD,0.08); this.b2=bead(GOLD,0.08); g.add(this.b1); g.add(this.b2);
    [[1,'trefoil T = 1','#f6c56a'],[3,'figure-eight T = 3','#7fbaff'],[6,'T = 6 → 34','#7fbaff']].forEach(([Tv,s,c])=>lbl(g,s,c,-1.9,this.y(Tv),0)); },
  y(Tv){ return (Tv-3)*0.55; },
  enter(S){ this.change(S); }, change(S){ this.S=S; },
  step(dt,S){ const Tv=S.T; const pos=sg=>{ if(Tv<2) return V3(Tv/2,this.y(Tv),-sg*Math.sqrt(1-Tv*Tv/4)); const l=(Tv+sg*Math.sqrt(Tv*Tv-4))/2; return V3(1+0.9*Math.log(l),this.y(Tv),0); };
    this.b1.position.copy(pos(1)); this.b2.position.copy(pos(-1)); const col=Tv<2?GOLD:BLUE; M.paintOrb(this.b1,col,0.8); M.paintOrb(this.b2,col,0.8);
    let reg, ang, lam; if(Tv<2-1e-9){ reg='band (rotates)'; ang=Math.acos(Tv/2)*180/Math.PI; lam=`e^{±i·${ang.toFixed(2)}°}`; } else if(Tv<=2+1e-9){ reg='edge (rails merged)'; lam='1, 1'; } else { reg='gap (stretches)'; const l=(Tv+Math.sqrt(Tv*Tv-4))/2; lam=`${l.toFixed(5)}, ${(1/l).toFixed(5)}`; }
    const rows=[['T',Tv.toFixed(2)],['regime',reg],['rails λ±',lam],['rungs t₀ … t₆',Array.from({length:7},(_,k)=>{const v=lad(Tv,k); return Math.abs(v-Math.round(v))<1e-9?String(Math.round(v)):v.toFixed(2);}).join(', ')]];
    if(Tv>2){ const psi=Math.acos(2/Tv); rows.push(['ψ (sec ψ = T/2)',(psi*180/Math.PI).toFixed(3)+'°']); rows.push(['gd⁻¹(ψ) = log λ₊',Math.log(1/Math.cos(psi)+Math.tan(psi)).toFixed(6)]); }
    else if(Tv<2) rows.push(['rotation per step',Math.acos(Tv/2)*180/Math.PI>0?(Math.acos(Tv/2)*180/Math.PI).toFixed(3)+'°':'0°']);
    return rows; }});
/* 7. A-polynomial */
eyes.push({id:'apoly',section:'§6 The A-polynomial of 4₁',grade:'[T] APoly.disc_split, golden_ramifies, regular_ramifies',title:'The branches are branch points',
  eq:'A = M⁴L² + b(M) L + M⁴,  x = M²\nb + 2a = −(x+1)²(x² − 3x + 1),  b − 2a = −(x−1)²(x² + x + 1)',
  text:'White: real points of A(L, M) = 0 over the real axis x = M² (horizontal) with L vertical. The two slices L = +1 (blue) and L = −1 (gold) are fixed by the amphichiral involution L ↦ 1/L. The golden shape squared, x = φ±², ramifies the curve on L = +1; the node x = 1 sits on L = −1. The gold ring holds the complex ramification points x² + x + 1 = 0.',
  uses:['x'],view:[0.0,0.12,8.4,0.3],
  make(g){ const n=2600; this.cur=M.points(n*2,0.045); g.add(this.cur); let i=0; this.sc=0.32;
    for(let j=0;j<n;j++){ const x=0.02+4.15*j/(n-1), a=x*x, b=-1+x+2*x*x+x**3-x**4, D=b*b-4*a*a; for(const sg of [1,-1]){ let P=V3(0,-50,0); if(D>=0){ const L=(-b+sg*Math.sqrt(D))/(2*a); if(Math.abs(L)<9) P=V3(x-1.8,L*this.sc,0); } M.setPt(this.cur,i++,P,WHITE.map(v=>v*0.6)); } } M.flush(this.cur);
    g.add(M.line([V3(-1.8,this.sc,0),V3(2.4,this.sc,0)],0x2f8dff,0.6)); g.add(M.line([V3(-1.8,-this.sc,0),V3(2.4,-this.sc,0)],0xf2c14e,0.6));
    [(3-Math.sqrt(5))/2,(3+Math.sqrt(5))/2].forEach(x=>{ const o=bead(BLUE,0.07); o.position.set(x-1.8,this.sc,0); g.add(o); });
    const nd=bead(WHITE,0.06); nd.position.set(-0.8,-this.sc,0); g.add(nd);
    const ring=circle(0.5,0,0xf2c14e,0.4); ring.rotation.x=Math.PI/2; ring.position.set(1.4,1.9,0); g.add(ring);
    [2*Math.PI/3,-2*Math.PI/3].forEach(a=>{ const o=bead(GOLD,0.055); o.position.set(1.4+0.5*Math.cos(a),1.9+0.5*Math.sin(a),0); g.add(o); });
    lbl(g,'L = +1','#7fbaff',2.75,this.sc,0); lbl(g,'L = −1','#f6c56a',2.75,-this.sc,0); lbl(g,'complex x','#f6c56a',1.4,2.55,0);
    this.m1=bead([1,1,1],0.06); this.m2=bead([1,1,1],0.06); g.add(this.m1); g.add(this.m2); },
  enter(S){ this.change(S); }, change(S){ this.S=S; },
  step(dt,S){ const {x,a,b}=S, D=b*b-4*a*a; const rows=[['x = M²',x.toFixed(3)],['b + 2a  (= A and ∂A/∂L at L = +1)',f(b+2*a)],['−(b − 2a)  (= A at L = −1)',f(-(b-2*a))],['discriminant b² − 4a²',f(D)]];
    if(D>=0){ const L1=(-b+Math.sqrt(D))/(2*a), L2=(-b-Math.sqrt(D))/(2*a); this.m1.position.set(x-1.8,Math.max(-8,Math.min(8,L1))*this.sc,0); this.m2.position.set(x-1.8,Math.max(-8,Math.min(8,L2))*this.sc,0); this.m1.visible=this.m2.visible=true; rows.push(['real L roots',`${L1.toFixed(4)}, ${L2.toFixed(4)}`]); rows.push(['product of roots','1 (palindromic)']); }
    else { this.m1.visible=this.m2.visible=false; rows.push(['real L roots','none (complex pair, |L| = 1)']); }
    const g1=(3-Math.sqrt(5))/2, g2=(3+Math.sqrt(5))/2; const near=Math.min(Math.abs(x-g1),Math.abs(x-g2));
    rows.push(['nearest golden ramification',`x = ${(Math.abs(x-g1)<Math.abs(x-g2)?g1:g2).toFixed(5)}  (distance ${near.toFixed(3)})`]); return rows; }});
/* 8. chirality */
eyes.push({id:'chirality',section:'§7 Chirality on the Seifert form',grade:'[T] Chirality.amphichiral_41, chiral_31',title:'One hand, and its mirror',
  eq:'Pᵀ V₄₁ P = −V₄₁ᵀ,  P = [[−1,−1],[2,1]]\nxᵀ(V₃₁ + V₃₁ᵀ)x = −2(x² − xy + y²) < 0',
  text:'Heights are xᵀ(V + Vᵀ)x over the plane. Left: the figure-eight saddle (signature 0, both signs, gold and blue), which a change of basis can turn into its mirror. Right: the trefoil cap (signature −2, negative at every lattice point but the origin), which no change of basis can. White beads: lattice points moved by the certificate P.',
  uses:[],view:[0.0,0.65,8.6,0.0],
  make(g){ const N=40; this.s1=M.surface(N,N,1.1,1.1); this.s2=M.surface(N,N,1.1,1.1); this.s1.position.x=-1.5; this.s2.position.x=1.5; g.add(this.s1); g.add(this.s2);
    const mk=(S,signed)=>{ const H=[],Cc=[]; for(let a=0;a<N;a++){ H.push([]);Cc.push([]); for(let b=0;b<N;b++){ const x=-1+2*a/(N-1), y=-1+2*b/(N-1); const q=S[0][0]*x*x+2*S[0][1]*x*y+S[1][1]*y*y; H[a].push(q*0.32); Cc[a].push(signed?(q>0?GOLD:BLUE).map(v=>v*0.8):ROSE.map(v=>v*0.75)); } } return [H,Cc]; };
    const [H1,C1]=mk([[2,-1],[-1,-2]],true), [H2,C2]=mk([[-2,1],[1,-2]],false); M.setSurface(this.s1,H1,C1); M.setSurface(this.s2,H2,C2);
    lbl(g,'figure-eight · signature 0','#f6c56a',-1.5,1.35,0); lbl(g,'trefoil · signature −2','#ff8fa0',1.5,1.35,0);
    this.ring=[[1,0],[0,1],[-1,0],[0,-1],[1,1],[-1,-1]]; this.rb=this.ring.map(()=>{ const o=bead(WHITE,0.04); g.add(o); return o; }); },
  enter(){}, change(){},
  step(dt,S,t){ const s=0.5-0.5*Math.cos(t*0.7), P=[[-1,-1],[2,1]];
    this.ring.forEach((p,i)=>{ const q=[P[0][0]*p[0]+P[0][1]*p[1],P[1][0]*p[0]+P[1][1]*p[1]]; let x=(1-s)*p[0]+s*q[0], y=(1-s)*p[1]+s*q[1]; const m=Math.max(1,Math.abs(x),Math.abs(y)); x/=m; y/=m; this.rb[i].position.set(-1.5+x*1.1,1.0,-y*1.1); });
    const V=[[1,-1],[0,-1]], PT=[[P[0][0],P[1][0]],[P[0][1],P[1][1]]], L=mm(mm(PT,V),P);
    return [['det P',String(P[0][0]*P[1][1]-P[0][1]*P[1][0])],['Pᵀ V₄₁ P',`[[${L[0][0]},${L[0][1]}],[${L[1][0]},${L[1][1]}]]`],['−V₄₁ᵀ','[[-1,0],[1,1]]'],['figure-eight: det(V+Vᵀ)','−5 (indefinite)'],['trefoil: det(V+Vᵀ)','3, top-left −2 (negative definite)']]; }});
/* ---------------- Part II: the Dirac anchor recovered ---------------- */
const TAU=Math.PI*2;
const frac=x=>x-Math.floor(x);
const etaC=a=>Number.isInteger(a)?0:1-2*frac(a);
function litherland(p,q,a){ let s=0; for(let i=1;i<p;i++) for(let j=1;j<q;j++){ const x=i/p+j/q; s+=(a<x&&x<a+1)?-1:1; } return s; }
function wallAt(a,walls,eps){ return walls.some(w=>Math.abs(frac(a)-w)<eps); }
/* exact integer q-series with BigInt, to degree N */
function qseries(N){
  const Z=()=>Array(N+1).fill(0n);
  const mul=(a,b)=>{ const c=Z(); for(let i=0;i<=N;i++){ if(a[i]===0n) continue; for(let j=0;i+j<=N;j++) if(b[j]!==0n) c[i+j]+=a[i]*b[j]; } return c; };
  const onep=(k,s)=>{ const p=Z(); p[0]=1n; if(k<=N) p[k]+=s; return p; };
  const shift=(p,k)=>{ const o=Z(); for(let i=0;i+k<=N;i++) o[i+k]=p[i]; return o; };
  const add=(a,b)=>a.map((x,i)=>x+b[i]);
  const negp=[]; { let p=Z(); p[0]=1n; negp.push(p); for(let j=1;j<=N+1;j++){ p=mul(p,onep(j,1n)); negp.push(p); } }
  let phi0=Z(), M=Z();
  for(let n=0;n<=N;n++){ phi0=add(phi0,shift(negp[Math.min(2*n+1,N+1)],n)); if(2*n<=N) M=add(M,shift(negp[Math.min(2*n+1,N+1)],2*n)); }
  const inv=p=>{ const q=Z(); q[0]=1n; for(let k=1;k<=N;k++){ let s=0n; for(let i=1;i<=k;i++) s+=p[i]*q[k-i]; q[k]=-s; } return q; };
  let psi=Z(); for(let m=1;m*m<=N;m++){ let den=Z(); den[0]=1n; for(let j=1;j<=m;j++) den=mul(den,onep(2*j-1,-1n)); psi=add(psi,shift(inv(den),m*m)); }
  const negInf=negp[N+1]; const ft=Z(); for(let n=0;n*(3*n+1)/2<=N;n++){ const e=n*(3*n+1)/2; ft[e]+=1n; if(e+2*n+1<=N) ft[e+2*n+1]-=1n; }
  return {phi0,M,psi,negInf,ft};
}
function tetraWire(color,size){ const Vt=[[1,1,1],[1,-1,-1],[-1,1,-1],[-1,-1,1]].map(v=>V3(v[0],v[1],v[2]).multiplyScalar(size)); const pairs=[]; for(let i=0;i<4;i++) for(let j=i+1;j<4;j++) pairs.push([Vt[i],Vt[j]]); return segs(pairs,color,0.95); }

/* 10. the trefoil's wall is the regular shape */
eyes.push({id:'wall',section:'II · Rule 1: one polynomial, now also the trefoil\'s wall',grade:'[T] D25 alex31_circle, alex31_circle_eq_zero_iff, alex41_circle_ne_zero · Bridge wall_regular_poly, wall_solves_edge, wall_half, wall_cubed',title:'The wall is the regular shape',
  eq:'Δ₃₁(e^(2πiα)) = 2cos2πα − 1 = 0  ⇔  α ≡ ±1/6\n|z| = 1, Δ₃₁(z) = 0  ⇒  z² − z + 1 = 0,  z(z − 1) = −1,  z³ = −1\nΔ₄₁(e^(2πiα)) = 3 − 2cos2πα ≥ 1',
  text:'White: the unit circle. Over each point e^(2πiα) the rose curve stands at the trefoil\'s Alexander value 2cos2πα − 1 and the blue curve at the figure-eight\'s 3 − 2cos2πα. The rose curve meets the circle only at the two gold beads e^(±iπ/3), where a regular ideal tetrahedron (gold wire) sits: the chiral knot\'s spectral wall is the amphichiral knot\'s geometry. The blue curve never comes down to the circle: the figure-eight has no wall, because its Alexander roots are the golden branch squared, which are real.',
  uses:['alpha'],view:[0.75,0.55,7.4,0.35],
  make(g){ const R=1.6,s=0.42,N=4000; g.add(circle(R,0,0xdfe9f2,0.55));
    const p1=M.points(N,0.05), p2=M.points(N,0.05); const rnd=mulberry(11);
    for(let i=0;i<N;i++){ const a=i/N, c=Math.cos(TAU*a), sn=Math.sin(TAU*a), j=()=>(rnd()-0.5)*0.03;
      M.setPt(p1,i,V3(R*c+j(),s*(2*c-1)+j(),R*sn+j()),ROSE); M.setPt(p2,i,V3(R*c+j(),s*(3-2*c)+j(),R*sn+j()),BLUE); }
    M.flush(p1); M.flush(p2); g.add(p1); g.add(p2);
    for(const sg of [1,-1]){ const x=R*0.5, z=sg*R*Math.sqrt(3)/2; const b=bead(GOLD,0.08); b.position.set(x,0,z); g.add(b);
      const t=tetraWire(0xf2a12e,0.2); t.position.set(x,0.42,z); g.add(t); this['tet'+sg]=t; lbl(g,sg>0?'e^(iπ/3)':'e^(−iπ/3)','#f6c56a',x+0.55,0.15,z); }
    lbl(g,'Δ₃₁ = 2cos2πα − 1','#ff9fb0',-R-0.2,-1.45,0); lbl(g,'Δ₄₁ = 3 − 2cos2πα ≥ 1','#7fbaff',-R-0.2,2.35,0);
    this.b0=bead(WHITE,0.06); this.b1=bead(ROSE,0.07); this.b2=bead(BLUE,0.07); g.add(this.b0); g.add(this.b1); g.add(this.b2);
    this.stem=M.line([V3(),V3()],0xffffff,0.5); g.add(this.stem); this.R=R; this.s=s; },
  enter(S){ this.change(S); }, change(S){ this.S=S; },
  step(dt,S,t){ const a=S.alpha, c=Math.cos(TAU*a), sn=Math.sin(TAU*a), R=this.R, s=this.s;
    this.b0.position.set(R*c,0,R*sn); this.b1.position.set(R*c,s*(2*c-1),R*sn); this.b2.position.set(R*c,s*(3-2*c),R*sn);
    M.setLine?M.setLine(this.stem,[V3(R*c,s*(2*c-1),R*sn),V3(R*c,s*(3-2*c),R*sn)]):null;
    this.tet1.rotation.y=0.6*t; this['tet-1'].rotation.y=-0.6*t;
    const z=C(c,sn), q=cadd(csub(cmul(z,z),z),C(1,0)), zz=cmul(z,csub(z,C(1,0))), z3=cmul(cmul(z,z),z);
    const d=Math.min(Math.abs(frac(a)-1/6),Math.abs(frac(a)-5/6));
    return [['α',a.toFixed(4)],['z = e^(2πiα)',fmtc(z)],['Δ₃₁ = 2cos2πα − 1',f(2*c-1,5)],['Δ₄₁ = 3 − 2cos2πα',f(3-2*c,5)],['z² − z + 1',fmtc(q,5)],['z(z − 1)',fmtc(zz)],['z³',fmtc(z3)],['distance to the wall α = ±1/6',d.toFixed(5)+(d<1e-9?'  (on the wall: the regular shape)':'')]]; }});

/* 11. chiral pairing kills eta */
eyes.push({id:'eta',section:'II · Rule 2: chiral pairing kills the flat-torus η',grade:'[T] D25 eta_eq_zero_of_chiral, σ₃_pauliSymbol_σ₃, pauli_eta_eq_zero, eta_neg, eta_one · D28 blockPauli_eta_eq_zero, pauliSymbol_det_eq_zero_iff',title:'Every plus has its minus',
  eq:'σ₃ (aσ₁ + bσ₂) σ₃ = −(aσ₁ + bσ₂),  eigenvalues ±√(a² + b²)\nη(D) = #{λ > 0} − #{λ < 0} = 0 on every block',
  text:'Each point of the lattice is one Fourier block (m + α, n + β) of the flat-torus Dirac operator. Above it the positive eigenvalue √((m+α)² + (n+β)²) (gold), below it the negative one (blue), at equal height. The σ₃ grading swaps the two (the beads trade places), so every block, and the whole truncation, has η = 0. A zero mode needs both twists to be integers: codimension two, never a wall. The raw ruler that survives is a difference of η between operators that are not paired.',
  uses:['alpha','beta'],view:[0.8,0.5,8.2,0.0],
  make(g){ this.K=6; const n=(2*this.K+1)**2; this.up=M.points(n,0.2); this.dn=M.points(n,0.2); g.add(this.up); g.add(this.dn);
    const pairs=[]; for(let m=-this.K;m<=this.K;m++){ pairs.push([V3(m*0.32,0,-this.K*0.32),V3(m*0.32,0,this.K*0.32)]); pairs.push([V3(-this.K*0.32,0,m*0.32),V3(this.K*0.32,0,m*0.32)]); }
    g.add(segs(pairs,0x3a5068,0.5)); },
  enter(S){ this.change(S); }, change(S){ this.S=S; },
  step(dt,S,t){ const K=this.K, sw=0.5-0.5*Math.cos(t*0.9); let i=0, pos=0, neg=0, zero=0, rmin=1e9;
    for(let m=-K;m<=K;m++) for(let n=-K;n<=K;n++){ const a=m+S.alpha, b=n+S.beta, r=Math.hypot(a,b); rmin=Math.min(rmin,r);
      if(r<1e-12) zero+=2; else { pos++; neg++; }
      const h=Math.min(2.2,0.22*r), x=m*0.32, z=n*0.32, y1=h*(1-2*sw), y2=-y1;
      M.setPt(this.up,i,V3(x,y1,z),GOLD.map(v=>v*1.6)); M.setPt(this.dn,i,V3(x,y2,z),BLUE.map(v=>v*1.6)); i++; }
    M.flush(this.up); M.flush(this.dn);
    return [['twists (α, β)',`(${S.alpha.toFixed(3)}, ${S.beta.toFixed(3)})`],['blocks shown',String((2*K+1)**2)],['positive eigenvalues',String(pos)],['negative eigenvalues',String(neg)],['zero modes',String(zero)+(zero?'  (both twists integer)':'')],['η of the truncation',String(pos-neg)],['smallest |λ|',rmin.toFixed(5)],['control: η(1ₙ) = n',`η(1₃₃₈) = ${2*(2*K+1)**2}`]]; }});

/* 12. the circle odometer */
eyes.push({id:'odometer',section:'II · Rule 2: the circle odometer and the missing drift term',grade:'[T] D25 odometer_identity, card_crossings_eq_odometer, etaCircle_add_one · D28 odometer_no_crossing, odometer_one_crossing',title:'The drift the old formula dropped',
  eq:'⌊a₁⌋ − ⌊a₀⌋ = (a₁ − a₀) + ½(η(a₁) − η(a₀)),   η(a) = 1 − 2{a}\nold: Δη = 2·SF   →   kept: Δη = 2(SF − Δa)',
  text:'The spectrum of D_a = −i d/dx + a on the circle is the set of lines λ = n + a (white). As a moves from a₀ to a₁, every line that crosses zero is one unit of spectral flow (gold beads). The rose sawtooth is η(a) = 1 − 2{a}; the blue ramp is the drift a₁ − a₀. The count of crossings is always the drift plus half the change of η, so η can change with no crossing at all, and a full loop has one crossing and no change in η. The drift is the raw difference the old formula threw away.',
  uses:['a0','a1'],view:[0.15,0.25,8.2,0.3],
  make(g){ const sx=1.1, lo=0, hi=3.2; this.sx=sx; this.lo=lo;
    const pairs=[]; for(let n=-4;n<=1;n++){ pairs.push([V3((lo-1.5)*sx,(lo+n)*0.55,0),V3((hi-1.5)*sx,(hi+n)*0.55,0)]); } g.add(segs(pairs,0xb8c8d8,0.35));
    g.add(segs([[V3((lo-1.5)*sx,0,0),V3((hi-1.5)*sx,0,0)]],0xffffff,0.6));
    const N=3000, p=M.points(N,0.045); for(let i=0;i<N;i++){ const a=lo+(hi-lo)*i/N; M.setPt(p,i,V3((a-1.5)*sx,-2.0+0.45*etaC(a),0.4),ROSE); } M.flush(p); g.add(p);
    lbl(g,'λ = n + a','#c9d6e2',(hi-1.5)*sx+0.1,1.5,0); lbl(g,'η(a) = 1 − 2{a}','#ff9fb0',(hi-1.5)*sx+0.2,-2.0,0.4);
    this.cross=[]; for(let k=0;k<4;k++){ const b=bead(GOLD,0.08); b.visible=false; g.add(b); this.cross.push(b); }
    this.m0=bead(WHITE,0.07); this.m1=bead(WHITE,0.07); g.add(this.m0); g.add(this.m1);
    this.drift=M.line([V3(),V3()],0x2f8dff,1); g.add(this.drift); },
  enter(S){ this.change(S); }, change(S){ this.S=S; },
  step(dt,S,t){ const sx=this.sx, a0=Math.min(S.a0,S.a1), a1=Math.max(S.a0,S.a1);
    this.m0.position.set((a0-1.5)*sx,-2.0+0.45*etaC(a0),0.4); this.m1.position.set((a1-1.5)*sx,-2.0+0.45*etaC(a1),0.4);
    let k=0; for(let n=Math.floor(a0)+1;n<a1&&k<4;n++,k++){ this.cross[k].visible=true; this.cross[k].position.set((n-1.5)*sx,0,0); } for(;k<4;k++) this.cross[k].visible=false;
    if(M.setLine) M.setLine(this.drift,[V3((a0-1.5)*sx,-2.9,0.4),V3((a1-1.5)*sx,-2.9+0.3*(a1-a0),0.4)]);
    const sf=Math.floor(a1)-Math.floor(a0), dr=a1-a0, de=etaC(a1)-etaC(a0), onInt=Number.isInteger(a0)||Number.isInteger(a1);
    return [['a₀ → a₁',`${a0.toFixed(3)} → ${a1.toFixed(3)}`],['crossings  ⌊a₁⌋ − ⌊a₀⌋',String(sf)],['drift  a₁ − a₀',f(dr,4)],['η(a₀), η(a₁)',`${f(etaC(a0),4)}, ${f(etaC(a1),4)}`],['½(η(a₁) − η(a₀))',f(de/2,4)],['drift + ½Δη',f(dr+de/2,4)+(onInt?'  (endpoint on an integer: η = 0 there by definition)':(Math.abs(dr+de/2-sf)<1e-9?'  = crossings ✓':''))],['old rule Δη = 2·SF would give',f(2*sf,4)+'  vs  Δη = '+f(de,4)]]; }});

/* 13. Levine–Tristram signatures */
eyes.push({id:'signature',section:'II · Rule 2: the APS ρ invariant and Levine–Tristram signatures',grade:'[T] D28 lt23_values, lt34_values, lt23_window, alexT34_circle_eq_zero_iff_fract · cited Litherland 1979',title:'Signature windows on the circle',
  eq:'σ_T(2,3)(e^(2πiα)) = −2 on (1/6, 5/6), 0 outside\nΔ_T(3,4) = (t² − t + 1)(t⁴ − t² + 1): walls at 1/12, 1/6, 5/12, 7/12, 5/6, 11/12',
  text:'Over the unit circle, the rose steps are the Levine–Tristram signature of the right-handed trefoil T(2,3), the blue steps that of 8₁₉ = T(3,4), both computed live by Litherland\'s count. Each step happens at a wall, a root of the Alexander polynomial on the circle; gold beads mark the walls. T(3,4) shares the trefoil\'s wall at e^(iπ/3). The mirror knot has the opposite sign everywhere. With a U(1) twist this signature fixes the APS ρ invariant of zero surgery, the raw difference of two η invariants: Dirac Time writes ρ = −σ, so its ρ = +2 window is the right-handed trefoil. BHL\'s ±2 surgeries are on the left-handed one, its mirror.',
  uses:['alpha'],view:[0.75,0.6,7.6,0.0],
  make(g){ const R=1.7, s=0.32, N=3600; this.R=R; this.s=s; g.add(circle(R,0,0xdfe9f2,0.5));
    const p1=M.points(N,0.05), p2=M.points(N,0.05); for(let i=0;i<N;i++){ const a=(i+0.5)/N, c=Math.cos(TAU*a), sn=Math.sin(TAU*a);
      M.setPt(p1,i,V3(R*c,s*litherland(2,3,a),R*sn),ROSE); M.setPt(p2,i,V3(1.12*R*c,s*litherland(3,4,a),1.12*R*sn),BLUE); }
    M.flush(p1); M.flush(p2); g.add(p1); g.add(p2);
    for(const w of [1/12,1/6,5/12,7/12,5/6,11/12]){ const b=bead(GOLD,0.06); b.position.set(R*Math.cos(TAU*w),0,R*Math.sin(TAU*w)); g.add(b); }
    lbl(g,'T(2,3): 0, −2','#ff9fb0',-R-0.3,-0.9,0); lbl(g,'T(3,4): 0, −2, −4, −6','#7fbaff',R+0.4,-2.1,0);
    this.b=bead(WHITE,0.07); g.add(this.b); },
  enter(S){ this.change(S); }, change(S){ this.S=S; },
  step(dt,S,t){ const a=S.alpha, R=this.R; this.b.position.set(R*Math.cos(TAU*a),0,R*Math.sin(TAU*a));
    const W23=[1/6,5/6], W34=[1/12,1/6,5/12,7/12,5/6,11/12], on23=wallAt(a,W23,1e-9), on34=wallAt(a,W34,1e-9);
    return [['α',a.toFixed(4)],['σ of T(2,3) (right-handed)',on23?'wall (jump)':String(litherland(2,3,a))],['σ of its mirror (left-handed)',on23?'wall (jump)':String(-litherland(2,3,a))],['σ of T(3,4) = 8₁₉',on34?'wall (jump)':String(litherland(3,4,a))],['walls of T(2,3)','1/6, 5/6  (e^(±iπ/3))'],['walls of T(3,4)','1/12, 1/6, 5/12, 7/12, 5/6, 11/12'],['ρ = −σ (Dirac Time), right-handed',on23?'wall (jump)':String(-litherland(2,3,a))],['figure-eight','σ ≡ 0 (amphichiral)'],['Dirac Time trefoil','right-handed (ρ = +2 on the window)'],['BHL trefoil','left-handed, its mirror']]; }});

/* 14. the boundary ruler phi0 - M */
eyes.push({id:'ruler',section:'II · The signed-boundary test: what is exact',grade:'[T] D25 BHL.phi0_ne_bhlM, rep17_phi0_sub_bhlM, eq15_iff_coeff · D28 phi0_sub_bhlM_pos (k ≤ 128), eq15_mod_q259, eq17_le128, rawDiff_term',title:'The boundary ruler',
  eq:'φ₀(q) = Σ qⁿ(−q)₂ₙ₊₁,   M(q) = Σ q²ⁿ(−q)₂ₙ₊₁\n2q²φ₀(q²) = ψ(q) + ψ(−q)  (1.5),   2 + 2q²M(q) = (−q)_∞ + Σ q^(n(3n+1)/2)(1 − q^(2n+1))  (1.7)',
  text:'Three rows of towers, one per power of q, computed live in exact integers: φ₀ (gold, back), M (blue, middle) and the raw difference φ₀ − M (white, front). Heights are square roots, so all three fit. The difference is positive at every power from q¹ to q¹²⁸ (checked live, and a Lean theorem over that range), although each of its summands qⁿ(1 − qⁿ)(−q)₂ₙ₊₁ has negative coefficients. The slider picks a power k; the readout checks Eq. (1.5) at q^(2k+2) and Eq. (1.7) at q^k.',
  uses:['K'],view:[0.35,0.45,8.6,0.35],
  make(g){ const N=260; this.Q=qseries(N); const Q=this.Q, top=Math.sqrt(Number(Q.phi0[128])); this.top=top;
    const rows=[[Q.phi0,GOLD,-0.7,0.55],[Q.M,BLUE,0,0.55],[Q.phi0.map((x,i)=>x-Q.M[i]),WHITE,0.7,0.9]]; const sx=0.034;
    let cnt=0; rows.forEach(r=>{ for(let k=1;k<=128;k++) cnt+=24; }); const p=M.points(cnt,0.05); let i=0;
    rows.forEach(([ser,col,z,br])=>{ for(let k=1;k<=128;k++){ const h=1.9*Math.sqrt(Number(ser[k]))/top; for(let j=0;j<24;j++){ M.setPt(p,i++,V3((k-64)*sx,h*j/23,z),col.map(v=>v*br)); } } });
    M.flush(p); g.add(p); g.add(segs([[V3(-64*sx,0,0.7),V3(64*sx,0,0.7)]],0xffffff,0.4));
    lbl(g,'φ₀','#f6c56a',-66*sx-0.25,0.2,-0.7); lbl(g,'M','#7fbaff',-66*sx-0.25,0.2,0); lbl(g,'φ₀ − M','#e8f0f6',-66*sx-0.45,0.2,0.7);
    this.mk=bead(ROSE,0.06); g.add(this.mk); this.sx=sx;
    let pos=true; for(let k=1;k<=128;k++) if(Q.phi0[k]-Q.M[k]<=0n) pos=false; this.pos=pos;
    let e15=true; for(let d=0;d<=258;d++){ const l=(d>=2&&(d-2)%2===0)?2n*Q.phi0[(d-2)/2]:0n, r=(d%2===0)?2n*Q.psi[d]:0n; if(l!==r) e15=false; } this.e15=e15;
    let e17=true; for(let d=0;d<=128;d++){ const l=(d===0?2n:0n)+(d>=2?2n*Q.M[d-2]:0n); if(l!==Q.negInf[d]+Q.ft[d]) e17=false; } this.e17=e17; },
  enter(S){ this.change(S); }, change(S){ this.S=S; },
  step(dt,S,t){ const Q=this.Q, k=Math.round(S.K), d=Q.phi0[k]-Q.M[k]; this.mk.position.set((k-64)*this.sx,1.9*Math.sqrt(Number(d))/this.top+0.08,0.7);
    const l15=2n*Q.phi0[k], r15=2n*Q.psi[2*k+2], l17=(k>=2?2n*Q.M[k-2]:0n)+(k===0?2n:0n), r17=Q.negInf[k]+Q.ft[k];
    return [['power k',String(k)],['[qᵏ] φ₀',Q.phi0[k].toString()],['[qᵏ] M',Q.M[k].toString()],['[qᵏ](φ₀ − M)',d.toString()+(d>0n?'  > 0':'')],['φ₀ − M > 0 for every k ≤ 128',this.pos?'yes (live)':'no'],['(1.5) at q^(2k+2): 2[qᵏ]φ₀ vs 2[q^(2k+2)]ψ',`${l15} vs ${r15}`],['(1.5) through q²⁵⁸',this.e15?'holds (live)':'fails'],['(1.7) at qᵏ',`${l17} vs ${r17}`],['(1.7) through q¹²⁸',this.e17?'holds (live)':'fails']]; }});

/* 15. the signed-boundary test */
eyes.push({id:'surgery',section:'II · The signed-boundary test for DT-O5',grade:'[T] D28 moser_fibre_orders, orbifold_euler, lens_L21 · cited Moser 1971, BHL, Hikami–Lovejoy',title:'Same knot, opposite slope',
  eq:'p-surgery on the right-handed trefoil: fibres (2, 3, |6 − p|);  left-handed: (2, 3, |6 + p|)\nχ = 2 − Σ(1 − 1/aᵢ):  (2,3,4) → 1/12 (spherical),  (2,3,8) → −1/24 (SL̃₂)',
  text:'Choose the knot, its hand and the slope ±2. For the trefoil the result is a Seifert manifold whose three exceptional fibres are drawn as torus curves winding 2, 3 and |6 ∓ p| times. Same knot, same crossing number, same H₁ = Z/2; only the sign of the slope differs, and the boundary records φ₀ and M differ already at q¹. The unknot gives L(2,1) = RP³ for both signs, which the gate cannot split; the figure-eight, being its own mirror, gives two results that differ only by orientation.',
  uses:['knot','slope','hand'],view:[0.0,0.55,7.8,0.2],
  make(g){ this.g=g; this.fib=[]; for(let k=0;k<3;k++){ const p=M.points(3000,0.05); g.add(p); this.fib.push(p); }
    this.knotP=knotPoints(fig8,5000,0.05,()=>BLUE.map(v=>v*0.7)); this.knotP.scale.set(0.8,0.8,0.8); g.add(this.knotP);
    this.knotM=knotPoints(fig8,5000,0.05,()=>GOLD.map(v=>v*0.7)); this.knotM.scale.set(-0.8,0.8,0.8); g.add(this.knotM);
    this.hopf=[circle(0.9,0,0xdfe9f2,0.8,-0.45,0),circle(0.9,0,0xf2a12e,0.8,0.45,0)]; this.hopf[1].rotation.x=Math.PI/2; this.hopf.forEach(h=>g.add(h)); this.key=''; },
  enter(S){ this.change(S); },
  change(S){ this.S=S; const kn=Math.round(S.knot), p=S.slope>=0?2:-2, left=Math.round(S.hand)===1;
    const c=Math.abs((left?-6:6)-p), orders=[2,3,c];
    this.fib.forEach((pp,k)=>{ pp.visible=(kn===2); const a=orders[k], cx=[-1.3,0,1.3][k], rnd=mulberry(31+k); const col=[GOLD,BLUE,ROSE][k];
      for(let i=0;i<3000;i++){ const u=TAU*i/3000; const r=0.48+0.16*Math.cos(a*u); M.setPt(pp,i,V3(cx+r*Math.cos(u)+(rnd()-0.5)*0.02,0.16*Math.sin(a*u)+(rnd()-0.5)*0.02,r*Math.sin(u)),col); } M.flush(pp); });
    this.knotP.visible=this.knotM.visible=(kn===1); this.hopf.forEach(h=>h.visible=(kn===0)); this.orders=orders; this.kn=kn; this.p=p; this.left=left; },
  step(dt,S,t){ const kn=this.kn, p=this.p, o=this.orders; this.fib.forEach(pp=>pp.rotation.y=0.25*t); this.knotP.rotation.y=0.2*t; this.knotM.rotation.y=-0.2*t;
    const name=['unknot','figure-eight 4₁','trefoil 3₁'][kn];
    if(kn===0) return [['knot',name],['slope',p>0?'+2':'−2'],['result','L(2,1) = RP³ for both signs'],['H₁','Z/2'],['orientation-reversing self-map','yes (1² ≡ −1 mod 2)'],['gate','cannot split: the unfolded seed']];
    if(kn===1) return [['knot',name],['slope',p>0?'+2':'−2'],['result','hyperbolic filling; S³₊₂(4₁) ≅ −S³₋₂(4₁)'],['H₁','Z/2'],['why','4₁ is its own mirror, and S³_p(K̄) ≅ −S³₋ₚ(K)'],['gate','splits only by orientation']];
    const chi=2-o.reduce((s,a)=>s+(1-1/a),0), rec=o[2]===8?'φ₀  (BHL: M(2,3,8))':'M  (BHL: M(2,3,4))';
    return [['knot',name+(this.left?', left-handed':', right-handed')],['slope',p>0?'+2':'−2'],['exceptional fibres',`(${o.join(', ')})`],['orbifold χ',(chi>0?'+':'')+chi.toFixed(5)+(Math.abs(chi-1/12)<1e-9?' = 1/12':Math.abs(chi+1/24)<1e-9?' = −1/24':'')],['geometry',chi>0?'spherical, finite π₁':'SL̃₂, infinite π₁'],['H₁','Z/2'],['boundary record',rec],['gate','passes at q¹: [q¹]φ₀ = 2 ≠ 1 = [q¹]M']]; }});

/* 16. repairs */
const REPAIRS=[
 ['B1','8₁₉ hyperbolic, volume 6.0259 or 10.149, CS = 1/24','8₁₉ = T(3,4) is a torus knot: Seifert fibred, volume 0','4₁ is the hyperbolic anchor, volume 2.0298832128; 8₁₉ enters through its signature walls'],
 ['B2','3₁ hyperbolic with volume 2.02988; composite volume 8.05576','3₁ is a torus knot; a connected sum is a satellite','2.02988 is the volume of 4₁; 3₁ enters through its chirality and walls'],
 ['B3','η ≈ 0.013 for 8₁₉ (raw CS/π)','no operator, flux or metric fixed','fix an operator family, then measure ρ differences'],
 ['B4','η = CS/π mod Z as a rule','holds only for a specified family, with spectral-flow and kernel terms','the APS variation formula, with its correction terms'],
 ['B5','η ≈ 1057.54, η ≈ 48 ± 2 on the flat torus','the sum dropped the sign','signed sum: η ≡ 0; the growth 0.7678N is the cutoff constant 8 asinh 1 − 2π'],
 ['B6','trefoil η = 0 for all k','with a U(1) twist the right-handed trefoil has σ = −2, so ρ = −σ = +2, on (1/6, 5/6)','the twisted trefoil signature window'],
 ['B7','η jumps by 2·SF','the odometer: η drifts with no crossing; a ↦ a + 1 has SF = 1, Δη = 0','Δη = 2(SF − Δa): the drift term kept'],
 ['B8','flat-torus zero modes on rational walls','aσ₁ + bσ₂ is singular only at a = b = 0','zero modes only at integer (α, β): codimension two'],
 ['B9','Spin^c ↔ H², where the knot flux lives','H²(S³ \\ K) = 0','one Spin^c structure; the flux enters through the U(1) character'],
 ['B10','boundary torus τ = e^(iπ/3)','SnapPy cusp shape 2√3 i','e^(iπ/3) is the tetrahedron shape; the cusp is 2√3 i in Q(√−3)'],
 ['B11','shell capacities 2k² from torus lattice counts','torus counts are (2k+1)² and 4k','2k² is the sphere-shell sum Σ 2(2l+1)'],
 ['B12','even-dimensional APS index on a 3D self-adjoint operator','index 0; the odd-dimensional boundary term is ξ','the odd-dimensional APS formula with ξ']];
eyes.push({id:'repairs',section:'II · Repairs: old readings and what replaces them',grade:'twelve REPAIRED rows (B1–B12) · nothing discarded',title:'Nothing thrown away',
  eq:'old reading  →  the exact test it fails  →  the repaired statement',
  text:'Twelve readings from the old chats, each a rose bead on the inner ring, joined by a strand to the gold bead of its repaired statement on the outer ring. Pick a row with the slider. A reading that fails its test is not deleted: the repair keeps what it was reaching for, on canonical geometry.',
  uses:['B'],view:[0.0,0.95,7.6,0.0],
  make(g){ this.inner=[]; this.outer=[]; const pairs=[]; for(let i=0;i<12;i++){ const a=i/12*TAU; const pi=V3(1.0*Math.cos(a),0,1.0*Math.sin(a)), po=V3(2.0*Math.cos(a),0.5,2.0*Math.sin(a));
      const bi=bead(ROSE,0.07), bo=bead(GOLD,0.08); bi.position.copy(pi); bo.position.copy(po); g.add(bi); g.add(bo); this.inner.push(bi); this.outer.push(bo); pairs.push([pi,po]);
      lbl(g,REPAIRS[i][0],'#c9d6e2',2.35*Math.cos(a),0.6,2.35*Math.sin(a),0.22); }
    g.add(segs(pairs,0x7a8a9b,0.5)); this.g=g; },
  enter(S){ this.change(S); }, change(S){ this.S=S; },
  step(dt,S,t){ const k=Math.round(S.B)-1; this.inner.forEach((b,i)=>b.scale.setScalar(i===k?1.9:1)); this.outer.forEach((b,i)=>b.scale.setScalar(i===k?1.9+0.2*Math.sin(3*t):1)); this.g.rotation.y=0.04*t; const r=REPAIRS[k];
    return [['row',r[0]+' · REPAIRED'],['old reading',r[1]],['test',r[2]],['repaired statement',r[3]]]; }});

/* 17. grades */
eyes.push({id:'grades',section:'II · Claim ledger and grade counts',grade:'110 claims · 46 backed by a named Lean theorem',title:'Every claim graded',
  eq:'EXACT 77 · DERIVED 10 · MODEL 4 · ANALOGY 7 · REPAIRED 12\n[T]: 46 claims, each naming a theorem in count-me-as-one-lean',
  text:'The claim ledger as towers: one bead per claim, grouped by grade. EXACT is a definition, an exact identity or a theorem (proved here or cited exactly); DERIVED follows from cited results by an argument not fully proved here; MODEL is a floating-point or software computation; ANALOGY is a structural reading or a held idea; REPAIRED is an old reading with its test and its repair. The gold ring on the EXACT tower marks the 46 claims tied to a named Lean theorem.',
  uses:[],view:[0.0,0.35,7.8,0.6],
  make(g){ const G=[['EXACT',77,GOLD],['DERIVED',10,BLUE],['MODEL',4,WHITE],['ANALOGY',7,[0.75,0.6,1.0]],['REPAIRED',12,ROSE]]; let tot=0; G.forEach(x=>tot+=x[1]);
    const p=M.points(tot,0.16); let i=0; G.forEach(([nm,n,col],k)=>{ const x=(k-2)*1.15; for(let j=0;j<n;j++){ const lay=Math.floor(j/8), r=j%8, a=r/8*TAU; M.setPt(p,i++,V3(x+0.28*Math.cos(a),0.12*lay-1.1,0.28*Math.sin(a)),(nm==='EXACT'&&j<46)?col:col.map(v=>v*0.55)); }
      lbl(g,nm+' '+n,'#dfe9f2',x,-1.5,0,0.24); }); M.flush(p); g.add(p); this.g=g; },
  enter(){}, change(){}, step(dt,S,t){ this.g.rotation.y=0.12*Math.sin(t*0.3); return [['claims',String(110)],['EXACT',String(77)],['  of which [T]','46'],['DERIVED','10'],['MODEL','4'],['ANALOGY','7'],['REPAIRED','12']]; }});

/* 18. relations */
eyes.push({id:'relations',section:'The relation graph of the whole project',grade:'harness: 280 nodes · 238 edges · every edge witnessed by a theorem · all checks pass on GitHub Actions',title:'Every link checked',
  eq:'node = a Lean theorem, tagged rule 1 / 2 / 3\nedge = a typed relation, named with its witness theorem',
  text:'The relation graph of count-me-as-one-lean in 3D. Each glowing node is a checked theorem, grouped by library on a ring: Part I (gold, blue and rose sectors), the chiral-η, wall and odometer results, the BHL boundary test, the bridge, and the bounded D28 identities. External sources sit on the outer ring. Gold edges share a polynomial, root or value; blue edges keep a difference or square a branch; rose edges carry mirror and contrast; faint edges are proof steps; grey edges point outside. The harness rejects the build if any theorem is unlinked or any edge lacks a proved witness.',
  uses:[],view:[0.4,0.95,10.5,0.0],
  make(g){ const R=window.RELATIONS; const names=Object.keys(R.nodes);
    const grp=nm=>{ const p=nm.split('.'); if(p[0]==='FigureEightAnchors') return p[1]; if(p[0]==='D28') return 'D28'; if(p[1]==='BHL') return 'BHL'; if(p[1]==='Bridge') return 'Bridge';
      const n=p[1]; if(/eta_|pauli|σ₃|charpoly/.test(n)&&!/etaCircle/.test(n)) return 'ChiralEta'; if(/alex|circ|cos_/.test(n)) return 'Walls'; return 'Odometer'; };
    const order=['Gluing','Eis','Riley','Monodromy','Ladder','APoly','Chirality','Walls','Bridge','ChiralEta','Odometer','BHL','D28'];
    const mcol={Gluing:GOLD,Eis:GOLD,Riley:GOLD,Monodromy:ROSE,Ladder:BLUE,APoly:BLUE,Chirality:ROSE,Walls:ROSE,Bridge:GOLD,ChiralEta:BLUE,Odometer:BLUE,BHL:WHITE,D28:[0.75,0.6,1.0]};
    const mods={}; names.forEach(nm=>{ const m=grp(nm); (mods[m]=mods[m]||[]).push(nm); });
    const tot=names.length; const pos={}; const p=M.points(tot+Object.keys(R.external).length,0.14); let i=0, acc=0;
    order.forEach(m=>{ const list=mods[m]||[]; const a0=acc/tot*TAU, span=list.length/tot*TAU; acc+=list.length;
      list.forEach((nm,j)=>{ const a=a0+(j+0.5)/list.length*span; const rr=2.2+0.35*((j%3)-1), y=0.45*Math.sin(j*1.9);
        pos[nm]=V3(rr*Math.cos(a),y,rr*Math.sin(a)); M.setPt(p,i++,pos[nm],mcol[m]); });
      const am=a0+span/2; lbl(g,m+' '+list.length,'#9fb3c6',3.15*Math.cos(am),0.9,3.15*Math.sin(am),0.26); });
    Object.keys(R.external).forEach((x,j,arr)=>{ const a=j/arr.length*TAU+0.2; pos[x]=V3(4.0*Math.cos(a),-1.1,4.0*Math.sin(a)); M.setPt(p,i++,pos[x],DIM.map(v=>v*2)); });
    M.flush(p); g.add(p);
    const kc=k=>['same-polynomial','same-root','same-value','ladder-step'].includes(k)?0xf2c14e:(['kept-difference','square-of','boundary'].includes(k)?0x2f8dff:(['mirror','contrast'].includes(k)?0xff6f8e:(k==='external'?0x6b7a8a:(k==='analogy-only'?0x555555:0x2a3a4e))));
    const groups={}; R.edges.forEach(e=>{ if(!pos[e.from]||!pos[e.to]) return; const c=kc(e.kind); (groups[c]=groups[c]||[]).push([pos[e.from],pos[e.to]]); });
    Object.entries(groups).forEach(([c,pairs])=>g.add(segs(pairs,+c,+c===0x2a3a4e?0.35:0.6)));
    this.counts={}; R.edges.forEach(e=>this.counts[e.kind]=(this.counts[e.kind]||0)+1); this.nn=names.length; this.ne=R.edges.length; this.mods=mods; this.g=g; },
  enter(){}, change(){},
  step(dt,S,t){ this.g.rotation.y=0.04*t; const c=this.counts, m=this.mods, n=k=>(m[k]||[]).length;
    return [['theorems (nodes)',String(this.nn)],['relations (edges)',String(this.ne)],['Part I (FigureEightAnchors)',String(['Gluing','Eis','Riley','Monodromy','Ladder','APoly','Chirality'].reduce((s,k)=>s+n(k),0))],['η, walls, odometer · BHL',`${n('ChiralEta')+n('Walls')+n('Odometer')} · ${n('BHL')}`],['bridge · D28',`${n('Bridge')} · ${n('D28')}`],['same polynomial / root / value',String((c['same-polynomial']||0)+(c['same-root']||0)+(c['same-value']||0))],['kept difference / square of',String((c['kept-difference']||0)+(c['square-of']||0))],['mirror / contrast',String((c['mirror']||0)+(c['contrast']||0))],['proof steps',String(c['proof-step']||0)],['external (recorded, not proved here)',String(c['external']||0)],['analogy only',String(c['analogy-only']||0)]]; }});

M.run({ title:'Count Me as One, with the Dirac Anchor Recovered', byline:'JEROMIE BEASLEY · MIXER', note:'every readout is computed live', feed, eyes,
  film:['gluing','branches','riley','trefoil','catmap','ladder','apoly','chirality','wall','eta','odometer','signature','ruler','surgery','repairs','grades','relations'] });
})();
