"""SCRIPT: COUNT-ME-AS-ONE-PLATES-PART2-01
Three plates for Part II of Count Me as One with the Dirac Anchor Recovered, drawn with the
same deterministic renderer as the film (luminous point samples, bloom, composited equations).
Every object is computed from the mathematics it depicts:
 P9  the trefoil's Alexander wall on the unit circle sits at the regular tetrahedron shape e^{+-i pi/3};
     the figure-eight's Alexander function stays >= 1 and never touches zero.
 P10 the circle odometer: floor(a1)-floor(a0) = (a1-a0) + (eta(a1)-eta(a0))/2, eta(a) = 1 - 2 frac(a).
 P11 the raw difference phi_0 - M: positive coefficients (gold) built from summands that are not (blue).
Point samples are rendering samples only, never a density of anything physical.
"""
import io, sys, math
import numpy as np
from PIL import Image
sys.path.insert(0, str(__import__('pathlib').Path(__file__).resolve().parent))
import render_knots as rk
from render_knots import GOLD, BLUE, ROSE, WHITE, RNG, tetra, rotz

def eq_image(tex):
    from matplotlib.mathtext import math_to_image
    from matplotlib.font_manager import FontProperties
    b = io.BytesIO(); math_to_image(tex, b, prop=FontProperties(size=22), dpi=160, color='black', format='png'); b.seek(0)
    ink = Image.open(b).convert('L'); im = Image.new('RGBA', ink.size, (232, 240, 248, 0)); im.putalpha(Image.eval(ink, lambda x: 255 - x)); return im

class Plates(rk.Renderer):
    def shoot(self, scene, tag, eq, foot, t=6.0):
        c = self.c; g = self.g
        self.fbo.use(); c.viewport = (0, 0, self.w, self.h); c.clear(0, 0, 0, 1)
        c.enable(g.BLEND | g.PROGRAM_POINT_SIZE); c.blend_func = (g.SRC_ALPHA, g.ONE)
        labels = scene(t)
        c.disable(g.BLEND); self.scene.use(0); self.sfb[0].use(); c.viewport = (0, 0, self.w//4, self.h//4)
        self.blur['direction'] = (4/self.w, 0); self.bvao.render()
        self.small[0].use(0); self.sfb[1].use(); self.blur['direction'] = (0, 4/self.h); self.bvao.render()
        self.out.use(); c.viewport = (0, 0, self.w, self.h); self.scene.use(0); self.small[1].use(1); self.qvao.render()
        im = Image.frombytes('RGB', (self.w, self.h), self.out.read(components=3, alignment=1)).transpose(Image.Transpose.FLIP_TOP_BOTTOM)
        self.text(im, (540, 46), tag, 21, '#8fbfd6', True, 'mm')
        for (xy, txt, size, col, bold) in labels: self.text(im, xy, txt, size, col, bold, 'mm')
        e = eq_image(eq); im.paste(e, (int(540*self.s - e.width/2), int(1060*self.s - e.height/2)), e)
        self.text(im, (540, 1150), foot, 21, '#e3edf2', False, 'mm')
        return im.crop((0, 0, self.w, int(1200*self.s)))

    # P9 -------------------------------------------------------------
    def wall(self, t):
        self.camera(t, eye_dist=8, elev=3.0, yaw0=.35, spin=0, scale=2.0, target=(0, 0, .15))
        a = np.linspace(0, 1, 2400, endpoint=False)
        circ = np.c_[np.cos(2*np.pi*a), np.sin(2*np.pi*a), 0*a]
        self.lines(np.r_[circ, circ[:1]], WHITE*.35)
        self.pts(circ.repeat(8, 0) + RNG.normal(0, .012, (len(circ)*8, 3)), WHITE*.55, t)
        s = .28
        d31 = 2*np.cos(2*np.pi*a) - 1; d41 = 3 - 2*np.cos(2*np.pi*a)
        tre = np.c_[circ[:, :2], s*d31]; fig = np.c_[circ[:, :2], s*d41]
        self.pts(tre.repeat(10, 0) + RNG.normal(0, .014, (len(a)*10, 3)), ROSE, t)
        self.pts(fig.repeat(8, 0) + RNG.normal(0, .014, (len(a)*8, 3)), BLUE, t)
        for k in range(0, len(a), 200):  # sparse stems from the circle to each curve
            self.lines([circ[k], tre[k]], ROSE*.12); self.lines([circ[k], fig[k]], BLUE*.10)
        labels = []
        for sg in (1, -1):
            z = np.array([.5, sg*3**.5/2, 0.])
            self.bead(z, GOLD, t, r=.03, n=2600)
            P, _ = tetra(z + np.array([0, 0, .22]), .16, .4*sg); self.pts(P, GOLD*1.2, t)
            x, y = self.project(z); labels.append(((x + 95, y + (34 if sg < 0 else -10)), 'e^(%siπ/3)' % ('' if sg > 0 else '−'), 20, '#f6c56a', True))
        xr, yr = self.project(np.array([-1, 0, s*(-3)])); labels.append(((xr, yr + 34), 'Δ₃₁ = 2cos2πα − 1', 19, '#ff9fb0', True))
        xb, yb = self.project(np.array([-1, 0, s*5])); labels.append(((xb, yb - 30), 'Δ₄₁ = 3 − 2cos2πα  ≥ 1', 19, '#7fbaff', True))
        labels.append(((540, 985), 'White: the unit circle.  Heights: the Alexander functions on it.', 19.5, '#b3c9d3', False))
        return labels

    # P10 ------------------------------------------------------------
    def odometer(self, t):
        self.camera(t, eye_dist=8, elev=1.6, yaw0=.32, spin=0, scale=2.45, target=(0, 0, .45))
        a0 = .25; A = np.linspace(a0, 2.75, 3000)
        fr = A - np.floor(A); eta = 1 - 2*fr
        X = (A - 1.5)*1.25
        stair = np.floor(A) - math.floor(a0)
        drift = A - a0
        half = .5*(eta - (1 - 2*(a0 - math.floor(a0))))
        sc = .45
        rows = [(stair, GOLD, .0), (drift, BLUE, .55), (half, ROSE, -.55)]
        for vals, col, yoff in rows:
            P = np.c_[X, np.full_like(X, yoff), sc*vals]
            self.pts(P.repeat(6, 0) + RNG.normal(0, .011, (len(P)*6, 3)), col, t)
        for n in (1, 2):
            x = (n - 1.5)*1.25
            self.lines([[x, 0, -.35], [x, 0, sc*2.3]], WHITE*.30)
            self.bead(np.array([x, 0, sc*(n - math.floor(a0))]), GOLD, t, r=.025, n=1500)
        labels = []
        def lab(xyz, txt, col, dy=0):
            x, y = self.project(np.array(xyz)); labels.append(((x, y + dy), txt, 19, col, True))
        lab([(2.75 - 1.5)*1.25, .55, sc*(2.5)], 'drift  a₁ − a₀', '#7fbaff', -26)
        lab([(2.75 - 1.5)*1.25, -.55, sc*(-.5)], '½(η(a₁) − η(a₀))', '#ff9fb0', 30)
        lab([(2.75 - 1.5)*1.25, 0, sc*2], 'crossings  ⌊a₁⌋ − ⌊a₀⌋', '#f6c56a', -30)
        labels.append(((540, 985), 'Gold = blue + rose at every a₁.  Lines: the integers crossed.', 19.5, '#b3c9d3', False))
        return labels

    # P11 ------------------------------------------------------------
    def ruler(self, t):
        self.camera(t, eye_dist=8, elev=2.2, yaw0=.3, spin=0, scale=2.0, target=(0, .2, .45))
        N = 60
        def series(term_fn):
            out = np.zeros(N + 1, dtype=object); out[:] = 0
            for n in range(N + 1):
                p = term_fn(n)
                for i, v in enumerate(p[:N + 1]): out[i] += v
            return out
        def negpoch(m):
            p = [1] + [0]*N
            for j in range(1, m + 1):
                q = p[:]
                for i in range(N + 1 - j): q[i + j] += p[i]
                p = q
            return p
        def sh(p, k): return ([0]*k + p)[:N + 1]
        phi0 = series(lambda n: sh(negpoch(2*n + 1), n)); M = series(lambda n: sh(negpoch(2*n + 1), 2*n))
        d = [int(x) for x in (phi0 - M)]
        s1 = sh(negpoch(3), 1); s1 = [s1[i] - (s1[i - 1] if i else 0) for i in range(N + 1)]  # q(1-q)(-q)_3
        top = math.sqrt(max(d[1:]))
        f = lambda v: math.copysign(math.sqrt(abs(v)), v)/top*1.25
        for k in range(1, N + 1):
            x = (k - N/2)*.052
            h = f(d[k]); n = max(30, int(abs(h)*700))
            P = np.c_[np.full(n, x), np.zeros(n), np.linspace(0, h, n)] + RNG.normal(0, .006, (n, 3)); self.pts(P, GOLD, t)
            if k < len(s1) and s1[k]:
                h2 = .18*(1 if s1[k] > 0 else -1); m = 140
                P = np.c_[np.full(m, x), np.full(m, .6), np.linspace(0, h2, m)] + RNG.normal(0, .006, (m, 3)); self.pts(P, BLUE, t)
        self.lines([[(-N/2)*.052, 0, 0], [(N/2)*.052, 0, 0]], WHITE*.35); self.lines([[(-N/2)*.052, .6, 0], [(N/2)*.052, .6, 0]], WHITE*.25)
        labels = []
        x, y = self.project(np.array([(N/2 - 6)*.052, 0, f(d[N])])); labels.append(((x - 40, y - 34), 'φ₀ − M  (all > 0 to q¹²⁸)', 19, '#f6c56a', True))
        x, y = self.project(np.array([(-N/2 + 3)*.052, .6, -.12])); labels.append(((x + 60, y + 40), 'one summand q(1−q)(−q)₃: signs only', 19, '#7fbaff', True))
        labels.append(((540, 985), 'Gold heights: square roots of the coefficients of q¹ … q⁶⁰.', 19.5, '#b3c9d3', False))
        return labels

if __name__ == '__main__':
    out = rk.ROOT / 'plates2'; out.mkdir(exist_ok=True)
    r = Plates(1080, 1350)
    r.shoot(r.wall, "THE TREFOIL'S WALL IS THE REGULAR SHAPE", r'$|z|=1,\ \Delta_{3_1}(z)=0\ \Rightarrow\ z^2-z+1=0$', 'The chiral knot jumps exactly where the tetrahedron is regular.').save(out/'p9_wall.jpg', quality=92)
    r.shoot(r.odometer, 'THE CIRCLE ODOMETER', r'$\lfloor a_1\rfloor-\lfloor a_0\rfloor=(a_1-a_0)+\frac{1}{2}\,(\eta(a_1)-\eta(a_0))$', 'The drift term is the raw difference the old formula threw away.').save(out/'p10_odometer.jpg', quality=92)
    r.shoot(r.ruler, 'THE BOUNDARY RULER', r'$\phi_0-M=q+q^2+2q^3+3q^4+3q^5+\cdots$', 'Positive as a sum, mixed term by term: the sign lives in the whole.').save(out/'p11_ruler.jpg', quality=92)
    print('done')
