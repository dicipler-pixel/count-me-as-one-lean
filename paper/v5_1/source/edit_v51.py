# SCRIPT: CMAO-V51-EDITS-01
import sys
p='/home/claude/v51/build/cmao_v51.tex'
s=open(p,encoding='utf-8').read()
R=[]
def rep(a,b):
    global s
    n=s.count(a)
    if n!=1: print('MATCH COUNT',n,'for:',a[:90]); sys.exit(1)
    s=s.replace(a,b)

rep(r"\date{20 November 2026}", r"\date{21 November 2026}")

rep(r"Part~I was written with Claude (Anthropic); Part~II was assembled by Ink Between the Stars (a Grok bot) and completed with Claude.",
    r"Part~I was written with Claude (Anthropic). Part~II was assembled by Ink Between the Stars (a Grok bot), which also prepared the statements of its Lean libraries; Lean Green PR Machine (a Grok bot) wrote those libraries, DiracTimeD25, CMaOBridge and D28; Part~II was completed with Claude.")

rep(r"the Lean source; Dirac Time v3.0.1, pp.~36--37.",
    r"the Lean source; Dirac Time v3.0.1 \cite{DiracTime}, pp.~36--44 (Section~13); KnotInfo's entries for $3_1$, $8_{19}$, $13a_{3542}$ and $13a_{4018}$ \cite{KnotInfo}.")

old_n18=s[s.index(r"For the zero surgery on a knot and a $U(1)$ character, $\rho$ equals the Levine--Tristram signature"):s.index(r"accounts for the sign is not fixed here.")+len(r"accounts for the sign is not fixed here.")]
rep(old_n18, r"For the zero surgery $S_K$ on a knot and the $U(1)$ character $\chi_\omega$ sending the meridian to $\omega$, the $\rho$ invariant of the twisted odd signature operator is the Levine--Tristram signature with a sign fixed by convention; Dirac Time v3.0.1, Section~13.4, writes it $\rho(S_K,\chi_\omega)=-\sigma_K(\omega)$ and checks its values against KnotInfo's signature functions \cite{DiracTime,KnotInfo} \dtag{\textsf{\small[N18\,$\cdot$\,DERIVED]}}. Its Theorem~13.2 (DT-T38) uses the character $e^{4\pi i\alpha}$ and finds $\rho=+2$ on $\alpha\in(\tfrac1{12},\tfrac5{12})$ for the trefoil. That is the window $2\alpha\in(\tfrac16,\tfrac56)$ of N17 below, where $\sigma=-2$. In KnotInfo's convention the right-handed trefoil, the closure of the positive braid $\sigma_1^3$, has $\sigma=-2$ on that window; the left-handed one has $+2$, since mirroring negates the signature (N49). So Dirac Time's trefoil is the right-handed one: $\rho=-\sigma=+2$. The signature check of Appendix~\ref{app:sig} recomputes these values from KnotInfo's Seifert matrices. It also explains a sign flip met in the Dirac Time census files: the Seifert matrix that SnapPy builds from a braid or a planar diagram gives minus KnotInfo's signature on every knot and every $\omega$ tested, on the same diagram (same writhe) with the same Alexander polynomial. That flip is a convention of the Seifert matrix, not a change of handedness. BHL's trefoil is the left-handed one (N32), the mirror of Dirac Time's, so in Dirac Time's convention its window carries $\rho=-2$.")

rep(r"The knot names and the agreement of those invariants are taken from the Dirac Time map and were not checked here.",
    r"Dirac Time v3.0.1, Section~13.5, names the pair: $13a_{3542}$ and the mirror of $13a_{4018}$, with common Alexander polynomial $1-7t+23t^2-48t^3+72t^4-83t^5+72t^6-48t^7+23t^8-7t^9+t^{10}$ and a window $\alpha\in(0.10971,0.11522)$ for $\omega=e^{4\pi i\alpha}$, on which $\sigma=-2$ for $13a_{3542}$ and $+2$ for the mirror of $13a_{4018}$. The signature check of Appendix~\ref{app:sig} confirms from KnotInfo's Seifert matrices that both knots have this Alexander polynomial, that its two unit-circle roots in the upper half sit at $\alpha=0.10971$ and $0.11522$, and that between them KnotInfo's $13a_{3542}$ and $13a_{4018}$, as stored, both read $\sigma=-2$: only the mirror of $13a_{4018}$ reads $+2$, so the mirror in the pair is required. The agreement of HOMFLY, Jones, Khovanov and knot Floer data is KnotInfo's and is not recomputed here.")

rep(r"The ``two or three Dirac builds that really had it all'' were not found in the four chats read.",
    r"A wider search by the Grok crew (issue~\#1 of \texttt{count-me-as-one-lean}, 20 November 2026) through every chat held on their machine adds two builds. The December 2025 \texttt{dirac\_review} chat builds a $\mathrm{Spin}^c$ operator $D_A$ on $S^3\setminus N(8_{19})$ with APS boundary conditions, the most complete of all, but on three broken premises: $8_{19}$ is not hyperbolic (B1), the boundary $\eta$ is taken on the flat-torus operator, where it is $0$ (N9--N10), and a bulk average is subtracted in place of a $\rho$ difference. The September 2026 circle operator $D_a=-i\,d/d\theta+a$ is correct, and the raw $\eta$ difference that becomes the $\rho$ ruler starts there; it is the operator of the circle odometer, but it carries no knot. The chiral seed and the $\rho$ ruler first meet in Dirac Time v3.0.1, Section~13, which is a paper, not a chat. The ``two or three Dirac builds that really had it all'' were not found in any chat held on the machines searched.")

rep(r"matches N17 after the substitution $2\alpha$ and a sign convention.", r"matches N17 after the substitution $2\alpha$, with $\rho=-\sigma$.")
rep(r"The sign of the window is discussed under N18.", r"The sign of the window makes Dirac Time's trefoil the right-handed one (N18).")

rep(r"B6 & ``trefoil $\eta=0$ for all $k$'' (closest located text: ``(CN=3): \dots $\eta\approx0$ (trivial holonomy)'', M099, sweep line 1435). & With a $U(1)$ twist the trefoil's $\rho$ invariant is its Levine--Tristram signature, $-2$ on $(\tfrac16,\tfrac56)$. & With a $U(1)$ twist, $\rho=\sigma=-2$ on $(\tfrac16,\tfrac56)$ for the right-handed trefoil (N17).",
    r"B6 & ``trefoil $\eta=0$ for all $k$'' (closest located text: ``(CN=3): \dots $\eta\approx0$ (trivial holonomy)'', M099, sweep line 1435). & With a $U(1)$ twist the trefoil's $\rho$ invariant is fixed by its Levine--Tristram signature, $\sigma=-2$ on $(\tfrac16,\tfrac56)$. & With a $U(1)$ twist, $\rho=-\sigma=+2$ on $(\tfrac16,\tfrac56)$ for the right-handed trefoil, in Dirac Time's convention (N17, N18).")

rep(r"N18 & DERIVED & APS $\rho_\alpha=\eta(D_\alpha)-\eta(D_0)$ of zero surgery equals the Levine--Tristram signature, up to sign convention; the DT-T38 window ($\rho=+2$ on $(\tfrac1{12},\tfrac5{12})$ for $\chi_{e^{4\pi i\alpha}}$) is N17 at $2\alpha$ with the sign of the mirror trefoil & --- & cited, APS II; DT-T38; handedness of DT-T38 not named in the pages read\\",
    r"N18 & DERIVED & APS $\rho$ of zero surgery with a $U(1)$ twist is $\rho(S_K,\chi_\omega)=-\sigma_K(\omega)$ in Dirac Time's convention; the DT-T38 window ($\rho=+2$ on $(\tfrac1{12},\tfrac5{12})$ for $\chi_{e^{4\pi i\alpha}}$) is N17 at $2\alpha$, so Dirac Time's trefoil is right-handed, the mirror of BHL's (N32) & --- & cited, APS II, DT Section~13.4; handedness from KnotInfo's Seifert matrix, App.~\ref{app:sig}\\")

rep(r"N36 & ANALOGY & DT-O6 bridge: the gate generalises to non-torus pairs where only Levine--Tristram/$\rho$ separate & --- & not computed here\\",
    r"N36 & ANALOGY & DT-O6 bridge: the gate generalises to non-torus pairs where only Levine--Tristram/$\rho$ separate; the pair is $13a_{3542}$ and the mirror of $13a_{4018}$ & --- & bridge not computed; Alexander polynomial, window and signs checked from KnotInfo, App.~\ref{app:sig}\\")

rep(r"\item The ``two or three Dirac builds that really had it all'' (Jeromie's words) were not among the four builds read; they are still to be found.",
    r"\item The ``two or three Dirac builds that really had it all'' (Jeromie's words) were not found in any chat held on the machines searched; they are most likely in older chats held elsewhere.")
rep("\\item The handedness behind the sign of DT-T38 (N18).\n", "\\item The HOMFLY, Jones, Khovanov and knot Floer agreement of the DT-O6 pair, recomputed rather than read from KnotInfo.\n")

rep(r"The sign convention of N18 and the 13-crossing data of DT-O6 are not verified here.",
    r"The handedness of N18 and the signature window of the DT-O6 pair are checked from KnotInfo's Seifert matrices in Appendix~\ref{app:sig}; the other DT-O6 invariants are KnotInfo's. An earlier local run of the same harness by the Grok crew at commit \texttt{3a4902c} also passed (280 theorems, 25 false controls, 280 nodes, 238 edges), but it reused a prebuilt Mathlib and rebuilt only the project's own modules; the public run of Appendix~\ref{app:ci} builds everything from the pinned toolchain and is the full check. The Lean libraries of Part~II were written at commits \texttt{cb2f1b2} (D25), \texttt{6c34d2c} (D27), \texttt{f4e3726} (combined port and bridge) and \texttt{aa1464b} to \texttt{3a4902c} (D28) of the Grok crew's working tree.")

rep(r"(entries $3_1$ and $4_1$: unknotting number,", r"(entries $3_1$, $4_1$, $8_{19}$, $13a_{3542}$ and $13a_{4018}$: Seifert matrix, braid and PD notation, unknotting number,")

rep("\\VerbatimInput{cmao_checks_v1_output.txt}\n",
    "\\VerbatimInput{cmao_checks_v1_output.txt}\n\\section{Signature convention check}\\label{app:sig}\nThe script below reads KnotInfo's stored Seifert matrices, braids and planar diagrams for $3_1$, $8_{19}$, $13a_{3542}$ and $13a_{4018}$ and computes Levine--Tristram signatures at $\\omega=e^{2\\pi i t}$ both from KnotInfo's matrix and from the Seifert matrix SnapPy builds from the same diagram. Why it proves what it claims: if the two matrices give opposite signatures at every $t$ while the writhe and the Alexander polynomial agree, the knot is the same and only the sign convention differs; if the signatures disagreed somewhere without being opposite, or the Alexander polynomials differed, a chirality or diagram error would show instead.\n\\VerbatimInput{sig_flip_check_v1.py}\n\\noindent Output:\n\\VerbatimInput{sig_flip_check_v1_output.txt}\n")
open(p,'w',encoding='utf-8').write(s)
print('ok')
