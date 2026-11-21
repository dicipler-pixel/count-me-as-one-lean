# SCRIPT: COUNT-ME-AS-ONE-HTML-V5-01
# Builds the self-contained HTML edition of the v5 paper from the same .tex as the PDF (pandoc),
# with the plates embedded, MathJax inlined (offline), and the Lean, harness and checks appendices.
import base64, html, pathlib, re
B=pathlib.Path('/home/claude/final/build'); H=pathlib.Path('/home/claude/final/html')
s=(H/'body2.html').read_text()
title=s[s.index('<header'):s.index('</header>')+9]
body=s[s.index('</header>')+9:s.index('</body>')]
def b64(m):
    p=B/m.group(1); return 'src="data:image/jpeg;base64,'+base64.b64encode(p.read_bytes()).decode()+'"'
body=re.sub(r'src="(plates/[^"]+)"',b64,body)
body=re.sub(r'(<a href="#app:ci"[^>]*>)\[app:ci\]</a>',r'\1D</a>',body)
body=re.sub(r'(<a href="#app:checks"[^>]*>)\[app:checks\]</a>',r'\1E</a>',body)
# grade chips
body=re.sub(r'<span class="sans-serif">\[([KNB]\d+[abc]?)[\s  ]*<span class="math inline">\\\(\\cdot\\\)</span>[\s  ]*(EXACT|DERIVED|MODEL|ANALOGY|REPAIRED)\]</span>',lambda m:f'<span class="chip c{m.group(2)}">{m.group(1)} · {m.group(2)}</span>',body)
body=body.replace('<span class="sans-serif">[T]</span>','<span class="chip cT">T</span>')
body=re.sub(r'<span class="sans-serif">\[T:',r'<span class="tag">[T:',body)
for g in 'CTRO': body=body.replace(f'<span class="sans-serif">[{g}]</span>',f'<span class="chip g{g}">{g}</span>')
def det(name,path,lang=''):
    t=html.escape(pathlib.Path(path).read_text())
    return f'<details><summary>{name}</summary><pre><code>{t}</code></pre></details>'
L=B/'lean'
app='<h1 id="appendix">Appendices</h1><p>The complete Lean source of <code>count-me-as-one-lean</code> at commit <code>cee88f2</code> (Lean v4.36.0-rc2, Mathlib <code>e8ba86fa</code>), the false controls, the harness, the record of the GitHub Actions run, and the checks script with its output. Open any file to read it.</p>'
app+='<h2>A. Lean source</h2><h3>Part I: FigureEightAnchors</h3>'+''.join(det(f+'.lean',L/(f+'.lean')) for f in ['Eisenstein','Gluing','Riley','Chirality','Monodromy','Ladder','APoly'])
app+='<h3>Part II: DiracTimeD25</h3>'+''.join(det(f+'.lean',L/(f+'.lean')) for f in ['ChiralEta','AlexanderWall','CircleOdometer','BhlBoundaryTest'])
app+='<h3>The bridge</h3>'+det('CMaOBridge.lean',L/'CMaOBridge.lean')
app+='<h3>D28: bounded identities, counts and arithmetic</h3>'+''.join(det(f+'.lean',L/(f+'.lean')) for f in ['Easy','Algebra','RawDiff','FastModel','FastPsi','Qq2Table','Eq15','Eq17','RawDiffPos'])
app+='<h2>B. False controls</h2>'+det('FalseControls (25 files)',L/'FalseControls.txt')
app+='<h2>C. Verification harness</h2>'+det('scripts/verify.py',L/'verify.py')
app+='<h2 id="app:ci">D. The GitHub Actions run</h2><p>Workflow <code>Lean proof check</code> on commit <code>cee88f2</code> of <code>dicipler-pixel/count-me-as-one-lean</code>, 20 November 2026, 23:36–23:46 UTC.</p><pre class="ci"><code>'+html.escape((B/'ci_output.txt').read_text())+'</code></pre>'
app+='<h2 id="app:checks">E. Checks script</h2>'+det('cmao_checks_v1.py',B/'cmao_checks_v1.py')+'<pre class="ci"><code>'+html.escape((B/'cmao_checks_v1_output.txt').read_text())+'</code></pre>'
nav='<nav><a href="#count-me-as-one">Part I</a><a href="#the-dirac-anchor-recovered">Part II</a><a href="#sec:ledger">Ledger</a><a href="#appendix">Lean and checks</a><a href="https://github.com/dicipler-pixel/count-me-as-one-lean">GitHub</a></nav>'
css='''
:root{color-scheme:dark}
body{margin:0;background:#05070b;color:#dfe7ef;font-family:"Iowan Old Style","Palatino Linotype",Georgia,serif;line-height:1.62;font-size:17.5px}
main{max-width:900px;margin:0 auto;padding:40px 24px 110px}
nav{position:sticky;top:0;z-index:5;background:#05070bee;border-bottom:1px solid #1d2a3a;padding:10px 0;margin-bottom:18px;display:flex;gap:18px;flex-wrap:wrap;font-family:"DejaVu Sans",sans-serif;font-size:13px}
nav a{color:#9fd0ff;text-decoration:none}
header h1.title{font-size:40px;line-height:1.15;margin:0;color:#f6e7c1}
header .subtitle{color:#b9c6d2;font-size:19px}
header .author,header .date{margin:4px 0;color:#dfe7ef}
.abstract{background:#0b111a;border:1px solid #1d2a3a;border-radius:10px;padding:6px 22px 12px;margin:20px 0}
h1{color:#f6e7c1;font-size:30px;margin:56px 0 10px;border-bottom:1px solid #1d2a3a;padding-bottom:6px}
h2{color:#f2c14e;font-size:24px;margin:40px 0 10px;font-weight:600}
h3{color:#79b8ff;font-size:19px;margin:24px 0 6px}
h6{font-size:16px;color:#f2c14e}
.theorem,.proposition,.lemma,.corollary,.remark,.definition{border-left:3px solid #f2c14e;padding:4px 0 4px 16px;margin:18px 0;background:linear-gradient(90deg,#0d1420,#05070b 70%)}
.theorem em,.proposition em,.corollary em,.remark em{font-style:normal}
.corollary,.remark{border-left-color:#79b8ff}
.proof{margin:0 0 14px 19px;color:#c9d4de}
.center{text-align:center;color:#b9c6d2}
code{font-family:"DejaVu Sans Mono",Menlo,monospace;font-size:13px;color:#9fd0ff;background:#0c1520;padding:1px 5px;border-radius:4px}
pre code{background:none;padding:0;color:#cfe3f4}
pre{background:#0a1018;border:1px solid #1d2a3a;border-radius:8px;padding:12px;overflow:auto;max-height:520px;font-size:12.5px;line-height:1.45}
details{margin:6px 0}summary{cursor:pointer;color:#f2c14e;font-family:"DejaVu Sans Mono",monospace;font-size:14px}
.chip{font-family:"DejaVu Sans",sans-serif;font-size:11px;font-weight:700;padding:1px 7px;border-radius:9px;letter-spacing:.04em;vertical-align:2px;white-space:nowrap}
.cEXACT,.gT,.cT{background:#3a2c08;color:#f6cd6a}.cDERIVED{background:#0f2c47;color:#7fbaff}.cMODEL{background:#1d2b3c;color:#9ec4e8}.cANALOGY{background:#2a2335;color:#c9b3f0}.cREPAIRED{background:#3a1820;color:#ff9fb0}
.gC{background:#1d2b3c;color:#9ec4e8}.gR{background:#0f2c47;color:#7fbaff}.gO{background:#2a2a2a;color:#c8c8c8}
.tag{font-family:"DejaVu Sans",sans-serif;font-size:12px;color:#8fa6b8}
table{border-collapse:collapse;width:100%;font-size:13.5px;margin:14px 0;display:block;overflow-x:auto}
th,td{border-bottom:1px solid #1d2a3a;padding:6px 8px;vertical-align:top;text-align:left}
th{color:#f2c14e;font-family:"DejaVu Sans",sans-serif;font-size:12.5px}
figure{margin:28px 0}figure p{display:flex;gap:12px;justify-content:center;margin:0}figure img{width:48%;border-radius:10px;border:1px solid #1d2a3a}
figure p:only-child img:only-child{width:60%}
figcaption{font-size:14.5px;color:#a9b6c3;margin:10px 0 0;line-height:1.5}
mjx-container[display="true"]{overflow:visible!important;margin:14px 0!important}mjx-container svg{color:#e8eef4}
.thebibliography{font-size:14.5px;color:#b8c4cf}
a{color:#79b8ff}
pre.ci{max-height:none}
@media(max-width:800px){figure p{flex-direction:column}figure img{width:100%}}
'''
MJ=pathlib.Path('/home/claude/npmx/node_modules/mathjax/es5/tex-svg.js').read_text()
doc=f'''<!doctype html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>Count Me as One, with the Dirac Anchor Recovered — Jeromie Beasley</title>
<script>window.MathJax={{tex:{{inlineMath:[["\\\\(","\\\\)"]],displayMath:[["\\\\[","\\\\]"]]}},svg:{{fontCache:"global"}}}};</script>
<script>{MJ}</script>
<style>{css}</style></head><body><main>{nav}{title}{body}{app}</main></body></html>'''
out=pathlib.Path('/home/claude/deliver/Count_Me_as_One_Dirac_Anchor_Recovered_v5.html'); out.write_text(doc)
print(out, len(doc)//1024,'KB')
